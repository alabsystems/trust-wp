// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    closure::{CaptureField, CaptureKind, ClosureCaptureInfo},
    formula::{ExprSort, PureExpr},
};
use trust_wp_driver::StdSpec;

use super::body_extraction::{try_extract_closure_body, try_extract_closure_body_with_effects};
use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

fn capture_kind_from_rustc(capture: &rustc_middle::ty::CapturedPlace<'_>) -> CaptureKind {
    match capture.info.capture_kind {
        rustc_middle::ty::UpvarCapture::ByValue | rustc_middle::ty::UpvarCapture::ByUse => {
            CaptureKind::ByValue
        }
        rustc_middle::ty::UpvarCapture::ByRef(
            rustc_middle::ty::BorrowKind::Mutable | rustc_middle::ty::BorrowKind::UniqueImmutable,
        ) => CaptureKind::ByMutRef,
        rustc_middle::ty::UpvarCapture::ByRef(rustc_middle::ty::BorrowKind::Immutable) => {
            CaptureKind::ByRef
        }
    }
}

fn capture_field_from_rustc<'tcx>(
    tcx: TyCtxt<'tcx>,
    capture: &rustc_middle::ty::CapturedPlace<'tcx>,
) -> CaptureField {
    let sort = ty_to_expr_sort_enriched(tcx, capture.place.ty()).unwrap_or(ExprSort::Int);
    let name = capture_field_name(capture);
    CaptureField::new(name, sort, capture_kind_from_rustc(capture))
}

/// Return the caller-side name used to identify a capture in encoder
/// projection assertions.
///
/// For root-variable captures (`|| use(x)`) this is the `var_ident` (`"x"`).
/// For RFC-2229 disjoint captures (`|| use(p.1)`) `var_ident` is the root
/// `"p"`, which collides with the outer fn's declaration of `p` and a
/// different sort (the projected field's sort vs. the root variable's sort).
/// Use `to_symbol()` for projected captures so the encoder declares a unique
/// caller-side name (e.g., `_ref__p__1`) at the projected field's sort.
/// See designs/2026-05-19-closure-body-extraction-gap.md (bug/962). (#8)
fn capture_field_name(capture: &rustc_middle::ty::CapturedPlace<'_>) -> String {
    let var_ident = capture.var_ident.as_str().to_string();
    let symbol = capture.to_symbol().to_string();
    if is_projected_capture(&var_ident, &symbol) {
        symbol
    } else {
        var_ident
    }
}

/// Detect whether `symbol` describes a projected field capture of `var_ident`.
///
/// Mirrors `parsing::arg_names::detect_field_projection`. For `p.1` captured
/// by `&mut`, rustc produces `to_symbol() = "_ref__p__1"`; for by-value
/// projected captures it is `"p__1"`. The double-underscore separator after
/// the root variable distinguishes projection from plain captures.
fn is_projected_capture(var_ident: &str, symbol: &str) -> bool {
    let stripped = symbol.strip_prefix("_ref__").unwrap_or(symbol);
    stripped
        .strip_prefix(var_ident)
        .and_then(|rest| rest.strip_prefix("__"))
        .is_some_and(|tail| tail.chars().all(|c| c.is_ascii_digit() || c == '_'))
}

pub(super) fn build_closure_capture_info(
    tcx: TyCtxt<'_>,
    closure_def_id: DefId,
    param_name: Option<String>,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<ClosureCaptureInfo> {
    let closure_local_def_id = closure_def_id.as_local()?;
    let has_user_spec = user_specs.contains_key(&closure_def_id);
    let captures = tcx.closure_captures(closure_local_def_id);
    let typed_captures: Vec<CaptureField> = captures
        .iter()
        .map(|capture| capture_field_from_rustc(tcx, capture))
        .collect();
    let def_id_str = tcx.def_path_str(closure_def_id);

    if !has_user_spec && captures.is_empty() {
        let (body_expr, param_names_vec) =
            try_extract_closure_body(tcx, closure_def_id, user_specs, trait_specs, extern_specs)?;
        return Some(
            ClosureCaptureInfo::new(def_id_str, Vec::new())
                .with_param_name(param_name)
                .with_body_expr(Some(body_expr))
                .with_param_names(Some(param_names_vec))
                .with_ensures_exprs(None),
        );
    }
    let (body_expr, param_names, ensures_exprs, requires_exprs) = if has_user_spec {
        let extracted_with_effects = try_extract_closure_body_with_effects(
            tcx,
            closure_def_id,
            &typed_captures,
            user_specs,
            trait_specs,
            extern_specs,
        );
        let (body_expr, param_names, synthesized_ensures) = extracted_with_effects
            .map_or((None, None, None), |(expr, names, ensures)| {
                (Some(expr), Some(names), ensures)
            });
        let ensures_exprs = user_specs.get(&closure_def_id).and_then(|spec| {
            if spec.ensures.is_empty() {
                return None;
            }
            let exprs: Vec<PureExpr> = spec
                .ensures
                .iter()
                .filter_map(|ensures| trust_wp_core::contract_parser::parse_contract(ensures).ok())
                .collect();
            (!exprs.is_empty()).then_some(exprs)
        });
        let ensures_exprs =
            if param_name.as_deref() == Some("self") && synthesized_ensures.is_some() {
                synthesized_ensures
            } else {
                ensures_exprs
            };
        // Extract requires expressions for precondition inlining (#2668).
        let requires_exprs = user_specs.get(&closure_def_id).and_then(|spec| {
            if spec.requires.is_empty() {
                return None;
            }
            let exprs: Vec<PureExpr> = spec
                .requires
                .iter()
                .filter_map(|requires| {
                    trust_wp_core::contract_parser::parse_contract(requires).ok()
                })
                .collect();
            (!exprs.is_empty()).then_some(exprs)
        });
        (body_expr, param_names, ensures_exprs, requires_exprs)
    } else {
        let extracted = try_extract_closure_body_with_effects(
            tcx,
            closure_def_id,
            &typed_captures,
            user_specs,
            trait_specs,
            extern_specs,
        );
        extracted.map_or((None, None, None, None), |(expr, names, ensures)| {
            (Some(expr), Some(names), ensures, None)
        })
    };

    Some(
        ClosureCaptureInfo::new(def_id_str, typed_captures)
            .with_param_name(param_name)
            .with_body_expr(body_expr)
            .with_param_names(param_names)
            .with_ensures_exprs(ensures_exprs)
            .with_requires_exprs(requires_exprs),
    )
}
