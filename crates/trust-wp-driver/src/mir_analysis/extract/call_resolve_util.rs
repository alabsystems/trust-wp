// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-site resolution utilities for MIR extraction.
//!
//! Low-level helpers for resolving function call targets, array `.len()`
//! folding, const-generic argument translation, and call-site side-effect
//! isolation. Used by `call_spec`, `spanned_extract`, and
//! `substitution::call_resolution`.

use std::sync::Arc;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, ProjectionElem, Rvalue, StatementKind},
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::{
    call_resolve::extract_call_def_id,
    diagnostics::{record_extraction_diag, ExtractionDiagKind, ExtractionDiagnosticSink},
    effects::CallEffects,
    spec_apply::TranslatedArg,
};

// ── Constants ───────────────────────────────────────────────────────

const MAX_ARRAY_LEN_BACKTRACK_DEPTH: usize = 8;
const MAX_CALL_DEF_BACKTRACK_DEPTH: usize = 8;

// ── Box::new path detection ─────────────────────────────────────────

pub(super) fn is_box_new_call_path(path: &str) -> bool {
    path.ends_with("::new") && path.contains("boxed::Box")
}

// ── Type-level const and array length translation ───────────────────

/// Translate a type-level array length const to a pure expression.
///
/// Supports concrete evaluable constants (`[T; 5]`) and const params
/// (`[T; N]`), returning either `Int(5)` or `Var("N")`.
fn translate_ty_const_len_expr(len_const: rustc_middle::ty::Const<'_>) -> Option<PureExpr> {
    if let Some(value) = len_const.try_to_value() {
        // Trust: ValTree::try_to_scalar removed; ty::Value now exposes try_to_scalar directly.
        let scalar = value
            .try_to_scalar()
            .and_then(|s| s.try_to_scalar_int().ok())?;
        let n = scalar.to_uint(scalar.size());
        return i64::try_from(n).ok().map(PureExpr::Int);
    }
    match len_const.kind() {
        rustc_middle::ty::ConstKind::Param(param) => Some(PureExpr::Var(
            param.name.as_str().to_string(),
            Some(ExprSort::Int),
        )),
        _ => None,
    }
}

fn array_len_from_ty(ty: rustc_middle::ty::Ty<'_>) -> Option<PureExpr> {
    match ty.peel_refs().kind() {
        rustc_middle::ty::TyKind::Array(_, len_const) => translate_ty_const_len_expr(*len_const),
        _ => None,
    }
}

pub(super) fn translate_const_generic_arg_expr(c: rustc_middle::ty::Const<'_>) -> Option<PureExpr> {
    use rustc_middle::ty::TyKind;
    if let Some(value) = c.try_to_value() {
        match value.ty.kind() {
            TyKind::Int(_) => {
                // Trust: ValTree::try_to_scalar removed; use ty::Value::try_to_scalar.
                let scalar = value
                    .try_to_scalar()
                    .and_then(|s| s.try_to_scalar_int().ok())?;
                let bits = scalar.to_int(scalar.size());
                return i64::try_from(bits).ok().map(PureExpr::Int);
            }
            TyKind::Uint(_) => {
                // Trust: ValTree::try_to_scalar removed; use ty::Value::try_to_scalar.
                let scalar = value
                    .try_to_scalar()
                    .and_then(|s| s.try_to_scalar_int().ok())?;
                let bits = scalar.to_uint(scalar.size());
                return i64::try_from(bits).ok().map(PureExpr::Int);
            }
            TyKind::Bool => {
                // Trust: ValTree::try_to_scalar removed; use ty::Value::try_to_scalar.
                let scalar = value
                    .try_to_scalar()
                    .and_then(|s| s.try_to_scalar_int().ok())?;
                return Some(PureExpr::Bool(scalar.to_uint(scalar.size()) != 0));
            }
            _ => {}
        }
    }
    match c.kind() {
        rustc_middle::ty::ConstKind::Param(param) => {
            // Const generic params are typically integral (Int/Uint) or Bool.
            // Int is correct for the vast majority (array lengths, counts).
            // Bool const generics would need the type from GenericParamDef
            // to get ExprSort::Bool — accepted as a known limitation. (#2052)
            Some(PureExpr::Var(
                param.name.as_str().to_string(),
                Some(ExprSort::Int),
            ))
        }
        _ => None,
    }
}

pub(super) fn extend_call_with_const_generic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    func: &Operand<'tcx>,
    translated_args: &mut Vec<TranslatedArg>,
    param_names: &mut Vec<String>,
) {
    use rustc_middle::ty::TyKind;
    let Operand::Constant(box constant) = func else {
        return;
    };
    let TyKind::FnDef(_, substs) = constant.ty().kind() else {
        return;
    };

    let generics = tcx.generics_of(callee_def_id);
    // Skip parent generic args — `substs` contains ALL args (parent + own),
    // but `own_params` only lists this function's own parameters. Without the
    // skip, own_params[i] is paired with the parent's substs[i], causing const
    // generics on methods of generic types to be silently dropped. (#2356)
    for (param_def, generic_arg) in generics
        .own_params
        .iter()
        .zip(substs.iter().skip(generics.parent_count))
    {
        if !matches!(
            param_def.kind,
            rustc_middle::ty::GenericParamDefKind::Const { .. }
        ) {
            continue;
        }
        let Some(actual_const) = generic_arg.as_const() else {
            continue;
        };
        let Some(actual_expr) = translate_const_generic_arg_expr(actual_const) else {
            continue;
        };
        param_names.push(param_def.name.as_str().to_string());
        translated_args.push(TranslatedArg::new(actual_expr));
    }
}

// ── Array length resolution with backtracking ───────────────────────

fn array_len_from_place<'tcx>(
    body: &Body<'tcx>,
    place: rustc_middle::mir::Place<'tcx>,
) -> Option<PureExpr> {
    array_len_from_ty(body.local_decls[place.local].ty)
}

/// Extract `[T; N]::len()` result directly from receiver type information.
fn array_len_from_operand<'tcx>(body: &Body<'tcx>, operand: &Operand<'tcx>) -> Option<PureExpr> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => array_len_from_place(body, *place),
        Operand::Constant(constant) => array_len_from_ty(constant.ty()),
        Operand::RuntimeChecks(_) => None,
    }
}

fn find_local_assignment_rvalue<'a, 'tcx>(
    body: &'a Body<'tcx>,
    bb: BasicBlock,
    local: Local,
) -> Option<&'a Rvalue<'tcx>> {
    body.basic_blocks[bb]
        .statements
        .iter()
        .rev()
        .find_map(|stmt| {
            let StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind else {
                return None;
            };
            (lhs.local == local && lhs.projection.is_empty()).then_some(rvalue)
        })
}

pub(super) fn resolve_call_def_id<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    diagnostics: Option<&ExtractionDiagnosticSink>,
) -> Option<DefId> {
    if let Some(def_id) = extract_call_def_id(func) {
        return Some(def_id);
    }

    let mut current_local = match func {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        // Function pointer calls through references: `(*_1)()` where _1 is
        // a `&fn()` reference. The func operand has a Deref projection; start
        // backtracking from the base local so we can resolve through the
        // reference chain to the underlying FnDef. (#1588)
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.len() == 1
                && matches!(place.projection[0], ProjectionElem::Deref) =>
        {
            Some(place.local)
        }
        _ => None,
    };

    for _ in 0..MAX_CALL_DEF_BACKTRACK_DEPTH {
        let Some(local) = current_local else {
            record_extraction_diag(
                diagnostics,
                "extract/call_resolve_util.rs",
                ExtractionDiagKind::CallResolutionBacktrackFailed,
                "call target backtracking lost the current local",
                None,
            );
            return None;
        };
        let Some(rvalue) = find_local_assignment_rvalue(body, bb, local) else {
            record_extraction_diag(
                diagnostics,
                "extract/call_resolve_util.rs",
                ExtractionDiagKind::CallResolutionBacktrackFailed,
                format!("no assignment found while backtracking call target local {local:?}"),
                None,
            );
            return None;
        };
        match rvalue {
            Rvalue::Use(Operand::Constant(box constant), _)
            | Rvalue::Cast(_, Operand::Constant(box constant), _) => {
                // Check for FnDef directly, or peel a reference layer for
                // promoted constants like `&some_fn`. Promoted `&fn_item`
                // has type `&fn() {fn_item}` where the inner type is FnDef. (#1636)
                let ty = constant.const_.ty();
                let inner_ty = match ty.kind() {
                    rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
                    _ => ty,
                };
                let rustc_middle::ty::TyKind::FnDef(def_id, _) = inner_ty.kind() else {
                    record_extraction_diag(
                        diagnostics,
                        "extract/call_resolve_util.rs",
                        ExtractionDiagKind::CallResolutionBacktrackFailed,
                        "backtracked call target did not resolve to an FnDef constant",
                        None,
                    );
                    return None;
                };
                return Some(*def_id);
            }
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
            | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                if place.projection.is_empty() =>
            {
                current_local = Some(place.local);
            }
            // Handle deref-through-reference in call backtracking: `_4 = copy *_1`
            // where _1 is a `&fn()` reference. Follow to the base local. (#1588)
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref) =>
            {
                current_local = Some(place.local);
            }
            Rvalue::Ref(_, _, place) | Rvalue::CopyForDeref(place)
                if place.projection.is_empty() =>
            {
                current_local = Some(place.local);
            }
            // Handle `_1 = &(*_8)` — reference to a dereferenced promoted constant.
            // MIR generates this for `&some_fn_item`: the fn item is promoted to a
            // constant, and the reference is formed via `&(*promoted)`. Follow the
            // base local through the Deref projection. (#1636)
            Rvalue::Ref(_, _, place)
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref) =>
            {
                current_local = Some(place.local);
            }
            _ => {
                record_extraction_diag(
                    diagnostics,
                    "extract/call_resolve_util.rs",
                    ExtractionDiagKind::CallResolutionBacktrackFailed,
                    format!("unsupported backtracking rvalue for call target: {rvalue:?}"),
                    None,
                );
                return None;
            }
        }
    }

    record_extraction_diag(
        diagnostics,
        "extract/call_resolve_util.rs",
        ExtractionDiagKind::CallResolutionBacktrackFailed,
        format!("call target backtracking exceeded depth limit ({MAX_CALL_DEF_BACKTRACK_DEPTH})"),
        None,
    );
    None
}

fn array_len_from_place_with_backtrack<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    place: rustc_middle::mir::Place<'tcx>,
    depth: usize,
) -> Option<PureExpr> {
    if depth >= MAX_ARRAY_LEN_BACKTRACK_DEPTH {
        return None;
    }
    if let Some(expr) = array_len_from_place(body, place) {
        return Some(expr);
    }
    if !place.projection.is_empty() {
        return None;
    }
    let rvalue = find_local_assignment_rvalue(body, bb, place.local)?;
    match rvalue {
        Rvalue::Use(operand, _) | Rvalue::Cast(_, operand, _) => {
            array_len_from_operand_with_backtrack(body, bb, operand, depth + 1)
        }
        Rvalue::Ref(_, _, inner_place) | Rvalue::CopyForDeref(inner_place) => {
            array_len_from_place_with_backtrack(body, bb, *inner_place, depth + 1)
        }
        _ => None,
    }
}

fn array_len_from_operand_with_backtrack<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    operand: &Operand<'tcx>,
    depth: usize,
) -> Option<PureExpr> {
    if depth >= MAX_ARRAY_LEN_BACKTRACK_DEPTH {
        return None;
    }
    if let Some(expr) = array_len_from_operand(body, operand) {
        return Some(expr);
    }
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            array_len_from_place_with_backtrack(body, bb, *place, depth + 1)
        }
        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
    }
}

pub(super) fn call_receiver_array_len_expr<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    args: &[Spanned<Operand<'tcx>>],
) -> Option<PureExpr> {
    let receiver = args.first()?;
    array_len_from_operand_with_backtrack(body, bb, &receiver.node, 0)
}

/// Drain call-site assumptions and obligations from `CallEffects` and wrap the
/// continuation expression in `LetAssume`/`LetObligation` nodes.
///
/// This scopes call-site postcondition assumptions and precondition obligations
/// to the branch they were created in, fixing #815 (branch-local assumption leak).
///
/// Phase C (#963): requires explicit `&mut CallEffects`. Thread-local fallback
/// removed — all callers already pass effects explicitly via `session.effects`.
pub(super) fn wrap_call_context(
    continuation: Option<PureExpr>,
    enabled: bool,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    if !enabled {
        return continuation;
    }
    let Some(mut expr) = continuation else {
        // Keep effects on the side channel when there is no expression to wrap,
        // so proof_assert cutoff snapshots can still consume them.
        return None;
    };
    let assumptions = std::mem::take(&mut effects.assumptions);
    let obligations = std::mem::take(&mut effects.obligations);

    if assumptions.is_empty() && obligations.is_empty() {
        return Some(expr);
    }

    for assumption in assumptions.into_iter().rev() {
        expr = PureExpr::LetAssume {
            assumption: Arc::new(assumption),
            body: Arc::new(expr),
        };
    }
    for obligation in obligations.into_iter().rev() {
        expr = PureExpr::LetObligation {
            obligation: Arc::new(obligation),
            body: Arc::new(expr),
        };
    }
    Some(expr)
}
