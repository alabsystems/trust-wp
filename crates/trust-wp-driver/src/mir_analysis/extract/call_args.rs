// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call argument translation helpers used by MIR extraction.

#[cfg(test)]
use std::collections::HashMap;

use rustc_middle::mir::{Body, Local, Operand};
use rustc_span::Spanned;
use trust_wp_core::formula::{internal::tuple_lowering::tuple_logic_fn_name, PureExpr};

use super::super::{
    spec_apply::TranslatedArg,
    translate::{
        translate_operand, translate_operand_with_tcx, translate_typed_field_place,
        ty_to_expr_sort_enriched, ExprLookup,
    },
};
use crate::callbacks::{strip_deref_wrappers, strip_receiver_state_wrappers};

/// Create a symbolic result variable for a function call destination.
///
/// Uses enriched sort resolution (ADT Datatype sorts) via the provided `TyCtxt`.
pub(super) fn call_result_symbol<'tcx>(
    body: &Body<'tcx>,
    destination: Local,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> PureExpr {
    if matches!(
        body.local_decls[destination].ty.kind(),
        rustc_middle::ty::TyKind::Tuple(fields) if fields.is_empty()
    ) {
        return PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(0),
            args: vec![],
        };
    }
    let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[destination].ty);
    PureExpr::Var(format!("call_{}", destination.as_u32()), sort)
}

#[cfg(test)]
pub(super) fn translate_call_args_for_substitutions<'tcx>(
    args: &[Spanned<Operand<'tcx>>],
    local_exprs: &HashMap<Local, PureExpr>,
) -> Vec<TranslatedArg> {
    translate_call_args_for_substitutions_with_tcx(args, local_exprs, None, None)
}

/// Translate call arguments into `TranslatedArg` values for substitution.
/// Accepts any `ExprLookup` implementation (e.g., `HashMap<Local, PureExpr>`
/// or `HashMap<Local, SpannedBodyExpr>`). Optional TyCtxt enables fallback
/// for unevaluated constants (e.g., promoted references to structs
/// in `Snapshot::capture(&NonCopy(1i32))`). (#1572)
pub(super) fn translate_call_args_for_substitutions_with_tcx<'tcx>(
    args: &[Spanned<Operand<'tcx>>],
    local_exprs: &impl ExprLookup,
    body: Option<&Body<'tcx>>,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
) -> Vec<TranslatedArg> {
    args.iter()
        .enumerate()
        .map(|(idx, arg)| {
            let expr = if let Some(tcx) = tcx {
                translate_operand_with_tcx(&arg.node, local_exprs, tcx).or_else(|| {
                    let body = body?;
                    match &arg.node {
                        Operand::Copy(place) | Operand::Move(place) => {
                            translate_typed_field_place(tcx, body, place, local_exprs)
                        }
                        // RuntimeChecks, like Constant, references no place/local.
                        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
                    }
                })
            } else {
                translate_operand(&arg.node, local_exprs)
            };
            if let Some(expr) = expr {
                TranslatedArg::new(expr)
            } else {
                TranslatedArg::fallback(fallback_arg_expr(idx, arg, body, tcx))
            }
        })
        .collect()
}

fn fallback_arg_expr<'tcx>(
    idx: usize,
    arg: &Spanned<Operand<'tcx>>,
    body: Option<&Body<'tcx>>,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
) -> PureExpr {
    let sort = match (body, tcx) {
        (Some(body), Some(tcx)) => {
            ty_to_expr_sort_enriched(tcx, arg.node.ty(&body.local_decls, tcx))
        }
        _ => None,
    };
    PureExpr::Var(format!("arg{idx}"), sort)
}

/// Derive `self_expr` from the first translated argument when it's not a
/// fallback. For method-like std_spec calls (Ghost::new, Snapshot::capture,
/// Deref::deref, etc.) the first argument is `self`. Without this, specs
/// containing `self` (e.g., `ensures: result == self`) are dropped as
/// "unresolved symbolic names" because `self` is never substituted.
pub(super) fn derive_self_expr_from_args(translated_args: &[TranslatedArg]) -> Option<PureExpr> {
    translated_args
        .first()
        .filter(|arg| !arg.is_fallback)
        .map(|arg| arg.expr.clone())
}

/// Normalize the explicit `self` expression for extern/spec-backed calls.
///
/// `DerefMut::deref_mut` specs quantify over the whole-borrow receiver
/// (`self: &mut T`), but MIR argument translation can surface the first arg as
/// `Deref(Var("x"))` after reborrow lowering. Strip receiver-state wrappers in
/// that narrow case so call-site pre/postcondition facts use the reference
/// carrier (`x`) rather than the current pointee (`*x`). This aligns the call
/// facts with user contracts such as Creusot's `generic_deref.rs`. (#2578)
pub(super) fn normalize_extern_spec_self_expr(
    def_path: &str,
    self_expr: Option<PureExpr>,
) -> Option<PureExpr> {
    self_expr.map(|expr| {
        if def_path.ends_with("::deref_mut") {
            strip_receiver_state_wrappers(&expr)
        } else if is_fnmut_call_mut_path(def_path) {
            strip_deref_wrappers(&expr)
        } else {
            expr
        }
    })
}

fn is_fnmut_call_mut_path(def_path: &str) -> bool {
    def_path.contains("FnMut::call_mut") || def_path.ends_with("::call_mut")
}
