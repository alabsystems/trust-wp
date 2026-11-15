// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Refuse the ENTRY pointee for a `&mut` borrow handed back after a write.
//! (handback-entry-value)
//!
//! A body that returns one of its own `&mut` parameters is extracted as the
//! parameter itself:
//!
//! ```text
//! fn hand_back(p: &mut u32) -> &mut u32 { p }   ==>  result_expr = Var("p")
//! ```
//!
//! Every lane then binds `result` to that carrier, so `result == p` is the
//! syntactic identity `p == p` and is discharged without looking at the body.
//! That is right only while the body never writes through `p`. Under the
//! Creusot reading a `&mut` equality is the pair equality
//!
//! ```text
//! result == p   ===   *result == *p  &&  ^result == ^p
//! ```
//!
//! and `*p` in a postcondition is the ENTRY pointee. A body that stores through
//! `p` before returning it therefore does NOT satisfy `result == p` — the
//! returned reference's current pointee is the stored value — yet
//!
//! ```text
//! #[ensures(result == p)] fn f(p: &mut u32) -> &mut u32 { *p = 9; p }
//! ```
//!
//! verified (exit 0) before this module existed.
//!
//! The refusal: when a store through the returned borrow's alias class reaches
//! the `Return` (`mir_analysis::deref_store_staleness::params_written_before_return`),
//! the result expression is replaced by a FRESH carrier of the same sort, so
//! nothing ties `*result` to the entry pointee any more. One sound premise
//! survives the swap, and only for a whole-parameter handback:
//!
//! ```text
//! ^<fresh> == ^p
//! ```
//!
//! which is the RustHorn resolution of a borrow reborrowed for the remainder of
//! `p`'s lifetime and handed to the caller — the same prophecy identity the
//! mut-borrow encoder already asserts for an unwritten handback
//! (`bind_whole_mut_ref_result`'s `result_final`). No premise is emitted for a
//! projection or any other shape: those fail closed with `result` free.
//!
//! This only DELETES an accept path. `#[ensures(^result == ^p)]` (a true claim
//! about the prophecy) still verifies; the honest twin with no write is
//! untouched because nothing is stale there.

use std::{collections::HashSet, sync::Arc};

use rustc_middle::{mir::Body, ty::TyCtxt};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

/// The fresh carrier standing for the borrow actually handed back.
///
/// A fixed name is enough: there is exactly one return value per body, and the
/// name is body-local (the solver state is rebuilt per contract).
pub(super) const HANDBACK_RESULT_VAR: &str = "__trust_wp_handback_result";

/// Is `expr` a whole `&mut` parameter carrier (`Var(p, MutRef(_))`)?
fn whole_mut_ref_param(expr: &PureExpr, arg_names: &[String]) -> Option<(String, ExprSort)> {
    let PureExpr::Var(name, Some(sort)) = expr else {
        return None;
    };
    if !matches!(sort, ExprSort::MutRef(_)) {
        return None;
    }
    arg_names
        .iter()
        .any(|arg| arg == name)
        .then(|| (name.clone(), sort.clone()))
}

/// Does `expr` denote a borrow (a `MutRef`-sorted carrier), rather than a value
/// read out of one?
fn is_mut_ref_carrier(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(sort)) => matches!(sort, ExprSort::MutRef(_)),
        PureExpr::LogicFnCall { args, .. } if args.len() == 1 => is_mut_ref_carrier(&args[0]),
        PureExpr::Ite(_, then_branch, else_branch) => {
            is_mut_ref_carrier(then_branch) || is_mut_ref_carrier(else_branch)
        }
        _ => false,
    }
}

/// Rewrite a stale handback result expression, appending the prophecy premise
/// that survives the swap. Returns the (possibly unchanged) result expression.
///
/// `written` is the over-approximate set of parameters written through before
/// the return; `arg_names` the body's parameter names in order.
pub(super) fn refuse_stale_handback_result<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    result_expr: Option<PureExpr>,
    call_assumptions: &mut Vec<PureExpr>,
) -> Option<PureExpr> {
    let expr = result_expr?;
    // The DECLARED return type decides whether a borrow leaves this body at
    // all. Without this gate a by-value return whose extraction happens to
    // carry a `MutRef` annotation (`fn g(a: &mut u32) -> u32 { let r = *a; *a
    // = 5; r }`) was swapped for a fresh carrier and stopped verifying.
    if !crate::mir_analysis::type_contains_mut_ref_with_tcx(tcx, body.return_ty()) {
        return Some(expr);
    }
    // Only a returned BORROW can carry the entry pointee of a parameter into
    // `result`. A by-value return is a different question (its own lane).
    if !is_mut_ref_carrier(&expr) {
        return Some(expr);
    }
    let written = crate::mir_analysis::deref_store_staleness::params_written_before_return(
        tcx, body, arg_names,
    );
    if written.is_empty() {
        return Some(expr);
    }
    // The returned borrow is rooted at a written parameter when that parameter
    // occurs free in the result expression.
    let free: HashSet<String> = expr.free_vars().into_iter().collect();
    if !free.iter().any(|name| written.contains(name)) {
        return Some(expr);
    }

    let sort = match &expr {
        PureExpr::Var(_, Some(sort)) => Some(sort.clone()),
        _ => None,
    };
    let fresh = PureExpr::Var(HANDBACK_RESULT_VAR.to_string(), sort);

    // The one premise that survives: a WHOLE parameter handed back is
    // reborrowed for the rest of that parameter's lifetime, so the two
    // prophecies resolve together. Projections and every other shape get
    // nothing — `result` stays free.
    if let Some((param, param_sort)) = whole_mut_ref_param(&expr, arg_names) {
        call_assumptions.push(PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(fresh.clone()))),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                param,
                Some(param_sort),
            )))),
        ));
    }
    Some(fresh)
}
