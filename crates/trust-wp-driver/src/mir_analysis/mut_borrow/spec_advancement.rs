// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Spec-driven state advancement for mutable borrow analysis (#2124).
//!
//! When a mutation call (e.g., `v.push(x)`) has a known spec with ensures
//! clauses relating `^self` (Final) to `self` (Current), these functions
//! parse the spec, extract the post-state expression, and substitute
//! call-site arguments to compute the new symbolic state.

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Local, Operand},
    ty::TyKind,
};
use trust_wp_core::formula::{CaptureAvoidingSubstOptions, PureExpr};
use trust_wp_driver::{lookup_spec_with_extern, StdSpec};

use super::{
    call_classification::is_fn_trait_call,
    data::{DerefLookup, MutBorrowBlockContext},
    place_utils::resolve_reborrow_param_local,
};
use crate::mir_analysis::{
    call_resolve::{extract_call_def_id, resolve_trait_method_def_id, ufcs_path_for_call},
    translate::translate_operand,
};

/// Result of a successful spec-driven state advancement.
pub(super) struct SpecAdvancement {
    /// The MIR local whose deref_expr should be updated.
    pub(super) receiver_local: Local,
    /// The new symbolic expression for the receiver's post-mutation state.
    pub(super) new_state: PureExpr,
}

/// Look up a spec for a call, using the same resolution chain as `resolve_call`.
pub(super) fn lookup_call_spec<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    func: &Operand<'tcx>,
    def_id: DefId,
) -> Option<StdSpec> {
    // Direct user/trait spec by DefId.
    if let Some(spec) = ctx
        .user_specs
        .get(&def_id)
        .or_else(|| ctx.trait_specs.get(&def_id))
    {
        return Some(spec.clone());
    }

    let extern_opt = (!ctx.extern_specs.is_empty()).then_some(ctx.extern_specs);

    // UFCS-qualified path lookup.
    let spec =
        ufcs_path_for_call(ctx.tcx, func).and_then(|p| lookup_spec_with_extern(extern_opt, &p));
    if spec.is_some() {
        return spec;
    }

    // Plain def_path_str lookup.
    let path = ctx.tcx.def_path_str(def_id);
    let spec = lookup_spec_with_extern(extern_opt, &path);
    if spec.is_some() {
        return spec;
    }

    // Trait method fallback.
    let trait_method_id = resolve_trait_method_def_id(ctx.tcx, def_id)?;
    let trait_path = ctx.tcx.def_path_str(trait_method_id);
    lookup_spec_with_extern(extern_opt, &trait_path)
}

/// Find which `&mut` argument is the mutation receiver and return its
/// tracked `deref_exprs` local and current symbolic expression.
pub(super) fn find_mutation_receiver<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    deref_exprs: &HashMap<Local, PureExpr>,
    reborrow_map: &HashMap<Local, Local>,
) -> Option<(Local, PureExpr)> {
    for arg in args {
        let local = match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => place.local,
            Operand::Constant(_) | Operand::RuntimeChecks(_) => continue,
        };
        let ty = ctx.body.local_decls[local].ty;
        if !matches!(
            ty.kind(),
            TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        ) {
            continue;
        }
        // Resolve through reborrow chain to the tracked param.
        let tracked_local =
            resolve_reborrow_param_local(local, ctx.mut_borrow_params, reborrow_map)?;
        let current_expr = deref_exprs.get(&tracked_local)?;
        return Some((tracked_local, current_expr.clone()));
    }
    None
}

/// Parse a spec's ensures clauses and extract the post-mutation state expression.
///
/// Looks for ensures clauses of the form `(^self)@ == <rhs>` or `^self == <rhs>`.
/// When found, substitutes call-site argument expressions for the spec's parameter
/// names in `<rhs>`, producing the new symbolic state for the receiver.
pub(super) fn extract_post_state_from_spec(
    spec: &StdSpec,
    receiver_expr: &PureExpr,
    args: &[rustc_span::Spanned<Operand<'_>>],
    lookup: &DerefLookup<'_>,
) -> Option<PureExpr> {
    for ensures_str in &spec.ensures {
        let ensures_expr = trust_wp_core::contract_parser::parse_contract(ensures_str).ok()?;

        // Look for `(^self)@ == <rhs>` pattern.
        if let Some(rhs) = extract_final_self_equation(&ensures_expr) {
            // Build substitution: spec param names → call-site expressions.
            let substituted = substitute_spec_params(rhs, spec, receiver_expr, args, lookup);
            return Some(substituted);
        }
    }
    None
}

/// Extract the RHS from an equation of the form `(^self)@ == <rhs>` or
/// `View(Final(Var("self"))) == <rhs>`.
///
/// Also handles the reversed form `<rhs> == (^self)@`.
fn extract_final_self_equation(expr: &PureExpr) -> Option<&PureExpr> {
    use trust_wp_core::formula::BinOp;

    if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr {
        if is_final_self_view(lhs) {
            return Some(rhs);
        }
        if is_final_self_view(rhs) {
            return Some(lhs);
        }
    }
    None
}

/// Check if an expression matches `View(Final(Var("self")))` or `Final(Var("self"))`.
fn is_final_self_view(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::View(inner) => is_final_self(inner),
        _ => is_final_self(expr),
    }
}

/// Check if an expression matches `Final(Var("self"))`.
fn is_final_self(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "self"))
}

/// Substitute spec parameter names with call-site argument expressions.
///
/// Replaces occurrences of `self@` / `View(Var("self"))` with the receiver's
/// current View expression, and other spec parameters (like `value`) with
/// their corresponding call-site arguments.
fn substitute_spec_params(
    rhs: &PureExpr,
    spec: &StdSpec,
    receiver_expr: &PureExpr,
    args: &[rustc_span::Spanned<Operand<'_>>],
    lookup: &DerefLookup<'_>,
) -> PureExpr {
    // Build name → expression map for substitution.
    let mut subs: HashMap<String, PureExpr> = HashMap::new();

    // "self" (current view) → receiver's current expression wrapped in View.
    // The spec uses `self@` which parses as View(Var("self")), so we map
    // "self" to the receiver expression (the view is applied by the parsed
    // spec structure itself).
    subs.insert("self".to_string(), receiver_expr.clone());

    // Map positional/named non-self parameters to call-site args.
    // args[0] is self; spec params skip self.
    let non_self_args: Vec<PureExpr> = args
        .iter()
        .skip(1) // Skip the `&mut self` receiver
        .filter_map(|a| translate_operand(&a.node, lookup))
        .collect();

    // Use param_names if available, otherwise use positional aliases.
    if let Some(ref names) = spec.param_names {
        for (idx, name) in names.iter().enumerate() {
            if name == "self" {
                continue;
            }
            if let Some(arg_expr) = non_self_args.get(idx.saturating_sub(1)) {
                subs.insert(name.clone(), arg_expr.clone());
            }
        }
    }
    // Always add positional fallbacks.
    for (idx, arg_expr) in non_self_args.iter().enumerate() {
        subs.insert(format!("arg{idx}"), arg_expr.clone());
        // Common spec aliases.
        if idx == 0 {
            subs.entry("value".to_string())
                .or_insert_with(|| arg_expr.clone());
            subs.entry("arg".to_string())
                .or_insert_with(|| arg_expr.clone());
            subs.entry("rhs".to_string())
                .or_insert_with(|| arg_expr.clone());
        }
    }

    substitute_in_expr(rhs, &subs)
}

/// Recursively substitute variable references in an expression.
pub(super) fn substitute_in_expr(expr: &PureExpr, subs: &HashMap<String, PureExpr>) -> PureExpr {
    expr.substitute_capture_avoiding(subs, &CaptureAvoidingSubstOptions::default())
}

// ── Spec-driven result binding (#2124 Phase 3) ───────────────────────

/// Try to bind a non-mutating call's result to a concrete expression using
/// the called function's spec.
///
/// For calls like `v.len()` within a `&mut`-parameter function body, the MIR
/// extractor previously created an opaque variable `_call_N`. This function
/// looks up the call's spec and, if it contains an `ensures: result == <expr>`
/// or `ensures: result@ == <expr>` clause, substitutes call-site arguments to
/// produce a concrete symbolic expression.
///
/// Example: `v.len()` with spec `ensures: result@ == self@.len()` produces
/// `MethodCall { receiver: View(<v_current_expr>), method: "len", args: [] }`
/// instead of an opaque `_call_N`.
pub(super) fn try_spec_result_binding<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    lookup: &DerefLookup<'_>,
) -> Option<PureExpr> {
    let def_id = extract_call_def_id(func)?;
    let spec = lookup_call_spec(ctx, func, def_id)?;

    // Resolve the receiver expression (first argument, typically `&self`).
    let receiver_expr = if args.is_empty() {
        None
    } else {
        translate_operand(&args[0].node, lookup)
    };

    extract_result_from_spec(&spec, receiver_expr.as_ref(), args, lookup)
}

/// Parse a spec's ensures clauses and extract the result expression.
///
/// Looks for ensures clauses of the form `result == <rhs>` or `result@ == <rhs>`.
/// When found, substitutes call-site argument expressions for the spec's parameter
/// names in `<rhs>`, producing the concrete expression for the call result.
fn extract_result_from_spec(
    spec: &StdSpec,
    receiver_expr: Option<&PureExpr>,
    args: &[rustc_span::Spanned<Operand<'_>>],
    lookup: &DerefLookup<'_>,
) -> Option<PureExpr> {
    for ensures_str in &spec.ensures {
        let ensures_expr = trust_wp_core::contract_parser::parse_contract(ensures_str).ok()?;

        // Look for `result == <rhs>` or `result@ == <rhs>` pattern.
        if let Some(rhs) = extract_result_equation(&ensures_expr) {
            let substituted = substitute_result_spec_params(rhs, spec, receiver_expr, args, lookup);
            return Some(substituted);
        }
    }
    None
}

/// Extract the RHS from an equation of the form `result == <rhs>`,
/// `result@ == <rhs>`, `View(Var("result")) == <rhs>`, or the reversed form.
fn extract_result_equation(expr: &PureExpr) -> Option<&PureExpr> {
    use trust_wp_core::formula::BinOp;

    if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr {
        if is_result_var(lhs) || is_result_view(lhs) {
            return Some(rhs);
        }
        if is_result_var(rhs) || is_result_view(rhs) {
            return Some(lhs);
        }
    }
    None
}

/// Check if an expression is `Var("result")`.
fn is_result_var(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == "result")
}

/// Check if an expression is `View(Var("result"))`.
fn is_result_view(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::View(inner) if is_result_var(inner))
}

/// Substitute spec parameter names with call-site argument expressions for
/// result-binding specs.
///
/// Similar to `substitute_spec_params` but handles the non-mutating call case
/// where the first argument is `&self` (shared reference) rather than `&mut self`.
fn substitute_result_spec_params(
    rhs: &PureExpr,
    spec: &StdSpec,
    receiver_expr: Option<&PureExpr>,
    args: &[rustc_span::Spanned<Operand<'_>>],
    lookup: &DerefLookup<'_>,
) -> PureExpr {
    let mut subs: HashMap<String, PureExpr> = HashMap::new();

    // "self" → receiver's expression (the first argument).
    // For shared refs, the MIR argument is typically `&(*v)`, and
    // translate_operand resolves through the deref chain to produce the
    // tracked expression (e.g., Deref(Var("v")) for a &mut param).
    if let Some(recv) = receiver_expr {
        subs.insert("self".to_string(), recv.clone());
    }

    // Map non-self arguments by name or position.
    let non_self_args: Vec<PureExpr> = args
        .iter()
        .skip(1)
        .filter_map(|a| translate_operand(&a.node, lookup))
        .collect();

    if let Some(ref names) = spec.param_names {
        for (idx, name) in names.iter().enumerate() {
            if name == "self" {
                continue;
            }
            if let Some(arg_expr) = non_self_args.get(idx.saturating_sub(1)) {
                subs.insert(name.clone(), arg_expr.clone());
            }
        }
    }
    for (idx, arg_expr) in non_self_args.iter().enumerate() {
        subs.insert(format!("arg{idx}"), arg_expr.clone());
        if idx == 0 {
            subs.entry("value".to_string())
                .or_insert_with(|| arg_expr.clone());
            subs.entry("arg".to_string())
                .or_insert_with(|| arg_expr.clone());
            subs.entry("rhs".to_string())
                .or_insert_with(|| arg_expr.clone());
        }
    }

    substitute_in_expr(rhs, &subs)
}

/// Try to advance the receiver's symbolic state using the called function's spec.
///
/// When a mutation call (e.g., `v.push(x)`) has a known spec with ensures
/// clauses relating `^self` (Final) to `self` (Current), this function
/// parses the spec, extracts the post-state expression, and substitutes
/// call-site arguments to compute the new symbolic state.
///
/// Returns `None` if:
/// - The call's DefId cannot be resolved
/// - No spec is found for the call
/// - The spec's ensures clauses don't contain a `^self`-style equation
/// - The receiver is not a tracked `&mut` parameter
pub(super) fn try_spec_advancement<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    local_exprs: &HashMap<Local, PureExpr>,
    deref_exprs: &HashMap<Local, PureExpr>,
    field_deref_exprs: &HashMap<(Local, u32), PureExpr>,
    reborrow_map: &HashMap<Local, Local>,
) -> Option<SpecAdvancement> {
    // Fn-trait calls must bail for identity-final-value synthesis (#537).
    if is_fn_trait_call(ctx.tcx, func) {
        return None;
    }

    // Step 1: Resolve the call's DefId.
    let def_id = extract_call_def_id(func)?;

    // Step 2: Look up the spec (same resolution chain as resolve_call).
    let spec = lookup_call_spec(ctx, func, def_id)?;

    // Step 3: Identify the receiver — the first `&mut` argument that maps
    // to a tracked mut_borrow param.
    let (receiver_local, receiver_expr) =
        find_mutation_receiver(ctx, args, deref_exprs, reborrow_map)?;

    // Step 4: Parse ensures clauses and extract the `^self` post-state.
    let lookup = DerefLookup {
        locals: local_exprs,
        deref_exprs,
        field_deref_exprs,
    };
    let new_state = extract_post_state_from_spec(&spec, &receiver_expr, args, &lookup)?;

    Some(SpecAdvancement {
        receiver_local,
        new_state,
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::BinOp;

    use super::*;

    #[test]
    fn substitute_in_expr_rewrites_through_forall_and_avoids_capture() {
        let expr = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("value".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Var("x".to_string(), None)),
            )),
            triggers: vec![],
        };
        let subs = HashMap::from([("value".to_string(), PureExpr::Var("x".to_string(), None))]);

        let result = substitute_in_expr(&expr, &subs);

        match result {
            PureExpr::Forall { var, body, .. } => {
                assert_ne!(var, "x", "forall binder should alpha-rename");
                match body.as_ref() {
                    PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
                        assert_eq!(
                            lhs.as_ref(),
                            &PureExpr::Var("x".to_string(), None),
                            "substitution should rewrite through the quantifier body"
                        );
                        assert_eq!(
                            rhs.as_ref(),
                            &PureExpr::Var(var, None),
                            "bound occurrence should use the renamed binder"
                        );
                    }
                    other => panic!("expected BinOp(Gt), got {other:?}"),
                }
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }
}
