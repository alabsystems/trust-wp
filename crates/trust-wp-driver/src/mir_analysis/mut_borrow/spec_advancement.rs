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
use trust_wp_core::formula::{elaborate::Signature, CaptureAvoidingSubstOptions, PureExpr};
use trust_wp_driver::StdSpec;

use super::{
    call_classification::is_fn_trait_call,
    data::{DerefLookup, MutBorrowBlockContext},
    place_utils::resolve_reborrow_param_local,
};
use crate::mir_analysis::{
    call_resolve::{extract_call_def_id, resolve_trait_method_def_id, ufcs_path_for_call},
    call_signature,
    spec_apply::clause_read_as_written,
    translate::translate_operand,
    CallSite,
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
    if let Some(spec) = crate::trait_credit::lookup_user_or_trait_spec(
        ctx.user_specs,
        ctx.trait_specs,
        def_id,
        crate::trait_credit::GrantSite {
            tcx: ctx.tcx,
            body: ctx.body,
            func,
        },
    ) {
        return Some(
            crate::logic::identity_typed::instantiate_generic_markers_for_call(
                ctx.tcx,
                ctx.body,
                func,
                def_id,
                spec.clone(),
            ),
        );
    }

    let extern_opt = (!ctx.extern_specs.is_empty()).then_some(ctx.extern_specs);
    let admission = crate::provenance::builtin_spec_admission_for_operand(
        ctx.tcx,
        func,
        Some(ctx.body.source.def_id()),
    );
    let site = crate::provenance::CallSite::of_operand(func, Some(ctx.body.source.def_id()));

    // UFCS-qualified path lookup.
    let spec = ufcs_path_for_call(ctx.tcx, func).and_then(|p| {
        crate::provenance::lookup_spec_for_def(ctx.tcx, def_id, admission, extern_opt, &p, site)
    });
    if spec.is_some() {
        return spec;
    }

    // Plain def_path_str lookup.
    let path = ctx.tcx.def_path_str(def_id);
    let spec =
        crate::provenance::lookup_spec_for_def(ctx.tcx, def_id, admission, extern_opt, &path, site);
    if spec.is_some() {
        return spec;
    }

    // Trait method fallback.
    let trait_method_id = resolve_trait_method_def_id(ctx.tcx, def_id)?;
    let trait_path = ctx.tcx.def_path_str(trait_method_id);
    crate::provenance::lookup_spec_for_def(
        ctx.tcx,
        trait_method_id,
        admission,
        extern_opt,
        &trait_path,
        site,
    )
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
/// names in `<rhs>`, producing the new symbolic state for the receiver. Only a
/// clause a call reads as written is matched (`spec_apply::clause_read_as_written`).
pub(super) fn extract_post_state_from_spec(
    spec: &StdSpec,
    callee: &Signature,
    receiver_expr: &PureExpr,
    args: &[rustc_span::Spanned<Operand<'_>>],
    lookup: &DerefLookup<'_>,
) -> Option<PureExpr> {
    for ensures_str in &spec.ensures {
        let Some(ensures_expr) = clause_read_as_written(ensures_str, callee) else {
            continue;
        };

        // Look for `(^self)@ == <rhs>` pattern.
        if let Some(rhs) = extract_final_self_equation(&ensures_expr) {
            // Build substitution: spec param names → call-site expressions.
            // A clause whose vocabulary cannot be bound refuses the advancement
            // rather than leaving callee parameter names free.
            return substitute_spec_params(rhs, spec, receiver_expr, args, lookup);
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
) -> Option<PureExpr> {
    // "self" (current view) → receiver's current expression. The spec uses
    // `self@` which parses as View(Var("self")), so the view is applied by the
    // parsed spec structure itself.
    substitute_call_site_params(rhs, spec, receiver_expr.clone(), args, lookup)
}

/// Bind a callee spec's parameter vocabulary to call-site arguments and
/// substitute it into `rhs`.
///
/// The binding follows `spec_apply::insert_std_symbolic_substitutions` and the
/// user-name override in `apply_postconditions_with_self_inner` EXACTLY, so a
/// name means the same argument on every path:
///
/// - a declared parameter name at position `idx` binds to `args[idx]`
///   (position 0 is the receiver `self` for methods);
/// - positional aliases `arg{idx}` bind to `args[idx]` and `value` / `default`
///   / `arg` / `rhs` to `args[1]` (else `args[0]`), but only where no declared
///   parameter already owns the name — real names always win;
/// - `self` binds to `self_expr`.
///
/// Returns `None` (no binding — the caller falls back to an opaque value) when
/// an argument the spec refers to cannot be translated: leaving the callee's
/// parameter name free would let it alias a caller variable of the same name.
fn substitute_call_site_params(
    rhs: &PureExpr,
    spec: &StdSpec,
    self_expr: PureExpr,
    args: &[rustc_span::Spanned<Operand<'_>>],
    lookup: &DerefLookup<'_>,
) -> Option<PureExpr> {
    let translated: Vec<Option<PureExpr>> = args
        .iter()
        .map(|a| translate_operand(&a.node, lookup))
        .collect();
    let mut subs: HashMap<String, PureExpr> = HashMap::new();
    if let Some(ref names) = spec.param_names {
        for (idx, name) in names.iter().enumerate() {
            if name == "self" || name == "result" {
                continue;
            }
            if let Some(Some(arg_expr)) = translated.get(idx) {
                subs.insert(name.clone(), arg_expr.clone());
            }
        }
    }
    for (idx, arg_expr) in translated.iter().enumerate() {
        if let Some(arg_expr) = arg_expr {
            subs.entry(format!("arg{idx}"))
                .or_insert_with(|| arg_expr.clone());
        }
    }
    if let Some(Some(value_arg)) = translated.get(1).or_else(|| translated.first()) {
        for alias in ["value", "default", "arg", "rhs"] {
            subs.entry(alias.to_string())
                .or_insert_with(|| value_arg.clone());
        }
    }
    subs.insert("self".to_string(), self_expr);

    let unresolved = crate::mir_analysis::spec_apply::unresolved_symbolic_names(
        rhs,
        &subs,
        spec.param_names.as_deref(),
    );
    if !unresolved.is_empty() {
        return None;
    }
    Some(substitute_in_expr(rhs, &subs))
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

    let callee = call_signature(
        ctx.tcx,
        def_id,
        spec.param_names.as_deref(),
        Some(CallSite {
            body: ctx.body,
            func,
        }),
    );
    extract_result_from_spec(&spec, &callee, receiver_expr.as_ref(), args, lookup)
}

/// Parse a spec's ensures clauses and extract the result expression.
///
/// Looks for ensures clauses of the form `result == <rhs>` or `result@ == <rhs>`.
/// When found, substitutes call-site argument expressions for the spec's parameter
/// names in `<rhs>`, producing the concrete expression for the call result. Only
/// a clause a call reads as written is matched (`spec_apply::clause_read_as_written`).
fn extract_result_from_spec(
    spec: &StdSpec,
    callee: &Signature,
    receiver_expr: Option<&PureExpr>,
    args: &[rustc_span::Spanned<Operand<'_>>],
    lookup: &DerefLookup<'_>,
) -> Option<PureExpr> {
    for ensures_str in &spec.ensures {
        let Some(ensures_expr) = clause_read_as_written(ensures_str, callee) else {
            continue;
        };

        // Look for `result == <rhs>` or `result@ == <rhs>` pattern.
        if let Some(rhs) = extract_result_equation(&ensures_expr) {
            return substitute_result_spec_params(rhs, spec, receiver_expr, args, lookup);
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
) -> Option<PureExpr> {
    // "self" → the first argument. For shared refs, the MIR argument is
    // typically `&(*v)`, and translate_operand resolves through the deref
    // chain to the tracked expression. A spec whose first declared parameter
    // is not `self` (a free function) has no receiver: `self` stays unbound
    // and any clause mentioning it is refused by the unresolved-name check.
    let first_is_self = spec
        .param_names
        .as_deref()
        .is_none_or(|names| names.first().is_some_and(|n| n == "self"));
    let self_expr = if first_is_self {
        receiver_expr.cloned()
    } else {
        None
    };
    match self_expr {
        Some(self_expr) => substitute_call_site_params(rhs, spec, self_expr, args, lookup),
        None => {
            if rhs.free_vars().contains("self") {
                return None;
            }
            // Bind a placeholder that the clause provably does not mention.
            substitute_call_site_params(
                rhs,
                spec,
                PureExpr::Var("self".to_string(), None),
                args,
                lookup,
            )
        }
    }
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
    carrier_read_locals: &std::collections::HashSet<Local>,
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
    // The spec's `^self` names the FIRST argument. Advancing some later `&mut`
    // argument with a `^self` equation would bind the wrong place.
    let first_local = match args.first().map(|a| &a.node) {
        Some(Operand::Copy(place) | Operand::Move(place)) => Some(place.local),
        _ => None,
    };
    let first_tracked = first_local
        .and_then(|local| resolve_reborrow_param_local(local, ctx.mut_borrow_params, reborrow_map));
    if first_tracked != Some(receiver_local) {
        return None;
    }

    // Step 4: Parse ensures clauses and extract the `^self` post-state.
    let lookup = DerefLookup {
        locals: local_exprs,
        deref_exprs,
        field_deref_exprs,
        carrier_read_locals: Some(carrier_read_locals),
    };
    let callee = call_signature(
        ctx.tcx,
        def_id,
        spec.param_names.as_deref(),
        Some(CallSite {
            body: ctx.body,
            func,
        }),
    );
    let new_state = extract_post_state_from_spec(&spec, &callee, &receiver_expr, args, &lookup)?;

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
