// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure body substitution functions for postcondition inlining.

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_arity},
    BinOp, CaptureAvoidingSubstOptions, ExprSort, PureExpr,
};

use super::super::MAX_ENCODING_DEPTH;
use crate::expr::expr_mentions_var;

/// Extract the variable name from a receiver expression (stripping wrappers).
///
/// Strips `Deref`, `Final`, and `Old` wrappers to reach the base `Var` name.
/// This handles closure receivers that arrive with various MIR-derived wrappings:
/// - `Deref`: from `Box<F>: Deref` and `(*self)` in Fn::call
/// - `Final`: from postcondition contexts (`^receiver`)
/// - `Old`: from old-state references in ensures clauses (`old(receiver)`)
pub(super) fn extract_receiver_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::Old(inner) => {
            extract_receiver_name(inner)
        }
        _ => None,
    }
}

/// Substitute formal parameters and "result" in a closure body expression.
///
/// For `postcondition(env, args..., result)` and `postcondition_once(env, args..., result)`:
/// - `param_names[i]` -> `args[i]` (formal closure params to actual call args)
/// - `"result"` -> `args.last()` (the result variable)
/// - Capture names are left as-is (they resolve to caller-side variables)
pub(super) fn substitute_closure_body(
    body: &PureExpr,
    _capture_names: &[String],
    param_names: &[String],
    args: &[PureExpr],
) -> PureExpr {
    // When a param is named "result", the body `result == computation` has a
    // name collision: the LHS "result" is the return value keyword, while
    // "result" inside `computation` is the formal param. A single HashMap
    // cannot map the same name to two different values.
    //
    // Fix (#2193): detect the collision and handle it with a two-phase
    // substitution. Phase 1 substitutes params in the computation (RHS),
    // mapping "result" -> param_arg. Phase 2 replaces the LHS "result" with
    // the return variable (args.last()).
    let result_is_param = param_names.iter().any(|p| p == "result");
    if result_is_param {
        return substitute_with_result_param_collision(body, param_names, args);
    }

    let mut subst = HashMap::new();

    // Map formal parameters to actual arguments
    for (i, param) in param_names.iter().enumerate() {
        if let Some(arg) = args.get(i) {
            subst.insert(param.clone(), arg.clone());
        }
    }

    // Check if body contains a "result" variable reference. Bodies from
    // user-annotated closures have `result == computation` form; unannotated
    // closure bodies from try_extract_closure_body_with_effects are raw return
    // values (e.g., `Int(5)`) with no "result" reference.
    let body_has_result = expr_mentions_var(body, "result");

    if body_has_result {
        // Map "result" to the last argument (the result variable)
        if let Some(result_arg) = args.last() {
            subst.insert("result".to_string(), result_arg.clone());
        }
        apply_substitution(body, &subst)
    } else {
        // Raw return value body: wrap as `result_var == substituted_body`.
        // The body represents just the return value (e.g., Int(5)), not a
        // Boolean equation. We need to produce a Bool-sorted expression for
        // the postcondition assumption.
        let body_sub = apply_substitution(body, &subst);
        if let Some(result_arg) = args.last() {
            PureExpr::BinOp(Arc::new(result_arg.clone()), BinOp::Eq, Arc::new(body_sub))
        } else {
            body_sub
        }
    }
}

/// Handle the case where a closure param is named "result" (#2193).
///
/// The body expression is `result == computation` where:
/// - LHS `result` -> should map to `args.last()` (return variable)
/// - RHS `result` references -> should map to param's actual arg
///
/// Since both use `Var("result")`, we split the substitution:
/// 1. Apply param-only substitution to the RHS (computation)
/// 2. Replace LHS with the return variable directly
pub(super) fn substitute_with_result_param_collision(
    body: &PureExpr,
    param_names: &[String],
    args: &[PureExpr],
) -> PureExpr {
    // Build param-only substitution (maps "result" to param's actual arg)
    let mut param_subst = HashMap::new();
    for (i, param) in param_names.iter().enumerate() {
        if let Some(arg) = args.get(i) {
            param_subst.insert(param.clone(), arg.clone());
        }
    }

    // Try to split `result == computation` at the top level
    if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = body {
        if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "result") {
            // Apply param substitution to RHS only
            let rhs_substituted = apply_substitution(rhs, &param_subst);
            // Replace LHS with the return variable (args.last())
            let lhs_substituted = if let Some(result_arg) = args.last() {
                result_arg.clone()
            } else {
                apply_substitution(lhs, &param_subst)
            };
            return PureExpr::BinOp(
                Arc::new(lhs_substituted),
                BinOp::Eq,
                Arc::new(rhs_substituted),
            );
        }
    }

    // Fallback: body doesn't have the expected `result == ...` structure.
    // Apply param substitution to the whole body (result keyword won't be
    // separately mapped, but this is the safest default).
    apply_substitution(body, &param_subst)
}

/// Conjoin a body substitution with synthesized ensures expressions.
///
/// For unannotated FnMut closures called through `postcondition_once`, the body
/// substitution only captures the return value (`result == 5`). The ensures
/// capture mutable state changes (`x == old(x) + 1`). Conjoining produces:
/// `result == 5 AND x == old(x) + 1`.
pub(super) fn conjoin_with_ensures(body_sub: &PureExpr, ensures: &[PureExpr]) -> PureExpr {
    if ensures.is_empty() {
        return body_sub.clone();
    }

    let mut result = body_sub.clone();
    for ens in ensures {
        result = PureExpr::BinOp(Arc::new(result), BinOp::And, Arc::new(ens.clone()));
    }
    result
}

fn project_capture_from_state(state: &PureExpr, field_idx: usize) -> PureExpr {
    if let PureExpr::LogicFnCall { name, args } = state {
        if tuple_logic_fn_arity(name) == Some(args.len()) {
            if let Some(arg) = args.get(field_idx) {
                return arg.clone();
            }
        }
    }

    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(field_idx),
        args: vec![state.clone()],
    }
}

fn capture_index(capture_names: &[String], name: &str) -> Option<usize> {
    capture_names.iter().position(|capture| capture == name)
}

fn substitute_closure_ensure_expr(
    expr: &PureExpr,
    capture_names: &[String],
    pre_state: &PureExpr,
    post_state: &PureExpr,
    inside_old: bool,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, _) => {
            let Some(index) = capture_index(capture_names, name) else {
                return expr.clone();
            };
            let state = if inside_old { pre_state } else { post_state };
            project_capture_from_state(state, index)
        }
        PureExpr::Old(inner) => {
            let transformed =
                substitute_closure_ensure_expr(inner, capture_names, pre_state, post_state, true);
            if &transformed == inner.as_ref() {
                PureExpr::Old(Arc::new(transformed))
            } else {
                transformed
            }
        }
        PureExpr::Final(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => capture_index(capture_names, name)
                .map(|index| project_capture_from_state(post_state, index))
                .unwrap_or_else(|| {
                    PureExpr::Final(Arc::new(substitute_closure_ensure_expr(
                        inner,
                        capture_names,
                        pre_state,
                        post_state,
                        inside_old,
                    )))
                }),
            _ => PureExpr::Final(Arc::new(substitute_closure_ensure_expr(
                inner,
                capture_names,
                pre_state,
                post_state,
                inside_old,
            ))),
        },
        PureExpr::Bool(_) | PureExpr::Int(_) => expr.clone(),
        PureExpr::BinOp(l, op, r) => PureExpr::BinOp(
            Arc::new(substitute_closure_ensure_expr(
                l,
                capture_names,
                pre_state,
                post_state,
                inside_old,
            )),
            *op,
            Arc::new(substitute_closure_ensure_expr(
                r,
                capture_names,
                pre_state,
                post_state,
                inside_old,
            )),
        ),
        PureExpr::UnOp(op, operand) => PureExpr::UnOp(
            *op,
            Arc::new(substitute_closure_ensure_expr(
                operand,
                capture_names,
                pre_state,
                post_state,
                inside_old,
            )),
        ),
        PureExpr::Ite(c, t, e) => PureExpr::Ite(
            Arc::new(substitute_closure_ensure_expr(
                c,
                capture_names,
                pre_state,
                post_state,
                inside_old,
            )),
            Arc::new(substitute_closure_ensure_expr(
                t,
                capture_names,
                pre_state,
                post_state,
                inside_old,
            )),
            Arc::new(substitute_closure_ensure_expr(
                e,
                capture_names,
                pre_state,
                post_state,
                inside_old,
            )),
        ),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(substitute_closure_ensure_expr(
            inner,
            capture_names,
            pre_state,
            post_state,
            inside_old,
        ))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(substitute_closure_ensure_expr(
            inner,
            capture_names,
            pre_state,
            post_state,
            inside_old,
        ))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(substitute_closure_ensure_expr(
                receiver,
                capture_names,
                pre_state,
                post_state,
                inside_old,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| {
                    substitute_closure_ensure_expr(
                        arg,
                        capture_names,
                        pre_state,
                        post_state,
                        inside_old,
                    )
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| {
                    substitute_closure_ensure_expr(
                        arg,
                        capture_names,
                        pre_state,
                        post_state,
                        inside_old,
                    )
                })
                .collect(),
        },
        _ => expr.clone(),
    }
}

pub(super) fn substitute_closure_ensures(
    ensures: &[PureExpr],
    capture_names: &[String],
    pre_state: &PureExpr,
    post_state: &PureExpr,
) -> Vec<PureExpr> {
    ensures
        .iter()
        .map(|ensure| {
            substitute_closure_ensure_expr(ensure, capture_names, pre_state, post_state, false)
        })
        .collect()
}

pub(super) fn substitute_ensures_only(
    param_names: &[String],
    args: &[PureExpr],
    ensures: &[PureExpr],
) -> Option<PureExpr> {
    if !ensures
        .iter()
        .any(|ensure| expr_mentions_var(ensure, "result"))
    {
        return None;
    }

    let substituted = ensures
        .iter()
        .map(|ensure| substitute_closure_contract_expr(ensure, param_names, args))
        .collect::<Option<Vec<_>>>()?;
    conjoin_ensures_only(&substituted)
}

pub(super) fn substitute_closure_contract_expr(
    expr: &PureExpr,
    param_names: &[String],
    args: &[PureExpr],
) -> Option<PureExpr> {
    // `result` is a reserved post-state keyword in closure contracts. If a
    // closure also has a formal parameter named `result`, the ensures-only path
    // cannot disambiguate arbitrary `Var("result")` occurrences soundly, so
    // fail closed and fall back to the UF encoding.
    if param_names.iter().any(|param| param == "result") && expr_mentions_var(expr, "result") {
        return None;
    }

    let mut subst = HashMap::new();

    for (i, param) in param_names.iter().enumerate() {
        if let Some(arg) = args.get(i) {
            subst.insert(param.clone(), arg.clone());
        }
    }

    if expr_mentions_var(expr, "result") {
        subst.insert("result".to_string(), args.last()?.clone());
    }

    Some(apply_substitution(expr, &subst))
}

pub(super) fn conjoin_ensures_only(ensures: &[PureExpr]) -> Option<PureExpr> {
    let (first, rest) = ensures.split_first()?;
    let mut result = first.clone();
    for ens in rest {
        result = PureExpr::BinOp(Arc::new(result), BinOp::And, Arc::new(ens.clone()));
    }
    Some(result)
}

pub(super) fn apply_substitution(expr: &PureExpr, subst: &HashMap<String, PureExpr>) -> PureExpr {
    expr.substitute_capture_avoiding(
        subst,
        &CaptureAvoidingSubstOptions {
            depth_limit: Some(MAX_ENCODING_DEPTH),
        },
    )
}

/// Substitute capture names whose receiver-projected field is a `MutRef`-sorted
/// carrier `Var` with the carrier's CURRENT pointee `Deref(<carrier>)`.
///
/// When the driver's closure-capture carrier lane rebinds a by-`&mut` capture's
/// environment field to a per-borrow prophecy carrier, the capture's call-entry
/// value is DEFINITIONALLY `mut_ref_current(<carrier>)` — pinned by the
/// caller-emitted entry binding `*carrier == <value>`. Leaving the capture name
/// free instead makes the inlined `precondition` obligation read the CALLER
/// scope's binding of that name, which after a consuming call is the POST-state
/// prophecy — the wrong state. Scoped narrowly: only fields that are literally
/// `Var(_, Some(MutRef(_)))` (i.e. minted carriers) are substituted; every
/// other capture stays a free variable.
pub(super) fn substitute_mutref_capture_currents(
    expr: &PureExpr,
    capture_names: &[String],
    receiver: &PureExpr,
) -> PureExpr {
    let mut subst = HashMap::new();
    for (idx, name) in capture_names.iter().enumerate() {
        let field = project_capture_from_state(receiver, idx);
        if matches!(&field, PureExpr::Var(_, Some(ExprSort::MutRef(_)))) {
            subst.insert(name.clone(), PureExpr::Deref(Arc::new(field)));
        }
    }
    if subst.is_empty() {
        expr.clone()
    } else {
        apply_substitution(expr, &subst)
    }
}

/// Substitute formal parameters in a closure's requires expression (#2668).
///
/// For `precondition(env, args...)`:
/// - `param_names[i]` -> `args[i]` (formal closure params to actual call args)
/// - Capture names are left as-is (they resolve to caller-side variables);
///   the carrier-backed exception is applied by the caller via
///   [`substitute_mutref_capture_currents`]
///
/// Unlike postcondition inlining, there is no "result" variable to bind.
/// The precondition args layout is: `[param_0, ..., param_N-1]` (no result).
pub(super) fn substitute_closure_requires(
    requires: &[PureExpr],
    _capture_names: &[String],
    param_names: &[String],
    args: &[PureExpr],
) -> Option<PureExpr> {
    if requires.is_empty() {
        return None;
    }

    let mut subst = HashMap::new();
    for (i, param) in param_names.iter().enumerate() {
        if let Some(arg) = args.get(i) {
            subst.insert(param.clone(), arg.clone());
        }
    }

    let substituted: Vec<PureExpr> = requires
        .iter()
        .map(|req| apply_substitution(req, &subst))
        .collect();
    conjoin_ensures_only(&substituted)
}

/// Substitute formal parameters, final state, and "result" in an FnMut closure body.
///
/// For `postcondition_mut(env, args..., final_state, result)`:
/// - `param_names[i]` -> `args[i]` (formal closure params to actual call args)
/// - `"result"` -> `args.last()` (the result variable, after final_state)
/// - Capture names are left as-is (they resolve to caller-side current-state variables)
/// - `Final(Var(capture))` references in the body resolve to caller-side final variables
///   through the normal encoding pipeline, so no special substitution is needed.
///
/// The argument layout is: `[param_0, ..., param_N-1, final_state, result]`
/// where N = param_names.len(). The `final_state` at index N is not directly
/// substituted into the body - it participates through the Final-wrapped capture
/// references that the encoder resolves separately.
pub(super) fn substitute_closure_body_mut(
    body: &PureExpr,
    _capture_names: &[String],
    param_names: &[String],
    args: &[PureExpr],
) -> PureExpr {
    // Same collision handling as substitute_closure_body (#2193)
    let result_is_param = param_names.iter().any(|p| p == "result");
    if result_is_param {
        return substitute_with_result_param_collision(body, param_names, args);
    }

    let mut subst = HashMap::new();

    // Map formal parameters to actual arguments (same as postcondition)
    for (i, param) in param_names.iter().enumerate() {
        if let Some(arg) = args.get(i) {
            subst.insert(param.clone(), arg.clone());
        }
    }

    // Same raw-body detection as substitute_closure_body.
    let body_has_result = expr_mentions_var(body, "result");

    if body_has_result {
        // Map "result" to the last argument.
        // For postcondition_mut, args layout is [params..., final_state, result],
        // so args.last() is still the result variable.
        if let Some(result_arg) = args.last() {
            subst.insert("result".to_string(), result_arg.clone());
        }
        apply_substitution(body, &subst)
    } else {
        // Raw return value body: wrap as `result_var == substituted_body`.
        let body_sub = apply_substitution(body, &subst);
        if let Some(result_arg) = args.last() {
            PureExpr::BinOp(Arc::new(result_arg.clone()), BinOp::Eq, Arc::new(body_sub))
        } else {
            body_sub
        }
    }
}

/// Bind a closure contract clause's OWN formal params and `result` to the
/// arguments of the call being inlined (D-30).
///
/// [`substitute_closure_ensures`] resolves a clause's CAPTURES against the
/// receiver's pre/post state and nothing else: the clause's `result` and its
/// formal params are left free. Free is not neutral. The encoder resolves a
/// free `result` against the ENCLOSING function's result variable, so an
/// inlined `#[ensures(result == 1)]` on a CALLED closure would be conjoined
/// into the caller's postcondition assumption as `result == 1` about the
/// CALLER's return value — a fact the closure's spec never states — and a
/// function returning something other than the call result would be accepted
/// on it (`tests/adversarial/cases/s71_closure_ensures_sole_owner_falsified.rs`).
///
/// Every clause is bound through [`substitute_closure_contract_expr`], the
/// same helper the body-less ensures-only path `substitute_ensures_only`
/// uses; a clause that cannot be bound soundly (a formal param named
/// `result`, or a call with no result argument) yields `None`, and the caller
/// falls back to the opaque UF encoding of the `postcondition*` call.
pub(super) fn bind_closure_contract_clauses(
    clauses: &[PureExpr],
    param_names: &[String],
    args: &[PureExpr],
) -> Option<Vec<PureExpr>> {
    clauses
        .iter()
        .map(|clause| substitute_closure_contract_expr(clause, param_names, args))
        .collect()
}

/// Can this call site bind the closure's own `result` and formal params into
/// its `ensures` without ambiguity? (D-30)
///
/// The binding runs AFTER the capture/state substitution, and it is positional.
/// Three shapes make that unsound rather than merely imprecise, and each one
/// fails closed here (the whole inlining falls back to the UF encoding):
///
/// 1. A formal param that shadows a capture name. The capture substitution has
///    already rewritten that name to a state projection, so the source's
///    `param` reads as the capture.
/// 2. A pre/post state term that itself mentions a name about to be bound. The
///    capture substitution splices those terms into the clause, so the
///    positional binding would reach inside a term it did not come from.
/// 3. An argument list that is not the flat `[param_0, .., param_{N-1},
///    (final_state,)? result]` layout this module's positional substitutions
///    assume — a contract that passes a single args-tuple, for instance. The
///    RESULT is the last argument under either layout, so only a clause that
///    names a formal param is refused here.
pub(super) fn closure_clause_binding_is_unambiguous(
    method: &str,
    ensures: &[PureExpr],
    param_names: &[String],
    capture_names: &[String],
    args: &[PureExpr],
    pre_state: &PureExpr,
    post_state: &PureExpr,
) -> bool {
    if param_names
        .iter()
        .any(|param| capture_names.contains(param))
    {
        return false;
    }

    let bound_names = param_names
        .iter()
        .map(String::as_str)
        .chain(std::iter::once("result"));
    for name in bound_names {
        if expr_mentions_var(pre_state, name) || expr_mentions_var(post_state, name) {
            return false;
        }
    }

    let result_tail = if method == "postcondition_mut" { 2 } else { 1 };
    !(args.len() != param_names.len() + result_tail
        && ensures.iter().any(|ensure| {
            param_names
                .iter()
                .any(|param| expr_mentions_var(ensure, param))
        }))
}
