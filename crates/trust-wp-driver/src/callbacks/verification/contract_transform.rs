// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract transformation: raw parsed contracts → effective requires/ensures.
//!
//! Applies A-F transform chain: mut-ref rewrite, closure capture field
//! transforms, call-assumption merging, and call-obligation merging.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{BinOp, ExprSort, MatchArm, PureExpr};

use super::super::{
    helpers::{extract_final_self_field_vars, extract_old_deref_vars},
    parsing::ParsedContract,
    proof_assert_extract::{
        constructor_equality_to_tester_selector_facts, normalize_old_constructor_equality_facts,
    },
};

/// Result of transforming a parsed contract's requires/ensures for verification.
///
/// Both `generate_smt_output` and `verify_contracts` apply identical transforms
/// to raw contracts: mut-ref postcondition rewriting, closure capture field
/// transforms, call-assumption merging, and call-obligation merging.
/// This struct captures the shared output (#564 dedup).
pub(in crate::callbacks) struct TransformedContract {
    pub(in crate::callbacks) effective_requires: Vec<PureExpr>,
    pub(in crate::callbacks) effective_ensures: Vec<PureExpr>,
    /// Original user requires after local rewrites but before call-site merges.
    ///
    /// Stored explicitly so downstream consumers do not have to recover the
    /// base clauses by slicing `effective_requires` and assuming append-only
    /// merge order.
    pub(in crate::callbacks) base_requires: Vec<PureExpr>,
    /// Original user ensures after local rewrites but before call-site merges.
    ///
    /// Stored explicitly so downstream consumers do not have to recover the
    /// base clauses by slicing `effective_ensures` and assuming append-only
    /// merge order.
    pub(in crate::callbacks) base_ensures: Vec<PureExpr>,
    /// Call-site obligations merged into `effective_ensures`.
    ///
    /// Stored separately so loop verification can inspect call obligations
    /// without reconstructing them via `base_ensures_count` slicing.
    pub(in crate::callbacks) call_obligation_ensures: Vec<PureExpr>,
    /// Call-site obligations that occur before the first loop.
    ///
    /// Loop-obligation verification checks only this subset before deciding
    /// whether to continue to post-loop function-level verification.
    pub(in crate::callbacks) pre_loop_call_obligation_ensures: Vec<PureExpr>,
    /// Call-site obligations that occur after loop exit.
    ///
    /// These are part of `call_obligation_ensures` and force the post-loop
    /// function-level path so they are checked with loop-exit assumptions.
    pub(in crate::callbacks) post_loop_call_obligation_ensures: Vec<PureExpr>,
    /// Count of original user requires before call-assumption merging.
    /// Retained for diagnostics/tests.
    pub(in crate::callbacks) base_requires_count: usize,
    /// How many entries of `effective_requires`, starting at
    /// `base_requires_count`, were derived from the BODY's call assumptions
    /// (the assumptions themselves plus their normalized-old, tester/selector
    /// and result-bridged forms).
    ///
    /// Everything outside `base_requires_count .. base_requires_count +
    /// call_assumption_derived_count` is derived from the user's `#[requires]`
    /// clauses — the base clauses themselves, and the mut-ref groundings and
    /// `inv` side conditions appended after the call-assumption region. The
    /// stale-entry-fact drop (`stale_entry_facts`, D-38) needs that split to
    /// remove the ENTRY facts a loop has invalidated without touching the
    /// body's call-assumption facts, which have their own invalidation lane.
    pub(in crate::callbacks) call_assumption_derived_count: usize,
    /// Count of original user ensures before call-obligation merging.
    /// Retained for diagnostics/tests.
    pub(in crate::callbacks) base_ensures_count: usize,
    /// Names of detected mutable reference parameters.
    pub(in crate::callbacks) mut_ref_params: HashSet<String>,
    /// Names of detected closure capture fields (self.0, self.1, etc.).
    pub(in crate::callbacks) closure_capture_fields: HashSet<String>,
}

impl TransformedContract {
    fn debug_assert_base_clause_storage(&self) {
        debug_assert_eq!(
            self.base_requires_count,
            self.base_requires.len(),
            "base requires count must track stored base requires",
        );
        debug_assert_eq!(
            self.base_ensures_count,
            self.base_ensures.len(),
            "base ensures count must track stored base ensures",
        );
        debug_assert!(
            self.effective_requires.starts_with(&self.base_requires),
            "effective requires must keep user clauses as a prefix",
        );
        debug_assert!(
            self.effective_ensures.starts_with(&self.base_ensures),
            "effective ensures must keep user clauses as a prefix",
        );
        debug_assert_eq!(
            &self.effective_ensures[self.base_ensures_count..],
            self.call_obligation_ensures.as_slice(),
            "call obligations must stay in the stored trailing partition",
        );
    }
}

/// Desugar closure-style ensures into applied form (#2676): `|x| body` is
/// `body[x := result]`, read by the same function a call of this function
/// reads the clause with (`formula::elaborate::applied_to_the_result`).
/// `parse_boolean_clause` refuses a closure postcondition of another arity.
fn desugar_closure_ensures(ensures: &[PureExpr]) -> Vec<PureExpr> {
    ensures
        .iter()
        .map(|e| {
            trust_wp_core::formula::elaborate::applied_to_the_result(e)
                .unwrap_or_else(|_| e.clone())
        })
        .collect()
}

/// Transform a parsed contract into effective requires/ensures for verification.
///
/// Applies these transforms in order:
/// 0. Desugar closure-style ensures into applied form (#2676)
/// A. Detect `&mut` parameters (from MIR analysis or old(*x) heuristic)
/// B. Detect closure capture fields and exclude from mut_ref_params (#616)
/// C. Rewrite ensures: `*x` → `^x` (Final) for mut ref params
/// D. Rewrite ensures/requires for closure captures
/// E. Merge call-site assumptions into requires
/// F. Merge call-site obligations into ensures
pub(in crate::callbacks) fn transform_contract(parsed: &ParsedContract) -> TransformedContract {
    // (0) Desugar closure-style ensures (#2676): `|(a, b)| body` → applied form.
    // Must run before all other transforms so downstream steps see plain exprs.
    let desugared_ensures = desugar_closure_ensures(&parsed.ensures);
    let has_current_closure_capture_fields = parsed
        .requires
        .iter()
        .chain(desugared_ensures.iter())
        .any(expr_mentions_self_capture_field);

    // (A) Detect &mut parameters for postcondition transformation (#414, #494)
    let mut mut_ref_params: HashSet<String> = parsed.mut_borrow.mut_ref_param_names.clone();
    if let Some(ref mut_borrow) = parsed.mut_borrow.mut_borrow_body {
        mut_ref_params.extend(mut_borrow.final_values.keys().cloned());
    } else {
        // Fallback heuristic for legacy paths that can mention mut refs only
        // through old(*x) while signature extraction is unavailable.
        for e in &desugared_ensures {
            extract_old_deref_vars(e, &mut mut_ref_params);
        }
    }

    // (B) Identify closure capture fields (#358, #616)
    let closure_capture_fields: HashSet<String> =
        if let Some(ref mut_borrow) = parsed.mut_borrow.mut_borrow_body {
            mut_borrow
                .final_values
                .keys()
                .filter(|k| k.starts_with("self."))
                .cloned()
                .collect()
        } else {
            // Fallback: when mut_borrow_body extraction fails (complex closure
            // bodies), identify closure capture fields from mut_ref_params that
            // have self.N naming, plus any self.N variables referenced via
            // Final(Var("self.N")) or Old(Var("self.N")) patterns in ensures.
            // This enables postcondition transformation even when body extraction
            // can't produce final values. (#2668)
            let mut fallback: HashSet<String> = mut_ref_params
                .iter()
                .filter(|k| k.starts_with("self."))
                .cloned()
                .collect();
            // Also scan ensures for Final(Var("self.N")) patterns that indicate
            // closure capture postcondition usage even when the fallback heuristic
            // in (A) didn't detect them through old(*x) patterns.
            for e in &parsed.ensures {
                extract_final_self_field_vars(e, &mut fallback);
            }
            fallback
        };
    if !closure_capture_fields.is_empty() {
        for field in &closure_capture_fields {
            mut_ref_params.remove(field);
        }
    }

    // (C) Transform ensures: *x -> ^x (Final) for mut ref params
    //
    //     Creusot semantics (soundness): in an `ensures`, `*p` is the value of
    //     the referent at ENTRY and only `^p` is the final value; a clause in
    //     the pre-Creusot dialect (it names a `&mut` param inside `old(..)`)
    //     reads its bare `*p` as the post-state. Every call of this function
    //     reads the clause through the same function
    //     (`formula::elaborate::postcondition_at_a_call`) over the same
    //     parameters (`state_params`, the signature's, not `mut_ref_params`,
    //     which body extraction widens), so the state the body is proved at
    //     is the state every caller is credited with. A pre-Creusot bare `*p`
    //     of a parameter the result may borrow was refused where the clause
    //     was placed (`place_parameter_reads`), in this lane and at each call.
    let mut transformed_ensures: Vec<_> = desugared_ensures
        .iter()
        .map(|e| {
            trust_wp_core::formula::elaborate::postcondition_states(
                e,
                &parsed.mut_borrow.state_params,
            )
        })
        .collect();

    // (D) Transform ensures/requires for closure captures
    let mut transformed_requires = if closure_capture_fields.is_empty() {
        parsed.requires.clone()
    } else {
        transformed_ensures = transformed_ensures
            .into_iter()
            .map(|e| e.transform_closure_capture_postcondition(&closure_capture_fields))
            .collect();
        parsed
            .requires
            .iter()
            .map(|e| e.transform_closure_capture_precondition(&closure_capture_fields))
            .collect()
    };

    let immutable_ref_params = immutable_ref_param_names(parsed, &mut_ref_params);
    if !immutable_ref_params.is_empty() {
        transformed_requires = transformed_requires
            .iter()
            .map(|expr| normalize_immutable_ref_param_vars(expr, &immutable_ref_params))
            .collect();
        transformed_ensures = transformed_ensures
            .iter()
            .map(|expr| normalize_immutable_ref_param_vars(expr, &immutable_ref_params))
            .collect();

        // (D2) `old(e)` over a parameter that is not a `&mut` reads it as the
        // parameter (`formula::elaborate::entry_reads_of_unchanging_params`).
        //
        // Such a parameter cannot change under the caller's feet: the callee
        // may rebind its own copy (`mut p: i32`), but nothing the caller can
        // observe moves, so the entry value and the specification's `p` are the
        // same thing. The encoder does not know that — left inside an `old` it
        // mints a SEPARATE, entirely unconstrained symbol `old_p`, and then
        // any contract relating the two is unprovable. Not merely declined:
        //
        //     #[ensures(result == old(x) + 1)]
        //     pub fn f(mut x: i32) -> i32 { x += 1; x }
        //     trust-wp: f FAILED ✗   counterexample: old_x = 1, x = 0
        //
        // A true contract reported as false, with a "counterexample" whose two
        // values have no relationship at all. `old(v@) + 1`, `old(v@ + 1)` and
        // `old(v@ + i)` were refuted alike while only the exact `old(v)` shape
        // was read as `v`. This is the non-mut-ref counterpart of
        // `verify::mut_borrow::collapse_old_over_mut_ref_currents`, whose
        // `old_body_is_mut_ref_entry_expr` already classifies a non-mut-ref
        // `Var` as an entry-state expression.
        let unchanging = |name: &str| immutable_ref_params.contains(name);
        for clause in transformed_requires
            .iter_mut()
            .chain(transformed_ensures.iter_mut())
        {
            *clause = trust_wp_core::formula::elaborate::entry_reads_of_unchanging_params(
                clause,
                &unchanging,
            );
        }
    }

    // (E) Merge call-site assumptions into requires
    //
    // Call-site assumptions are postconditions extracted by spec_apply, which
    // already binds `self` to the reference directly (#2578). Do NOT apply
    // postcondition transform here — that would transform the reference into
    // `^x` (Final), mismatching the ensures form. (#717)
    let base_requires = transformed_requires;
    let mut effective_requires = base_requires.clone();
    let base_requires_count = base_requires.len();
    let requires_len_before_call_assumptions = effective_requires.len();
    if !parsed.call_assumptions.is_empty() {
        let call_assumptions: Vec<PureExpr> = parsed.call_assumptions.clone();
        effective_requires.extend(call_assumptions.iter().cloned());
        let normalized_old_facts: Vec<PureExpr> = call_assumptions
            .iter()
            .flat_map(normalize_old_constructor_equality_facts)
            .collect();
        if !normalized_old_facts.is_empty() {
            effective_requires.extend(normalized_old_facts.iter().cloned());
        }
        let ctor_tester_selector_facts: Vec<PureExpr> = call_assumptions
            .iter()
            .chain(normalized_old_facts.iter())
            .flat_map(constructor_equality_to_tester_selector_facts)
            .collect();
        if !ctor_tester_selector_facts.is_empty() {
            effective_requires.extend(ctor_tester_selector_facts.iter().cloned());
        }
        if let Some(PureExpr::Var(body_result_name, result_sort)) = parsed.result_expr.as_ref() {
            if body_result_name != "result" {
                let mut substitutions = HashMap::new();
                substitutions.insert(
                    body_result_name.clone(),
                    PureExpr::Var("result".to_string(), result_sort.clone()),
                );
                let bridged: Vec<PureExpr> = parsed
                    .call_assumptions
                    .iter()
                    .map(|a| a.substitute(&substitutions))
                    .collect();
                effective_requires.extend(bridged);
                let bridged_old_facts: Vec<PureExpr> = normalized_old_facts
                    .iter()
                    .map(|a| a.substitute(&substitutions))
                    .collect();
                if !bridged_old_facts.is_empty() {
                    effective_requires.extend(bridged_old_facts);
                }
                let bridged_tester_selector_facts: Vec<PureExpr> = ctor_tester_selector_facts
                    .iter()
                    .map(|a| a.substitute(&substitutions))
                    .collect();
                if !bridged_tester_selector_facts.is_empty() {
                    effective_requires.extend(bridged_tester_selector_facts);
                }
            }
        }
    }
    let call_assumption_derived_count =
        effective_requires.len() - requires_len_before_call_assumptions;
    // Mutable-reference reborrows carry invariant side conditions in Creusot.
    // Keep the pointee invariant for structural type-invariant rewriting, and
    // also add the whole-borrow invariant so clauses like generic_deref.rs'
    // `forall<y: &mut T> inv(y) && *y == *x ==> ...` can use `y = x`. (#717)
    if !mut_ref_params.is_empty() {
        let mut names: Vec<_> = mut_ref_params.iter().cloned().collect();
        names.sort();
        for name in names {
            if name == "self" && has_current_closure_capture_fields {
                continue;
            }
            let whole_borrow = typed_mut_ref_param_expr(parsed, &name);
            let grounded_preconditions: Vec<PureExpr> = base_requires
                .iter()
                .filter_map(|require| {
                    ground_mut_ref_precondition_quantifier(require, &name, &whole_borrow)
                })
                .collect();
            effective_requires.extend(grounded_preconditions);
            effective_requires.push(PureExpr::LogicFnCall {
                name: "inv".to_string(),
                args: vec![whole_borrow],
            });
            effective_requires.push(PureExpr::LogicFnCall {
                name: "inv".to_string(),
                args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(name, None)))],
            });
        }
    }

    // (F) Merge call-site obligations into ensures.
    //
    // Keep `parsed.call_obligations` intact because downstream diagnostics
    // still report the extracted obligations after transformation.
    // (F0) #1075/#1401 returning-path facts premise ONLY the postconditions:
    // `facts ==> ensures`. They are never merged into `effective_requires`,
    // where they would also premise the call obligations merged below (the
    // diverging arm's own call preconditions, and obligations emitted before
    // the diverging switch). Dropped — a completeness cost only — when a
    // `&mut` parameter or a closure capture field is involved, because the
    // facts are stated over the program-point state while those ensures are
    // rewritten to prophecy / capture form.
    if !parsed.returning_path_facts.is_empty()
        && mut_ref_params.is_empty()
        && closure_capture_fields.is_empty()
    {
        let facts = parsed
            .returning_path_facts
            .iter()
            .map(|fact| normalize_immutable_ref_param_vars(fact, &immutable_ref_params))
            .reduce(|lhs, rhs| PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)));
        if let Some(facts) = facts {
            transformed_ensures = transformed_ensures
                .into_iter()
                .map(|ensures| {
                    PureExpr::BinOp(Arc::new(facts.clone()), BinOp::Implies, Arc::new(ensures))
                })
                .collect();
        }
    }
    let mut effective_ensures = transformed_ensures;
    let base_ensures = effective_ensures.clone();
    let base_ensures_count = base_ensures.len();
    let call_obligation_ensures = parsed.call_obligations.clone();
    let pre_loop_call_obligation_ensures = parsed.pre_loop_call_obligations.clone();
    let post_loop_call_obligation_ensures = parsed.post_loop_call_obligations.clone();
    effective_ensures.extend(call_obligation_ensures.iter().cloned());

    let transformed = TransformedContract {
        effective_requires,
        effective_ensures,
        base_requires,
        base_ensures,
        call_obligation_ensures,
        pre_loop_call_obligation_ensures,
        post_loop_call_obligation_ensures,
        base_requires_count,
        call_assumption_derived_count,
        base_ensures_count,
        mut_ref_params,
        closure_capture_fields,
    };
    transformed.debug_assert_base_clause_storage();
    transformed
}

fn expr_mentions_self_capture_field(expr: &PureExpr) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if let PureExpr::Var(name, _) = node {
            found |= is_self_capture_field_name(name);
        }
    });
    found
}

fn is_self_capture_field_name(name: &str) -> bool {
    name.strip_prefix("self.")
        .is_some_and(|field| !field.is_empty() && field.bytes().all(|byte| byte.is_ascii_digit()))
}

pub(in crate::callbacks) fn immutable_ref_param_names(
    parsed: &ParsedContract,
    mut_ref_params: &HashSet<String>,
) -> HashSet<String> {
    parsed
        .arg_names
        .iter()
        .filter(|name| !mut_ref_params.contains(*name))
        .cloned()
        .collect()
}

pub(in crate::callbacks) fn normalize_immutable_ref_param_vars(
    expr: &PureExpr,
    immutable_ref_params: &HashSet<String>,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, Some(ExprSort::Ref(inner))) if immutable_ref_params.contains(name) => {
            PureExpr::Var(name.clone(), Some((**inner).clone()))
        }
        PureExpr::Deref(inner) => {
            if let PureExpr::Var(name, Some(ExprSort::Ref(inner_sort))) = inner.as_ref() {
                if immutable_ref_params.contains(name) {
                    return PureExpr::Var(name.clone(), Some((**inner_sort).clone()));
                }
            }
            PureExpr::Deref(Arc::new(normalize_immutable_ref_param_vars(
                inner,
                immutable_ref_params,
            )))
        }
        PureExpr::BinOp(lhs, op, rhs) => PureExpr::BinOp(
            Arc::new(normalize_immutable_ref_param_vars(
                lhs,
                immutable_ref_params,
            )),
            *op,
            Arc::new(normalize_immutable_ref_param_vars(
                rhs,
                immutable_ref_params,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(normalize_immutable_ref_param_vars(
                inner,
                immutable_ref_params,
            )),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(normalize_immutable_ref_param_vars(
                cond,
                immutable_ref_params,
            )),
            Arc::new(normalize_immutable_ref_param_vars(
                then_expr,
                immutable_ref_params,
            )),
            Arc::new(normalize_immutable_ref_param_vars(
                else_expr,
                immutable_ref_params,
            )),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(normalize_immutable_ref_param_vars(
            inner,
            immutable_ref_params,
        ))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(normalize_immutable_ref_param_vars(
            inner,
            immutable_ref_params,
        ))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(normalize_immutable_ref_param_vars(
            inner,
            immutable_ref_params,
        ))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(normalize_immutable_ref_param_vars(
                receiver,
                immutable_ref_params,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| normalize_immutable_ref_param_vars(arg, immutable_ref_params))
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(normalize_immutable_ref_param_vars(
                body,
                immutable_ref_params,
            )),
            triggers: triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|part| normalize_immutable_ref_param_vars(part, immutable_ref_params))
                        .collect()
                })
                .collect(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(normalize_immutable_ref_param_vars(
                body,
                immutable_ref_params,
            )),
            triggers: triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|part| normalize_immutable_ref_param_vars(part, immutable_ref_params))
                        .collect()
                })
                .collect(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(normalize_immutable_ref_param_vars(
                scrutinee,
                immutable_ref_params,
            )),
            arms: arms
                .iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern.clone(),
                    body: normalize_immutable_ref_param_vars(&arm.body, immutable_ref_params),
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| normalize_immutable_ref_param_vars(arg, immutable_ref_params))
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(normalize_immutable_ref_param_vars(
                value,
                immutable_ref_params,
            )),
            body: Arc::new(normalize_immutable_ref_param_vars(
                body,
                immutable_ref_params,
            )),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(normalize_immutable_ref_param_vars(
                assumption,
                immutable_ref_params,
            )),
            body: Arc::new(normalize_immutable_ref_param_vars(
                body,
                immutable_ref_params,
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(normalize_immutable_ref_param_vars(
                obligation,
                immutable_ref_params,
            )),
            body: Arc::new(normalize_immutable_ref_param_vars(
                body,
                immutable_ref_params,
            )),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params: params.clone(),
            body: Arc::new(normalize_immutable_ref_param_vars(
                body,
                immutable_ref_params,
            )),
        },
        _ => expr.clone(),
    }
}

fn typed_mut_ref_param_expr(parsed: &ParsedContract, name: &str) -> PureExpr {
    parsed
        .mut_borrow
        .mut_borrow_body
        .as_ref()
        .and_then(|body| body.final_values.get(name))
        .and_then(|expr| match expr {
            PureExpr::Deref(inner) => match inner.as_ref() {
                PureExpr::Var(var_name, sort) if var_name == name => {
                    Some(PureExpr::Var(var_name.clone(), sort.clone()))
                }
                _ => None,
            },
            _ => None,
        })
        .unwrap_or_else(|| PureExpr::Var(name.to_string(), None))
}

fn ground_mut_ref_precondition_quantifier(
    expr: &PureExpr,
    param_name: &str,
    whole_borrow: &PureExpr,
) -> Option<PureExpr> {
    let PureExpr::Forall { var, body, .. } = expr else {
        return None;
    };
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = body.as_ref() else {
        return None;
    };
    if !is_mut_ref_invariant_antecedent(antecedent, var, param_name) {
        return None;
    }
    let PureExpr::MethodCall { method, args, .. } = consequent.as_ref() else {
        return None;
    };
    if method != "precondition"
        || !matches!(args.as_slice(), [PureExpr::Var(name, _)] if name == var)
    {
        return None;
    }

    let mut substitutions = HashMap::new();
    substitutions.insert(var.clone(), whole_borrow.clone());
    Some(consequent.substitute(&substitutions))
}

fn is_mut_ref_invariant_antecedent(expr: &PureExpr, quant_var: &str, param_name: &str) -> bool {
    let PureExpr::BinOp(left, BinOp::And, right) = expr else {
        return false;
    };
    (is_inv_of_var(left, quant_var) && is_same_pointee_eq(right, quant_var, param_name))
        || (is_inv_of_var(right, quant_var) && is_same_pointee_eq(left, quant_var, param_name))
}

fn is_inv_of_var(expr: &PureExpr, var: &str) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if name == "inv"
                && matches!(args.as_slice(), [PureExpr::Var(arg, _)] if arg == var)
    )
}

fn is_same_pointee_eq(expr: &PureExpr, quant_var: &str, param_name: &str) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return false;
    };
    (is_deref_of_var(left, quant_var) && is_deref_of_var(right, param_name))
        || (is_deref_of_var(right, quant_var) && is_deref_of_var(left, param_name))
}

fn is_deref_of_var(expr: &PureExpr, var: &str) -> bool {
    matches!(
        expr,
        PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == var)
    )
}

// ── Phase 5b: SSA renaming for sequential mutations (#2124) ──────────

/// Rewrite `Final^k` chains in call_assumptions to use SSA intermediates.
///
/// When a `&mut` parameter `v` is mutated N times sequentially, the extraction
/// pipeline produces call_assumptions with increasing `Final` depth:
///
/// ```text
/// View(Final(Var("v")))         == push_back(View(Deref(Var("v"))), 0)   // depth 1
/// View(Final(Final(Var("v"))))  == push_back(View(Final(Var("v"))), 1)   // depth 2
/// ```
///
/// In the ay layer, `Final(Var("v"))` resolves to `v_final` and
/// `Final(Final(Var("v")))` resolves to `v_final_final`. But postconditions
/// only reference `v_final` (= `^v@`), so the chain is disconnected: `v_final`
/// is constrained by call 1, and `v_final_final` by call 2, but the postcondition
/// `^v@ == push_back(push_back(*v@, 0), 1)` references only `v_final`.
///
/// This function rewrites intermediate depths to fresh SSA variables:
///
/// ```text
/// View(Var("v_ssa_1"))    == push_back(View(Deref(Var("v"))), 0)   // depth 1 → ssa_1
/// View(Final(Var("v")))   == push_back(View(Var("v_ssa_1")), 1)    // depth 2 → v_final
/// ```
///
/// The maximum depth maps to `Final(Var("v"))` so the postcondition connects.
/// Only applied to mut borrow verification contexts where `v_final` is the prophecy.
pub(in crate::callbacks) fn ssa_rename_call_assumptions(assumptions: &mut [PureExpr]) -> bool {
    // Phase 1: scan for max Final depth per variable name.
    let mut max_depth: HashMap<String, usize> = HashMap::new();
    for assumption in assumptions.iter() {
        scan_final_depth(assumption, &mut max_depth);
    }

    // Only rename variables that have depth > 1 (sequential mutations).
    let rename_targets: HashMap<String, usize> = max_depth
        .into_iter()
        .filter(|&(_, depth)| depth > 1)
        .collect();

    if rename_targets.is_empty() {
        return false;
    }

    // Phase 2: rewrite assumptions in place.
    for assumption in assumptions.iter_mut() {
        *assumption = rewrite_final_chains(assumption, &rename_targets);
    }

    true
}

/// Recursively scan a PureExpr for `Final^N(Var(name))` and `Final^N(Deref(Var(name)))`
/// patterns, recording the maximum depth per variable name.
fn scan_final_depth(expr: &PureExpr, max_depth: &mut HashMap<String, usize>) {
    expr.for_each_recursive(|node| {
        if let Some((name, depth)) = measure_final_chain(node) {
            if depth > 0 {
                let entry = max_depth.entry(name).or_insert(0);
                if depth > *entry {
                    *entry = depth;
                }
            }
        }
    });
}

/// Measure the Final chain depth of an expression, returning the base variable
/// name and depth if the expression is `Final^N(Var(name))` or `Final^N(Deref(Var(name)))`.
fn measure_final_chain(expr: &PureExpr) -> Option<(String, usize)> {
    match expr {
        PureExpr::Final(inner) => {
            if let Some((name, depth)) = measure_final_chain(inner) {
                Some((name, depth + 1))
            } else {
                None
            }
        }
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some((name.clone(), 0)),
            _ => None,
        },
        PureExpr::Var(name, _) => Some((name.clone(), 0)),
        _ => None,
    }
}

/// Rewrite `Final^k` chains to SSA variables. For a variable with max depth N:
/// - `Final^k(base)` where k < N → replace with SSA variable `{name}_ssa_{k}`
/// - `Final^N(base)` → collapse to `Final(base_without_finals)` (= `v_final`)
fn rewrite_final_chains(expr: &PureExpr, targets: &HashMap<String, usize>) -> PureExpr {
    // Check if this entire expression is a Final chain that should be rewritten.
    if let Some(rewritten) = try_rewrite_chain(expr, targets) {
        return rewritten;
    }
    // Not a rewritable chain — recurse into children.
    rewrite_children(expr, targets)
}

/// Try to rewrite a Final chain expression. Returns `Some` if the expression
/// is a `Final^k(Var(name))` chain that maps to a rename target.
fn try_rewrite_chain(expr: &PureExpr, targets: &HashMap<String, usize>) -> Option<PureExpr> {
    let (name, depth) = measure_final_chain(expr)?;
    let &max = targets.get(&name)?;
    if depth > 0 && depth < max {
        // Intermediate: replace with SSA variable.
        let base = strip_finals(expr);
        let ssa_name = format!("{name}_ssa_{depth}");
        Some(match base {
            PureExpr::Deref(inner) => match inner.as_ref() {
                PureExpr::Var(_, sort) => {
                    PureExpr::Deref(Arc::new(PureExpr::Var(ssa_name, sort.clone())))
                }
                _ => PureExpr::Var(ssa_name, None),
            },
            PureExpr::Var(_, sort) => PureExpr::Var(ssa_name, sort.clone()),
            _ => PureExpr::Var(ssa_name, None),
        })
    } else if depth == max {
        // Maximum depth: collapse to Final(base) so it maps to v_final.
        Some(PureExpr::Final(Arc::new(strip_finals(expr))))
    } else {
        None
    }
}

/// Recursively rewrite children of a PureExpr, applying SSA renaming.
fn rewrite_children(expr: &PureExpr, targets: &HashMap<String, usize>) -> PureExpr {
    let rewrite = |child: &PureExpr| rewrite_final_chains(child, targets);
    match expr {
        PureExpr::BinOp(lhs, op, rhs) => {
            PureExpr::BinOp(Arc::new(rewrite(lhs)), *op, Arc::new(rewrite(rhs)))
        }
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, Arc::new(rewrite(inner))),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(rewrite(inner))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(rewrite(inner))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(rewrite(inner))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(rewrite(inner))),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(rewrite(cond)),
            Arc::new(rewrite(then_expr)),
            Arc::new(rewrite(else_expr)),
        ),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(rewrite(receiver)),
            method: method.clone(),
            args: args.iter().map(rewrite).collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args.iter().map(rewrite).collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(rewrite(body)),
            triggers: triggers
                .iter()
                .map(|trigger| trigger.iter().map(rewrite).collect())
                .collect(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(rewrite(body)),
            triggers: triggers
                .iter()
                .map(|trigger| trigger.iter().map(rewrite).collect())
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(rewrite(value)),
            body: Arc::new(rewrite(body)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(rewrite(assumption)),
            body: Arc::new(rewrite(body)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(rewrite(obligation)),
            body: Arc::new(rewrite(body)),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(rewrite(scrutinee)),
            arms: arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: rewrite(&arm.body),
                })
                .collect(),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params: params.clone(),
            body: Arc::new(rewrite(body)),
        },
        PureExpr::Var(..) | PureExpr::Bool(_) | PureExpr::Int(_) => expr.clone(),
        #[allow(unreachable_patterns)]
        _ => expr.clone(),
    }
}

/// Strip all `Final(...)` wrappers from an expression, returning the innermost
/// non-Final expression.
fn strip_finals(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Final(inner) => strip_finals(inner),
        _ => expr.clone(),
    }
}

#[cfg(test)]
#[path = "contract_transform_tests.rs"]
mod tests;
