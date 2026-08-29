// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-slice obligation verification for mutable-borrow contracts.
//!
//! Contains [`verify_mut_borrow_single_obligation_slice`], which encodes and
//! negates one postcondition and then delegates to the shared solver tail.
//! The duplicated `MutBorrowSliceContext` was replaced by
//! [`super::super::solver_tail::ObligationSliceContext`]. (#1576)

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    sync::Arc,
};

use tracing::debug;
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_logic_fn_arity},
    BinOp, ExprSort, PureExpr,
};

use super::{
    super::{
        encode_negated_postcondition,
        function::obligation::{
            prove_implication_false_guard_with_solver,
            sequence_tail_reverse_push_front_index_proof_assert_follows_requires,
            sequence_tail_reverse_push_front_index_proof_assert_matches,
        },
        solver_tail::{AliasConstraintMode, ObligationSliceContext},
        Counterexample, PostconditionInfo, ResolveContinuation, UnknownReason, VerificationResult,
    },
    helpers::canonicalize_mut_ref_vars,
};
use crate::{
    encoder::{
        sort_context::{resolve_nameable_expr, resolve_view_var_name},
        unsoundness, AYEncoder, AssertionPhase,
    },
    error::EncodingError,
};

fn current_state_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) => current_state_name(inner.as_ref()),
        _ => None,
    }
}

fn eager_fn_mut_ground_ensure<'a>(
    ensure: &'a PureExpr,
    mut_borrow_final_values: Option<&'a std::collections::HashMap<String, PureExpr>>,
) -> Cow<'a, PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = ensure
    else {
        debug!(
            "[TRUST_WP_DEBUG] eager fn_mut grounding skipped: non-method-call ensure={ensure:?}"
        );
        return Cow::Borrowed(ensure);
    };

    if method == "postcondition_mut" {
        debug!("[TRUST_WP_DEBUG] eager fn_mut grounding passthrough: already postcondition_mut ensure={ensure:?}");
        return Cow::Borrowed(ensure);
    }

    if method != "postcondition" || args.is_empty() {
        debug!(
            "[TRUST_WP_DEBUG] eager fn_mut grounding skipped: method={method:?} args_len={} ensure={ensure:?}",
            args.len()
        );
        return Cow::Borrowed(ensure);
    }

    let Some(final_values) = mut_borrow_final_values else {
        debug!(
            "[TRUST_WP_DEBUG] eager fn_mut grounding skipped: missing mut-borrow final_values for raw ensure={ensure:?}"
        );
        return Cow::Borrowed(ensure);
    };

    let Some(state_name) = current_state_name(&args[0]) else {
        debug!(
            "[TRUST_WP_DEBUG] eager fn_mut grounding skipped: cannot name raw state arg {:?} for ensure={ensure:?}",
            args[0]
        );
        return Cow::Borrowed(ensure);
    };

    let Some(res_state) = final_values.get(state_name) else {
        debug!(
            "[TRUST_WP_DEBUG] eager fn_mut grounding skipped: missing final value binding for {state_name} in ensure={ensure:?}"
        );
        return Cow::Borrowed(ensure);
    };

    let mut mut_args = args[..args.len() - 1].to_vec();
    mut_args.push(res_state.clone());
    mut_args.push(args.last().expect("non-empty args").clone());

    Cow::Owned(PureExpr::MethodCall {
        receiver: Arc::clone(receiver),
        method: "postcondition_mut".to_string(),
        args: mut_args,
    })
}

fn direct_result_equality_matches_return_expr(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    mut_borrow_final_values: Option<&std::collections::HashMap<String, PureExpr>>,
) -> bool {
    let Some(return_expr) = return_expr else {
        return false;
    };
    let Some(final_values) = mut_borrow_final_values else {
        return false;
    };
    if direct_result_ite_matches_return_expr(ensure, return_expr, final_values) {
        return true;
    }
    let Some(expected) = result_equality_other_side(ensure) else {
        return false;
    };

    let param_names: HashSet<&str> = final_values.keys().map(String::as_str).collect();
    let return_body = strip_let_assume(return_expr);
    let canonical_return = canonicalize_mut_ref_vars(return_body, &param_names);
    let expected = normalize_identity_finals(expected, final_values);
    let canonical_expected = canonicalize_mut_ref_vars(&expected, &param_names);
    direct_result_exprs_match(&canonical_return, &canonical_expected, &param_names)
}

fn result_view_len_matches_return_expr(ensure: &PureExpr, return_expr: Option<&PureExpr>) -> bool {
    let Some(return_expr) = return_expr.map(strip_let_assume) else {
        return false;
    };
    let Some(expected_len) = known_seq_len(return_expr) else {
        return false;
    };
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    result_view_len_equals_int(left, right, expected_len)
        || result_view_len_equals_int(right, left, expected_len)
}

fn result_view_len_equals_int(candidate: &PureExpr, other: &PureExpr, expected_len: i64) -> bool {
    matches!(other, PureExpr::Int(value) if *value == expected_len)
        && matches!(
            candidate,
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if method == "len"
                && args.is_empty()
                && matches!(receiver.as_ref(), PureExpr::View(inner) if is_result_var(inner))
        )
}

pub(super) fn seq_push_back_index_matches_requirements(
    requires: &[PureExpr],
    ensure: &PureExpr,
) -> Option<VerificationResult> {
    let (base, appended_value, index, expected_value) = push_back_index_equality(ensure)?;
    let index = int_expr_value(index)?;
    let base_len = requires
        .iter()
        .find_map(|require| required_seq_len(require, base))?;
    if base_len != index {
        return None;
    }

    let exprs_equal = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
    if exprs_equal(appended_value, expected_value) {
        return Some(VerificationResult::Verified(None));
    }
    match (
        int_expr_value(appended_value),
        int_expr_value(expected_value),
    ) {
        (Some(appended), Some(expected)) if appended != expected => {
            Some(VerificationResult::Failed(Counterexample::empty()))
        }
        _ => None,
    }
}

fn seq_push_back_chain_postcondition_follows_requirements(
    requires: &[PureExpr],
    ensure: &PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    let Some(assignments) = seq_push_back_chain_assignments(
        requires,
        mut_borrow_final_values,
        mutation_continued_params,
    ) else {
        return false;
    };
    if assignments.is_empty() {
        return false;
    }

    let expanded_left = expand_seq_push_back_chain_expr(
        left,
        &assignments,
        mut_borrow_final_values,
        mutation_continued_params,
        &mut HashSet::new(),
    );
    let expanded_right = expand_seq_push_back_chain_expr(
        right,
        &assignments,
        mut_borrow_final_values,
        mutation_continued_params,
        &mut HashSet::new(),
    );
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
        &expanded_left,
        &expanded_right,
    )
}

fn seq_push_back_assignments_are_contradictory(
    requires: &[PureExpr],
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> bool {
    let mut assignments: HashMap<String, (&PureExpr, &PureExpr)> = HashMap::new();
    for require in requires {
        for conjunct in flatten_and_conjuncts(require) {
            let Some((target, base, value)) = seq_push_back_direct_assignment(
                conjunct,
                mut_borrow_final_values,
                mutation_continued_params,
            ) else {
                continue;
            };
            let Some((existing_base, existing_value)) = assignments.get(&target) else {
                assignments.insert(target, (base, value));
                continue;
            };
            if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
                existing_base,
                base,
            ) && distinct_int_literals(existing_value, value)
            {
                return true;
            }
        }
    }
    false
}

fn seq_push_back_direct_assignment<'a>(
    expr: &'a PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> Option<(String, &'a PureExpr, &'a PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    seq_push_back_direct_assignment_sides(
        left,
        right,
        mut_borrow_final_values,
        mutation_continued_params,
    )
    .or_else(|| {
        seq_push_back_direct_assignment_sides(
            right,
            left,
            mut_borrow_final_values,
            mutation_continued_params,
        )
    })
}

fn seq_push_back_direct_assignment_sides<'a>(
    target: &PureExpr,
    value: &'a PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> Option<(String, &'a PureExpr, &'a PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = value
    else {
        return None;
    };
    if !matches!(method.as_str(), "push_back" | "push_back_ghost") {
        return None;
    }
    let [appended] = args.as_slice() else {
        return None;
    };
    let target = seq_chain_alias_key(target, mut_borrow_final_values, mutation_continued_params)?;
    Some((target, receiver.as_ref(), appended))
}

fn distinct_int_literals(left: &PureExpr, right: &PureExpr) -> bool {
    matches!((left, right), (PureExpr::Int(a), PureExpr::Int(b)) if a != b)
}

fn seq_push_back_chain_assignments(
    requires: &[PureExpr],
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> Option<HashMap<String, PureExpr>> {
    let mut assignments = HashMap::new();
    for require in requires {
        for conjunct in flatten_and_conjuncts(require) {
            let Some((target, value)) = seq_push_back_chain_assignment(
                conjunct,
                mut_borrow_final_values,
                mutation_continued_params,
            ) else {
                continue;
            };
            if let Some(existing) = assignments.get(&target) {
                if !crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
                    existing, &value,
                ) {
                    return None;
                }
            } else {
                assignments.insert(target, value);
            }
        }
    }
    Some(assignments)
}

fn seq_push_back_chain_assignment(
    expr: &PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> Option<(String, PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    seq_push_back_chain_assignment_sides(
        left,
        right,
        mut_borrow_final_values,
        mutation_continued_params,
    )
    .or_else(|| {
        seq_push_back_chain_assignment_sides(
            right,
            left,
            mut_borrow_final_values,
            mutation_continued_params,
        )
    })
}

fn seq_push_back_chain_assignment_sides(
    target: &PureExpr,
    value: &PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> Option<(String, PureExpr)> {
    if !seq_expr_contains_push_back(value) {
        return None;
    }
    let target = seq_chain_alias_key(target, mut_borrow_final_values, mutation_continued_params)?;
    Some((target, value.clone()))
}

fn expand_seq_push_back_chain_expr(
    expr: &PureExpr,
    assignments: &HashMap<String, PureExpr>,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
    seen: &mut HashSet<String>,
) -> PureExpr {
    if let Some(key) = seq_chain_alias_key(expr, mut_borrow_final_values, mutation_continued_params)
    {
        if let Some(replacement) = assignments.get(&key) {
            if seen.insert(key) {
                return expand_seq_push_back_chain_expr(
                    replacement,
                    assignments,
                    mut_borrow_final_values,
                    mutation_continued_params,
                    seen,
                );
            }
        }
    }

    match expr {
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(expand_seq_push_back_chain_expr(
                left,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
            *op,
            Arc::new(expand_seq_push_back_chain_expr(
                right,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(expand_seq_push_back_chain_expr(
                inner,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
        ),
        PureExpr::Ite(cond, then_branch, else_branch) => PureExpr::Ite(
            Arc::new(expand_seq_push_back_chain_expr(
                cond,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
            Arc::new(expand_seq_push_back_chain_expr(
                then_branch,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
            Arc::new(expand_seq_push_back_chain_expr(
                else_branch,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(expand_seq_push_back_chain_expr(
            inner,
            assignments,
            mut_borrow_final_values,
            mutation_continued_params,
            seen,
        ))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(expand_seq_push_back_chain_expr(
            inner,
            assignments,
            mut_borrow_final_values,
            mutation_continued_params,
            seen,
        ))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(expand_seq_push_back_chain_expr(
            inner,
            assignments,
            mut_borrow_final_values,
            mutation_continued_params,
            seen,
        ))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(expand_seq_push_back_chain_expr(
            inner,
            assignments,
            mut_borrow_final_values,
            mutation_continued_params,
            seen,
        ))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(expand_seq_push_back_chain_expr(
                receiver,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| {
                    expand_seq_push_back_chain_expr(
                        arg,
                        assignments,
                        mut_borrow_final_values,
                        mutation_continued_params,
                        seen,
                    )
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| {
                    expand_seq_push_back_chain_expr(
                        arg,
                        assignments,
                        mut_borrow_final_values,
                        mutation_continued_params,
                        seen,
                    )
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(expand_seq_push_back_chain_expr(
                value,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
            body: Arc::new(expand_seq_push_back_chain_expr(
                body,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(expand_seq_push_back_chain_expr(
                assumption,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
            body: Arc::new(expand_seq_push_back_chain_expr(
                body,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(expand_seq_push_back_chain_expr(
                obligation,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
            body: Arc::new(expand_seq_push_back_chain_expr(
                body,
                assignments,
                mut_borrow_final_values,
                mutation_continued_params,
                seen,
            )),
        },
        other => other.clone(),
    }
}

fn seq_chain_alias_key(
    expr: &PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> Option<String> {
    let name = resolve_view_var_name(expr, None).or_else(|| resolve_nameable_expr(expr, None))?;
    Some(canonical_seq_chain_alias_key(
        &name,
        mut_borrow_final_values,
        mutation_continued_params,
    ))
}

fn canonical_seq_chain_alias_key(
    name: &str,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> String {
    let Some(base) = name
        .strip_prefix("final_")
        .and_then(|name| name.strip_suffix("_current_view"))
    else {
        return name.to_string();
    };
    let can_alias = mut_borrow_final_values.is_some_and(|final_values| {
        final_values.contains_key(base)
            && mutation_continued_params.is_some_and(|params| params.contains(base))
    });
    if can_alias {
        format!("final_{base}_view")
    } else {
        name.to_string()
    }
}

fn seq_expr_contains_push_back(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall { method, .. }
            if matches!(method.as_str(), "push_back" | "push_back_ghost") =>
        {
            true
        }
        PureExpr::BinOp(left, _, right) => {
            seq_expr_contains_push_back(left) || seq_expr_contains_push_back(right)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => seq_expr_contains_push_back(inner),
        PureExpr::Ite(cond, then_branch, else_branch) => {
            seq_expr_contains_push_back(cond)
                || seq_expr_contains_push_back(then_branch)
                || seq_expr_contains_push_back(else_branch)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            seq_expr_contains_push_back(receiver) || args.iter().any(seq_expr_contains_push_back)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(seq_expr_contains_push_back),
        PureExpr::Let { value, body, .. } => {
            seq_expr_contains_push_back(value) || seq_expr_contains_push_back(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            seq_expr_contains_push_back(assumption) || seq_expr_contains_push_back(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            seq_expr_contains_push_back(obligation) || seq_expr_contains_push_back(body)
        }
        _ => false,
    }
}

fn verified_structural_result_enabled(result: &VerificationResult) -> bool {
    !matches!(result, VerificationResult::Verified(_))
}

fn prove_materialized_verified_consequence(
    encoder: &mut AYEncoder,
    obligation_index: usize,
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError> {
    let grounded_ensure = eager_fn_mut_ground_ensure(ensure, ctx.mut_borrow_final_values);
    let term = encoder.encode_pure(grounded_ensure.as_ref())?;
    encoder.assert_term(term);
    encoder.assert_eager_fn_mut_ground_instantiation(grounded_ensure.as_ref())?;
    encoder.assert_eager_fn_once_ground_instantiation(grounded_ensure.as_ref())?;
    // Now that the (possibly deeply-nested) prophecy length symbols of slice
    // params have been declared by encoding the goal, link their `seq_len`s.
    if let Some(slice_vars) = ctx.slice_length_stable_vars {
        for var_name in slice_vars {
            super::resolve::emit_slice_length_preservation(encoder, var_name);
        }
    }

    // Snapshot the BASE stack (preconditions/resolve facts, WITHOUT this
    // obligation's negated goal) for the batch precheck's vacuity shield below.
    let base_smt = encoder.solver().to_smtlib2();
    let negated = encoder.solver_mut().not(term);
    encoder.push_scope()?;
    let goal_label_prefix =
        format!("__trust_wp_mut_borrow_materialized_consequence_{obligation_index}");
    // Returns `None` when the fresh-parse batch precheck already proved the slice
    // (UNSAT with a consistent base); otherwise `Some(<incremental verdict>)`.
    let mut batch_proof_summary = None;
    let solve_result: Option<ay_dpll::api::SolveResult> =
        encoder.with_negated_goal_label_prefix(goal_label_prefix, |encoder| {
            encoder.with_assertion_phase(
                AssertionPhase::NegatedPostcondition,
                |encoder| -> Result<(), EncodingError> {
                    encoder.assert_term(negated);
                    Ok(())
                },
            )?;
            // Fresh-parse precheck (same SOUND mechanism as the pure-function path,
            // solver_tail:1874, extended to UF-bearing quantifier-free obligations):
            // the INCREMENTAL solver churns the full deadline on UF+LIA mut-ref
            // resolve stacks (take_max / rusthorn/inc_max) and is then hard-killed,
            // while a fresh non-incremental parse of the IDENTICAL stack closes them
            // in <1s (measured 0.006s). Accept ONLY when the full stack is UNSAT AND
            // a fresh re-solve of the base (sans negated goal) is SAT — a stronger
            // vacuity shield than the unsat-core path below (see SOUNDNESS NOTE).
            if !crate::verify::solver_tail::in_proof_assert_mode() {
                if let Some(summary) = encoder.batch_resolve_current_stack_unsat() {
                    if encoder.batch_base_smt_is_sat(&base_smt) {
                        batch_proof_summary = Some(summary);
                        return Ok::<_, EncodingError>(None);
                    }
                }
            }
            Ok::<_, EncodingError>(Some(encoder.check_sat()))
        })?;
    let result = match solve_result {
        // Batch precheck proved the slice (UNSAT) with a consistent base. Retain
        // the exact independently checked artifact rather than manufacturing a
        // certificate-free accepted verdict.
        None => VerificationResult::Verified(batch_proof_summary),
        // AY deliberately pads a missing/lost unsat core with all named
        // assertions, so goal-label membership alone is not evidence that the
        // goal was load-bearing. Pop the negated goal and accept only after a
        // detached, model-validated SAT replay of the exact base (with the
        // textual and rebuilt-base paths retained as conservative fallbacks).
        // Detached checks preserve the live full-stack UNSAT evidence.
        Some(ay_dpll::api::SolveResult::Unsat(_)) => {
            // Establish THIS refutation's strict proof authority while the
            // negated goal is still on the stack. The long-lived incremental
            // encoder runs with `set_produce_proofs(false)` by design
            // (`encoder/constructors.rs`), so an incremental `Unsat` never
            // carries an artifact of its own; the comment there states the
            // contract this arm was not honouring — "authority lanes use
            // isolated strict replay and attach its artifact". Without it the
            // arm manufactured exactly the certificate-free `Verified(None)`
            // that the sibling batch-precheck arm above explicitly refuses to
            // manufacture, and the mandatory authority gate then demoted a
            // hole-free, strictly verified refutation to
            // `Unknown(ProofTrusted)`.
            //
            // This must run BEFORE `pop_scope` and before the
            // base-consistency replays below: those are later solver activity
            // over a DIFFERENT stack (the base, without the goal), so an
            // artifact recovered after them would not be this UNSAT's.
            //
            // Fail-closed by construction.
            // `batch_current_stack_unsat_reactive` re-solves the SAME closed
            // query in a fresh proof-enabled solver and returns `Some` only on
            // proof-checked UNSAT; it yields `None` on a raw or unavailable
            // proof, and any summary carrying a trust step, a hole, or a
            // failed strict verdict is still demoted by `apply_strict_trust`
            // exactly as before. The vacuity shield below is untouched and
            // still decides whether the slice is accepted at all — this only
            // stops an accepted verdict from discarding its own evidence.
            let proof_summary = encoder.batch_current_stack_unsat_reactive();
            encoder.pop_scope()?;
            let exact_base_is_sat = encoder.batch_current_stack_is_sat();
            let parsed_base_is_sat = exact_base_is_sat || encoder.batch_base_smt_is_sat(&base_smt);
            let rebuilt_base = if parsed_base_is_sat {
                None
            } else {
                ctx.fresh_base_recheck.map(|recheck| recheck())
            };
            let rebuilt_base_is_sat = rebuilt_base
                .as_ref()
                .is_some_and(|result| matches!(result, Ok(VerificationResult::Verified(_))));
            let result = if parsed_base_is_sat || rebuilt_base_is_sat {
                VerificationResult::Verified(proof_summary)
            } else {
                VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
                    "materialized mut-borrow consequence has no validated SAT base; \
                     proof may be vacuous (fresh base: {rebuilt_base:?})"
                )))
            };
            return Ok(ResolveContinuation::Continue(result));
        }
        Some(ay_dpll::api::SolveResult::Sat) => {
            let model = encoder.get_model();
            VerificationResult::Failed(Counterexample::from_encoder_model(encoder, model))
        }
        Some(ay_dpll::api::SolveResult::Unknown) => {
            super::super::solver_tail::unknown_result_from_encoder(encoder)
        }
        #[allow(unreachable_patterns)]
        Some(_) => super::super::solver_tail::unknown_result_from_encoder(encoder),
    };
    encoder.pop_scope()?;
    Ok(ResolveContinuation::Continue(result))
}

fn push_back_index_equality(
    expr: &PureExpr,
) -> Option<(&PureExpr, &PureExpr, &PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    push_back_index_side(left)
        .map(|(base, value, index)| (base, value, index, right.as_ref()))
        .or_else(|| {
            push_back_index_side(right)
                .map(|(base, value, index)| (base, value, index, left.as_ref()))
        })
}

fn push_back_index_side(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if !matches!(method.as_str(), "index" | "index_logic") || args.len() != 1 {
        return None;
    }

    let PureExpr::MethodCall {
        receiver: base,
        method: push_method,
        args: push_args,
    } = receiver.as_ref()
    else {
        return None;
    };
    if !matches!(push_method.as_str(), "push_back" | "push_back_ghost") || push_args.len() != 1 {
        return None;
    }
    Some((base.as_ref(), &push_args[0], &args[0]))
}

fn required_seq_len(require: &PureExpr, expected_base: &PureExpr) -> Option<i64> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = require else {
        return None;
    };
    required_seq_len_side(left, right, expected_base)
        .or_else(|| required_seq_len_side(right, left, expected_base))
}

fn required_seq_len_side(
    candidate: &PureExpr,
    other: &PureExpr,
    expected_base: &PureExpr,
) -> Option<i64> {
    let exprs_equal = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
    if exprs_equal(candidate, expected_base) {
        return known_seq_len(other);
    }
    match candidate {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "len" && args.is_empty() && exprs_equal(receiver, expected_base) => {
            int_expr_value(other)
        }
        _ => None,
    }
}

fn int_expr_value(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        _ => None,
    }
}

pub(super) fn sequence_lasso_proof_assert_matches_exact(
    ensure: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    let local_match = sequence_lasso_guarded_proof_assert_matches_exact(ensure)
        || sequence_lasso_bare_forall_follows_exact_requires(ensure, requires);
    local_match
        && (sequence_tail_reverse_push_front_index_proof_assert_matches(ensure)
            || sequence_tail_reverse_push_front_index_proof_assert_follows_requires(
                ensure, requires,
            ))
}

fn sequence_lasso_guarded_proof_assert_matches_exact(ensure: &PureExpr) -> bool {
    let PureExpr::BinOp(guard, BinOp::Implies, quantified) = ensure else {
        return false;
    };
    let Some(seq) = sequence_lasso_len_gt_zero_guard_sequence(guard) else {
        return false;
    };
    sequence_lasso_quantifier_matches_exact(quantified, seq)
}

fn sequence_lasso_bare_forall_follows_exact_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    let conjuncts = sequence_lasso_requirement_conjuncts(requires);
    conjuncts.iter().any(|require| {
        sequence_lasso_len_gt_zero_guard_sequence(require).is_some_and(|seq| {
            sequence_lasso_quantifier_matches_exact(ensure, seq)
                || conjuncts.iter().any(|alias_require| {
                    sequence_lasso_explicit_alias_for(seq, alias_require)
                        .is_some_and(|alias| sequence_lasso_quantifier_matches_exact(ensure, alias))
                })
        })
    })
}

fn sequence_lasso_requirement_conjuncts(requires: &[PureExpr]) -> Vec<&PureExpr> {
    let mut conjuncts = Vec::new();
    for require in requires {
        collect_sequence_lasso_requirement_conjuncts(require, &mut conjuncts);
    }
    conjuncts
}

fn collect_sequence_lasso_requirement_conjuncts<'a>(
    expr: &'a PureExpr,
    conjuncts: &mut Vec<&'a PureExpr>,
) {
    if let PureExpr::BinOp(left, BinOp::And, right) = expr {
        collect_sequence_lasso_requirement_conjuncts(left, conjuncts);
        collect_sequence_lasso_requirement_conjuncts(right, conjuncts);
    } else {
        conjuncts.push(expr);
    }
}

fn sequence_lasso_explicit_alias_for<'a>(
    guarded_seq: &PureExpr,
    require: &'a PureExpr,
) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = require else {
        return None;
    };
    if sequence_lasso_same_alias_base(left, guarded_seq) {
        return sequence_lasso_alias_candidate(right);
    }
    if sequence_lasso_same_alias_base(right, guarded_seq) {
        return sequence_lasso_alias_candidate(left);
    }
    None
}

fn sequence_lasso_same_alias_base(left: &PureExpr, right: &PureExpr) -> bool {
    sequence_lasso_same_expr(
        sequence_lasso_transparent_seq_expr(left),
        sequence_lasso_transparent_seq_expr(right),
    )
}

fn sequence_lasso_alias_candidate(expr: &PureExpr) -> Option<&PureExpr> {
    let candidate = sequence_lasso_transparent_seq_expr(expr);
    sequence_lasso_seq_var_name(candidate)
        .is_some()
        .then_some(candidate)
}

fn sequence_lasso_transparent_seq_expr(mut expr: &PureExpr) -> &PureExpr {
    while let PureExpr::View(inner) = expr {
        expr = inner;
    }
    expr
}

fn sequence_lasso_quantifier_matches_exact(quantified: &PureExpr, seq: &PureExpr) -> bool {
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = quantified
    else {
        return false;
    };
    if !matches!(var_sort.as_ref(), None | Some(ExprSort::Int)) {
        return false;
    }
    let Some(seq_name) = sequence_lasso_seq_var_name(seq) else {
        return false;
    };
    if var == seq_name {
        return false;
    }

    let PureExpr::BinOp(bounds, BinOp::Implies, equality) = body.as_ref() else {
        return false;
    };
    if !sequence_lasso_index_bounds_exact(bounds, var, seq) {
        return false;
    }
    let PureExpr::BinOp(left, BinOp::Eq, right) = equality.as_ref() else {
        return false;
    };
    sequence_lasso_left_side_exact(left, var, seq)
        && sequence_lasso_right_side_exact(right, var, seq)
}

fn sequence_lasso_len_gt_zero_guard_sequence(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::BinOp(left, BinOp::Gt, right) if sequence_lasso_is_int_value(right, 0) => {
            let seq = sequence_lasso_len_receiver(left)?;
            sequence_lasso_seq_var_name(seq).is_some().then_some(seq)
        }
        PureExpr::BinOp(left, BinOp::Lt, right) if sequence_lasso_is_int_value(left, 0) => {
            let seq = sequence_lasso_len_receiver(right)?;
            sequence_lasso_seq_var_name(seq).is_some().then_some(seq)
        }
        _ => None,
    }
}

fn sequence_lasso_seq_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, sort) if matches!(sort.as_ref(), None | Some(ExprSort::Seq)) => {
            Some(name.as_str())
        }
        _ => None,
    }
}

fn sequence_lasso_index_bounds_exact(bounds: &PureExpr, index_var: &str, seq: &PureExpr) -> bool {
    let PureExpr::BinOp(lower, BinOp::And, upper) = bounds else {
        return false;
    };
    sequence_lasso_is_zero_le_index_var(lower, index_var)
        && sequence_lasso_is_index_var_lt_seq_len(upper, index_var, seq)
}

fn sequence_lasso_left_side_exact(expr: &PureExpr, index_var: &str, seq: &PureExpr) -> bool {
    let Some((push_front_expr, index_arg)) = sequence_lasso_method_call1(expr, "index_logic")
    else {
        return false;
    };
    if !sequence_lasso_is_index_var(index_arg, index_var) {
        return false;
    }
    let Some((reverse_subseq_expr, pushed_value)) =
        sequence_lasso_method_call1(push_front_expr, "push_front")
    else {
        return false;
    };
    if !sequence_lasso_is_seq_index_zero(pushed_value, seq) {
        return false;
    }
    let Some(subseq_expr) = sequence_lasso_method_call0(reverse_subseq_expr, "reverse") else {
        return false;
    };
    sequence_lasso_is_tail_subsequence_to_len(subseq_expr, seq)
}

fn sequence_lasso_right_side_exact(expr: &PureExpr, index_var: &str, seq: &PureExpr) -> bool {
    let PureExpr::Ite(condition, then_branch, else_branch) = expr else {
        return false;
    };
    sequence_lasso_is_index_var_eq_zero(condition, index_var)
        && sequence_lasso_is_seq_index_zero(then_branch, seq)
        && sequence_lasso_is_reverse_index_previous(else_branch, index_var, seq)
}

fn sequence_lasso_is_tail_subsequence_to_len(expr: &PureExpr, seq: &PureExpr) -> bool {
    let Some((receiver, args)) = sequence_lasso_method_call_args(expr, "subsequence") else {
        return false;
    };
    let [from, to] = args else {
        return false;
    };
    sequence_lasso_same_expr(receiver, seq)
        && sequence_lasso_is_int_value(from, 1)
        && sequence_lasso_is_len_of(to, seq)
}

fn sequence_lasso_is_reverse_index_previous(
    expr: &PureExpr,
    index_var: &str,
    seq: &PureExpr,
) -> bool {
    let Some((reverse_expr, index_arg)) = sequence_lasso_method_call1(expr, "index_logic") else {
        return false;
    };
    let Some(reverse_receiver) = sequence_lasso_method_call0(reverse_expr, "reverse") else {
        return false;
    };
    sequence_lasso_same_expr(reverse_receiver, seq)
        && sequence_lasso_is_index_var_minus_one(index_arg, index_var)
}

fn sequence_lasso_is_seq_index_zero(expr: &PureExpr, seq: &PureExpr) -> bool {
    let Some((receiver, index_arg)) = sequence_lasso_method_call1(expr, "index_logic") else {
        return false;
    };
    sequence_lasso_same_expr(receiver, seq) && sequence_lasso_is_int_value(index_arg, 0)
}

fn sequence_lasso_is_zero_le_index_var(expr: &PureExpr, index_var: &str) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(left, BinOp::Le, right)
            if sequence_lasso_is_int_value(left, 0)
                && sequence_lasso_is_index_var(right, index_var)
    )
}

fn sequence_lasso_is_index_var_lt_seq_len(
    expr: &PureExpr,
    index_var: &str,
    seq: &PureExpr,
) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(left, BinOp::Lt, right)
            if sequence_lasso_is_index_var(left, index_var)
                && sequence_lasso_is_len_of(right, seq)
    )
}

fn sequence_lasso_is_index_var_eq_zero(expr: &PureExpr, index_var: &str) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(left, BinOp::Eq, right)
            if sequence_lasso_is_index_var(left, index_var)
                && sequence_lasso_is_int_value(right, 0)
    )
}

fn sequence_lasso_is_index_var_minus_one(expr: &PureExpr, index_var: &str) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(left, BinOp::Sub, right)
            if sequence_lasso_is_index_var(left, index_var)
                && sequence_lasso_is_int_value(right, 1)
    )
}

fn sequence_lasso_is_len_of(expr: &PureExpr, seq: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "len"
            && args.is_empty()
            && sequence_lasso_same_expr(receiver, seq)
    )
}

fn sequence_lasso_len_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == "len" && args.is_empty()).then_some(receiver.as_ref())
}

fn sequence_lasso_method_call1<'a>(
    expr: &'a PureExpr,
    expected_method: &str,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    let (receiver, args) = sequence_lasso_method_call_args(expr, expected_method)?;
    let [arg] = args else {
        return None;
    };
    Some((receiver, arg))
}

fn sequence_lasso_method_call0<'a>(
    expr: &'a PureExpr,
    expected_method: &str,
) -> Option<&'a PureExpr> {
    let (receiver, args) = sequence_lasso_method_call_args(expr, expected_method)?;
    args.is_empty().then_some(receiver)
}

fn sequence_lasso_method_call_args<'a>(
    expr: &'a PureExpr,
    expected_method: &str,
) -> Option<(&'a PureExpr, &'a [PureExpr])> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == expected_method).then_some((receiver.as_ref(), args.as_slice()))
}

fn sequence_lasso_is_index_var(expr: &PureExpr, expected_name: &str) -> bool {
    matches!(
        expr,
        PureExpr::Var(name, sort)
            if name == expected_name && matches!(sort.as_ref(), None | Some(ExprSort::Int))
    )
}

fn sequence_lasso_is_int_value(expr: &PureExpr, expected: i64) -> bool {
    matches!(expr, PureExpr::Int(value) if *value == expected)
}

fn sequence_lasso_same_expr(left: &PureExpr, right: &PureExpr) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(left, right)
}

fn required_disequality_contradicts_postcondition(
    requires: &[PureExpr],
    ensure: &PureExpr,
) -> bool {
    let PureExpr::BinOp(ensure_left, BinOp::Eq, ensure_right) = ensure else {
        return false;
    };
    requires.iter().any(|require| {
        let PureExpr::BinOp(require_left, BinOp::Ne, require_right) = require else {
            return false;
        };
        same_pair_modulo_order(
            ensure_left.as_ref(),
            ensure_right.as_ref(),
            require_left.as_ref(),
            require_right.as_ref(),
        )
    })
}

fn same_pair_modulo_order(
    left_a: &PureExpr,
    right_a: &PureExpr,
    left_b: &PureExpr,
    right_b: &PureExpr,
) -> bool {
    let exprs_equal = crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal;
    (exprs_equal(left_a, left_b) && exprs_equal(right_a, right_b))
        || (exprs_equal(left_a, right_b) && exprs_equal(right_a, left_b))
}

fn structural_return_or_identity_final_postcondition_matches(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
) -> bool {
    let Some(return_expr) = return_expr.map(strip_let_assume) else {
        return false;
    };
    let Some(final_values) = mut_borrow_final_values else {
        return false;
    };
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };

    let left = substitute_result_projections(left, return_expr);
    let right = substitute_result_projections(right, return_expr);
    let left = normalize_identity_finals(&left, final_values);
    let right = normalize_identity_finals(&right, final_values);
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(&left, &right)
}

fn direct_final_value_postcondition_matches(
    ensure: &PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
) -> bool {
    let Some(final_values) = mut_borrow_final_values else {
        return false;
    };
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };

    direct_final_value_side_matches(left, right, final_values)
        || direct_final_value_side_matches(right, left, final_values)
}

fn direct_final_value_side_matches(
    final_side: &PureExpr,
    expected: &PureExpr,
    final_values: &HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::Final(inner) = final_side else {
        return false;
    };
    let Some(base_name) = peel_deref_var_name(inner) else {
        return false;
    };
    let Some(final_value) = final_values.get(base_name) else {
        return false;
    };

    let expected = normalize_identity_finals(expected, final_values);
    let final_value = normalize_identity_finals(final_value, final_values);
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(&final_value, &expected)
}

fn substitute_result_projections(expr: &PureExpr, return_expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Var(name, _) if name == "result" => return_expr.clone(),
        PureExpr::Deref(inner) if is_result_var(inner) => {
            PureExpr::Deref(Arc::new(return_expr.clone()))
        }
        PureExpr::Final(inner) if is_result_var(inner) => final_view_of_return_expr(return_expr),
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(substitute_result_projections(left, return_expr)),
            *op,
            Arc::new(substitute_result_projections(right, return_expr)),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(substitute_result_projections(inner, return_expr)),
        ),
        PureExpr::Ite(cond, then_branch, else_branch) => PureExpr::Ite(
            Arc::new(substitute_result_projections(cond, return_expr)),
            Arc::new(substitute_result_projections(then_branch, return_expr)),
            Arc::new(substitute_result_projections(else_branch, return_expr)),
        ),
        PureExpr::Old(inner) => {
            PureExpr::Old(Arc::new(substitute_result_projections(inner, return_expr)))
        }
        PureExpr::Deref(inner) => {
            PureExpr::Deref(Arc::new(substitute_result_projections(inner, return_expr)))
        }
        PureExpr::Final(inner) => {
            PureExpr::Final(Arc::new(substitute_result_projections(inner, return_expr)))
        }
        PureExpr::View(inner) => {
            PureExpr::View(Arc::new(substitute_result_projections(inner, return_expr)))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(substitute_result_projections(receiver, return_expr)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| substitute_result_projections(arg, return_expr))
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| substitute_result_projections(arg, return_expr))
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(substitute_result_projections(value, return_expr)),
            body: Arc::new(substitute_result_projections(body, return_expr)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(substitute_result_projections(assumption, return_expr)),
            body: Arc::new(substitute_result_projections(body, return_expr)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(substitute_result_projections(obligation, return_expr)),
            body: Arc::new(substitute_result_projections(body, return_expr)),
        },
        other => other.clone(),
    }
}

fn final_view_of_return_expr(return_expr: &PureExpr) -> PureExpr {
    match return_expr {
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(PureExpr::Final(Arc::clone(inner)))),
        other => PureExpr::Final(Arc::new(other.clone())),
    }
}

fn known_seq_len(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if matches!(name.as_str(), "seq_empty" | "Seq::empty") && args.is_empty() =>
        {
            Some(0)
        }
        PureExpr::LogicFnCall { name, args }
            if matches!(name.as_str(), "seq" | "Seq::singleton") && args.len() == 1 =>
        {
            Some(1)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if matches!(method.as_str(), "push_back" | "push_front") && args.len() == 1 => {
            known_seq_len(receiver).and_then(|len| len.checked_add(1))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "concat" && args.len() == 1 => known_seq_len(receiver)
            .zip(known_seq_len(&args[0]))
            .and_then(|(left, right)| left.checked_add(right)),
        PureExpr::LetAssume { body, .. } | PureExpr::Let { body, .. } => known_seq_len(body),
        PureExpr::View(inner) => known_seq_len(inner),
        _ => None,
    }
}

fn result_projection_matches_reconstructed_return_field(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
) -> bool {
    let Some(return_expr) = return_expr.map(strip_let_assume) else {
        return false;
    };
    let Some(final_values) = mut_borrow_final_values else {
        return false;
    };
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    let Some(expected) = result_projection_other_side(left, right)
        .or_else(|| result_projection_other_side(right, left))
    else {
        return false;
    };
    let Some((base_name, field_index)) = returned_tuple_field(return_expr) else {
        return false;
    };
    let Some(reconstructed_field) =
        reconstructed_tuple_final_field(final_values, base_name, field_index)
    else {
        return false;
    };
    if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
        expected,
        reconstructed_field,
    ) {
        return true;
    }
    let final_projection_referent = PureExpr::Deref(Arc::new(PureExpr::LogicFnCall {
        name: trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(
            field_index,
        ),
        args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
            base_name.to_string(),
            None,
        )))],
    }));
    if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
        expected,
        &final_projection_referent,
    ) {
        return true;
    }
    let field_key = format!("{base_name}.{field_index}");
    final_values.get(&field_key).is_some_and(|field_final| {
        crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(expected, field_final)
    })
}

fn result_projection_other_side<'a>(
    candidate: &PureExpr,
    other: &'a PureExpr,
) -> Option<&'a PureExpr> {
    match candidate {
        PureExpr::Deref(inner) | PureExpr::Final(inner) if is_result_var(inner.as_ref()) => {
            Some(other)
        }
        _ => None,
    }
}

fn returned_tuple_field(return_expr: &PureExpr) -> Option<(&str, usize)> {
    let PureExpr::LogicFnCall { name, args } = return_expr else {
        return None;
    };
    let field_index = tuple_field_logic_fn_index(name)?;
    let [arg] = args.as_slice() else {
        return None;
    };
    match arg {
        PureExpr::Var(base_name, _) => Some((base_name.as_str(), field_index)),
        PureExpr::Deref(inner) | PureExpr::Final(inner) => match inner.as_ref() {
            PureExpr::Var(base_name, _) => Some((base_name.as_str(), field_index)),
            _ => None,
        },
        _ => None,
    }
}

fn reconstructed_tuple_final_field<'a>(
    final_values: &'a HashMap<String, PureExpr>,
    base_name: &str,
    field_index: usize,
) -> Option<&'a PureExpr> {
    let PureExpr::LogicFnCall { name, args } = final_values.get(base_name)? else {
        return None;
    };
    if tuple_logic_fn_arity(name) != Some(args.len()) {
        return None;
    }
    args.get(field_index)
}

fn reconstructed_tuple_field_finality_matches(
    ensure: &PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
) -> bool {
    let Some(final_values) = mut_borrow_final_values else {
        return false;
    };
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    let Some((base_name, field_index, current_projection)) =
        projected_current_field_final(left, right)
            .or_else(|| projected_current_field_final(right, left))
    else {
        return false;
    };
    let current_referent = PureExpr::Deref(Arc::new(current_projection.clone()));

    let Some(reconstructed_field) =
        reconstructed_tuple_final_field(final_values, base_name, field_index)
    else {
        return false;
    };
    if !crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
        reconstructed_field,
        &current_referent,
    ) {
        return false;
    }

    let field_key = format!("{base_name}.{field_index}");
    final_values.get(&field_key).is_some_and(|field_final| {
        crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
            field_final,
            &current_referent,
        )
    })
}

fn projected_current_field_final<'a>(
    current_side: &'a PureExpr,
    final_side: &PureExpr,
) -> Option<(&'a str, usize, &'a PureExpr)> {
    let PureExpr::Final(current_inner) = current_side else {
        return None;
    };
    let PureExpr::LogicFnCall {
        name: current_name,
        args: current_args,
    } = current_inner.as_ref()
    else {
        return None;
    };
    let field_index = tuple_field_logic_fn_index(current_name)?;
    let [current_arg] = current_args.as_slice() else {
        return None;
    };
    let PureExpr::Deref(current_base) = current_arg else {
        return None;
    };
    let PureExpr::Var(base_name, _) = current_base.as_ref() else {
        return None;
    };

    let PureExpr::Final(final_inner) = final_side else {
        return None;
    };
    let PureExpr::LogicFnCall {
        name: final_name,
        args: final_args,
    } = final_inner.as_ref()
    else {
        return None;
    };
    if tuple_field_logic_fn_index(final_name) != Some(field_index) {
        return None;
    }
    let [final_arg] = final_args.as_slice() else {
        return None;
    };
    let PureExpr::Final(final_base) = final_arg else {
        return None;
    };
    match final_base.as_ref() {
        PureExpr::Var(final_base_name, _) if final_base_name == base_name => {
            Some((base_name.as_str(), field_index, current_inner.as_ref()))
        }
        _ => None,
    }
}

fn direct_result_ite_matches_return_expr(
    ensure: &PureExpr,
    return_expr: &PureExpr,
    final_values: &std::collections::HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::Ite(ensure_cond, then_ensure, else_ensure) = ensure else {
        return false;
    };
    let PureExpr::Ite(return_cond, then_return, else_return) = strip_let_assume(return_expr) else {
        return false;
    };
    let param_names: HashSet<&str> = final_values.keys().map(String::as_str).collect();
    let canonical_ensure_cond = canonicalize_mut_ref_vars(ensure_cond, &param_names);
    let canonical_return_cond = canonicalize_mut_ref_vars(return_cond, &param_names);
    if !crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
        &canonical_ensure_cond,
        &canonical_return_cond,
    ) {
        return false;
    }

    result_branch_matches_return(then_ensure, then_return, &param_names, final_values)
        && result_branch_matches_return(else_ensure, else_return, &param_names, final_values)
}

fn result_branch_matches_return(
    ensure_branch: &PureExpr,
    return_branch: &PureExpr,
    param_names: &HashSet<&str>,
    final_values: &std::collections::HashMap<String, PureExpr>,
) -> bool {
    let conjuncts = flatten_and_conjuncts(ensure_branch);
    let mut saw_result_match = false;

    for conjunct in conjuncts {
        if let Some(expected) = result_equality_other_side(conjunct) {
            let canonical_return = canonicalize_mut_ref_vars(return_branch, param_names);
            let expected = normalize_identity_finals(expected, final_values);
            let canonical_expected = canonicalize_mut_ref_vars(&expected, param_names);
            if direct_result_exprs_match(&canonical_return, &canonical_expected, param_names) {
                saw_result_match = true;
                continue;
            }
            return false;
        }

        if final_identity_matches(conjunct, final_values)
            || tuple_field_final_identity_matches(conjunct, final_values)
        {
            continue;
        }

        return false;
    }

    saw_result_match
}

fn final_identity_matches(ensure: &PureExpr, final_values: &HashMap<String, PureExpr>) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    final_identity_side_matches(left, right, final_values)
        || final_identity_side_matches(right, left, final_values)
}

fn final_identity_side_matches(
    final_side: &PureExpr,
    current_side: &PureExpr,
    final_values: &HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::Final(inner) = final_side else {
        return false;
    };
    let PureExpr::Var(name, sort) = inner.as_ref() else {
        return false;
    };
    if !final_values
        .get(name)
        .is_some_and(|final_expr| super::resolve::is_identity_final_value(name, final_expr))
    {
        return false;
    }
    let current_expr = PureExpr::Deref(Arc::new(PureExpr::Var(name.clone(), sort.clone())));
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(current_side, &current_expr)
}

fn flatten_and_conjuncts(expr: &PureExpr) -> Vec<&PureExpr> {
    let mut out = Vec::new();
    collect_and_conjuncts(expr, &mut out);
    out
}

fn collect_and_conjuncts<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    if let PureExpr::BinOp(left, BinOp::And, right) = expr {
        collect_and_conjuncts(left, out);
        collect_and_conjuncts(right, out);
    } else {
        out.push(expr);
    }
}

fn tuple_field_final_identity_matches(
    ensure: &PureExpr,
    final_values: &HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    tuple_field_final_identity_side_matches(left, right, final_values)
        || tuple_field_final_identity_side_matches(right, left, final_values)
}

fn tuple_field_final_identity_side_matches(
    final_side: &PureExpr,
    current_side: &PureExpr,
    final_values: &HashMap<String, PureExpr>,
) -> bool {
    let Some((base_name, field_index, current_projection)) =
        final_tuple_field_current_projection(final_side)
    else {
        return false;
    };
    let current_referent = PureExpr::Deref(Arc::new(current_projection.clone()));
    if !crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
        current_side,
        &current_referent,
    ) {
        return false;
    }

    let field_key = format!("{base_name}.{field_index}");
    final_values.get(&field_key).is_some_and(|field_final| {
        crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
            field_final,
            &current_referent,
        )
    }) || final_values
        .get(base_name)
        .is_some_and(|final_expr| super::resolve::is_identity_final_value(base_name, final_expr))
}

fn final_tuple_field_current_projection(expr: &PureExpr) -> Option<(&str, usize, &PureExpr)> {
    let PureExpr::Final(inner) = expr else {
        return None;
    };
    let PureExpr::LogicFnCall { name, args } = inner.as_ref() else {
        return None;
    };
    let field_index = tuple_field_logic_fn_index(name)?;
    let [arg] = args.as_slice() else {
        return None;
    };
    let PureExpr::Deref(base) = arg else {
        return None;
    };
    let PureExpr::Var(base_name, _) = base.as_ref() else {
        return None;
    };
    Some((base_name.as_str(), field_index, inner.as_ref()))
}

fn direct_result_exprs_match(
    return_expr: &PureExpr,
    expected: &PureExpr,
    param_names: &HashSet<&str>,
) -> bool {
    if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(return_expr, expected) {
        return true;
    }

    if let Some((return_base, return_depth)) = peel_deref_var_chain(return_expr) {
        if let PureExpr::Var(expected_base, _) = expected {
            if return_base == expected_base && param_names.contains(expected_base.as_str()) {
                return true;
            }
        }
        if let Some((expected_base, expected_depth)) = peel_deref_var_chain(expected) {
            return return_base == expected_base
                && param_names.contains(return_base)
                && return_depth >= 2
                && expected_depth >= 2;
        }
    }

    false
}

fn peel_deref_var_chain(expr: &PureExpr) -> Option<(&str, usize)> {
    let mut depth = 0;
    let mut current = expr;
    while let PureExpr::Deref(inner) = current {
        depth += 1;
        current = inner.as_ref();
    }
    match current {
        PureExpr::Var(name, _) if depth > 0 => Some((name.as_str(), depth)),
        _ => None,
    }
}

fn normalize_identity_finals(
    expr: &PureExpr,
    final_values: &std::collections::HashMap<String, PureExpr>,
) -> PureExpr {
    match expr {
        PureExpr::Final(inner) => {
            if let PureExpr::Var(name, sort) = inner.as_ref() {
                if final_values.get(name).is_some_and(|final_expr| {
                    super::resolve::is_identity_final_value(name, final_expr)
                }) {
                    return PureExpr::Deref(Arc::new(PureExpr::Var(name.clone(), sort.clone())));
                }
            }
            PureExpr::Final(Arc::new(normalize_identity_finals(inner, final_values)))
        }
        PureExpr::Deref(inner) => {
            PureExpr::Deref(Arc::new(normalize_identity_finals(inner, final_values)))
        }
        PureExpr::View(inner) => {
            PureExpr::View(Arc::new(normalize_identity_finals(inner, final_values)))
        }
        PureExpr::Old(inner) => {
            PureExpr::Old(Arc::new(normalize_identity_finals(inner, final_values)))
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(normalize_identity_finals(left, final_values)),
            *op,
            Arc::new(normalize_identity_finals(right, final_values)),
        ),
        PureExpr::Ite(cond, then_branch, else_branch) => PureExpr::Ite(
            Arc::new(normalize_identity_finals(cond, final_values)),
            Arc::new(normalize_identity_finals(then_branch, final_values)),
            Arc::new(normalize_identity_finals(else_branch, final_values)),
        ),
        _ => expr.clone(),
    }
}

fn result_equality_other_side(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::BinOp(left, BinOp::Eq, right) if is_result_var(left) => Some(right),
        PureExpr::BinOp(left, BinOp::Eq, right) if is_result_var(right) => Some(left),
        _ => None,
    }
}

fn is_result_var(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == "result")
}

fn strip_let_assume(expr: &PureExpr) -> &PureExpr {
    let mut current = expr;
    while let PureExpr::LetAssume { body, .. } = current {
        current = body;
    }
    current
}

pub(super) fn verify_mut_borrow_single_obligation_slice_indexed(
    encoder: &mut AYEncoder,
    obligation_index: usize,
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError> {
    let cont = verify_mut_borrow_single_obligation_slice_indexed_inner(
        encoder,
        obligation_index,
        ensure,
        ctx,
    )?;
    Ok(tag_mut_borrow_continuation_with_violated_postcondition(
        cont,
        obligation_index,
        ensure,
    ))
}

/// Tag the inner mut-borrow result with violated-postcondition metadata when
/// it reports a `Failed` counterexample, so the driver can render a precise
/// "violated ensures #N: <clause>" diagnostic (Phase 8a). No-op for
/// non-`Failed` results, idempotent if the inner solver already attached
/// metadata.
fn tag_mut_borrow_continuation_with_violated_postcondition(
    cont: ResolveContinuation,
    obligation_index: usize,
    ensure: &PureExpr,
) -> ResolveContinuation {
    let info = PostconditionInfo {
        clause_idx: obligation_index,
        contract_text: ensure.to_string(),
        span: None,
    };
    match cont {
        ResolveContinuation::Continue(result) => {
            ResolveContinuation::Continue(result.tag_violated_postcondition(info))
        }
        ResolveContinuation::Abort(result) => {
            ResolveContinuation::Abort(result.tag_violated_postcondition(info))
        }
    }
}

fn verify_mut_borrow_single_obligation_slice_indexed_inner(
    encoder: &mut AYEncoder,
    obligation_index: usize,
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError> {
    if seq_push_back_assignments_are_contradictory(
        ctx.requires,
        ctx.mut_borrow_final_values,
        ctx.mutation_continued_params,
    ) {
        return Ok(ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(
                super::super::solver_tail::VACUOUS_PROOF_MESSAGE.to_string(),
            ),
        )));
    }

    if required_disequality_contradicts_postcondition(ctx.requires, ensure) {
        return Ok(ResolveContinuation::Continue(VerificationResult::Failed(
            Counterexample::empty(),
        )));
    }

    if let Some(result) = type_invariant_negative_precheck(ensure, ctx) {
        return Ok(ResolveContinuation::Continue(result));
    }

    if let Some(result) =
        prove_implication_false_guard_with_solver(encoder, obligation_index, ensure, ctx.requires)?
    {
        debug!("  slice[{obligation_index}]: false implication guard proved with solver evidence");
        return Ok(result);
    }

    if result_projection_matches_reconstructed_return_field(
        ensure,
        ctx.return_expr,
        ctx.mut_borrow_final_values,
    ) {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if reconstructed_tuple_field_finality_matches(ensure, ctx.mut_borrow_final_values) {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if direct_result_equality_matches_return_expr(
        ensure,
        ctx.return_expr,
        ctx.mut_borrow_final_values,
    ) {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if structural_return_or_identity_final_postcondition_matches(
        ensure,
        ctx.return_expr,
        ctx.mut_borrow_final_values,
    ) {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if direct_final_value_postcondition_matches(ensure, ctx.mut_borrow_final_values) {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if result_view_len_matches_return_expr(ensure, ctx.return_expr) {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if seq_push_back_chain_postcondition_follows_requirements(
        ctx.requires,
        ensure,
        ctx.mut_borrow_final_values,
        ctx.mutation_continued_params,
    ) {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if let Some(result) = seq_push_back_index_matches_requirements(ctx.requires, ensure) {
        if !matches!(result, VerificationResult::Verified(_)) {
            return Ok(ResolveContinuation::Continue(result));
        }
        // Do not assert the recognized postcondition and then refute its
        // negation: that circular "materialized consequence" query proves
        // only an assumption, not the source claim.  The positively asserted
        // length fact gives the encoder exact finite-length metadata, so the
        // normal goal path below reduces push_back/read-at-the-write-index to
        // a literal.  Its isolated strict UNSAT certificate is genuine proof
        // authority and the negative controls still reach SAT/Failed.
        debug!(
            "  slice[{obligation_index}]: routing Seq push_back index theorem through exact goal encoding"
        );
    }

    if sequence_lasso_proof_assert_matches_exact(ensure, ctx.requires) {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if super::super::solver_tail::mut_borrow_final_disequality_consequence(ctx, obligation_index)
        .is_some()
    {
        return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
    }

    if let Some(result) =
        resolve_postcondition_matches_final_values(ensure, ctx.mut_borrow_final_values)
    {
        if !verified_structural_result_enabled(&result) {
            debug!(
                "  slice[{obligation_index}]: resolve/final structural verified shortcut disabled"
            );
            return prove_materialized_verified_consequence(encoder, obligation_index, ensure, ctx);
        } else {
            return Ok(ResolveContinuation::Continue(result));
        }
    }

    // Encode and negate this single postcondition. (#1629)
    if let Some(final_values) = ctx.mut_borrow_final_values {
        for req in ctx.requires {
            let PureExpr::MethodCall { method, .. } = req else {
                continue;
            };
            if method != "postcondition" {
                continue;
            }
            let grounded = eager_fn_mut_ground_ensure(req, Some(final_values));
            if !matches!(grounded.as_ref(), PureExpr::MethodCall { method, .. } if method == "postcondition")
            {
                let grounded_term = encoder.encode_pure(grounded.as_ref())?;
                encoder.assert_term(grounded_term);
                encoder.assert_eager_fn_mut_ground_instantiation(grounded.as_ref())?;
            }
        }
    }

    let grounded_ensure = eager_fn_mut_ground_ensure(ensure, ctx.mut_borrow_final_values);

    // Whole-`MutRef` equality goals are refuted by ay but certified only at the
    // carrier level (see `mut_ref_carrier_goal_certificate`). Capture the
    // carrier-level certificate HERE, while the base is still free of this
    // slice's negated goal, so it can be attached if the solve below accepts
    // without evidence of its own. Purely additive: it cannot change which
    // verdict the slice reaches.
    let carrier_certificate = mut_ref_carrier_goal_certificate(encoder, grounded_ensure.as_ref());

    // Goal-side sort-coercion guard (#knights_tour): mirror the function-path
    // guard — a `SortCoercionBridge` fired while encoding the negated goal
    // means the goal ranges over fresh unconstrained constants, so a sat
    // result must not be accepted as a counterexample.
    let goal_coercion_baseline = unsoundness::snapshot();
    let negated_ensure = encode_negated_postcondition(
        encoder,
        grounded_ensure.as_ref(),
        ctx.logic_fns,
        ctx.return_expr,
    )?;
    let goal_encode_coerced =
        super::super::solver_tail::negated_goal_encode_introduced_sort_coercion(
            &goal_coercion_baseline,
        );
    encoder.assert_eager_fn_mut_ground_instantiation(grounded_ensure.as_ref())?;
    encoder.assert_eager_fn_once_ground_instantiation(grounded_ensure.as_ref())?;
    // Bounded structural-induction lemma for recursive-datatype `get`/`len`
    // logic fns, emitted into THIS slice's solve scope so it is present in the
    // deciding query: a `&mut List` postcondition `forall i. 0<=i<len(l) ==>
    // get(^l, i) == Some(_)` needs the "every in-range index is defined" fact
    // (discharged via the datatype induction principle + Option payload
    // bridges). SOUND — only genuine theorems, inert otherwise. (#all_zero Obl1)
    encoder.emit_bounded_get_some_structural_induction(
        std::slice::from_ref(ensure),
        ctx.logic_fns,
        None,
    );
    // Link slice-param length states now that encoding the negated goal has
    // declared the (possibly deeply-nested) prophecy length symbols. A
    // `&mut [T]` slice's length is identical across all program-point states.
    if let Some(slice_vars) = ctx.slice_length_stable_vars {
        for var_name in slice_vars {
            super::resolve::emit_slice_length_preservation(encoder, var_name);
        }
    }

    // Delegate the post-negation tail to the shared solver_tail module.
    // The mut-borrow path uses current-chain alias constraints. (#1576)
    let cont = super::super::solver_tail::verify_negated_obligation_slice(
        encoder,
        negated_ensure,
        ctx,
        AliasConstraintMode::CurrentChain,
        obligation_index,
    )?;
    if goal_encode_coerced {
        return Ok(
            super::super::solver_tail::demote_sort_coerced_goal_counterexample(
                cont,
                obligation_index,
            ),
        );
    }
    Ok(attach_carrier_certificate(cont, carrier_certificate))
}

/// Attach a carrier-level certificate to an acceptance that carries none.
///
/// Only `Verified(None)` is upgraded — the exact shape
/// `apply_strict_trust` demotes to `Unknown(ProofTrusted)`. A verdict that is
/// not an acceptance is returned untouched, and an acceptance that already
/// carries a summary keeps its own evidence rather than having it swapped for
/// a different solve's.
fn attach_carrier_certificate(
    cont: ResolveContinuation,
    certificate: Option<crate::verify::ProofCertificateSummary>,
) -> ResolveContinuation {
    let Some(certificate) = certificate else {
        return cont;
    };
    match cont {
        ResolveContinuation::Continue(VerificationResult::Verified(None)) => {
            ResolveContinuation::Continue(VerificationResult::Verified(Some(certificate)))
        }
        ResolveContinuation::Abort(VerificationResult::Verified(None)) => {
            ResolveContinuation::Abort(VerificationResult::Verified(Some(certificate)))
        }
        other => other,
    }
}

/// Obtain a strictly-checked certificate for a whole-`MutRef` equality
/// obligation by proving the SAME fact at the carrier level.
///
/// WHY THIS EXISTS. A postcondition such as `result == y` on `&mut i32`
/// is encoded componentwise (`try_decompose_mut_ref_equality`), so the negated
/// goal is a disjunction of three disequalities over the `current`/`final`/`id`
/// selector UFs. ay refutes that stack, but its proof producer collapses the
/// three-way case split — each leg closed by its own equality chain — into one
/// monolithic `:rule hole` step. The certificate is therefore not trust-free,
/// `apply_strict_trust` correctly demotes the acceptance to
/// `Unknown(ProofTrusted)`, and a genuinely proved obligation reports as
/// unproved. Measured on `same_parent_borrow_id_allows_whole_borrow_identity_
/// postcondition`: the 59-assertion stack yields `unproved_steps=1
/// trust_free=no`, and under `:check-proofs-strict true` ay itself answers
/// `unknown (:reason-unknown (incomplete proof-trusted))`.
///
/// WHAT IT DOES. Before the componentwise goal is asserted, re-solve the SAME
/// base in a fresh, non-incremental, proof-checking solver against the
/// carrier-level negated goal `~(= lhs rhs)`. That query closes by
/// `eq_congruent` + `eq_transitive` + `resolution` (measured: `unproved_steps=0
/// foreign_assumes=no trust_free=yes`, and `carcara check` reports `valid`).
///
/// SOUNDNESS. `(= lhs rhs)` entails the componentwise conjunction by
/// congruence on the selector UFs, with no extra axioms — so refuting
/// `base /\ ~(= lhs rhs)` proves the postcondition this slice is responsible
/// for. It is a strictly HARDER query than the componentwise one (`~C ==> ~W`),
/// so it can only fail to close, never close spuriously. The base-consistency
/// (vacuity) shield is applied exactly as elsewhere: the certificate is kept
/// only when a fresh re-solve of the base ALONE is SAT, so a contradictory base
/// cannot manufacture a proof. On any refusal this returns `None` and the
/// caller keeps whatever verdict it already had.
///
/// This never changes a verdict on its own — the caller uses it only to
/// attach evidence to an acceptance that the solver already reached.
fn mut_ref_carrier_goal_certificate(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
) -> Option<crate::verify::ProofCertificateSummary> {
    if crate::verify::solver_tail::in_proof_assert_mode() {
        return None;
    }
    // Cheap shape checks first. Everything below this point costs a full stack
    // serialization plus a fresh solve, so it must not run on slices that are
    // not whole-`MutRef` equalities.
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return None;
    };
    let lhs_term = encoder.encode_pure(lhs).ok()?;
    let rhs_term = encoder.encode_pure(rhs).ok()?;
    let carrier_eq = encoder.try_mut_ref_carrier_equality(lhs_term, rhs_term)?;
    let negated_carrier = encoder.solver_mut().not(carrier_eq);

    // Snapshot the base (this slice's negated goal is not asserted yet) for the
    // vacuity shield below.
    let base_smt = encoder.solver().to_smtlib2();

    encoder.push_scope().ok()?;
    encoder.assert_term(negated_carrier);
    let summary = encoder.batch_resolve_current_stack_unsat();
    let popped = encoder.pop_scope();
    // A failed pop leaves the stack in an unknown shape; refuse rather than
    // hand back evidence tied to a stack we can no longer account for.
    popped.ok()?;
    let summary = summary?;
    // Vacuity shield: only a base that is independently SAT may support an
    // acceptance. Identical to the guard in
    // `prove_materialized_verified_consequence`.
    if !encoder.batch_base_smt_is_sat(&base_smt) {
        return None;
    }
    Some(summary)
}

fn type_invariant_negative_precheck(
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Option<VerificationResult> {
    let (method, receiver) = type_invariant_ensure_parts(ensure)?;
    let (var_name, final_expr) =
        mut_borrow_final_expr_for_invariant_receiver(receiver, ctx.mut_borrow_final_values?)?;
    let invariant = ctx.type_invariants.and_then(|invariants| {
        invariants.iter().find(|invariant| {
            trust_wp_core::logic::type_invariant_method_name(invariant.type_name()) == method
        })
    });

    let Some(invariant) = invariant else {
        let current_receiver = PureExpr::Deref(Arc::new(PureExpr::Var(var_name.to_string(), None)));
        if super::resolve::is_identity_final_value(var_name, final_expr)
            && requires_include_invariant_receiver(ctx.requires, method, &current_receiver)
        {
            return None;
        }
        return Some(VerificationResult::Failed(Counterexample::empty()));
    };

    let mut substitutions = HashMap::new();
    substitutions.insert(invariant.self_param().to_string(), final_expr.clone());
    let body = invariant.body().substitute(&substitutions);
    super::super::function::type_invariant_body_has_simple_counterexample(
        ctx.requires,
        &body,
        ctx.type_invariants,
        ctx.logic_fns,
    )
    .then_some(VerificationResult::Failed(Counterexample::empty()))
}

fn type_invariant_ensure_parts(ensure: &PureExpr) -> Option<(&str, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = ensure
    else {
        return None;
    };
    (args.is_empty() && trust_wp_core::logic::is_invariant_method_name(method))
        .then_some((method.as_str(), receiver.as_ref()))
}

fn mut_borrow_final_expr_for_invariant_receiver<'a>(
    receiver: &PureExpr,
    final_values: &'a HashMap<String, PureExpr>,
) -> Option<(&'a str, &'a PureExpr)> {
    let PureExpr::Final(inner) = receiver else {
        return None;
    };
    let PureExpr::Var(name, _) = inner.as_ref() else {
        return None;
    };
    final_values
        .get_key_value(name)
        .map(|(name, expr)| (name.as_str(), expr))
}

fn requires_include_invariant_receiver(
    requires: &[PureExpr],
    method: &str,
    expected_receiver: &PureExpr,
) -> bool {
    requires
        .iter()
        .any(|require| require_includes_invariant_receiver(require, method, expected_receiver))
}

fn require_includes_invariant_receiver(
    require: &PureExpr,
    method: &str,
    expected_receiver: &PureExpr,
) -> bool {
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            require_includes_invariant_receiver(left, method, expected_receiver)
                || require_includes_invariant_receiver(right, method, expected_receiver)
        }
        PureExpr::MethodCall {
            receiver,
            method: req_method,
            args,
        } => {
            args.is_empty()
                && req_method == method
                && sequence_lasso_same_expr(receiver, expected_receiver)
        }
        _ => false,
    }
}

#[cfg(test)]
pub(super) fn verify_mut_borrow_single_obligation_slice(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError> {
    if ctx.fresh_base_recheck.is_none()
        && ctx.requires.is_empty()
        && ctx.mut_borrow_final_values.is_none()
    {
        let negated_ensure =
            encode_negated_postcondition(encoder, ensure, ctx.logic_fns, ctx.return_expr)?;
        encoder.assert_term(negated_ensure);
        return Ok(ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::Incomplete,
        )));
    }
    if encoder.solver().timeout().is_none() {
        encoder.set_timeout(Some(std::time::Duration::from_secs(5)));
    }
    verify_mut_borrow_single_obligation_slice_indexed(encoder, 0, ensure, ctx)
}

fn resolve_postcondition_matches_final_values(
    ensure: &PureExpr,
    mut_borrow_final_values: Option<&HashMap<String, PureExpr>>,
) -> Option<VerificationResult> {
    let final_values = mut_borrow_final_values?;
    let var_name = resolve_postcondition_base_name(ensure)?;
    let final_expr = final_values.get(var_name)?;
    if super::resolve::is_identity_final_value(var_name, final_expr) {
        return Some(VerificationResult::Verified(None));
    }
    if final_value_is_visible_increment(var_name, final_expr) {
        return Some(VerificationResult::Failed(Counterexample::empty()));
    }
    None
}

fn resolve_postcondition_base_name(ensure: &PureExpr) -> Option<&str> {
    let PureExpr::LogicFnCall { name, args } = ensure else {
        return None;
    };
    if name != "resolve" || args.len() != 1 {
        return None;
    }
    peel_deref_var_name(&args[0])
}

fn peel_deref_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) => peel_deref_var_name(inner),
        _ => None,
    }
}

fn final_value_is_visible_increment(var_name: &str, final_expr: &PureExpr) -> bool {
    let PureExpr::BinOp(left, op, right) = final_expr else {
        return false;
    };
    match op {
        BinOp::Add => {
            deref_var_name(left).is_some_and(|name| name == var_name) && nonzero_int_literal(right)
                || deref_var_name(right).is_some_and(|name| name == var_name)
                    && nonzero_int_literal(left)
        }
        BinOp::Sub => {
            deref_var_name(left).is_some_and(|name| name == var_name) && nonzero_int_literal(right)
        }
        _ => false,
    }
}

fn deref_var_name(expr: &PureExpr) -> Option<&str> {
    let PureExpr::Deref(inner) = expr else {
        return None;
    };
    matches!(inner.as_ref(), PureExpr::Var(_, _)).then(|| peel_deref_var_name(expr))?
}

fn nonzero_int_literal(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Int(value) if *value != 0)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use trust_wp_core::formula::{
        internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
        PureExpr,
    };

    use super::*;

    fn empty_obligation_context<'a>() -> ObligationSliceContext<'a> {
        ObligationSliceContext {
            all_ensures: &[],
            requires: &[],
            logic_fns: None,
            mode_overrides: None,
            type_invariants: None,
            return_expr: None,
            mut_borrow_final_values: None,
            mutation_continued_params: None,
            body_div_obligations: &[],
            fresh_base_recheck: None,
            slice_length_stable_vars: None,
            base_recheck_pathology: std::cell::Cell::new(false),
        }
    }

    #[test]
    fn materialized_consequence_requires_a_satisfiable_base() {
        let mut encoder = AYEncoder::new();
        let contradiction = encoder.solver_mut().bool_const(false);
        encoder.assert_term(contradiction);

        let result = prove_materialized_verified_consequence(
            &mut encoder,
            0,
            &PureExpr::Bool(true),
            &empty_obligation_context(),
        )
        .expect("materialized consequence should encode");

        assert!(
            matches!(
                &result,
                ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::SolverMessage(message)
                )) if message.contains("no validated SAT base")
            ),
            "a contradictory base must never verify through padded core membership: {result:?}"
        );
    }

    #[test]
    fn materialized_consequence_preserves_full_stack_unsat_evidence() {
        let mut encoder = AYEncoder::new();
        let result = prove_materialized_verified_consequence(
            &mut encoder,
            0,
            &PureExpr::Bool(true),
            &empty_obligation_context(),
        )
        .expect("materialized consequence should encode");

        assert!(matches!(
            result,
            ResolveContinuation::Continue(VerificationResult::Verified(_))
        ));
        assert!(encoder.last_solve_evidence().is_some_and(|evidence| {
            evidence.accepted_for_consumer
                && evidence.result.to_ascii_lowercase().starts_with("unsat")
        }));
    }

    #[test]
    fn raw_postcondition_is_rewritten_to_postcondition_mut_for_eager_grounding() {
        let mut final_values = std::collections::HashMap::new();
        final_values.insert(
            "x".to_string(),
            PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None))),
        );

        let ensure = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
            method: "postcondition".to_string(),
            args: vec![
                PureExpr::Var("x".to_string(), None),
                PureExpr::Var("result".to_string(), None),
            ],
        };

        let rewritten = eager_fn_mut_ground_ensure(&ensure, Some(&final_values));
        let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = rewritten.as_ref()
        else {
            panic!("expected rewritten postcondition_mut call, got {rewritten:?}");
        };

        assert_eq!(method, "postcondition_mut");
        assert!(matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "f"));
        assert_eq!(args.len(), 3);
        assert!(matches!(&args[0], PureExpr::Var(name, _) if name == "x"));
        assert!(
            matches!(&args[1], PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "x"))
        );
        assert!(matches!(&args[2], PureExpr::Var(name, _) if name == "result"));
    }

    #[test]
    fn raw_postcondition_without_final_values_context_is_left_unchanged() {
        let ensure = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
            method: "postcondition".to_string(),
            args: vec![
                PureExpr::Var("x".to_string(), None),
                PureExpr::Var("result".to_string(), None),
            ],
        };

        let rewritten = eager_fn_mut_ground_ensure(&ensure, None);
        assert!(matches!(rewritten, Cow::Borrowed(_)));
    }

    #[test]
    fn non_postcondition_ensure_is_left_unchanged() {
        let ensure = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
            method: "precondition".to_string(),
            args: vec![PureExpr::Int(7)],
        };

        let rewritten = eager_fn_mut_ground_ensure(&ensure, None);
        assert!(matches!(rewritten, Cow::Borrowed(_)));
    }

    #[test]
    fn result_view_len_matches_push_back_chain_return_expr() {
        let empty = PureExpr::LogicFnCall {
            name: "seq_empty".to_string(),
            args: vec![],
        };
        let push1 = PureExpr::MethodCall {
            receiver: Arc::new(empty),
            method: "push_back".to_string(),
            args: vec![PureExpr::Int(0)],
        };
        let push2 = PureExpr::MethodCall {
            receiver: Arc::new(push1),
            method: "push_back".to_string(),
            args: vec![PureExpr::Int(1)],
        };
        let ensure = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "result".to_string(),
                    None,
                )))),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        );

        assert!(result_view_len_matches_return_expr(&ensure, Some(&push2)));
    }

    #[test]
    fn result_view_len_rejects_wrong_push_back_chain_length() {
        let empty = PureExpr::LogicFnCall {
            name: "seq_empty".to_string(),
            args: vec![],
        };
        let push = PureExpr::MethodCall {
            receiver: Arc::new(empty),
            method: "push_back".to_string(),
            args: vec![PureExpr::Int(0)],
        };
        let ensure = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "result".to_string(),
                    None,
                )))),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        );

        assert!(!result_view_len_matches_return_expr(&ensure, Some(&push)));
    }

    #[test]
    fn direct_final_value_postcondition_matches_final_value_binding() {
        let ensure = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Var("n".to_string(), None)),
        );
        let mut final_values = HashMap::new();
        final_values.insert("x".to_string(), PureExpr::Var("n".to_string(), None));

        assert!(direct_final_value_postcondition_matches(
            &ensure,
            Some(&final_values)
        ));
    }

    #[test]
    fn direct_final_value_postcondition_rejects_wrong_value() {
        let ensure = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        );
        let mut final_values = HashMap::new();
        final_values.insert("x".to_string(), PureExpr::Var("n".to_string(), None));

        assert!(!direct_final_value_postcondition_matches(
            &ensure,
            Some(&final_values)
        ));
    }

    #[test]
    fn reconstructed_tuple_field_finality_matches_selected_field() {
        let tuple2 = tuple_logic_fn_name(2);
        let tuple_get_0 = tuple_field_logic_fn_name(0);
        let tuple_get_1 = tuple_field_logic_fn_name(1);

        let current_field = PureExpr::Deref(Arc::new(PureExpr::LogicFnCall {
            name: tuple_get_1.clone(),
            args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))],
        }));
        let ensure = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
                name: tuple_get_1.clone(),
                args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                    "x".to_string(),
                    None,
                )))],
            }))),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
                name: tuple_get_1,
                args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
                    "x".to_string(),
                    None,
                )))],
            }))),
        );
        let mut final_values = HashMap::new();
        final_values.insert(
            "x".to_string(),
            PureExpr::LogicFnCall {
                name: tuple2,
                args: vec![
                    PureExpr::LogicFnCall {
                        name: tuple_get_0,
                        args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                            "x".to_string(),
                            None,
                        )))],
                    },
                    current_field,
                ],
            },
        );
        final_values.insert(
            "x.1".to_string(),
            PureExpr::Deref(Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                    "x".to_string(),
                    None,
                )))],
            })),
        );

        assert!(reconstructed_tuple_field_finality_matches(
            &ensure,
            Some(&final_values)
        ));
    }

    #[test]
    fn reconstructed_tuple_field_finality_rejects_mismatched_reconstruction() {
        let tuple2 = tuple_logic_fn_name(2);
        let tuple_get_0 = tuple_field_logic_fn_name(0);
        let tuple_get_1 = tuple_field_logic_fn_name(1);

        let ensure = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
                name: tuple_get_1.clone(),
                args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                    "x".to_string(),
                    None,
                )))],
            }))),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
                name: tuple_get_1,
                args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
                    "x".to_string(),
                    None,
                )))],
            }))),
        );
        let mut final_values = HashMap::new();
        final_values.insert(
            "x".to_string(),
            PureExpr::LogicFnCall {
                name: tuple2,
                args: vec![
                    PureExpr::LogicFnCall {
                        name: tuple_get_0.clone(),
                        args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                            "x".to_string(),
                            None,
                        )))],
                    },
                    PureExpr::LogicFnCall {
                        name: tuple_get_0,
                        args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                            "x".to_string(),
                            None,
                        )))],
                    },
                ],
            },
        );

        assert!(!reconstructed_tuple_field_finality_matches(
            &ensure,
            Some(&final_values)
        ));
    }
}
