// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the local `solver_tail` helpers.
//!
//! The production module keeps the verification tail and helper logic in
//! `mod.rs`; the inline tests live here to keep that file below the file-size
//! threshold.

use std::{collections::HashMap, sync::Arc};

use ay_dpll::api::{Sort, Term};

use super::*;
use crate::shared_types::{
    SolveEvidenceSnapshot, SolveResourceSnapshot, SolveVerificationLevelSnapshot,
    SolveVerificationSnapshot,
};

// ── VACUOUS_PROOF_MESSAGE constant ──────────────────────────────────

#[test]
fn test_vacuous_proof_message_content() {
    assert!(
        VACUOUS_PROOF_MESSAGE.contains("vacuous"),
        "message should mention 'vacuous'"
    );
    assert!(
        VACUOUS_PROOF_MESSAGE.contains("UNSAT"),
        "message should mention 'UNSAT'"
    );
    assert!(
        VACUOUS_PROOF_MESSAGE.contains("negated postcondition"),
        "message should mention 'negated postcondition'"
    );
}

// ── AliasConstraintMode ─────────────────────────────────────────────

#[test]
fn test_alias_constraint_mode_copy() {
    let mode = AliasConstraintMode::ByValue;
    let copied = mode;
    // Verify Copy is implemented by using after assignment.
    let also_copied = mode;
    assert!(matches!(copied, AliasConstraintMode::ByValue));
    assert!(matches!(also_copied, AliasConstraintMode::ByValue));
}

#[test]
fn test_alias_constraint_mode_variants_exist() {
    assert!(matches!(
        AliasConstraintMode::ByValue,
        AliasConstraintMode::ByValue
    ));
    assert!(matches!(
        AliasConstraintMode::CurrentChain,
        AliasConstraintMode::CurrentChain
    ));
}

// ── post-axiom fallback unknown attribution ─────────────────────────

#[test]
fn test_fallback_unknown_prefers_specific_retry_reason() {
    let result = prefer_specific_fallback_unknown(
        &UnknownReason::QuantifierUnhandled,
        VerificationResult::Unknown(UnknownReason::Incomplete),
    );

    assert!(
        matches!(
            result,
            VerificationResult::Unknown(UnknownReason::Incomplete)
        ),
        "fallback should report the retry's specific unknown reason, got {result:?}"
    );
}

#[test]
fn test_fallback_unknown_keeps_original_when_retry_unspecified() {
    let result = prefer_specific_fallback_unknown(
        &UnknownReason::QuantifierUnhandled,
        VerificationResult::Unknown(UnknownReason::Unspecified),
    );

    assert!(
        matches!(
            result,
            VerificationResult::Unknown(UnknownReason::QuantifierUnhandled)
        ),
        "unspecified fallback reason should preserve the original reason, got {result:?}"
    );
}

#[test]
fn test_axiom_free_sat_rescue_includes_timeout() {
    assert!(
        should_rescue_with_axiom_free_sat(&UnknownReason::Timeout),
        "timeout after an axiom-free SAT counterexample should use the safe Failed fallback"
    );
}

#[test]
fn recursive_open_probe_skip_matches_qualified_and_method_calls_only_when_referenced() {
    let mut recursive = trust_wp_core::logic::LogicFnDef::new(
        "walk".to_string(),
        "crate::tree::walk".to_string(),
        vec!["x".to_string()],
        PureExpr::Bool(true),
    );
    recursive.set_is_recursive(true);
    recursive.set_mode(trust_wp_core::logic::LogicMode::Open);
    let logic_fns = [recursive];
    let body_div_obligations = [];

    for call in [
        PureExpr::LogicFnCall {
            name: "crate::tree::walk".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        },
        PureExpr::LogicFnCall {
            name: "Self::walk".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        },
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
            method: "walk".to_string(),
            args: vec![],
        },
    ] {
        let ensures = [call];
        let ctx = ObligationSliceContext {
            all_ensures: &ensures,
            requires: &[],
            logic_fns: Some(&logic_fns),
            mode_overrides: None,
            type_invariants: None,
            return_expr: None,
            mut_borrow_final_values: None,
            mutation_continued_params: None,
            body_div_obligations: &body_div_obligations,
            fresh_base_recheck: None,
            literal_false_base_recheck: None,
            slice_length_stable_vars: None,
            base_recheck_pathology: std::cell::Cell::new(false),
        };
        assert!(
            should_skip_axiom_free_probe_for_recursive_logic(&ctx),
            "recursive open call should skip the incomplete axiom-free probe"
        );
    }

    let unrelated = [PureExpr::LogicFnCall {
        name: "other".to_string(),
        args: vec![],
    }];
    let unrelated_ctx = ObligationSliceContext {
        all_ensures: &unrelated,
        requires: &[],
        logic_fns: Some(&logic_fns),
        mode_overrides: None,
        type_invariants: None,
        return_expr: None,
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };
    assert!(
        !should_skip_axiom_free_probe_for_recursive_logic(&unrelated_ctx),
        "an unrelated recursive definition must not disable the optional probe"
    );
}

#[test]
fn test_axiom_free_sat_rescue_includes_ematching_exists_incomplete() {
    assert!(
        should_rescue_with_axiom_free_sat(&UnknownReason::QuantifierEmatchingExistsIncomplete),
        "quantifier exists incompleteness after an axiom-free SAT counterexample should use the safe Failed fallback"
    );
}

#[test]
fn test_axiom_free_sat_rescue_keeps_non_tail_unknowns() {
    assert!(
        !should_rescue_with_axiom_free_sat(&UnknownReason::MemoryOut),
        "non-tail resource failures should not be reclassified through the SAT fallback"
    );
}

#[test]
fn test_axiom_free_sat_underflow_panic_uses_abort_rescue() {
    assert!(
        should_abort_with_axiom_free_sat_after_solver_panic(&UnknownReason::SolverPanic(
            "ay solver panicked: BUG: IncrementalTheoryState::pop() underflow".to_string(),
        )),
        "ay incremental pop-underflow corrupts cleanup scope state and should abort after rescue"
    );
}

#[test]
fn test_axiom_free_sat_abort_rescue_keeps_other_panics() {
    assert!(
        !should_abort_with_axiom_free_sat_after_solver_panic(&UnknownReason::SolverPanic(
            "ay solver panicked: BUG(#6853): conflict verification failed".to_string(),
        )),
        "unrelated ay solver panics should not be hidden by the underflow rescue"
    );
}

#[test]
fn test_incremental_pop_underflow_error_detection() {
    let error =
        EncodingError::solver_error("BUG: IncrementalTheoryState::pop() underflow -- more pops");

    assert!(
        is_incremental_pop_underflow_error(&error),
        "ay pop-underflow errors should be recognized for abort-style cleanup rescue"
    );
}

#[test]
fn test_verified_solve_evidence_result_detection_accepts_unsat_forms() {
    assert!(solve_evidence_result_is_unsat("unsat"));
    assert!(solve_evidence_result_is_unsat("UNSAT"));
    assert!(solve_evidence_result_is_unsat("Unsat(core)"));
}

#[test]
fn test_verified_solve_evidence_result_detection_rejects_sat_and_shortcuts() {
    assert!(!solve_evidence_result_is_unsat("sat"));
    assert!(!solve_evidence_result_is_unsat("unknown"));
    assert!(!solve_evidence_result_is_unsat(
        "trust-wp-structural-provenance"
    ));
}

fn accepted_unsat_evidence_for_test() -> SolveEvidenceSnapshot {
    SolveEvidenceSnapshot {
        result: "unsat".to_string(),
        model_validated: false,
        accepted_for_consumer: true,
        consumer_rejection: None,
        verification: SolveVerificationSnapshot::default(),
        verification_level: SolveVerificationLevelSnapshot::Unknown,
        resource_usage: SolveResourceSnapshot::default(),
    }
}

fn store_preferred_evidence_for_test() {
    PREFERRED_VERIFIED_SOLVE_EVIDENCE.with(|slot| {
        *slot.borrow_mut() = Some(PreferredVerifiedSolveDiagnostics {
            evidence: accepted_unsat_evidence_for_test(),
            statistics: None,
            claim_identity: None,
            problem_hash: None,
            native_problem_json: None,
            slice_generation: current_preferred_evidence_slice_generation(),
        });
    });
}

#[test]
fn test_preferred_verified_evidence_is_cleared_for_structural_consequence() {
    clear_preferred_verified_solve_evidence();

    store_preferred_evidence_for_test();
    assert!(
        take_preferred_verified_solve_evidence().is_some(),
        "test setup should produce preferred evidence"
    );

    store_preferred_evidence_for_test();
    let mut structural_encoder = AYEncoder::new_pure();
    structural_encoder.record_structural_ground_consequence("test-structural-consequence");
    let mut result = VerificationResult::Verified(None);
    record_preferred_verified_solve_evidence(&mut structural_encoder, &mut result);
    assert!(
        take_preferred_verified_solve_evidence().is_none(),
        "structurally assisted verified results must not leave stale accepted UNSAT evidence"
    );

    store_preferred_evidence_for_test();
    let mut main_encoder = AYEncoder::new_pure();
    main_encoder.record_structural_ground_consequence("main-structural-consequence");
    assert!(
        take_preferred_verified_solve_evidence_for_encoder(&main_encoder).is_none(),
        "pipeline-level preferred evidence extraction must not overwrite structural provenance"
    );
}

fn closure_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn closure_method(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

#[test]
fn test_closure_fn_to_fnmut_precheck_rejects_non_identity_res_state() {
    let ensures = vec![closure_method(
        closure_var("f"),
        "postcondition_mut",
        vec![closure_var("a"), closure_var("g"), closure_var("result")],
    )];
    let requires = vec![closure_method(
        closure_var("f"),
        "postcondition",
        vec![closure_var("a"), closure_var("result")],
    )];
    let body_div_obligations: Vec<Term> = Vec::new();
    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &requires,
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        return_expr: None,
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    assert!(
        !closure_postcondition_mut_follows_from_context(&ensures[0], &ctx),
        "plain Fn postcondition must not imply FnMut postcondition with arbitrary post-state"
    );
}

#[test]
fn test_closure_fn_to_fnmut_precheck_allows_identity_res_state() {
    let ensures = vec![closure_method(
        closure_var("f"),
        "postcondition_mut",
        vec![closure_var("a"), closure_var("f"), closure_var("result")],
    )];
    let requires = vec![closure_method(
        closure_var("f"),
        "postcondition",
        vec![closure_var("a"), closure_var("result")],
    )];
    let body_div_obligations: Vec<Term> = Vec::new();
    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &requires,
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        return_expr: None,
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    assert!(
        closure_postcondition_mut_follows_from_context(&ensures[0], &ctx),
        "Fn postcondition may only bridge to FnMut when the post-state is the same closure state"
    );
}

#[test]
fn test_post_axiom_clean_retry_includes_timeout() {
    assert!(
        should_retry_without_axioms_after_unknown(&UnknownReason::Timeout),
        "timeout from the full axiom solve should get a clean axiom-free retry"
    );
}

#[test]
fn test_post_axiom_clean_retry_includes_ematching_exists_incomplete() {
    assert!(
        should_retry_without_axioms_after_unknown(
            &UnknownReason::QuantifierEmatchingExistsIncomplete
        ),
        "quantifier exists incompleteness from the full axiom solve should get a clean axiom-free retry"
    );
}

#[test]
fn test_post_axiom_clean_retry_keeps_memoryout() {
    assert!(
        !should_retry_without_axioms_after_unknown(&UnknownReason::MemoryOut),
        "memory exhaustion should not trigger another solver retry"
    );
}

#[test]
fn test_type_invariant_obligation_detection() {
    let ensures = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "__trust_wp_invariant_NonZero".to_string(),
        args: vec![],
    }];
    let body_div_obligations: Vec<Term> = Vec::new();
    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &[],
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        return_expr: None,
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    assert!(is_type_invariant_obligation(&ctx, 0));
    assert!(!is_type_invariant_obligation(&ctx, 1));
}

#[test]
fn test_triangular_sum_postcondition_consequence_for_inclusive_range_start_one() {
    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }
    fn view(expr: PureExpr) -> PureExpr {
        PureExpr::View(Arc::new(expr))
    }
    fn len(expr: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(expr),
            method: "len".to_string(),
            args: vec![],
        }
    }
    fn bin(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }

    let n = view(var("n"));
    let result = view(var("result"));
    let sum = view(var("sum"));
    let produced_len = len(view(var("produced")));
    let bare_produced_len = len(var("produced"));
    let invariant = bin(
        bin(sum, BinOp::Mul, PureExpr::Int(2)),
        BinOp::Eq,
        bin(
            produced_len.clone(),
            BinOp::Mul,
            bin(produced_len, BinOp::Add, PureExpr::Int(1)),
        ),
    );
    let completion = bin(
        bare_produced_len,
        BinOp::Eq,
        PureExpr::Ite(
            Arc::new(bin(n.clone(), BinOp::Ge, PureExpr::Int(1))),
            Arc::new(bin(
                bin(n.clone(), BinOp::Sub, PureExpr::Int(1)),
                BinOp::Add,
                PureExpr::Int(1),
            )),
            Arc::new(PureExpr::Int(0)),
        ),
    );
    let nonnegative = bin(PureExpr::Int(0), BinOp::Le, n.clone());
    let ensure = bin(
        result.clone(),
        BinOp::Eq,
        bin(
            bin(
                n.clone(),
                BinOp::Mul,
                bin(n.clone(), BinOp::Add, PureExpr::Int(1)),
            ),
            BinOp::Div,
            PureExpr::Int(2),
        ),
    );
    let requires = vec![invariant, completion, nonnegative];
    let ensures = vec![ensure];
    let return_expr = var("sum");
    let body_div_obligations: Vec<Term> = Vec::new();
    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &requires,
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        return_expr: Some(&return_expr),
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    let fact = triangular_sum_postcondition_consequence(&ctx, 0)
        .expect("triangular range context should synthesize direct equality");

    assert_eq!(fact, expanded_triangular_equality(&result, &n));
}

#[test]
fn test_triangular_sum_postcondition_consequence_uses_loop_exit_result_bridge() {
    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }
    fn view(expr: PureExpr) -> PureExpr {
        PureExpr::View(Arc::new(expr))
    }
    fn len(expr: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(expr),
            method: "len".to_string(),
            args: vec![],
        }
    }
    fn bin(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }

    let n = view(var("n"));
    let result = view(var("result"));
    let sum = view(var("sum"));
    let produced_len = len(view(var("produced")));
    let invariant = bin(
        bin(sum.clone(), BinOp::Mul, PureExpr::Int(2)),
        BinOp::Eq,
        bin(
            produced_len.clone(),
            BinOp::Mul,
            bin(produced_len.clone(), BinOp::Add, PureExpr::Int(1)),
        ),
    );
    let completion = bin(produced_len, BinOp::Eq, n.clone());
    let result_bridge = bin(var("sum"), BinOp::Eq, var("result"));
    let ensure = bin(
        result.clone(),
        BinOp::Eq,
        bin(
            bin(
                n.clone(),
                BinOp::Mul,
                bin(n.clone(), BinOp::Add, PureExpr::Int(1)),
            ),
            BinOp::Div,
            PureExpr::Int(2),
        ),
    );
    let requires = vec![invariant, completion, result_bridge];
    let ensures = vec![ensure];
    let return_expr = var("result");
    let body_div_obligations: Vec<Term> = Vec::new();
    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &requires,
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        return_expr: Some(&return_expr),
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    let fact = triangular_sum_postcondition_consequence(&ctx, 0)
        .expect("loop-exit result equality should connect the accumulator to result@");

    assert_eq!(fact, expanded_triangular_equality(&result, &n));
}

#[test]
fn test_mut_borrow_final_disequality_consequence_for_inc_max_3_network() {
    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }
    fn deref(expr: PureExpr) -> PureExpr {
        PureExpr::Deref(Arc::new(expr))
    }
    fn final_expr(expr: PureExpr) -> PureExpr {
        PureExpr::Final(Arc::new(expr))
    }
    fn int(value: i64) -> PureExpr {
        PureExpr::Int(value)
    }
    fn bin(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }
    fn add(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        bin(lhs, BinOp::Add, rhs)
    }
    fn lt(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        bin(lhs, BinOp::Lt, rhs)
    }
    fn ne(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        bin(lhs, BinOp::Ne, rhs)
    }
    fn ite(condition: PureExpr, then_expr: PureExpr, else_expr: PureExpr) -> PureExpr {
        PureExpr::Ite(
            Arc::new(condition),
            Arc::new(then_expr),
            Arc::new(else_expr),
        )
    }

    let a = deref(var("ma"));
    let b = deref(var("mb"));
    let c = deref(var("mc"));

    let cond1 = lt(a.clone(), b.clone());
    let s1_a = ite(cond1.clone(), b.clone(), a.clone());
    let s1_b = ite(cond1, a.clone(), b.clone());

    let cond2 = lt(s1_b.clone(), c.clone());
    let s2_a = s1_a;
    let s2_b = ite(cond2.clone(), c.clone(), s1_b.clone());
    let s2_c = ite(cond2, s1_b, c);

    let cond3 = lt(s2_a.clone(), s2_b.clone());
    let s3_a = ite(cond3.clone(), s2_b.clone(), s2_a.clone());
    let s3_b = ite(cond3, s2_a, s2_b);
    let s3_c = s2_c;

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), add(s3_a, int(2)));
    final_values.insert("mb".to_string(), add(s3_b, int(1)));
    final_values.insert("mc".to_string(), s3_c);

    let ensures = vec![
        ne(final_expr(var("ma")), final_expr(var("mb"))),
        ne(final_expr(var("mb")), final_expr(var("mc"))),
        ne(final_expr(var("mc")), final_expr(var("ma"))),
    ];
    let body_div_obligations: Vec<Term> = Vec::new();
    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &[],
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        return_expr: None,
        mut_borrow_final_values: Some(&final_values),
        mutation_continued_params: None,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    for (index, ensure) in ensures.iter().enumerate() {
        assert_eq!(
            mut_borrow_final_disequality_consequence(&ctx, index),
            Some(ensure.clone()),
            "inc_max_3 final disequality {index} should be proved directly"
        );
    }
}

#[test]
fn test_mut_borrow_final_disequality_consequence_fails_closed_for_unordered_values() {
    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }
    fn deref(expr: PureExpr) -> PureExpr {
        PureExpr::Deref(Arc::new(expr))
    }
    fn final_expr(expr: PureExpr) -> PureExpr {
        PureExpr::Final(Arc::new(expr))
    }
    fn ne(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Ne, Arc::new(rhs))
    }

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), deref(var("ma")));
    final_values.insert("mb".to_string(), deref(var("mb")));

    let ensures = vec![ne(final_expr(var("ma")), final_expr(var("mb")))];
    let body_div_obligations: Vec<Term> = Vec::new();
    let ctx = ObligationSliceContext {
        all_ensures: &ensures,
        requires: &[],
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        return_expr: None,
        mut_borrow_final_values: Some(&final_values),
        mutation_continued_params: None,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: None,
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };

    assert_eq!(mut_borrow_final_disequality_consequence(&ctx, 0), None);
}

// ── assert_negated_goal_with_div_obligations ────────────────────────

#[test]
fn test_negated_goal_no_div_obligations_asserts_directly() {
    let mut encoder = AYEncoder::new();
    // Create a negated ensure term: NOT(x > 0) i.e., x <= 0
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let negated = encoder.solver_mut().not(x_gt_0);

    assert_negated_goal_with_div_obligations(&mut encoder, negated, &[], &[]);

    // With the negation asserted (x <= 0), the solver should find SAT
    // (x = 0 or x = -1 etc.)
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "negated goal alone should be satisfiable"
    );
}

#[test]
fn test_negated_goal_with_body_div_obligations() {
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let negated = encoder.solver_mut().not(x_gt_0);

    // Body div obligation: x != 0 (division safety) — split to avoid nested borrow
    let x_eq_zero = encoder.solver_mut().eq(x, zero);
    let div_obligation = encoder.solver_mut().not(x_eq_zero);

    assert_negated_goal_with_div_obligations(&mut encoder, negated, &[div_obligation], &[]);

    // The disjunction is: NOT(x > 0) OR NOT(x != 0)
    // = (x <= 0) OR (x == 0) which is (x <= 0). SAT.
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "disjunction with div obligation should be satisfiable"
    );
}

#[test]
fn test_negated_goal_with_post_div_obligations() {
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let negated = encoder.solver_mut().not(x_gt_0);

    // Post div obligation: x != 0 — split to avoid nested borrow
    let x_eq_zero = encoder.solver_mut().eq(x, zero);
    let post_div = encoder.solver_mut().not(x_eq_zero);

    assert_negated_goal_with_div_obligations(&mut encoder, negated, &[], &[post_div]);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "disjunction with post div obligation should be satisfiable"
    );
}

#[test]
fn test_negated_goal_with_both_div_obligations() {
    let mut encoder = AYEncoder::new();
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");
    let y = encoder
        .get_or_declare_var("y", Sort::Int)
        .expect("declare y");
    let zero = encoder.solver_mut().int_const(0);

    // Negated ensure: NOT(x > 0)
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let negated = encoder.solver_mut().not(x_gt_0);

    // Body div: y != 0 — split to avoid nested borrow
    let y_eq_zero = encoder.solver_mut().eq(y, zero);
    let body_div = encoder.solver_mut().not(y_eq_zero);
    // Post div: x != 0
    let x_eq_zero = encoder.solver_mut().eq(x, zero);
    let post_div = encoder.solver_mut().not(x_eq_zero);

    assert_negated_goal_with_div_obligations(&mut encoder, negated, &[body_div], &[post_div]);

    // Disjunction: NOT(x>0) OR NOT(y!=0) OR NOT(x!=0)
    // = (x<=0) OR (y==0) OR (x==0). Very satisfiable.
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "disjunction with both div obligations should be satisfiable"
    );
}

#[test]
fn test_negated_goal_contradiction_becomes_unsat() {
    // Set up a scenario where the goal is a tautology AND all div
    // obligations are also tautologies. Then negating everything yields
    // UNSAT.
    let mut encoder = AYEncoder::new();

    // Assert x == 5 (constrain x).
    let x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare x");
    let five = encoder.solver_mut().int_const(5);
    let x_eq_5 = encoder.solver_mut().eq(x, five);
    encoder.assert_term(x_eq_5);

    // Negated ensure: NOT(x == 5) i.e., x != 5. Combined with x == 5
    // above, this disjunction still needs to be UNSAT if the div obligation
    // is also defeated.
    let negated = encoder.solver_mut().not(x_eq_5);

    // Div obligation: true (trivially satisfied, so NOT(true) = false).
    let t = encoder.solver_mut().bool_const(true);

    assert_negated_goal_with_div_obligations(&mut encoder, negated, &[t], &[]);

    // Disjunction: NOT(x==5) OR NOT(true) = NOT(x==5) OR false = NOT(x==5)
    // With x == 5 asserted, NOT(x==5) is false. So the whole thing is UNSAT.
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "negated tautology goal should be UNSAT, got {result:?}"
    );
}

// ── axiom_free_solve_with_sat_extended ──────────────────────────────
//
// Tests for the extended axiom-free probe used by the post-axiom
// fallback (#2692). This probe retries UNSAT checking without quantified
// axioms using a 5s timeout, covering cases where axiom injection pushes
// a decidable QF_LIA problem into undecidable AUFLIA.

#[test]
fn test_extended_probe_finds_unsat_for_sorting_network_vc() {
    // Sorting network VC: after conditional swaps, a <= b <= c.
    // This is pure integer arithmetic — QF_LIA decidable.
    //
    // Model: three inputs a, b, c. Two conditional swaps:
    //   if a > b { swap(a, b) }
    //   if b > c { swap(b, c) }
    //   if a > b { swap(a, b) }  // third pass to fix up
    // Postcondition: a <= b AND b <= c AND a <= c
    let mut encoder = AYEncoder::new();
    let a = encoder.get_or_declare_var("a", Sort::Int).expect("a");
    let b = encoder.get_or_declare_var("b", Sort::Int).expect("b");
    let c = encoder.get_or_declare_var("c", Sort::Int).expect("c");

    // Build ITE chain for 3-element sorting network
    let solver = encoder.solver_mut();
    let a_gt_b = solver.gt(a, b);
    // After first swap: (a1, b1) = if a > b then (b, a) else (a, b)
    let a1 = solver.ite(a_gt_b, b, a);
    let b1 = solver.ite(a_gt_b, a, b);
    let b1_gt_c = solver.gt(b1, c);
    // After second swap: (b2, c2) = if b1 > c then (c, b1) else (b1, c)
    let b2 = solver.ite(b1_gt_c, c, b1);
    let c2 = solver.ite(b1_gt_c, b1, c);
    let a1_gt_b2 = solver.gt(a1, b2);
    // After third swap: (a3, b3) = if a1 > b2 then (b2, a1) else (a1, b2)
    let a3 = solver.ite(a1_gt_b2, b2, a1);
    let b3 = solver.ite(a1_gt_b2, a1, b2);

    // Postcondition: a3 <= b3 AND b3 <= c2 AND a3 <= c2
    let a3_le_b3 = solver.le(a3, b3);
    let b3_le_c2 = solver.le(b3, c2);
    let a3_le_c2 = solver.le(a3, c2);
    let post = solver.and(a3_le_b3, b3_le_c2);
    let post = solver.and(post, a3_le_c2);

    // Negate the postcondition (refutation-based verification)
    let negated_post = solver.not(post);
    encoder.assert_term(negated_post);

    // The extended probe should find UNSAT: the sorting network
    // always produces sorted output, so the negated postcondition
    // is unsatisfiable.
    let outcome = axiom_free_solve_with_sat_extended(&mut encoder);
    assert!(
        matches!(outcome, AxiomFreeOutcome::Unsat),
        "sorting network VC should be UNSAT without axioms, got {:?}",
        match &outcome {
            AxiomFreeOutcome::Unsat => "Unsat",
            AxiomFreeOutcome::Sat(_) => "Sat",
            AxiomFreeOutcome::Inconclusive => "Inconclusive",
        }
    );
}

#[test]
fn test_extended_probe_finds_sat_for_false_property() {
    // A false property should return SAT (counterexample).
    let mut encoder = AYEncoder::new();
    let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");
    let y = encoder.get_or_declare_var("y", Sort::Int).expect("y");

    // Assert x > 0 AND y > 0 (preconditions)
    let zero = encoder.solver_mut().int_const(0);
    let x_gt_0 = encoder.solver_mut().gt(x, zero);
    let y_gt_0 = encoder.solver_mut().gt(y, zero);
    encoder.assert_term(x_gt_0);
    encoder.assert_term(y_gt_0);

    // Negated postcondition: NOT(x + y > 100) — this is satisfiable
    // (e.g., x = 1, y = 1 satisfies x > 0 AND y > 0 AND x + y <= 100)
    let hundred = encoder.solver_mut().int_const(100);
    let sum = encoder.solver_mut().add(x, y);
    let sum_gt_100 = encoder.solver_mut().gt(sum, hundred);
    let negated = encoder.solver_mut().not(sum_gt_100);
    encoder.assert_term(negated);

    let outcome = axiom_free_solve_with_sat_extended(&mut encoder);
    assert!(
        matches!(outcome, AxiomFreeOutcome::Sat(_)),
        "false property should produce SAT counterexample"
    );
}

// ── extract_proof_summary ───────────────────────────────────────────

#[test]
fn test_extract_proof_summary_returns_none_without_proof() {
    let encoder = AYEncoder::new();
    // No check_sat has been called, so no proof artifact exists.
    let summary = extract_proof_summary(encoder.solver());
    assert!(
        summary.is_none(),
        "should return None when no proof artifact exists"
    );
}

// ── ObligationSliceContext construction ─────────────────────────────

#[test]
fn test_obligation_slice_context_empty() {
    let ctx = ObligationSliceContext {
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
        literal_false_base_recheck: None,
        slice_length_stable_vars: None,
        base_recheck_pathology: std::cell::Cell::new(false),
    };
    assert!(ctx.all_ensures.is_empty());
    assert!(ctx.requires.is_empty());
    assert!(ctx.logic_fns.is_none());
    assert!(ctx.mode_overrides.is_none());
    assert!(ctx.return_expr.is_none());
    assert!(ctx.body_div_obligations.is_empty());
    assert!(ctx.fresh_base_recheck.is_none());
}

// ── Goal-side sort-coercion guard (#knights_tour) ───────────────────

#[test]
fn negated_goal_sort_coercion_detected_from_snapshot_delta() {
    let restore_point = unsoundness::snapshot();
    let baseline = unsoundness::snapshot();
    assert!(
        !negated_goal_encode_introduced_sort_coercion(&baseline),
        "no increment yet — must not report coercion"
    );
    unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
    assert!(
        negated_goal_encode_introduced_sort_coercion(&baseline),
        "SortCoercionBridge increment after the baseline must be detected"
    );
    unsoundness::restore(&restore_point);
}

#[test]
fn sort_coerced_goal_demotes_failed_to_unknown() {
    let cont = ResolveContinuation::Continue(VerificationResult::Failed(Counterexample::empty()));
    let demoted = demote_sort_coerced_goal_counterexample(cont, 3);
    match demoted {
        ResolveContinuation::Continue(VerificationResult::Unknown(UnknownReason::Demoted(
            message,
        ))) => {
            assert!(
                message.contains("sort-coercion bridge in negated goal"),
                "demotion reason should identify the coerced goal: {message}"
            );
        }
        other => panic!("Failed must demote to Unknown(Demoted), got {other:?}"),
    }
}

#[test]
fn sort_coerced_goal_demotes_aborted_failed_to_unknown() {
    let cont = ResolveContinuation::Abort(VerificationResult::Failed(Counterexample::empty()));
    let demoted = demote_sort_coerced_goal_counterexample(cont, 0);
    assert!(
        matches!(
            demoted,
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Demoted(_)))
        ),
        "aborted Failed must also demote, got {demoted:?}"
    );
}

#[test]
fn sort_coerced_goal_leaves_non_failed_results_untouched() {
    let verified = ResolveContinuation::Continue(VerificationResult::Verified(None));
    assert!(
        matches!(
            demote_sort_coerced_goal_counterexample(verified, 0),
            ResolveContinuation::Continue(VerificationResult::Verified(None))
        ),
        "Verified must pass through the guard unchanged"
    );
    let unknown =
        ResolveContinuation::Continue(VerificationResult::Unknown(UnknownReason::Timeout));
    assert!(
        matches!(
            demote_sort_coerced_goal_counterexample(unknown, 0),
            ResolveContinuation::Continue(VerificationResult::Unknown(UnknownReason::Timeout))
        ),
        "Unknown must pass through the guard unchanged"
    );
}
