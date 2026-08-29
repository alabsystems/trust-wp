// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Memory safety audit tests for the trust-wp-ay encoder and verifier.
//!
//! Exercises edge cases identified in the memory_verification phase:
//! - Deep AST recursion (stack overflow risk in encode_pure_impl)
//! - Trigger synthesis on deep/wide expressions
//! - De Morgan transform with varied nesting patterns
//! - Non-consecutive existential handling correctness
//!
//! Re: #1018 (trigger synthesis), #970 (De Morgan transform)

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::helpers::{
    add, and, binop, exists, exists_with_sort, forall, forall_with_sort, formula_and, gt, int,
    logic_fn_call, not, or, var,
};
use crate::{
    encoder::{AYEncoder, MAX_ENCODING_DEPTH},
    BinOp, ExprSort, Formula, PureExpr,
};

#[path = "memory_safety/de_morgan_output_trigger_synthesis_tests.rs"]
mod de_morgan_output_trigger_synthesis_tests;

// ── Deep AST recursion tests ──────────────────────────────────────

/// Encode a moderately deep BinOp chain to verify the encoder doesn't
/// stack-overflow on non-trivial nesting.
///
/// 100 levels of nesting is safely below `MAX_ENCODING_DEPTH` while still
/// exercising non-trivial recursive encoding.
///
/// Runs in a thread with an 8 MB stack because `encode_pure_impl` stack
/// frames are large in debug builds and 100 recursive calls can exceed the
/// default 2 MB test-thread stack. (#2047)
#[test]
#[timeout(30000)]
fn deep_binop_chain_100_encodes_without_overflow() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut expr = int(0);
            for i in 1..=100 {
                expr = binop(expr, BinOp::Add, int(i));
            }
            let mut encoder = AYEncoder::new_pure();
            let term = encoder
                .encode_pure(&expr)
                .expect("100-deep BinOp chain should encode");
            let expected = encoder.solver_mut().int_const(5050);
            let eq_expected = encoder.solver_mut().eq(term, expected);
            let not_expected = encoder.solver_mut().not(eq_expected);
            encoder.assert_term(not_expected);
            assert_eq!(
                encoder.check_sat(),
                SolveResult::unsat(),
                "1..=100 additive chain should encode to 5050"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Encode a moderately deep Ite chain (if-then-else tower).
///
/// Each level adds one stack frame in encode_pure_impl. 100 levels
/// exercises the recursion pattern without tripping the guard.
///
/// Runs in a thread with an 8 MB stack because `encode_pure_impl` stack
/// frames are large in debug builds and 100 recursive Ite calls can exceed the
/// default 2 MB test-thread stack. (#2047)
#[test]
#[timeout(30000)]
fn deep_ite_chain_100_encodes_without_overflow() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut expr = int(0);
            for _ in 0..100 {
                expr = PureExpr::Ite(
                    Arc::new(PureExpr::Bool(true)),
                    Arc::new(expr),
                    Arc::new(int(1)),
                );
            }
            let mut encoder = AYEncoder::new_pure();
            let term = encoder
                .encode_pure(&expr)
                .expect("100-deep Ite chain should encode");
            let zero = encoder.solver_mut().int_const(0);
            let eq_zero = encoder.solver_mut().eq(term, zero);
            let non_zero = encoder.solver_mut().not(eq_zero);
            encoder.assert_term(non_zero);
            assert_eq!(
                encoder.check_sat(),
                SolveResult::unsat(),
                "all-true Ite chain should evaluate to the initial branch value (0)"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Encode a deeply nested Old(Deref(Old(Deref(...)))) chain.
///
/// Old and Deref each add a stack frame in encode_pure_impl.
/// This pattern exercises the wrapper-rewriting paths.
///
/// Runs in a thread with an 8 MB stack because `encode_pure_impl` stack
/// frames are large in debug builds and 100 recursive calls (50 Old + 50 Deref)
/// can exceed the default 2 MB test-thread stack. (#2047)
#[test]
#[timeout(30000)]
fn deep_old_deref_chain_100_encodes_without_overflow() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut expr: PureExpr = var("x");
            for _ in 0..50 {
                expr = PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(expr))));
            }
            let mut encoder = AYEncoder::new_pure();
            let result = encoder.encode_pure(&expr);
            // The encoder may reject deep Deref chains (no deref-target found),
            // but it should not stack-overflow. Accept Unsupported errors (expected
            // for deep deref chains) but reject SolverError or SortInference.
            match &result {
                Ok(term) => {
                    // Encoding succeeded — verify we got a real term, not a default
                    assert!(
                        !format!("{term:?}").is_empty(),
                        "encoded term should be non-empty"
                    );
                }
                Err(crate::EncodingError::Unsupported { .. }) => {
                    // Expected: deep Deref chains may be unsupported
                }
                Err(e) => {
                    panic!(
                        "deep Old/Deref chain should not stack-overflow; unexpected error variant: {e:?}"
                    );
                }
            }
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

// ── Depth limit enforcement tests (#1116) ────────────────────────

/// BinOp chain exceeding `MAX_ENCODING_DEPTH` must be rejected.
///
/// Runs in a thread with an 8 MB stack because `encode_pure_impl` stack
/// frames are large in debug builds and 129 recursive calls can exceed the
/// default 2 MB test-thread stack before the depth guard triggers. (#1116)
#[test]
#[timeout(30000)]
fn expr_depth_exceeding_limit_returns_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let depth = MAX_ENCODING_DEPTH + 1;
            let mut expr = int(0);
            #[allow(clippy::cast_possible_wrap)]
            for i in 1..=depth {
                expr = binop(expr, BinOp::Add, int(i as i64));
            }
            let mut encoder = AYEncoder::new_pure();
            let result = encoder.encode_pure(&expr);
            let err = result.unwrap_err();
            let msg = format!("{err}");
            assert!(
                msg.contains("nesting exceeds maximum depth"),
                "error should mention depth limit, got: {msg}"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Formula::And chain exceeding `MAX_ENCODING_DEPTH` must be rejected.
#[test]
#[timeout(30000)]
fn formula_depth_exceeding_limit_returns_error() {
    let depth = MAX_ENCODING_DEPTH + 1;
    let mut formula = Formula::True;
    for _ in 0..depth {
        formula = formula_and(formula, Formula::True);
    }
    let mut encoder = AYEncoder::new();
    let result = encoder.encode(&formula);
    assert!(
        result.is_err(),
        "depth {depth} should exceed limit, got Ok({:?})",
        result.as_ref().ok()
    );
    let msg = format!("{}", result.unwrap_err());
    assert!(
        msg.contains("nesting exceeds maximum depth"),
        "error should mention depth limit, got: {msg}"
    );
}

/// After a depth-limit error, the encoder's depth counter must be
/// properly reset so subsequent encoding calls succeed.
///
/// Runs in a thread with an 8 MB stack because `encode_pure_impl` stack
/// frames are large in debug builds. (#1116)
#[test]
#[timeout(30000)]
fn depth_counter_resets_after_error() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new_pure();

            // First: trigger a depth-limit error
            let depth = MAX_ENCODING_DEPTH + 1;
            let mut deep_expr = int(0);
            #[allow(clippy::cast_possible_wrap)]
            for i in 1..=depth {
                deep_expr = binop(deep_expr, BinOp::Add, int(i as i64));
            }
            let err_result = encoder.encode_pure(&deep_expr);
            assert!(
                err_result.is_err(),
                "should fail on over-deep expr, got Ok({:?})",
                err_result.as_ref().ok()
            );

            // Second: a shallow expression must still succeed on the same encoder
            let shallow = binop(int(1), BinOp::Add, int(2));
            let ok_result = encoder.encode_pure(&shallow);
            assert!(
                ok_result.is_ok(),
                "shallow expr after depth error should encode: {:?}",
                ok_result.err()
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

// ── Trigger synthesis stress tests ────────────────────────────────

/// Trigger synthesis with many candidate function calls in the body.
///
/// The pair-search in synthesize_triggers is O(n^2) where n is the
/// number of candidates. 50 candidates produces 1225 pairs, which
/// should still be fast.
///
/// NOTE: encoding-only — stress test for trigger synthesis pair-search performance.
/// check_sat would likely return Unknown due to the large number of synthesized
/// trigger candidates. The test's purpose is to verify no panic under load. See #1990.
#[test]
#[timeout(30000)]
fn trigger_synthesis_many_candidates_no_panic() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register 50 logic functions
    for k in 0..50 {
        let name = format!("f_{k}");
        let def = LogicFnDef::new(
            name.clone(),
            format!("crate::mem_audit::{name}"),
            vec!["x".to_string()],
            add(var("x"), int(k)),
        );
        encoder.register_logic_fn(&def).expect("register fn");
    }

    // forall<i> f_0(i) > 0 AND f_1(i) > 0 AND ... AND f_49(i) > 0
    let mut body = gt(logic_fn_call("f_0", vec![var("i")]), int(0));
    for k in 1..50 {
        body = and(
            body,
            gt(logic_fn_call(&format!("f_{k}"), vec![var("i")]), int(0)),
        );
    }
    let expr = forall("i", body);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "50-candidate trigger synthesis should not panic: {:?}",
        result.err()
    );
}

// ── De Morgan transform edge cases ───────────────────────────────

/// Non-consecutive existential under AND: the slow path should still
/// produce correct verification when the inner existential is not directly
/// nested under the outer existential.
///
/// Input postcondition: exists<a:Bool> (a AND exists<b:Bool> b)
/// Body result: true (via result == true)
///
/// The De Morgan transform only affects the outer exists; the inner
/// exists<b> under AND is preserved and evaluated normally.
#[test]
#[timeout(30000)]
fn de_morgan_non_consecutive_existential_verifies_correctly() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // exists<a:Bool> (a AND exists<b:Bool> b)
    // This is true because a=true AND b=true satisfies it.
    let inner_exists = exists_with_sort("b", ExprSort::Bool, var("b"));
    let postcondition = exists_with_sort("a", ExprSort::Bool, and(var("a"), inner_exists));

    let return_expr = PureExpr::Bool(true);
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[postcondition]).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "non-consecutive existential postcondition should verify: got {result:?}"
    );
}

/// Quadruple nested exists: NOT(exists<a> exists<b> exists<c> exists<d> P)
/// should produce forall<a> forall<b> forall<c> forall<d> NOT P.
///
/// This exercises the recursion depth of negate_existential_postcondition
/// beyond the triple test in de_morgan_proofs.rs.
#[test]
#[timeout(30000)]
fn de_morgan_quadruple_nested_existentials_equivalence() {
    let body = and(and(and(var("a"), var("b")), var("c")), var("d"));
    let original = exists_with_sort(
        "a",
        ExprSort::Bool,
        exists_with_sort(
            "b",
            ExprSort::Bool,
            exists_with_sort(
                "c",
                ExprSort::Bool,
                exists_with_sort("d", ExprSort::Bool, body.clone()),
            ),
        ),
    );
    let de_morgan = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort(
            "b",
            ExprSort::Bool,
            forall_with_sort(
                "c",
                ExprSort::Bool,
                forall_with_sort("d", ExprSort::Bool, not(body)),
            ),
        ),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "quadruple nested De Morgan must be semantically equivalent"
    );
}

/// De Morgan with exists-exists-forall-exists alternation:
/// NOT(exists<a> exists<b> forall<c> exists<d> P)
/// The consecutive exists<a> exists<b> are converted to forall<a> forall<b>,
/// then the forall<c> stops further recursion.
///
/// Expected: forall<a> forall<b> NOT(forall<c> exists<d> P)
#[test]
#[timeout(30000)]
fn de_morgan_exists_exists_forall_exists_alternation() {
    let body = and(and(and(var("a"), var("b")), var("c")), var("d"));
    let original = exists_with_sort(
        "a",
        ExprSort::Bool,
        exists_with_sort(
            "b",
            ExprSort::Bool,
            forall_with_sort(
                "c",
                ExprSort::Bool,
                exists_with_sort("d", ExprSort::Bool, body.clone()),
            ),
        ),
    );
    let de_morgan = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort(
            "b",
            ExprSort::Bool,
            not(forall_with_sort(
                "c",
                ExprSort::Bool,
                exists_with_sort("d", ExprSort::Bool, body),
            )),
        ),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "exists-exists-forall-exists De Morgan must be semantically equivalent"
    );
}

// ── Trigger synthesis edge case: same-name rebinding ──────────────

/// Nested quantifiers that rebind the same variable name.
///
/// `forall<i> forall<i> f(i) > 0`
///
/// The inner `i` shadows the outer `i`. After collapse,
/// `collect_nested_quantifier_vars` returns `["i", "i"]`.
/// Trigger synthesis should still encode without panic, though
/// the coverage check may be suboptimal.
///
/// NOTE: encoding-only — same-name rebinding is a degenerate edge case where
/// trigger coverage is suboptimal and check_sat behavior is undefined. See #1990.
#[test]
#[timeout(30000)]
fn trigger_synthesis_same_name_rebinding_no_panic() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::mem_audit::test_f".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    );
    encoder.register_logic_fn(&f_def).expect("register fn");

    // forall<i> forall<i> test_f(i) > 0
    let inner = forall("i", gt(logic_fn_call("test_f", vec![var("i")]), int(0)));
    let expr = forall("i", inner);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "same-name rebinding should not panic: {:?}",
        result.err()
    );
}

// ── Trigger synthesis: exists inside OR body ──────────────────────

/// Trigger synthesis for forall with exists in an OR branch.
///
/// `forall<i> (f(i) > 0 OR exists<j> g(j) > i)`
///
/// The exists<j> is opaque to the outer forall's trigger synthesis.
/// Only f(i) should be found as a trigger candidate for the outer forall.
#[test]
#[timeout(30000)]
fn trigger_synthesis_exists_inside_or_body() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let f_def = LogicFnDef::new(
        "test_f".to_string(),
        "crate::mem_audit::test_f".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    );
    let g_def = LogicFnDef::new(
        "test_g".to_string(),
        "crate::mem_audit::test_g".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(2)),
    );
    encoder.register_logic_fn(&f_def).expect("register fn f");
    encoder.register_logic_fn(&g_def).expect("register fn g");

    // forall<i> (test_f(i) > 0 OR exists<j> test_g(j) > i)
    let inner_exists = exists("j", gt(logic_fn_call("test_g", vec![var("j")]), var("i")));
    let body = or(
        gt(logic_fn_call("test_f", vec![var("i")]), int(0)),
        inner_exists,
    );
    let expr = forall("i", body);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "forall with exists inside OR should encode: {:?}",
        result.err()
    );

    // The formula is satisfiable (for each i, either i+1>0 or exists j with j+2>i)
    let term = result.unwrap();
    encoder.assert_term(term);
    let sat_result = encoder.check_sat();
    assert!(
        sat_result != SolveResult::unsat(),
        "formula should be satisfiable, got {:?}",
        sat_result
    );
}

// ── Encoder handles empty-args method/logic-fn calls gracefully ──

/// LogicFnCall with zero arguments should encode as a constant
/// function call, not panic on empty args.
#[test]
#[timeout(30000)]
fn logic_fn_call_zero_args_encodes() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // LogicMode::Open makes the body visible — the axiom const_fn() = 42
    // is asserted directly (zero params → ground equality, no quantifier).
    // LogicMode::Default would suppress the defining axiom (opaque body).
    let f_def = LogicFnDef::new(
        "const_fn".to_string(),
        "crate::mem_audit::const_fn".to_string(),
        vec![],
        int(42),
    )
    .with_mode(LogicMode::Open);
    encoder.register_logic_fn(&f_def).expect("register fn");

    let expr = gt(logic_fn_call("const_fn", vec![]), int(0));
    let term = encoder
        .encode_pure(&expr)
        .expect("zero-arg logic fn call should encode");
    let neg_term = encoder.solver_mut().not(term);
    encoder.assert_term(neg_term);
    let sat = encoder.check_sat();
    // With LogicMode::Open, the solver knows const_fn() = 42, so
    // !(const_fn() > 0) is !(42 > 0) which is Unsat.
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "const_fn() == 42 (Open mode) makes !(const_fn() > 0) Unsat: got {sat:?}"
    );
}

// ── Wide conjunction in postcondition negation ────────────────────

/// Wide conjunction: 20 postconditions, one with existential.
///
/// Exercises the slow path of encode_and_assert_negated_postconditions
/// with many disjuncts in the negated output.
#[test]
#[timeout(30000)]
fn wide_postcondition_negation_with_one_existential() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let mut ensures = Vec::new();
    // 19 simple postconditions: result > -k for k in 1..20
    for k in 1..20 {
        ensures.push(gt(var("result"), int(-k)));
    }
    // 1 existential postcondition: exists<a:Bool> a
    ensures.push(exists_with_sort("a", ExprSort::Bool, var("a")));

    let return_expr = int(5);
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "all postconditions hold (5 > -k for k>=1, and exists a. a): got {result:?}"
    );
}

/// Multi-variable Bool quantifier expansion gap: when trigger synthesis collapses
/// 2+ Bool-sorted variables into a single quantifier, the `vars_collected.len() == 1`
/// guard at logic_fn.rs:841 prevents case-split expansion. The quantifier falls
/// through to ay's quantifier engine which cannot enumerate Bool domains.
///
/// This test documents the gap: a single Bool var expands correctly, but
/// two nested Bool vars with synthesized triggers may not expand.
///
/// Re: proof_coverage audit — #1027 Bool expansion only handles single-variable case.
#[test]
#[timeout(30000)]
fn multi_var_bool_quantifier_single_var_expands_correctly() {
    // Single Bool var: forall<a:Bool> (a OR NOT a) — should expand to case splits
    // and be decidable (tautology → Sat when asserted directly)
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let single_var = forall_with_sort("a", ExprSort::Bool, or(var("a"), not(var("a"))));
    let term = encoder.encode_pure(&single_var).expect("should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "single Bool var tautology must be decidable via case-split expansion"
    );
}

/// Document that two nested Bool quantifiers each individually expand via
/// the single-variable path (outer forall expands a, inner body encoding
/// expands b). This works because each nesting level is a separate
/// `encode_pure_quantifier_impl` call.
///
/// Re: proof_coverage audit — verifies nested-but-separate Bool quantifiers.
#[test]
#[timeout(30000)]
fn nested_bool_quantifiers_each_expand_independently() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // forall<a:Bool> forall<b:Bool> (a OR b OR (NOT a AND NOT b))
    // This is a tautology. Each forall is handled separately.
    let body = or(or(var("a"), var("b")), and(not(var("a")), not(var("b"))));
    let expr = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort("b", ExprSort::Bool, body),
    );
    let term = encoder.encode_pure(&expr).expect("should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "nested Bool quantifiers should each expand independently via #1027 case splits"
    );
}

/// Multi-variable Bool quantifier expansion (#1134): when trigger synthesis
/// collapses nested same-kind triggerless Bool quantifiers into a single
/// multi-variable quantifier, the cartesian product expansion must still
/// produce correct results.
///
/// `forall<a:Bool, b:Bool> (a OR b)` is NOT a tautology (false when a=F, b=F),
/// so asserting it should make the formula UNSAT.
///
/// Before #1134, the `vars_collected.len() == 1` guard prevented Bool expansion
/// for collapsed multi-variable quantifiers, falling through to ay's quantifier
/// engine which cannot enumerate Bool domains.
#[test]
#[timeout(30000)]
fn multi_var_bool_forall_non_tautology_is_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // forall<a:Bool> forall<b:Bool> (a OR b)
    // Collapsed by trigger synthesis into forall<a,b:Bool> (a OR b).
    // NOT a tautology: counterexample a=false, b=false.
    let body = or(var("a"), var("b"));
    let expr = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort("b", ExprSort::Bool, body),
    );
    let term = encoder.encode_pure(&expr).expect("should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "forall<a,b:Bool> (a OR b) is not a tautology — must be UNSAT when asserted"
    );
}

/// Multi-variable Bool existential expansion (#1134): `exists<a,b:Bool> (a AND b)`
/// should be SAT because the valuation a=true, b=true satisfies it.
#[test]
#[timeout(30000)]
fn multi_var_bool_exists_satisfiable() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // exists<a:Bool> exists<b:Bool> (a AND b)
    // Collapsed by trigger synthesis into exists<a,b:Bool> (a AND b).
    // SAT: witness a=true, b=true.
    let body = and(var("a"), var("b"));
    let expr = exists_with_sort(
        "a",
        ExprSort::Bool,
        exists_with_sort("b", ExprSort::Bool, body),
    );
    let term = encoder.encode_pure(&expr).expect("should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "exists<a,b:Bool> (a AND b) is satisfiable (a=T,b=T) — must be SAT"
    );
}

/// Multi-variable Bool forall tautology (#1134): `forall<a,b:Bool> (a OR NOT a)`
/// is a tautology regardless of b. Verifies that unused variables in the
/// cartesian product don't break the expansion.
#[test]
#[timeout(30000)]
fn multi_var_bool_forall_tautology_with_unused_var() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // forall<a:Bool> forall<b:Bool> (a OR NOT a)
    // Tautology. b is unused but still participates in the expansion.
    let body = or(var("a"), not(var("a")));
    let expr = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort("b", ExprSort::Bool, body),
    );
    let term = encoder.encode_pure(&expr).expect("should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "forall<a,b:Bool> (a OR NOT a) is a tautology — must be SAT when asserted"
    );
}

// ── DepthGuard counter consistency ────────────────────────────────

/// Verify that the recursion depth counter returns to zero after a
/// successful nested encoding. Tests the DepthGuard RAII pattern
/// through multiple `encode_pure` calls.
///
/// Re: #1116 (recursion depth guard), memory_verification audit
#[test]
#[timeout(30000)]
fn depth_counter_returns_to_zero_after_successful_encoding() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Encode a moderately nested expression
    let nested = and(
        gt(add(var("x"), int(1)), int(0)),
        or(not(gt(var("y"), int(10))), and(var("a"), not(var("b")))),
    );
    let _ = encoder.encode_pure(&nested).expect("should encode");

    // Encode another expression — if depth counter leaked, this would
    // accumulate and eventually hit the limit.
    for _ in 0..200 {
        let simple = gt(var("x"), int(0));
        let _ = encoder.encode_pure(&simple).expect("should encode");
    }
    // If depth leaked, 200 calls × nesting depth > MAX_ENCODING_DEPTH.
    // Reaching here without error proves the counter resets correctly.
}

/// Verify that the depth counter stays consistent when a deep encoding
/// hits the limit and subsequent shallow encodings succeed.
///
/// Runs in a thread with an 8 MB stack because `encode_pure_impl` stack
/// frames are large in debug builds and 138 recursive calls can exceed the
/// default 2 MB test-thread stack before the depth guard triggers. (#1116)
///
/// Re: #1116, memory_verification audit
#[test]
#[timeout(30000)]
fn depth_counter_consistent_after_limit_then_success() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new_pure_with_quantifiers();

            // Build a chain that exceeds MAX_ENCODING_DEPTH
            let mut deep = int(0);
            for _ in 0..MAX_ENCODING_DEPTH + 10 {
                deep = not(deep);
            }
            let result = encoder.encode_pure(&deep);
            assert!(
                result.is_err(),
                "deep chain should exceed limit, got Ok({:?})",
                result.as_ref().ok()
            );

            // Now encode something shallow — must succeed if counter was reset
            let shallow = gt(var("x"), int(0));
            let result2 = encoder.encode_pure(&shallow);
            assert!(
                result2.is_ok(),
                "shallow encoding after depth error should succeed: {:?}",
                result2.err()
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

// ── Panic isolation and RAII guard tests ──────────────────────────

/// Verify that PathConditionGuard properly pops path_conditions on the
/// then-branch error path. If the guard leaks (doesn't pop), subsequent
/// Ite encoding would have a stale path condition on the stack.
///
/// Runs in a thread with an 8 MB stack because `encode_pure_impl` stack
/// frames are large in debug builds and 133 recursive calls can exceed the
/// default 2 MB test-thread stack before the depth guard triggers. (#1116)
/// Re: #1207, memory_verification audit
#[test]
#[timeout(30000)]
fn path_condition_guard_pops_on_encode_error_path() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            // Build a deeply nested expression that will exceed MAX_ENCODING_DEPTH
            // inside an Ite then-branch. This triggers an EncodingError return path
            // through the PathConditionGuard's scope.
            let mut deep = PureExpr::Bool(true);
            for _ in 0..MAX_ENCODING_DEPTH + 5 {
                deep = PureExpr::UnOp(crate::UnOp::Not, Arc::new(deep));
            }

            let ite_expr = PureExpr::Ite(
                Arc::new(PureExpr::Bool(true)),
                Arc::new(deep), // will fail with depth exceeded
                Arc::new(PureExpr::Bool(false)),
            );

            // Encoding should fail due to depth exceeded in the then-branch,
            // but PathConditionGuard must still pop the path condition.
            let result = encoder.encode_pure(&ite_expr);
            assert!(
                result.is_err(),
                "Ite with depth-exceeding then-branch should return error: {result:?}"
            );

            // Encode a simple expression to verify the encoder is still usable
            // (path_conditions stack is balanced, depth counter reset).
            let simple = encoder.encode_pure(&PureExpr::Bool(true));
            assert!(
                simple.is_ok(),
                "encoder should remain usable after Ite encoding error: {simple:?}"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Verify that DepthGuard properly decrements recursion_depth even when
/// encoding exits via the error return path (exceeding MAX_ENCODING_DEPTH).
///
/// Each round builds an expression exceeding MAX_ENCODING_DEPTH, triggers
/// the depth-exceeded error, then verifies the encoder is still usable.
/// If DepthGuard leaked (didn't decrement), successive rounds would
/// accumulate depth and the simple `Bool(true)` encoding would also fail.
///
/// Runs in a thread with an 8 MB stack because `encode_pure_impl` stack
/// frames are large in debug builds and 130 recursive calls can be
/// borderline for the default 2 MB test-thread stack. (#1116)
/// Re: #1116, memory_verification audit
#[test]
#[timeout(30000)]
fn depth_guard_resets_after_chain_of_errors() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let mut encoder = AYEncoder::new();

            // Attempt multiple depth-exceeding encodings.
            // After each error, the depth counter must return to 0.
            for i in 0..5 {
                // Build an expression exceeding MAX_ENCODING_DEPTH
                let mut deep = PureExpr::Int(0);
                for _ in 0..MAX_ENCODING_DEPTH + 2 {
                    deep = PureExpr::UnOp(crate::UnOp::Not, Arc::new(deep));
                }

                let result = encoder.encode_pure(&deep);
                assert!(
                    result.is_err(),
                    "encoding round {i}: depth-exceeding expression should error"
                );

                // If DepthGuard leaked, this would fail with depth exceeded
                let ok = encoder.encode_pure(&PureExpr::Bool(true));
                assert!(
                    ok.is_ok(),
                    "encoding round {i}: depth guard leaked — encoder unusable after error: {ok:?}"
                );
            }
        })
        .expect("thread spawn")
        .join()
        .expect("thread panicked");
}

/// Verify that solver panic isolation via catch_solver_panic correctly
/// sets the solver_panic_reason flag, preventing further SAT queries from
/// returning misleading results.
/// Re: #997, memory_verification audit
#[test]
#[timeout(30000)]
fn solver_panic_flag_prevents_post_panic_sat_queries() {
    let mut encoder = AYEncoder::new();

    // Create a valid assertion first
    let valid = encoder.encode_pure(&PureExpr::Bool(true)).unwrap();
    encoder.assert_term(valid);

    // Verify solver works before panic
    let pre_panic = encoder.check_sat();
    assert_eq!(
        pre_panic,
        SolveResult::Sat,
        "solver should be SAT before any panic"
    );

    // Force a solver panic by asserting a non-Bool term
    let non_bool = encoder.solver_mut().int_const(42);
    let catch_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(non_bool);
    }));
    assert!(
        catch_result.is_ok(),
        "assert_term should isolate the solver panic: {catch_result:?}"
    );

    // After panic, solver_panic_reason should be set
    assert!(
        encoder.solver_panic_reason().is_some(),
        "solver_panic_reason should be set after asserting non-Bool term"
    );

    // All subsequent SAT queries must return Unknown
    let post_panic = encoder.check_sat();
    assert_eq!(
        post_panic,
        SolveResult::Unknown,
        "all SAT queries after solver panic must return Unknown"
    );
}

/// Verify that after a solver panic, the encoder is poisoned and all
/// subsequent operations degrade gracefully to Unknown rather than
/// producing incorrect results.
/// Re: #1098, memory_verification audit
#[test]
#[timeout(30000)]
fn encoder_graceful_degradation_after_multiple_panics() {
    let mut encoder = AYEncoder::new();

    // First panic: assert non-Bool term
    let non_bool = encoder.solver_mut().int_const(99);
    let _result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(non_bool);
    }));

    // After first panic, check_sat must return Unknown
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "first panic: check_sat must return Unknown"
    );

    // Second panic attempt: assert another non-Bool term
    let non_bool2 = encoder.solver_mut().int_const(42);
    let _result2 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(non_bool2);
    }));

    // After second panic, still Unknown (not crash, not Sat, not Unsat)
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Unknown,
        "second panic: check_sat must still return Unknown"
    );

    // Encoding should still work (for error reporting / diagnostics)
    let ok = encoder.encode_pure(&PureExpr::Bool(true));
    assert!(
        ok.is_ok(),
        "encode_pure should still work after solver panic for diagnostic purposes: {ok:?}"
    );
}

/// Verify that encoding the same separation logic formula multiple times
/// produces consistent results and doesn't corrupt encoder state.
/// The footprint_cache / variable declarations must handle repeated
/// `PointsTo` encodings for the same location without panic or
/// inconsistent term generation.
/// Re: #668, memory_verification audit
#[test]
#[timeout(30000)]
fn repeated_formula_encoding_produces_consistent_results() {
    use trust_wp_core::formula::{Location, Permission, Value};

    let mut encoder = AYEncoder::new();

    // Encode the same PointsTo formula multiple times
    let formula = Formula::PointsTo {
        location: Location("x".to_string()),
        value: Value::Expr(PureExpr::Int(1)),
        permission: Permission::FULL,
    };

    let t1 = encoder.encode(&formula).unwrap();
    let t2 = encoder.encode(&formula).unwrap();

    // Assert both encodings that x points to 1
    encoder.assert_term(t1);
    encoder.assert_term(t2);

    // The conjunction of two identical PointsTo assertions should be SAT
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "two identical PointsTo assertions should be satisfiable"
    );

    // Now encode a contradictory PointsTo (x points to 2)
    let formula2 = Formula::PointsTo {
        location: Location("x".to_string()),
        value: Value::Expr(PureExpr::Int(2)),
        permission: Permission::FULL,
    };
    let t3 = encoder.encode(&formula2).unwrap();
    encoder.assert_term(t3);

    // x can't point to both 1 and 2 with full permission
    let result2 = encoder.check_sat();
    assert_eq!(
        result2,
        SolveResult::unsat(),
        "x pointing to both 1 and 2 with FULL permission should be UNSAT: got {result2:?}"
    );
}

// ── Recursive walker depth semantics tests ──────────────────────────
//
// These tests verify that recursive PureExpr analysis functions either
// survive moderately deep expression trees or switch to their documented
// conservative behavior once MAX_ENCODING_DEPTH is exceeded.
//
// Part of #1294 (LOW: "Unbounded recursive walks (15 functions)")
// Re: memory_verification phase audit

/// `collect_logic_fn_names` stops at `MAX_ENCODING_DEPTH`; verify it survives
/// a 500-deep nested expression tree and still reports reachable names from
/// within the active depth window.
///
/// Uses a dedicated thread with 4MB stack since the default test thread
/// stack may be too small for deeply recursive traversals in debug builds.
#[test]
#[timeout(30000)]
fn collect_logic_fn_names_survives_deep_nesting() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            use std::collections::HashSet;
            // Build a 500-deep left-recursive BinOp tree with logic fn calls at leaves.
            // The collector stops at MAX_ENCODING_DEPTH, so the deepest leaf
            // "deep_fn" at depth 500 will NOT be collected — this is correct
            // behavior (collector returns partial results at depth limit).
            let leaf = logic_fn_call("deep_fn", vec![int(1)]);
            let mut expr = leaf;
            for _ in 0..500 {
                expr = add(expr, logic_fn_call("other_fn", vec![int(2)]));
            }
            let mut names = HashSet::new();
            crate::expr::collect_logic_fn_names(&expr, &mut names);
            // "other_fn" appears as the right child at every level — found within depth limit
            assert!(
                names.contains("other_fn"),
                "Should find other_fn within depth limit"
            );
            // "deep_fn" is at the leftmost leaf (depth 500, beyond limit)
            // Collector stops early; deep_fn may not be collected
            // The important property is survival without stack overflow
            assert!(
                !names.is_empty(),
                "Should collect at least one fn name from within depth limit"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("collect_logic_fn_names stack-overflowed on 500-deep tree");
}

/// `expr_needs_quantifiers` (recursive walker in `expr.rs`) flips to a
/// conservative `true` result beyond `MAX_ENCODING_DEPTH`. Verify both the
/// exact within-window semantics and the over-limit fail-closed behavior.
#[test]
#[timeout(30000)]
fn expr_needs_quantifiers_survives_deep_nesting() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            let within_guard_depth = MAX_ENCODING_DEPTH.saturating_sub(8);

            // Stay below MAX_ENCODING_DEPTH so this assertion proves the
            // walker still detects real quantifiers before the guard fires.
            let mut within_guard_quantified = forall("i", gt(var("i"), int(0)));
            for _ in 0..within_guard_depth {
                within_guard_quantified = add(within_guard_quantified, int(1));
            }
            assert!(
                crate::expr::expr_needs_quantifiers(&within_guard_quantified),
                "Within the active depth window, expr_needs_quantifiers should detect a deep quantifier"
            );

            // Build a much deeper tree to prove the walker survives the
            // recursion and keeps returning the conservative fail-closed value.
            let mut deep_quantified = forall("i", gt(var("i"), int(0)));
            for _ in 0..500 {
                deep_quantified = add(deep_quantified, int(1));
            }
            assert!(
                crate::expr::expr_needs_quantifiers(&deep_quantified),
                "Beyond MAX_ENCODING_DEPTH, expr_needs_quantifiers should remain true for deep trees"
            );
            // Tree without quantifiers but beyond MAX_ENCODING_DEPTH:
            // the depth guard conservatively returns true (fail-closed)
            let mut no_quant = int(0);
            for _ in 0..500 {
                no_quant = add(no_quant, int(1));
            }
            assert!(
                crate::expr::expr_needs_quantifiers(&no_quant),
                "Beyond MAX_ENCODING_DEPTH, should conservatively assume quantifiers exist"
            );
            // Shallow tree without quantifiers should correctly return false
            let mut shallow_no_quant = int(0);
            for _ in 0..50 {
                shallow_no_quant = add(shallow_no_quant, int(1));
            }
            assert!(
                !crate::expr::expr_needs_quantifiers(&shallow_no_quant),
                "Shallow tree without quantifiers should return false"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("expr_needs_quantifiers stack-overflowed on 500-deep tree");
}

/// `substitute_vars_in_expr` clones the binding HashMap at every binder
/// (Forall/Exists/Let/Closure) during recursive descent. Verify that a
/// tree with 50 nested Let-binders and a 50-entry binding map doesn't
/// cause pathological allocation (50 * 50 = 2500 map entries cloned).
///
/// This is a documenting regression test — it passes currently but
/// exercises the O(depth × bindings) memory amplification pattern.
#[test]
#[timeout(30000)]
fn substitute_vars_in_expr_nested_binders_completes() {
    use std::collections::HashMap;
    // Build a 50-entry binding map
    let mut binding: HashMap<String, PureExpr> = HashMap::new();
    for i in 0..50 {
        binding.insert(format!("x{i}"), int(i));
    }
    // Build 50 nested Let binders: let y0 = 0 in (let y1 = 1 in ... (x0 + x49))
    let mut body = add(var("x0"), var("x49"));
    for i in (0..50).rev() {
        body = PureExpr::Let {
            var: format!("y{i}"),
            value: Arc::new(int(i)),
            body: Arc::new(body),
        };
    }
    let result = crate::verify::substitute_vars_in_expr(&body, &binding);
    // After substitution, x0 -> 0 and x49 -> 49, so the innermost
    // body should be Add(Int(0), Int(49))
    fn find_innermost_add(expr: &PureExpr) -> Option<&PureExpr> {
        match expr {
            PureExpr::Let { body, .. } => find_innermost_add(body),
            other => Some(other),
        }
    }
    let inner = find_innermost_add(&result).expect("should have innermost expression");
    match inner {
        PureExpr::BinOp(l, BinOp::Add, r) => {
            assert_eq!(**l, PureExpr::Int(0), "x0 should be substituted to 0");
            assert_eq!(**r, PureExpr::Int(49), "x49 should be substituted to 49");
        }
        other => panic!("expected BinOp::Add at innermost level, got {other:?}"),
    }
}

// ── closure_inline apply_substitution depth-guard gap tests ────────
//
// apply_substitution in encoder/closure_inline.rs is a near-duplicate of
// substitute_vars_inner (verify/expr_subst.rs:346) but LACKS the
// MAX_ENCODING_DEPTH guard. These tests verify it survives deep trees
// without stack overflow and document the gap.
//
// Part of #1945

/// closure_inline::apply_substitution has NO depth guard — verify it
/// survives a 200-deep nested expression through the closure body
/// inlining pipeline (try_inline_closure_postcondition).
///
/// Uses 8MB stack thread since apply_substitution stack frames include
/// HashMap clones at binding sites in debug builds.
#[test]
#[timeout(30000)]
fn closure_inline_apply_substitution_survives_deep_nesting() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            // Build a 200-deep left-recursive BinOp tree as a closure body.
            // This exercises apply_substitution through the closure inlining
            // path without any depth guard protection.
            let mut body = var("result");
            for i in 0..200 {
                body = binop(body, BinOp::Add, int(i as i64));
            }
            // Wrap as `result == deep_expr`
            let body = binop(var("result"), BinOp::Eq, body);

            let capture_info = crate::closure_capture_info! {
                def_id: "depth_test::closure#0".to_string(),
                captures: vec![],
                param_name: Some("f".to_string()),
                body_expr: Some(body),
                param_names: Some(vec![]),
                ensures_exprs: None,
            };

            let mut encoder = AYEncoder::new_pure();
            encoder.register_closure_body(&capture_info);

            // Build postcondition(f, call_0)
            let receiver = PureExpr::Var("f".to_string(), None);
            let result = encoder.try_inline_closure_postcondition(
                &receiver,
                "postcondition",
                &[PureExpr::Var("call_0".to_string(), None)],
                None,
            );
            assert!(
                result.is_some(),
                "Should inline 200-deep closure body without stack overflow"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("apply_substitution stack-overflowed on 200-deep tree");
}

/// collect_trigger_candidates should fail closed once the only trigger-shaped
/// term sits deeper than `MAX_ENCODING_DEPTH`.
#[test]
#[timeout(30000)]
fn collect_trigger_candidates_depth_limit_skips_too_deep_nesting() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            use std::collections::HashSet;
            // Build 300-deep tree with MethodCall nodes at leaves
            let leaf = PureExpr::MethodCall {
                receiver: Arc::new(var("x")),
                method: "get".to_string(),
                args: vec![var("i")],
            };
            let mut expr = leaf;
            for _ in 0..300 {
                expr = binop(expr, BinOp::Add, int(1));
            }

            let vars = vec!["i".to_string()];
            let mut shadowed = HashSet::new();
            let mut candidates = Vec::new();
            crate::encoder::trigger::collect_trigger_candidates(
                &expr,
                &vars,
                &mut shadowed,
                0,
                &mut candidates,
            );
            assert!(
                candidates.is_empty(),
                "candidate collection should stop once the trigger term is deeper than MAX_ENCODING_DEPTH"
            );
        })
        .expect("thread spawn")
        .join()
        .expect("collect_trigger_candidates stack-overflowed on too-deep tree");
}

/// extract_footprint now uses iterative traversal, so it should preserve the
/// full footprint even on a 300-deep Formula tree.
#[test]
#[timeout(30000)]
fn extract_footprint_survives_deep_formula() {
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            use crate::{Location, Permission, Value};
            // Build 300-deep SepConj chain
            let leaf = Formula::PointsTo {
                location: Location("x".to_string()),
                value: Value::Expr(int(1)),
                permission: Permission::FULL,
            };
            let mut formula = leaf;
            for i in 0..300 {
                let right = Formula::PointsTo {
                    location: Location(format!("loc_{i}")),
                    value: Value::Expr(int(i as i64)),
                    permission: Permission::FULL,
                };
                formula = Formula::SepConj(Arc::new(formula), Arc::new(right));
            }

            let encoder = AYEncoder::new_pure();
            let footprint = encoder.extract_footprint(&formula);
            // Should find x + 300 unique loc_N names = 301 total
            assert_eq!(
                footprint.len(),
                301,
                "Should extract 301 heap locations from 300-deep SepConj chain"
            );
            assert_eq!(footprint[0], "x", "First location should be 'x'");
        })
        .expect("thread spawn")
        .join()
        .expect("extract_footprint stack-overflowed on 300-deep formula");
}
