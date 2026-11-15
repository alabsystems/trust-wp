// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Formal verification tests for the De Morgan existential negation transform.
//!
//! The `negate_existential_postcondition` function in `verify/mod.rs` rewrites
//! `NOT(exists<x> P(x))` as `forall<x> NOT P(x)` at the PureExpr level. These
//! tests verify that the rewrite is semantically equivalent to direct negation
//! by encoding both forms in ay and checking for equivalence via UNSAT.
//!
//! ## Bool-sort limitation (#1087)
//!
//! The core equivalence proofs use `ExprSort::Bool` quantifiers, which ay
//! expands to finite case splits (via `encode_pure_bool_expansion`), making
//! equivalence trivially decidable. For `ExprSort::Int` quantifiers — the
//! common case in verification — ay relies on E-matching rather than integer
//! enumeration, so these tests pin the current deterministic outcomes.
//!
//! This is a fundamental solver limitation, not a soundness gap: the De Morgan
//! transform is mathematically correct for all sorts. The Int-sorted tests
//! below verify that (a) the transform produces encodable terms for Int sort,
//! and (b) the solver's incompleteness does not produce false verifications.
//! ay currently verifies simple Int-sorted witnesses but may still return
//! conservative Unknown results for mixed or nested quantified obligations.
//! (#1296)
//!
//! Re: #970 (closure spec negation), #1018 (trigger synthesis audit), #1087

use std::sync::Arc;

use ay_dpll::api::SolveResult;
use ntest::timeout;

use super::helpers::{
    and, binop, exists, exists_with_sort, forall_with_sort, gt, implies, int, let_assume,
    logic_fn_call, method_call, not, or, var,
};
use crate::{
    encoder::AYEncoder, verify_function_with_modes, BinOp, ExprSort, PureExpr, VerificationRequest,
    VerificationResult,
};

#[path = "de_morgan_equivalence.rs"]
mod de_morgan_equivalence;

/// Verify that trigger patterns are preserved through De Morgan rewriting.
///
/// Construct an exists with explicit triggers, negate it, then verify
/// the forall rewrite structurally preserves the trigger pattern.
///
/// Triggered quantifiers are NOT expanded to case splits (#1027), so we cannot
/// check semantic equivalence via solver for triggered forms. Instead, we verify:
/// 1. Both triggered forms (original exists and expected forall) encode successfully
/// 2. Triggerless equivalents ARE semantically equivalent (solver-decidable with Bool)
/// 3. Both triggered forms produce the same `var_names()` state (no variable leaks)
#[test]
#[timeout(30000)]
fn de_morgan_preserves_trigger_patterns() {
    // exists<a:Bool> {:pattern a} a
    // After De Morgan: forall<a:Bool> {:pattern a} NOT a
    // The trigger {:pattern a} should be preserved.
    let trigger = vec![vec![var("a")]];
    let exists_triggered = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(var("a")),
        triggers: trigger.clone(),
    };

    let forall_triggered = PureExpr::Forall {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(not(var("a"))),
        triggers: trigger,
    };

    // 1. Both triggered forms encode successfully. Keep these encoders scoped
    // so tests still run when TRUST_WP_MAX_TEST_SOLVERS is set to 2.
    {
        let mut encoder1 = AYEncoder::new_pure_with_quantifiers();
        encoder1
            .encode_pure(&exists_triggered)
            .expect("exists with triggers should encode");
        assert!(
            encoder1.var_names().is_empty(),
            "triggered exists should not leak bound vars: {:?}",
            encoder1.var_names()
        );
    }

    {
        let mut encoder2 = AYEncoder::new_pure_with_quantifiers();
        encoder2
            .encode_pure(&forall_triggered)
            .expect("forall with same triggers should encode");
        assert!(
            encoder2.var_names().is_empty(),
            "triggered forall should not leak bound vars: {:?}",
            encoder2.var_names()
        );
    }

    // 2. Triggerless equivalents prove the underlying transform is correct
    let exists_triggerless = exists_with_sort("a", ExprSort::Bool, var("a"));
    let forall_triggerless = forall_with_sort("a", ExprSort::Bool, not(var("a")));

    let mut equiv_encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(exists_triggerless);
    let violates = not(binop(direct_negation, BinOp::Eq, forall_triggerless));
    let term = equiv_encoder
        .encode_pure(&violates)
        .expect("equivalence check should encode");
    equiv_encoder.assert_term(term);
    assert_eq!(
        equiv_encoder.check_sat(),
        SolveResult::unsat(),
        "triggerless De Morgan rewrite must be semantically equivalent to direct negation"
    );
}

/// End-to-end: verify_function with mixed existential + non-existential
/// postconditions exercises the slow path of `encode_and_assert_negated_postconditions`.
///
/// Postconditions: [result > 0, exists<a:Bool> a]
/// Body result: 5
/// Both postconditions hold (5 > 0, and exists a. a is true for a=true).
/// The slow path negates individually and combines with OR, expecting UNSAT.
#[test]
#[timeout(30000)]
fn slow_path_mixed_existential_postcondition_via_verify_function() {
    let requires = [];
    let ensures = vec![
        gt(var("result"), int(0)),
        exists_with_sort("a", ExprSort::Bool, var("a")),
    ];
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "mixed existential + non-existential postconditions should verify when both hold: got {result:?}"
    );
}

/// End-to-end: slow path detects failure when one postcondition does not hold.
///
/// Postconditions: [exists<a:Bool> a, result < 0]
/// Body result: 5
/// Second postcondition fails (5 < 0 is false), so verification should fail.
#[test]
#[timeout(30000)]
fn slow_path_mixed_existential_detects_failure_via_verify_function() {
    let requires = [];
    let ensures = vec![
        exists_with_sort("a", ExprSort::Bool, var("a")),
        binop(var("result"), BinOp::Lt, int(0)),
    ];
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "should detect failing postcondition: got {result:?}"
    );
}

/// Non-consecutive existentials: `exists<a> (a AND exists<b> b)`.
///
/// The De Morgan transform only rewrites consecutive existentials.
/// For non-consecutive (exists nested under AND/OR), only the outer exists
/// is converted to forall, and the inner exists under AND remains as-is
/// with a NOT wrapper around the whole body.
///
/// Verifies: `forall<a> NOT(a AND exists<b> b)` ≡ `NOT(exists<a> (a AND exists<b> b))`
///
/// Note: We cannot distinguish the correct form from over-eager rewriting
/// (`forall<a> forall<b> NOT(a AND b)`) in Bool domain because Bool quantifiers
/// are case-split to finite domains where both happen to be equivalent. The
/// structural guarantee (inner exists is preserved) depends on the PureExpr-level
/// `negate_existential_postcondition` stopping at non-consecutive exists nodes,
/// which is tested in verify/mod.rs inline tests.
#[test]
#[timeout(30000)]
fn de_morgan_non_consecutive_existential_preserves_inner() {
    // Build: NOT(exists<a:Bool> (a AND exists<b:Bool> b))
    let inner_exists = exists_with_sort("b", ExprSort::Bool, var("b"));
    let outer_exists = exists_with_sort("a", ExprSort::Bool, and(var("a"), inner_exists));
    let direct_negation = not(outer_exists);

    // Correct De Morgan form: forall<a> NOT(a AND exists<b> b)
    let inner_exists2 = exists_with_sort("b", ExprSort::Bool, var("b"));
    let correct_de_morgan =
        forall_with_sort("a", ExprSort::Bool, not(and(var("a"), inner_exists2)));

    // Correct form is equivalent to direct negation
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let equiv = not(binop(direct_negation, BinOp::Eq, correct_de_morgan));
    let term = encoder.encode_pure(&equiv).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "correct (outer-only) De Morgan must be equivalent to direct negation"
    );
}

/// Verify: NOT(exists<a> forall<b> exists<c> (a AND b AND c))
///       ≡ forall<a> NOT(forall<b> exists<c> (a AND b AND c))
///
/// The exists-forall-exists alternation pattern: only the outermost exists is
/// converted to forall. The inner forall<b> is a non-Exists node so the
/// recursive `negate_existential_postcondition` stops, leaving the inner
/// `forall<b> exists<c>` structure negated as a whole.
#[test]
#[timeout(30000)]
fn de_morgan_exists_forall_exists_alternation() {
    let body = and(and(var("a"), var("b")), var("c"));
    let original = exists_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort(
            "b",
            ExprSort::Bool,
            exists_with_sort("c", ExprSort::Bool, body.clone()),
        ),
    );
    // After De Morgan: forall<a> NOT(forall<b> exists<c> (a AND b AND c))
    let de_morgan = forall_with_sort(
        "a",
        ExprSort::Bool,
        not(forall_with_sort(
            "b",
            ExprSort::Bool,
            exists_with_sort("c", ExprSort::Bool, body),
        )),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "exists-forall-exists alternation De Morgan must be semantically equivalent"
    );
}

/// Verify: the slow-path AND of two equivalent negation forms is at least as
/// strong as either form alone (soundness), but demonstrate that AND is strictly
/// stronger than OR (the OR version admits more models).
///
/// This test encodes the AND vs OR difference that #1106 tracks.
/// For Bool-sorted quantifiers, ay expands to case splits so both AND and OR
/// yield UNSAT on valid postconditions. The issue manifests with Int-sorted
/// quantifiers where E-matching is incomplete.
///
/// Here we verify the structural property: AND(A, B) implies OR(A, B).
#[test]
#[timeout(30000)]
fn slow_path_and_implies_or_soundness() {
    // For any existential postcondition, the rewritten and direct negation forms
    // are logically equivalent. Verify: AND(R, D) => OR(R, D) is a tautology.
    let a = var("a");
    let exists_pc = exists_with_sort("a", ExprSort::Bool, a);
    let rewritten = forall_with_sort("a", ExprSort::Bool, not(var("a")));
    let direct = not(exists_pc);

    let and_form = and(rewritten.clone(), direct.clone());
    let or_form = or(rewritten, direct);
    // AND(R,D) => OR(R,D) should be tautologically true
    let implication = implies(and_form, or_form);
    let violates = not(implication);

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "AND(rewritten, direct) must imply OR(rewritten, direct) — #1106 soundness"
    );
}

/// Verify: NOT(exists<a:Bool> NOT a) ≡ forall<a:Bool> NOT(NOT a) ≡ forall<a:Bool> a
///
/// When the existential body already contains a negation, the De Morgan
/// transform produces a double negation: `forall<a> NOT(NOT a)`. ay's `mk_not`
/// eliminates the double negation at the term level, so the final encoding is
/// `forall<a> a`. This test verifies the double-negation path is semantically
/// correct.
///
/// Re: proof_coverage audit — this path had zero test coverage.
#[test]
#[timeout(30000)]
fn de_morgan_double_negation_exists_not_body() {
    // NOT(exists<a:Bool> NOT a) should equal forall<a:Bool> a
    let original = exists_with_sort("a", ExprSort::Bool, not(var("a")));
    let expected = forall_with_sort("a", ExprSort::Bool, var("a"));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, expected));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "De Morgan double negation must be equivalent: NOT(exists<a> NOT a) == forall<a> a"
    );
}

/// Verify: NOT(exists<a:Bool> (assume P(a); Q(a))) ≡ forall<a:Bool> NOT(assume P(a); Q(a))
///
/// `LetAssume` in the existential body is a non-Exists node, so
/// `negate_existential_postcondition` wraps the entire body in NOT without
/// descending. Verify this is semantically correct.
///
/// Re: proof_coverage audit — LetAssume/LetObligation bodies had zero De Morgan
/// test coverage.
#[test]
#[timeout(30000)]
fn de_morgan_exists_with_let_assume_body() {
    // exists<a:Bool> (assume a; a) — the assumption forces a=true, body is a,
    // so the exists is satisfiable (a=true makes both hold).
    let body = let_assume(var("a"), var("a"));
    let original = exists_with_sort("a", ExprSort::Bool, body.clone());
    // After De Morgan: forall<a:Bool> NOT(assume a; a)
    let de_morgan = forall_with_sort("a", ExprSort::Bool, not(body));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "De Morgan with LetAssume body must be semantically equivalent"
    );
}

// ---------------------------------------------------------------------------
// Int-sorted De Morgan encoder-level tests (#1087)
//
// These tests verify that the De Morgan transform produces valid, encodable
// terms for Int-sorted quantifiers. Unlike the Bool-sorted proofs above,
// ay's E-matching engine can be incomplete over infinite integer domains, so
// each test pins the strongest currently deterministic solver result.
// ---------------------------------------------------------------------------

/// Int-sorted De Morgan: NOT(exists<a:Int> a > 0) vs forall<a:Int> NOT(a > 0).
///
/// Both forms should encode successfully and the equivalence check should
/// return Unsat: no counterexample exists where the two forms differ.
///
/// Re: #1087
#[test]
#[timeout(30000)]
fn de_morgan_int_sorted_single_existential_not_provably_different() {
    let original = exists_with_sort("a", ExprSort::Int, gt(var("a"), int(0)));
    let de_morgan = forall_with_sort("a", ExprSort::Int, not(gt(var("a"), int(0))));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder
        .encode_pure(&violates)
        .expect("Int-sorted De Morgan equivalence check should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "Int-sorted De Morgan forms must not be provably different, got {result:?}"
    );
}

/// Int-sorted De Morgan: nested existentials with arithmetic body.
///
/// NOT(exists<a:Int> exists<b:Int> a + b > 0)
///   vs forall<a:Int> forall<b:Int> NOT(a + b > 0)
///
/// Verifies that nested Int-sorted De Morgan produces encodable terms
/// and the solver does not find a counterexample to equivalence.
///
/// Re: #1087
#[test]
#[timeout(30000)]
fn de_morgan_int_sorted_nested_existentials_not_provably_different() {
    let sum = PureExpr::BinOp(Arc::new(var("a")), BinOp::Add, Arc::new(var("b")));
    let body = gt(sum, int(0));

    let original = exists_with_sort(
        "a",
        ExprSort::Int,
        exists_with_sort("b", ExprSort::Int, body.clone()),
    );
    let de_morgan = forall_with_sort(
        "a",
        ExprSort::Int,
        forall_with_sort("b", ExprSort::Int, not(body)),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder
        .encode_pure(&violates)
        .expect("nested Int-sorted De Morgan equivalence check should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "nested Int-sorted De Morgan forms must not be provably different, got {result:?}"
    );
}

/// Int-sorted De Morgan: mixed exists-forall with Int quantifiers.
///
/// NOT(exists<a:Int> forall<b:Int> a > b)
///   vs forall<a:Int> NOT(forall<b:Int> a > b)
///
/// Only the outer exists is converted; the inner forall remains.
/// `Unsat` would prove no counterexample exists; `Unknown` is a conservative
/// E-matching limitation for this mixed quantified shape. `Sat` would be a
/// real soundness failure because it would exhibit a difference between
/// logically equivalent formulas.
///
/// Re: #1087
#[test]
#[timeout(60000)]
fn de_morgan_int_sorted_mixed_exists_forall_not_provably_different() {
    let inner = forall_with_sort("b", ExprSort::Int, gt(var("a"), var("b")));
    let original = exists_with_sort("a", ExprSort::Int, inner.clone());
    let de_morgan = forall_with_sort("a", ExprSort::Int, not(inner));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder
        .encode_pure(&violates)
        .expect("mixed Int-sorted De Morgan equivalence check should encode");
    encoder.assert_term(term);
    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Sat),
        "mixed Int-sorted De Morgan forms must not be provably different, got {result:?}"
    );
}

/// End-to-end: slow-path with mixed Forall + Exists postconditions.
///
/// Postconditions: [forall<a:Bool> a, exists<b:Bool> b]
/// The first postcondition (forall<a> a) is false (fails for a=false).
/// The slow path negates each individually: NOT(forall a. a) and
/// AND(forall b. NOT b, NOT(exists b. b)) combined with OR.
/// Since the first postcondition fails, verification should detect the failure.
///
/// Re: proof_coverage audit — the slow-path had no test with a Forall
/// postcondition alongside an Exists postcondition.
#[test]
#[timeout(30000)]
fn slow_path_forall_and_exists_postconditions_detects_failure() {
    let requires = [];
    let ensures = vec![
        // forall<a:Bool> a — false (a=false violates)
        forall_with_sort("a", ExprSort::Bool, var("a")),
        // exists<b:Bool> b — true (b=true satisfies)
        exists_with_sort("b", ExprSort::Bool, var("b")),
    ];
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "forall<a> a postcondition is false — should detect failure: got {result:?}"
    );
}

/// End-to-end: slow-path with mixed Forall + Exists postconditions that
/// both hold. Verification should succeed.
///
/// Postconditions: [forall<a:Bool> (a OR NOT a), exists<b:Bool> b]
/// First postcondition is a tautology. Second is satisfiable. Both hold.
#[test]
#[timeout(30000)]
fn slow_path_forall_and_exists_postconditions_verifies_when_both_hold() {
    let requires = [];
    let ensures = vec![
        // forall<a:Bool> (a OR NOT a) — tautology, always true
        forall_with_sort("a", ExprSort::Bool, or(var("a"), not(var("a")))),
        // exists<b:Bool> b — satisfiable (b=true)
        exists_with_sort("b", ExprSort::Bool, var("b")),
    ];
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "both postconditions hold — should verify: got {result:?}"
    );
}

// ── Int-sorted De Morgan smoke tests (#1087) ─────────────────────────
//
// Bool-sorted quantifiers are expanded to finite case splits, making
// equivalence proofs trivially decidable. Int-sorted quantifiers use
// E-matching which cannot enumerate all integers. These tests verify that
// the slow-path De Morgan transform correctly handles Int-sorted
// existentials in end-to-end verification scenarios.

/// Int-sorted existential postcondition with an obvious syntactic witness.
///
/// Postcondition: exists<a:Int> a == result
/// Body: result = 42
/// The verifier should instantiate the existential with `result` before
/// reaching ay's quantified negation path, avoiding an E-matching timeout.
#[test]
#[timeout(30000)]
fn slow_path_int_sorted_existential_uses_syntactic_witness() {
    let requires = [];
    let ensures = vec![exists_with_sort(
        "a",
        ExprSort::Int,
        binop(var("a"), BinOp::Eq, var("result")),
    )];
    let return_expr = int(42);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("Int-sorted existential VC should encode");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Int-sorted existential with syntactic witness should verify: got {result:?}"
    );
}

/// Int-sorted nested existential postcondition with a simple additive witness.
///
/// Postconditions: [result > 0, exists<a:Int> exists<b:Int> a + b == result]
/// Body: result = 10
/// The verifier can use `a = result, b = 0`, so it should not send the
/// existential to the quantified De Morgan path.
#[test]
#[timeout(30000)]
fn slow_path_int_sorted_nested_existential_uses_additive_witness() {
    let requires = [];
    let ensures = vec![
        gt(var("result"), int(0)),
        exists_with_sort(
            "a",
            ExprSort::Int,
            exists_with_sort(
                "b",
                ExprSort::Int,
                binop(
                    PureExpr::BinOp(Arc::new(var("a")), BinOp::Add, Arc::new(var("b"))),
                    BinOp::Eq,
                    var("result"),
                ),
            ),
        ),
    ];
    let return_expr = int(10);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("nested Int-sorted existential VC should encode");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "nested Int existential with additive witness should verify: got {result:?}"
    );
}

/// Int-sorted existential postcondition mixed with a failing non-existential.
///
/// Postconditions: [exists<a:Int> a > result, result < 0]
/// Body: result = 5
/// The existential slice fails from ay incompleteness, and obligation slicing
/// lets the scalar `result < 0` slice fail independently, so the aggregate
/// verifier result must be Failed.
#[test]
#[timeout(30000)]
fn slow_path_int_sorted_existential_mixed_failure_aggregates_to_failed() {
    let requires = [];
    let ensures = vec![
        exists_with_sort("a", ExprSort::Int, gt(var("a"), var("result"))),
        PureExpr::BinOp(Arc::new(var("result")), BinOp::Lt, Arc::new(int(0))),
    ];
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("Int-sorted existential VC should encode");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "scalar failure should keep the aggregate result Failed: got {result:?}"
    );
}

/// Verify: the slow-path top-level check skips existentials nested inside
/// conjunctions. `exists<a:Bool> (a AND exists<b:Bool> b)` has the outermost
/// constructor `Exists`, so the slow path fires. But `(a AND exists<b:Bool> b)`
/// is a `BinOp`, so `negate_existential_postcondition` only transforms the
/// outer exists into forall, producing `forall<a:Bool> NOT(a AND exists<b> b)`.
///
/// The inner `exists<b>` is preserved inside the NOT wrapper — this is correct
/// because De Morgan should not recurse through non-Exists nodes.
///
/// Re: #1152 (nested existential inside conjunction gap)
#[test]
#[timeout(30000)]
fn de_morgan_exists_with_inner_exists_in_conjunction_is_sound() {
    // exists<a:Bool> (a AND exists<b:Bool> b)
    let inner_exists = exists_with_sort("b", ExprSort::Bool, var("b"));
    let original = exists_with_sort("a", ExprSort::Bool, and(var("a"), inner_exists.clone()));

    // After De Morgan: forall<a:Bool> NOT(a AND exists<b:Bool> b)
    // The inner exists is preserved — NOT wraps the conjunction.
    let inner_exists2 = exists_with_sort("b", ExprSort::Bool, var("b"));
    let de_morgan = forall_with_sort("a", ExprSort::Bool, not(and(var("a"), inner_exists2)));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let direct_negation = not(original);
    let violates = not(binop(direct_negation, BinOp::Eq, de_morgan));
    let term = encoder.encode_pure(&violates).expect("should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "De Morgan with inner exists inside conjunction must be semantically equivalent — #1152"
    );
}

/// Verify: a postcondition that is a conjunction with a nested existential
/// takes the FAST path (no top-level Exists), so ay handles the negation.
///
/// Postconditions: [(a_free AND exists<b:Bool> b)] — outer is BinOp, not Exists.
/// The fast path negates at ay level: NOT(a_free AND exists<b> b).
/// After #1152, nested existentials route through the slow path (which
/// delegates to `encode_negated_postcondition`). The result should still
/// be Verified — the slow path is sound and now also has the embedded
/// existential handling benefit.
///
/// Re: #1152 (nested existentials now use slow path)
#[test]
#[timeout(30000)]
fn slow_path_conjunction_with_nested_existential_is_sound() {
    let requires = [];
    // result > 0 AND exists<b:Bool> b
    // The outer node is BinOp(And) with an embedded Exists, so the slow path fires.
    let ensures = vec![and(
        gt(var("result"), int(0)),
        exists_with_sort("b", ExprSort::Bool, var("b")),
    )];
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("conjunction with nested existential should encode");
    // result=5 > 0 is true. exists<b:Bool> b is true (b=true). Both hold.
    // Fast path negates: NOT(5>0 AND exists<b> b) should be Unsat → Verified.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "fast-path conjunction with nested existential should verify: got {result:?}",
    );
}

/// Isolation test: assert ONLY the De Morgan rewritten form (forall<x> NOT P(x)),
/// without the direct-negation fallback NOT(exists<x> P(x)).
///
/// The slow path in `encode_and_assert_negated_postconditions` (verify/mod.rs:267-270)
/// asserts AND(rewritten, direct), which means a broken De Morgan path is masked by
/// the direct negation (#1183). This test exercises the rewritten form alone.
///
/// Setup: postcondition `exists<a:Bool> a` is true (a=true satisfies it).
/// Negation via De Morgan: `forall<a:Bool> NOT a`.
/// If body result satisfies the postcondition, asserting the De Morgan negation
/// alone should yield Unsat.
///
/// Re: #1183 (dual-negation masking trigger regressions)
#[test]
#[timeout(30000)]
fn de_morgan_only_without_direct_negation_fallback() {
    // Postcondition: exists<a:Bool> a (satisfiable: a=true)
    // Body result: irrelevant for pure quantifier (no `result` var)
    // De Morgan negation: forall<a:Bool> NOT a (false: a=true violates it)
    //
    // Assert ONLY the De Morgan form. If Unsat, the rewrite path alone
    // is sufficient to prove the postcondition holds.
    let de_morgan_negation = forall_with_sort("a", ExprSort::Bool, not(var("a")));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let term = encoder
        .encode_pure(&de_morgan_negation)
        .expect("De Morgan form should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "De Morgan form alone (without direct-negation fallback) must be Unsat \
         when the existential postcondition is valid — if this fails, the rewrite \
         path is broken and the dual-assertion in verify/mod.rs is masking it (#1183)"
    );
}

/// Isolation test: De Morgan-only form for nested existentials.
///
/// Postcondition: `exists<a:Bool> exists<b:Bool> (a AND b)` (satisfied by a=true, b=true).
/// De Morgan negation: `forall<a:Bool> forall<b:Bool> NOT(a AND b)` (false: a=true, b=true).
///
/// Asserts ONLY the De Morgan form to verify nested rewrites work without the
/// direct-negation fallback.
///
/// Re: #1183
#[test]
#[timeout(30000)]
fn de_morgan_only_nested_exists_without_direct_fallback() {
    let de_morgan_negation = forall_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort("b", ExprSort::Bool, not(and(var("a"), var("b")))),
    );

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let term = encoder
        .encode_pure(&de_morgan_negation)
        .expect("nested De Morgan form should encode");
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "nested De Morgan form alone must be Unsat when the existential is valid (#1183)"
    );
}

/// Isolation test: De Morgan-only form detects invalid postcondition.
///
/// Postcondition: `exists<a:Bool> (a AND NOT a)` (unsatisfiable: contradiction).
/// De Morgan negation: `forall<a:Bool> NOT(a AND NOT a)` (true: tautology).
///
/// Asserts ONLY the De Morgan form — should be SAT (postcondition doesn't hold,
/// so its negation is satisfiable). This is the negative counterpart to
/// `de_morgan_only_without_direct_negation_fallback`.
///
/// Re: #1183
#[test]
#[timeout(30000)]
fn de_morgan_only_detects_invalid_postcondition() {
    // NOT(a AND NOT a) is always true, so forall<a> NOT(a AND NOT a) is true.
    // Asserting a true formula should be SAT.
    let de_morgan_negation =
        forall_with_sort("a", ExprSort::Bool, not(and(var("a"), not(var("a")))));

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let term = encoder
        .encode_pure(&de_morgan_negation)
        .expect("De Morgan form should encode");
    encoder.assert_term(term);
    // The negation of an unsatisfiable existential is a tautology → Sat
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "De Morgan negation of unsatisfiable existential should be Sat (postcondition invalid)"
    );
}

/// End-to-end: slow-path with 3 postconditions (existential + forall + non-quantified).
///
/// Postconditions: [result > 0, exists<a:Bool> a, forall<b:Bool> (b OR NOT b)]
/// Body result: 5
/// All three hold: 5 > 0, exists a. a (true for a=true), forall b. tautology.
/// The slow path negates each individually and combines with OR:
///   NOT(5>0) OR (De Morgan + direct)_exists OR NOT(forall b. b OR NOT b)
/// This is UNSAT because all postconditions hold → all negations are false.
///
/// Re: #1106 (OR completeness), previously only tested with 1-2 postconditions.
#[test]
#[timeout(30000)]
fn slow_path_three_postconditions_all_hold_verifies() {
    let requires = [];
    let ensures = vec![
        gt(var("result"), int(0)),
        exists_with_sort("a", ExprSort::Bool, var("a")),
        forall_with_sort("b", ExprSort::Bool, or(var("b"), not(var("b")))),
    ];
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "all three postconditions hold — should verify: got {result:?}"
    );
}

/// End-to-end: slow-path with 3 postconditions where the middle one fails.
///
/// Postconditions: [result > 0, exists<a:Bool> (a AND NOT a), forall<b:Bool> (b OR NOT b)]
/// Body result: 5
/// Second postcondition (exists a. contradiction) fails. Slow path should detect it:
///   NOT(5>0) OR (De Morgan + direct)_exists OR NOT(forall b. tautology)
/// The second disjunct (De Morgan negation of the contradiction) should be SAT
/// (since the postcondition is unsatisfiable, its negation is a tautology).
///
/// Re: #1106 (OR completeness)
#[test]
#[timeout(30000)]
fn slow_path_three_postconditions_middle_fails_detects_failure() {
    let requires = [];
    let ensures = vec![
        gt(var("result"), int(0)),
        // exists<a:Bool> (a AND NOT a) — unsatisfiable contradiction
        exists_with_sort("a", ExprSort::Bool, and(var("a"), not(var("a")))),
        forall_with_sort("b", ExprSort::Bool, or(var("b"), not(var("b")))),
    ];
    let return_expr = int(5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "middle existential postcondition is unsatisfiable — should detect failure: got {result:?}"
    );
}

/// Structural test: `negate_existential_postcondition` with `var_sort: None`
/// (no explicit sort annotation) preserves the None sort through the transform.
///
/// With None annotation, the variable defaults to Int sort. Int-sorted quantifiers
/// use E-matching, and both encodings should produce the same strict solver
/// result.
///
/// Re: proof_coverage audit — sort preservation with None annotation was untested.
#[test]
#[timeout(30000)]
fn de_morgan_preserves_none_sort_annotation_encodes_consistently() {
    // exists<a: ?> (a > 0) — no sort annotation (defaults to Int)
    let expr = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: None,
        body: Arc::new(gt(var("a"), int(0))),
        triggers: vec![],
    };

    // De Morgan form: forall<a: ?> NOT(a > 0)
    let de_morgan = PureExpr::Forall {
        var: "a".to_string(),
        var_sort: None,
        body: Arc::new(not(gt(var("a"), int(0)))),
        triggers: vec![],
    };

    // Encode the direct negation form
    let mut encoder1 = AYEncoder::new_pure_with_quantifiers();
    let direct_neg = not(expr);
    let term1 = encoder1
        .encode_pure(&direct_neg)
        .expect("direct negation should encode");
    encoder1.assert_term(term1);
    let result1 = encoder1.check_sat();

    // Encode the De Morgan form
    let mut encoder2 = AYEncoder::new_pure_with_quantifiers();
    let term2 = encoder2
        .encode_pure(&de_morgan)
        .expect("De Morgan form should encode");
    encoder2.assert_term(term2);
    let result2 = encoder2.check_sat();

    assert_eq!(
        result1,
        SolveResult::unsat(),
        "direct negation should be UNSAT, got {result1:?}"
    );
    assert_eq!(
        result2,
        SolveResult::unsat(),
        "De Morgan form should be UNSAT, got {result2:?}"
    );
}

/// Eager negated existential instantiation: multi-variable existential postcondition
/// with postcondition_mut method calls is proved using ground witness terms from
/// preconditions.
///
/// Simulates the `call_fnmut` pattern from closures/07_mutable_capture:
/// - Requires: postcondition_mut(f, (), f_final, call_0) AND
///   postcondition_mut(f_final, (), f_final_final, result) AND
///   resolve(f_final_final)
/// - Ensures: exists<st1, st2, r>
///   f.postcondition_mut((), st1, r) AND
///   st1.postcondition_mut((), st2, result) AND
///   resolve(st2)
///
/// Without eager instantiation, E-matching fails because no single trigger
/// pattern covers all three bound variables (st1, st2, r). The eager
/// instantiation matches body patterns against ground precondition calls
/// and asserts the ground negated clause directly. (#970)
#[test]
#[timeout(30000)]
fn eager_negated_existential_instantiation_call_fnmut_pattern() {
    use super::helpers::{resolve_call, value_state};

    // Ground precondition terms (what the verifier knows after two f() calls).
    // The terminal state is annotated at a sort holding no borrow, whose
    // `resolve` is the by-value `true` (D-126).
    let req_mut_1 = method_call(
        var("f"),
        "postcondition_mut",
        vec![int(0), var("f_final"), var("call_0")],
    );
    let req_mut_2 = method_call(
        var("f_final"),
        "postcondition_mut",
        vec![int(0), value_state("f_final_final"), var("result")],
    );
    let req_resolve = resolve_call(value_state("f_final_final"));
    let requires = vec![and(req_mut_1, and(req_mut_2, req_resolve))];

    // Existential postcondition:
    // exists<st1> exists<st2> exists<r>
    //   f.postcondition_mut((), st1, r) &&
    //   st1.postcondition_mut((), st2, result) &&
    //   resolve(st2)
    let body = and(
        method_call(
            var("f"),
            "postcondition_mut",
            vec![int(0), var("st1"), var("r")],
        ),
        and(
            method_call(
                var("st1"),
                "postcondition_mut",
                vec![int(0), var("st2"), var("result")],
            ),
            resolve_call(var("st2")),
        ),
    );
    let ensures = vec![exists("st1", exists("st2", exists("r", body)))];

    // Body result: var("result") — the function returns the second call's result
    let return_expr = var("result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("verification should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "call_fnmut existential postcondition should verify with eager instantiation: got {result:?}"
    );
}

/// Same as above but using the real PureExpr structures from the driver:
/// call-site assumptions use `Deref(Var("f"))` for `(*self)` and
/// `Final(Var("f"))` for `^self`, while the ensures body uses bare variables.
/// The eager instantiation normalizes Deref/Final before matching. (#970)
///
/// Not credited since D-127: the premise `resolve(^f_final)` resolves the
/// value `^f_final` at its own type, a closure state that may hold the
/// caller's borrow, and the goal's `resolve(st2)` reads the final value of a
/// written binder with no sort. Both are refused rather than read as the
/// collapse `st2 == st2` the idiom verified through, which also verified the
/// same claim of a function that RETURNS the state.
#[test]
#[timeout(30000)]
fn eager_negated_existential_with_deref_final_wrappers_is_not_credited() {
    use super::helpers::resolve_call;

    let deref_f = PureExpr::Deref(Arc::new(var("f")));
    let final_f = PureExpr::Final(Arc::new(var("f")));
    let deref_f_final = PureExpr::Deref(Arc::new(var("f_final")));
    let final_f_final = PureExpr::Final(Arc::new(var("f_final")));

    // Ground precondition terms using Deref/Final wrappers (as produced by
    // the driver's call-site assumption extraction):
    //   (*f).postcondition_mut((), ^f, call_0)
    //   (*f_final).postcondition_mut((), ^f_final, result)   [bridged]
    //   resolve(^f_final)   [from axiom system]
    let req_mut_1 = method_call(
        deref_f,
        "postcondition_mut",
        vec![int(0), final_f, var("call_0")],
    );
    let req_mut_2_bridged = method_call(
        deref_f_final,
        "postcondition_mut",
        vec![int(0), final_f_final.clone(), var("result")],
    );
    let req_resolve = resolve_call(final_f_final);
    let requires = vec![and(req_mut_1, and(req_mut_2_bridged, req_resolve))];

    // Existential postcondition (same as before — uses bare variables):
    let body = and(
        method_call(
            var("f"),
            "postcondition_mut",
            vec![int(0), var("st1"), var("r")],
        ),
        and(
            method_call(
                var("st1"),
                "postcondition_mut",
                vec![int(0), var("st2"), var("result")],
            ),
            resolve_call(var("st2")),
        ),
    );
    let ensures = vec![exists("st1", exists("st2", exists("r", body)))];
    let return_expr = var("result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    );
    assert!(
        !matches!(result, Ok(VerificationResult::Verified(_))),
        "call_fnmut's resolve of a closure state must not be credited (D-127): got {result:?}"
    );
}

/// De Morgan transform handles exists-forall alternation correctly by stopping
/// at the first non-Exists body. For `exists<a> forall<b> P(a, b)`, only
/// the outer `exists<a>` is rewritten: `forall<a> NOT(forall<b> P(a, b))`.
/// The inner `forall<b>` is preserved under the negation.
///
/// Soundness check: both forms are equivalent under Bool-sorted quantifiers.
///
/// Re: #1087 (De Morgan transform soundness audit)
#[test]
#[timeout(30000)]
fn de_morgan_exists_forall_alternation_stops_at_forall() {
    // exists<a:Bool> forall<b:Bool> (a IMPLIES b)
    // De Morgan: forall<a:Bool> NOT(forall<b:Bool> (a IMPLIES b))
    // which is: forall<a:Bool> exists<b:Bool> NOT(a IMPLIES b)
    // Intuitively: for all a, there exists b such that a does not imply b.
    // For a=true, we need b such that NOT(true => b), i.e., NOT(b), so b=false. Sat.
    // For a=false, (false => b) is always true, so NOT(false => b) is false. No b works.
    // So exists<a> forall<b> (a => b) means: there is an a such that a implies everything.
    // Only a=false works (false implies everything). So the original is Sat.
    let original = exists_with_sort(
        "a",
        ExprSort::Bool,
        forall_with_sort("b", ExprSort::Bool, implies(var("a"), var("b"))),
    );

    // Direct negation: NOT(exists<a> forall<b> (a => b))
    let mut enc1 = AYEncoder::new_pure_with_quantifiers();
    let neg_original = not(original.clone());
    let t1 = enc1
        .encode_pure(&neg_original)
        .expect("direct negation encodes");
    enc1.assert_term(t1);
    let r1 = enc1.check_sat();

    // De Morgan form: forall<a> NOT(forall<b> (a => b))
    let de_morgan_form = forall_with_sort(
        "a",
        ExprSort::Bool,
        not(forall_with_sort(
            "b",
            ExprSort::Bool,
            implies(var("a"), var("b")),
        )),
    );
    let mut enc2 = AYEncoder::new_pure_with_quantifiers();
    let t2 = enc2
        .encode_pure(&de_morgan_form)
        .expect("De Morgan form encodes");
    enc2.assert_term(t2);
    let r2 = enc2.check_sat();

    assert_eq!(
        r1, r2,
        "exists-forall alternation: direct negation and De Morgan must agree"
    );
    // Pin expected result: original is Sat (a=false), so NOT(original) is Unsat.
    // Bool-sorted quantifiers allow complete case-splitting.
    assert_eq!(
        r1,
        SolveResult::unsat(),
        "NOT(exists<a:Bool> forall<b:Bool> (a => b)) should be Unsat (original is true via a=false)"
    );
}

/// Pins the behavioral asymmetry between `negate_existential_postcondition`
/// and `flatten_nested_existentials` for triggered inner existentials.
///
/// `negate_existential_postcondition` recurses through ALL nested Exists,
/// regardless of triggers. `flatten_nested_existentials` stops at triggered
/// Exists. This test verifies the De Morgan path handles
/// `exists<a> exists<b: trigger=[g(b)]> P` correctly by rewriting BOTH levels.
///
/// Since both are Bool-sorted, ay can verify equivalence directly.
///
/// Re: #1087, #1018 (trigger handling consistency audit)
#[test]
#[timeout(30000)]
fn de_morgan_nested_exists_with_triggered_inner_rewrites_both_levels() {
    // exists<a:Bool> exists<b:Bool, trigger=[g(b)]> (a AND b)
    // De Morgan should produce: forall<a:Bool> forall<b:Bool, trigger=[g(b)]> NOT(a AND b)
    let inner_exists = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(and(var("a"), var("b"))),
        triggers: vec![vec![logic_fn_call("g", vec![var("b")])]],
    };
    let original = exists_with_sort("a", ExprSort::Bool, inner_exists);

    // Expected De Morgan form (manually constructed):
    // forall<a:Bool> forall<b:Bool, trigger=[g(b)]> NOT(a AND b)
    let expected_de_morgan = forall_with_sort(
        "a",
        ExprSort::Bool,
        PureExpr::Forall {
            var: "b".to_string(),
            var_sort: Some(ExprSort::Bool),
            body: Arc::new(not(and(var("a"), var("b")))),
            triggers: vec![vec![logic_fn_call("g", vec![var("b")])]],
        },
    );

    // Verify direct negation and De Morgan form agree via ay
    let mut enc1 = AYEncoder::new_pure_with_quantifiers();
    let neg_original = not(original);
    let t1 = enc1
        .encode_pure(&neg_original)
        .expect("direct negation of triggered exists encodes");
    enc1.assert_term(t1);
    let r1 = enc1.check_sat();

    let mut enc2 = AYEncoder::new_pure_with_quantifiers();
    let t2 = enc2
        .encode_pure(&expected_de_morgan)
        .expect("De Morgan form with triggers encodes");
    enc2.assert_term(t2);
    let r2 = enc2.check_sat();

    assert_eq!(
        r1, r2,
        "triggered inner exists: direct negation and De Morgan must agree"
    );
    // Pin expected result: original is Sat (a=true, b=true), so NOT(original) is Unsat.
    // Bool-sorted quantifiers allow complete case-splitting even with triggers.
    assert_eq!(
        r1,
        SolveResult::unsat(),
        "NOT(exists<a:Bool> exists<b:Bool> (a AND b)) should be Unsat (original is true via a=b=true)"
    );
}

/// Slow path with mixed triggered and triggerless existential postconditions
/// handles both correctly — the triggerless one gets De Morgan rewrite,
/// while the triggered one gets De Morgan rewrite (since the function is
/// trigger-agnostic) plus the direct ay negation.
///
/// Re: #1087 (slow path trigger handling edge case)
#[test]
#[timeout(30000)]
fn slow_path_mixed_triggered_and_triggerless_existential_postconditions() {
    // Two postconditions:
    //   1. exists<a:Bool> a  (triggerless, tautologically satisfiable)
    //   2. exists<b:Bool, trigger=[g(b)]> b  (triggered, also tautologically satisfiable)
    // Body returns true. Both postconditions hold, so verification should succeed.
    let post1 = exists_with_sort("a", ExprSort::Bool, var("a"));
    let post2 = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(var("b")),
        triggers: vec![vec![logic_fn_call("g", vec![var("b")])]],
    };

    let requires = vec![gt(int(1), int(0))];
    let ensures = vec![post1, post2];
    let return_expr = PureExpr::Bool(true);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("mixed triggered/triggerless existentials should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "both existential postconditions are satisfiable — should verify: got {result:?}"
    );
}
