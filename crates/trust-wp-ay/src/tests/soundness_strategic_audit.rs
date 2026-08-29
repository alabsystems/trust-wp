// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strategic soundness audit tests — Prover iteration 506.
//!
//! Tests for soundness-critical code paths identified during strategic audit:
//!
//! 1. Custom enum constructor inner pattern drop (match_enc.rs:754,761,767)
//! 2. LetAssume dropped assumption transitive effect on caller verification
//! 3. Solver panic `bool_const(true)` fallback safety net validation
//! 4. Empty postcondition early-return-Verified path
//! 5. Unverified axiom demonstrating false verification of caller

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use super::{super::*, helpers::*};
use crate::{AYEncoder, BodyEffects};

// ── Finding: Custom enum constructor inner literal pattern silently dropped ──
//
// When `encode_pattern_condition_with_sort` encounters a Constructor pattern
// with an inner pattern for a non-Option/Result constructor, and the datatype
// selector extraction fails or the constructor is unrecognized, the code at
// match_enc.rs:754,761,767 returns `Ok(ctor_cond)` — dropping the inner
// pattern constraint entirely.
//
// Impact: `match x { MyEnum::A(42) => ... }` encodes as just `is_A(x)` without
// checking that the payload is 42.

/// Custom enum with literal inner pattern (positive case): the encoder should
/// create a native datatype and use its constructor/selector for the match.
/// After encoding, assert the scrutinee is the matching constructor and verify
/// the match produces the correct result.
#[test]
#[timeout(30000)]
fn match_custom_enum_inner_literal_positive_case() {
    let mut encoder = AYEncoder::new();

    // Let encode_pure infer the UserDefined datatype from the arm constructors.
    // match c { Red(42) => 1, _ => 0 }
    let match_result = match_expr(
        var("c"),
        vec![
            (
                Pattern::Constructor {
                    name: "Red".to_string(),
                    inner: Some(Box::new(Pattern::Literal(int(42)))),
                },
                int(1),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("Custom enum match with literal inner pattern should encode");

    // After encoding, `c` is declared as the auto-inferred datatype.
    // Construct Red(42) using the declared datatype and assert c = Red(42).
    let c_var = *encoder.vars_for_test().get("c").unwrap();
    let dt = encoder
        .decls()
        .datatypes_iter()
        .find(|d| d.constructors.iter().any(|c| c.name == "Red"))
        .cloned()
        .expect("Red datatype should be declared by encode_pure");

    let forty_two = encoder.solver.int_const(42);
    let red_42 = encoder
        .solver
        .datatype_constructor(&dt, "Red", &[forty_two]);
    let eq_red_42 = encoder.solver.eq(c_var, red_42);
    encoder.solver.assert_term(eq_red_42);

    // match should return 1 when c = Red(42). Assert NOT 1 → UNSAT.
    let one = encoder.solver.int_const(1);
    let eq_one = encoder.solver.eq(match_term, one);
    let neq_one = encoder.solver.not(eq_one);
    encoder.solver.assert_term(neq_one);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Red(42) vs Red(42) should return 1 (UNSAT expected), got: {result:?}"
    );
}

/// CRITICAL SOUNDNESS TEST: Custom enum inner literal must REJECT non-matching values.
///
/// If match_enc.rs drops the inner literal (42), then Red(99) would incorrectly
/// match the `Red(42)` arm. This directly tests the gap at match_enc.rs:754,761,767.
#[test]
#[timeout(30000)]
fn match_custom_enum_inner_literal_rejects_wrong_value() {
    let mut encoder = AYEncoder::new();

    // match c { Red(42) => 1, _ => 0 }
    let match_result = match_expr(
        var("c"),
        vec![
            (
                Pattern::Constructor {
                    name: "Red".to_string(),
                    inner: Some(Box::new(Pattern::Literal(int(42)))),
                },
                int(1),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("Custom enum match should encode");

    // Construct Red(99) and assert c = Red(99)
    let c_var = *encoder.vars_for_test().get("c").unwrap();
    let dt = encoder
        .decls()
        .datatypes_iter()
        .find(|d| d.constructors.iter().any(|c| c.name == "Red"))
        .cloned()
        .expect("Red datatype should be declared");

    let ninety_nine = encoder.solver.int_const(99);
    let red_99 = encoder
        .solver
        .datatype_constructor(&dt, "Red", &[ninety_nine]);
    let eq_red_99 = encoder.solver.eq(c_var, red_99);
    encoder.solver.assert_term(eq_red_99);

    // c = Red(99), pattern is Red(42). Should fall through to wildcard → 0.
    // Assert match == 1 → should be UNSAT if inner literal is checked.
    // If inner literal is dropped (bug), is_Red(Red(99)) is true, match returns 1 → SAT.
    let one = encoder.solver.int_const(1);
    let eq_one = encoder.solver.eq(match_term, one);
    encoder.solver.assert_term(eq_one);

    let result = encoder.check_sat();
    match result {
        SolveResult::Unsat(_) => {
            // CORRECT: Red(99) did NOT match Red(42), fell through to wildcard (0).
        }
        SolveResult::Sat => {
            panic!(
                "SOUNDNESS BUG: Red(99) matched pattern Red(42) — inner literal constraint \
                 was silently dropped by match_enc.rs fallback (lines 754/761/767). \
                 The verifier would accept incorrect programs."
            );
        }
        SolveResult::Unknown => {
            panic!(
                "INCONCLUSIVE: solver returned Unknown for Red(99) vs Red(42) match. \
                 The encoding may be incomplete for custom enum literal patterns."
            );
        }
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// Custom enum constructor with binding inner pattern — payload must be
/// correctly extracted, not left unconstrained.
#[test]
#[timeout(30000)]
fn match_custom_enum_binding_extracts_payload() {
    let mut encoder = AYEncoder::new();

    // match w { Wrap(x) => x, Empty => 0 }
    let match_result = match_expr(
        var("w"),
        vec![
            (
                Pattern::Constructor {
                    name: "Wrap".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".into()))),
                },
                var("x"),
            ),
            (
                Pattern::Constructor {
                    name: "Empty".to_string(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("Custom enum match with binding should encode");

    // Construct Wrap(10) and assert w = Wrap(10)
    let w_var = *encoder.vars_for_test().get("w").unwrap();
    let dt = encoder
        .decls()
        .datatypes_iter()
        .find(|d| d.constructors.iter().any(|c| c.name == "Wrap"))
        .cloned()
        .expect("Wrap datatype should be declared");

    let ten = encoder.solver.int_const(10);
    let wrap_10 = encoder.solver.datatype_constructor(&dt, "Wrap", &[ten]);
    let eq_wrap = encoder.solver.eq(w_var, wrap_10);
    encoder.solver.assert_term(eq_wrap);

    // w = Wrap(10). Result should be 10. Assert != 10 → UNSAT.
    let ten_term = encoder.solver.int_const(10);
    let eq_ten = encoder.solver.eq(match_term, ten_term);
    let neq_ten = encoder.solver.not(eq_ten);
    encoder.solver.assert_term(neq_ten);

    let result = encoder.check_sat();
    match result {
        SolveResult::Unsat(_) => {
            // Correct: x is bound to the payload selector of Wrap, which is 10.
        }
        SolveResult::Sat => {
            panic!(
                "SOUNDNESS BUG: Wrap(x) => x did not bind x to payload. \
                 x was unconstrained, allowing solver to pick x != 10."
            );
        }
        SolveResult::Unknown => {
            panic!("INCONCLUSIVE: solver returned Unknown for Wrap(x) => x payload binding.");
        }
        _ => panic!("unexpected SolveResult variant"),
    }
}

// ── Finding: LetAssume transitive soundness ──
//
// When a callee postcondition cannot be encoded (LetAssume error path at
// pure_encoding.rs:738-751), the assumption is dropped. The claim is that
// this is sound (weakens proof context). This test validates the mechanism:
// without callee assumption, caller postcondition is NOT trivially verified.

/// Without a callee assumption `result > 0`, the caller postcondition
/// `output > 0` (where output = result + 1) should NOT verify because
/// result is unconstrained.
#[test]
#[timeout(30000)]
fn unconstrained_callee_result_does_not_trivially_verify_caller() {
    let mut encoder = AYEncoder::new();

    let result_var = encoder.get_or_declare_var("result", Sort::Int).unwrap();
    let one = encoder.solver.int_const(1);
    let output = encoder.solver.add(result_var, one);

    // Negated postcondition: NOT(output > 0)
    let zero = encoder.solver.int_const(0);
    let output_gt_0 = encoder.solver.gt(output, zero);
    let neg_post = encoder.solver.not(output_gt_0);
    encoder.solver.assert_term(neg_post);

    // Without callee assumption, should find counterexample (result = -2)
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Without callee assumption, postcondition should be refutable (SAT), got: {result:?}"
    );
}

/// With the callee assumption `result > 0`, the postcondition `output > 0`
/// (where output = result + 1) should verify.
#[test]
#[timeout(30000)]
fn callee_assumption_enables_caller_verification() {
    let mut encoder = AYEncoder::new();

    let result_var = encoder.get_or_declare_var("result", Sort::Int).unwrap();
    let one = encoder.solver.int_const(1);
    let output = encoder.solver.add(result_var, one);
    let zero = encoder.solver.int_const(0);

    // Callee assumption: result > 0
    let result_gt_0 = encoder.solver.gt(result_var, zero);
    encoder.solver.assert_term(result_gt_0);

    // Negated postcondition: NOT(output > 0)
    let output_gt_0 = encoder.solver.gt(output, zero);
    let neg_post = encoder.solver.not(output_gt_0);
    encoder.solver.assert_term(neg_post);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "With callee assumption result>0, postcondition output>0 should verify (UNSAT), \
         got: {result:?}"
    );
}

// ── Finding: Solver panic safety net ──
//
// When assert_term panics (e.g., non-Bool assertion), the panic is caught
// and solver_panic_reason is set. check_sat must return Unknown.

/// After forcing a solver panic via non-Bool assertion, check_sat must
/// return Unknown (not Sat/Unsat).
#[test]
#[timeout(30000)]
fn solver_panic_via_assert_forces_unknown_check_sat() {
    let mut encoder = AYEncoder::new();

    // Establish valid state first
    let valid = encoder.encode_pure(&PureExpr::Bool(true)).unwrap();
    encoder.assert_term(valid);

    // Force panic: assert an Int term (not Bool)
    let non_bool = encoder.solver_mut().int_const(42);
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encoder.assert_term(non_bool);
    }));

    // Verify the panic was recorded
    assert!(
        encoder.solver_panic_reason().is_some(),
        "solver_panic_reason must be set after asserting non-Bool term"
    );

    // check_sat must return Unknown — this is the safety net
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unknown),
        "check_sat after solver panic must return Unknown, got: {result:?}"
    );
}

// ── Finding: Unverified axiom false verification ──
//
// A false axiom makes the proof context inconsistent. Before the vacuity
// guard (#2414), ANY postcondition would silently verify (ex falso).
// Now the vacuity guard detects this and demotes to Unknown.

/// A contradictory precondition (x > 0 AND x < 0) is caught by the
/// vacuity guard (#2414) — the negated postcondition is not in the unsat
/// core because the preconditions alone are already UNSAT.
#[test]
#[timeout(30000)]
fn false_precondition_caught_by_vacuity_guard() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // requires: x > 0 AND x < 0 (contradictory)
    // ensures: result == 999 (nonsensical)
    let requires = vec![binop(
        gt(var("x"), int(0)),
        BinOp::And,
        lt(var("x"), int(0)),
    )];
    let ensures = vec![eq(var("result"), int(999))];

    let result = verify_function_with_modes(VerificationRequest::new(&requires, &ensures));
    assert!(
        matches!(result, Ok(VerificationResult::Unknown(..))),
        "Contradictory precondition should be caught by vacuity guard (#2414), got: {result:?}"
    );
    // Verify the message mentions vacuity specifically
    if let Ok(VerificationResult::Unknown(reason)) = &result {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("vacuous"),
            "Unknown reason should mention vacuity, got: {msg}"
        );
    }
}

// ── Finding: Empty postcondition early-return-Verified ──

/// A function with no postconditions is verified by an accepted literal-false
/// solver proof for the negated empty obligation.
#[test]
#[timeout(30000)]
fn empty_postcondition_is_vacuously_verified() {
    use crate::{
        verify_function_with_modes, verify_function_with_modes_outcome, VerificationRequest,
        VerificationResult,
    };

    let requires: Vec<PureExpr> = vec![PureExpr::Bool(true)];
    let ensures: Vec<PureExpr> = vec![];
    let request = VerificationRequest::new(&requires, &ensures);

    let outcome = verify_function_with_modes_outcome(request.clone())
        .expect("empty postcondition outcome should encode");
    let evidence = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .expect("empty postcondition should carry solver evidence");
    assert!(
        evidence.accepted_for_consumer,
        "empty postcondition proof should be accepted solver evidence: {evidence:?}"
    );
    assert!(
        evidence.result.eq_ignore_ascii_case("unsat") || evidence.result.starts_with("Unsat"),
        "empty postcondition evidence should be UNSAT, got {}",
        evidence.result
    );

    let result = verify_function_with_modes(request);
    match result {
        Ok(VerificationResult::Verified(_)) => {
            // Accepted solver evidence above is the soundness gate for the
            // legacy clean result.
        }
        other => {
            panic!("Function with no postconditions should verify with evidence, got: {other:?}")
        }
    }
}

/// A function with no postconditions and a false precondition is still
/// rejected as vacuous: requires(false) must never verify.
#[test]
#[timeout(30000)]
fn empty_postcondition_with_false_precondition_is_vacuous_unknown() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let requires: Vec<PureExpr> = vec![PureExpr::Bool(false)]; // unsatisfiable
    let ensures: Vec<PureExpr> = vec![];

    let result = verify_function_with_modes(VerificationRequest::new(&requires, &ensures));
    match result {
        Ok(VerificationResult::Unknown(reason)) if reason.as_str().contains("vacuous") => {}
        other => panic!(
            "Empty postcondition with false precondition should be Unknown(vacuous), got: {other:?}"
        ),
    }
}

// ── Regression test for #1681: UF fallback inner pattern encoding ──
//
// When the UF fallback path is taken (no native datatype), custom constructor
// patterns like `Foo(42)` must still check the inner literal against the
// payload, not just test `is_foo(x)`. Pre-declaring the scrutinee as Sort::Int
// forces the UF fallback (scrutinee_has_conflicting_sort returns true).

/// UF fallback: `Red(42)` must reject `Red(99)` even without native DT selectors.
///
/// Before #1681, the fallback at match_enc.rs:767 returned `Ok(ctor_cond)` for
/// non-Option/Result constructors, encoding `Red(42)` as just `is_red(c)` and
/// silently dropping the `== 42` inner literal constraint. This allowed Red(99)
/// to incorrectly match the `Red(42)` arm.
#[test]
#[timeout(30000)]
fn uf_fallback_custom_constructor_inner_literal_rejects_wrong_value() {
    let mut encoder = AYEncoder::new();

    // Pre-declare `c` as Sort::Int to force UF fallback path.
    // This triggers scrutinee_has_conflicting_sort → datatype = None.
    let c_term = encoder
        .get_or_declare_var("c", Sort::Int)
        .expect("should declare c as Int");

    // match c { Red(42) => 1, _ => 0 }
    let match_result = match_expr(
        var("c"),
        vec![
            (
                Pattern::Constructor {
                    name: "Red".to_string(),
                    inner: Some(Box::new(Pattern::Literal(int(42)))),
                },
                int(1),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("Custom enum UF fallback match should encode");

    // Assert is_red(c) — the constructor tester should be true.
    // Then assert payload_red(c) == 99 — the inner value is NOT 42.
    let is_red = encoder
        .decls()
        .get_spec_func("is_red")
        .cloned()
        .expect("is_red tester should be declared by UF fallback path");
    let is_red_c = encoder.solver.apply(&is_red, &[c_term]);
    encoder.solver.assert_term(is_red_c);

    let payload_red = encoder
        .decls()
        .get_spec_func("payload_red")
        .cloned()
        .expect("payload_red accessor should be declared by #1681 fix");
    let ninety_nine = encoder.solver.int_const(99);
    let payload_red_applied = encoder.solver.apply(&payload_red, &[c_term]);
    let payload_eq_99 = encoder.solver.eq(payload_red_applied, ninety_nine);
    encoder.solver.assert_term(payload_eq_99);

    // c is Red with payload 99. Pattern is Red(42). Should fall through
    // to wildcard → result is 0. Assert match == 1 → should be UNSAT.
    let one = encoder.solver.int_const(1);
    let eq_one = encoder.solver.eq(match_term, one);
    encoder.solver.assert_term(eq_one);

    let result = encoder.check_sat();
    match result {
        SolveResult::Unsat(_) => {
            // CORRECT: Red(99) did NOT match Red(42) on UF fallback path.
        }
        SolveResult::Sat => {
            panic!(
                "SOUNDNESS BUG (#1681): UF fallback path dropped inner literal constraint. \
                 Red(99) matched pattern Red(42) — payload_red accessor was not checked."
            );
        }
        SolveResult::Unknown => {
            panic!(
                "INCONCLUSIVE: solver returned Unknown for UF fallback Red(99) vs Red(42). \
                 The UF encoding may be incomplete."
            );
        }
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// UF fallback positive case: `Red(42)` with payload exactly 42 should match the
/// `Red(42)` arm on the UF path.
///
/// Dual of `uf_fallback_custom_constructor_inner_literal_rejects_wrong_value`.
/// Together, these two tests prove the UF fallback encoding is complete for
/// inner literal patterns: it accepts exact matches and rejects mismatches.
#[test]
#[timeout(30000)]
fn uf_fallback_custom_constructor_inner_literal_accepts_correct_value() {
    let mut encoder = AYEncoder::new();

    // Pre-declare `c` as Sort::Int to force UF fallback path.
    let c_term = encoder
        .get_or_declare_var("c", Sort::Int)
        .expect("should declare c as Int");

    // match c { Red(42) => 1, _ => 0 }
    let match_result = match_expr(
        var("c"),
        vec![
            (
                Pattern::Constructor {
                    name: "Red".to_string(),
                    inner: Some(Box::new(Pattern::Literal(int(42)))),
                },
                int(1),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("Custom enum UF fallback match should encode");

    // Assert is_red(c) AND payload_red(c) == 42 — the correct value.
    let is_red = encoder
        .decls()
        .get_spec_func("is_red")
        .cloned()
        .expect("is_red tester should be declared");
    let is_red_c = encoder.solver.apply(&is_red, &[c_term]);
    encoder.solver.assert_term(is_red_c);

    let payload_red = encoder
        .decls()
        .get_spec_func("payload_red")
        .cloned()
        .expect("payload_red accessor should be declared");
    let forty_two = encoder.solver.int_const(42);
    let payload_red_applied = encoder.solver.apply(&payload_red, &[c_term]);
    let payload_eq_42 = encoder.solver.eq(payload_red_applied, forty_two);
    encoder.solver.assert_term(payload_eq_42);

    // c is Red with payload 42. Pattern is Red(42). Should take the first arm
    // → result is 1. Assert match != 1 → should be UNSAT.
    let one = encoder.solver.int_const(1);
    let eq_one = encoder.solver.eq(match_term, one);
    let neq_one = encoder.solver.not(eq_one);
    encoder.solver.assert_term(neq_one);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "UF fallback positive case: Red(42) should match Red(42) pattern arm (expected UNSAT for != 1), got: {result:?}"
    );
}

/// UF fallback binding: `Wrap(x) => x` must extract the payload through
/// the generic UF accessor, not a fresh unconstrained variable.
///
/// Forces UF path by pre-declaring the scrutinee as Sort::Int, then
/// verifies that the binding variable `x` is constrained to equal
/// `payload_wrap(w)`, not left free.
#[test]
#[timeout(30000)]
fn uf_fallback_custom_constructor_binding_extracts_payload() {
    let mut encoder = AYEncoder::new();

    // Pre-declare `w` as Sort::Int to force UF fallback path.
    let w_term = encoder
        .get_or_declare_var("w", Sort::Int)
        .expect("should declare w as Int");

    // match w { Wrap(x) => x, _ => 0 }
    let match_result = match_expr(
        var("w"),
        vec![
            (
                Pattern::Constructor {
                    name: "Wrap".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".into()))),
                },
                var("x"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("UF fallback match with binding should encode");

    // Assert is_wrap(w) — we're in the Wrap branch.
    let is_wrap = encoder
        .decls()
        .get_spec_func("is_wrap")
        .cloned()
        .expect("is_wrap tester should be declared");
    let is_wrap_w = encoder.solver.apply(&is_wrap, &[w_term]);
    encoder.solver.assert_term(is_wrap_w);

    // Assert payload_wrap(w) == 10.
    let payload_wrap = encoder
        .decls()
        .get_spec_func("payload_wrap")
        .cloned()
        .expect("payload_wrap accessor should be declared by #1681 fix");
    let ten = encoder.solver.int_const(10);
    let payload_applied = encoder.solver.apply(&payload_wrap, &[w_term]);
    let payload_eq_10 = encoder.solver.eq(payload_applied, ten);
    encoder.solver.assert_term(payload_eq_10);

    // w is Wrap with payload 10. Wrap(x) => x should yield 10.
    // Assert match != 10 → should be UNSAT (if binding is correctly constrained).
    let match_eq_10 = encoder.solver.eq(match_term, ten);
    let match_neq_10 = encoder.solver.not(match_eq_10);
    encoder.solver.assert_term(match_neq_10);

    let result = encoder.check_sat();
    match result {
        SolveResult::Unsat(_) => {
            // CORRECT: UF fallback binding extracted payload correctly.
        }
        SolveResult::Sat => {
            panic!(
                "SOUNDNESS BUG: UF fallback binding did not constrain x to payload_wrap(w). \
                 Expected match == 10 when payload_wrap(w) == 10, but solver found a model \
                 where match != 10."
            );
        }
        SolveResult::Unknown => {
            panic!(
                "INCONCLUSIVE: solver returned Unknown for UF fallback binding. \
                 The payload accessor must connect to the binding variable strictly."
            );
        }
        _ => panic!("unexpected SolveResult variant"),
    }
}

/// UF fallback multi-arm: each constructor arm has its own inner literal.
///
/// Tests that the UF encoding correctly distinguishes between different
/// constructors with different payload values. Specifically:
///   match c { Red(42) => 1, Blue(7) => 2, _ => 0 }
/// with c = Blue(7), the result must be 2 (not 1, not 0).
///
/// This exercises that each constructor's `payload_<name>` UF accessor is
/// independent — `payload_red(c)` and `payload_blue(c)` are separate functions.
#[test]
#[timeout(30000)]
fn uf_fallback_multi_constructor_arms_discriminate_correctly() {
    let mut encoder = AYEncoder::new();

    // Pre-declare `c` as Sort::Int to force UF fallback path.
    let c_term = encoder
        .get_or_declare_var("c", Sort::Int)
        .expect("should declare c as Int");

    // match c { Red(42) => 1, Blue(7) => 2, _ => 0 }
    let match_result = match_expr(
        var("c"),
        vec![
            (
                Pattern::Constructor {
                    name: "Red".to_string(),
                    inner: Some(Box::new(Pattern::Literal(int(42)))),
                },
                int(1),
            ),
            (
                Pattern::Constructor {
                    name: "Blue".to_string(),
                    inner: Some(Box::new(Pattern::Literal(int(7)))),
                },
                int(2),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("Multi-arm UF fallback match should encode");

    // Assert c is Blue with payload 7: is_blue(c) AND payload_blue(c) == 7.
    let is_blue = encoder
        .decls()
        .get_spec_func("is_blue")
        .cloned()
        .expect("is_blue tester should be declared");
    let is_blue_c = encoder.solver.apply(&is_blue, &[c_term]);
    encoder.solver.assert_term(is_blue_c);

    let payload_blue = encoder
        .decls()
        .get_spec_func("payload_blue")
        .cloned()
        .expect("payload_blue accessor should be declared");
    let seven = encoder.solver.int_const(7);
    let payload_blue_c = encoder.solver.apply(&payload_blue, &[c_term]);
    let payload_eq_7 = encoder.solver.eq(payload_blue_c, seven);
    encoder.solver.assert_term(payload_eq_7);

    // Also assert NOT is_red(c) to disambiguate UF testers.
    let is_red = encoder
        .decls()
        .get_spec_func("is_red")
        .cloned()
        .expect("is_red tester should be declared");
    let is_red_c = encoder.solver.apply(&is_red, &[c_term]);
    let not_red = encoder.solver.not(is_red_c);
    encoder.solver.assert_term(not_red);

    // c is Blue(7). Should match the second arm → result is 2.
    // Assert match != 2 → should be UNSAT.
    let two = encoder.solver.int_const(2);
    let eq_two = encoder.solver.eq(match_term, two);
    let neq_two = encoder.solver.not(eq_two);
    encoder.solver.assert_term(neq_two);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "UF fallback multi-arm: Blue(7) should match Blue(7) arm (result 2), got: {result:?}"
    );
}

/// UF fallback: mismatched constructor with correct payload must NOT match.
///
/// Verifies that `is_red` and `is_blue` are independent testers:
///   match c { Red(42) => 1, _ => 0 }
/// with c satisfying `is_blue(c)` AND `payload_blue(c) == 42`.
/// The payload value matches but the constructor doesn't → wildcard arm → 0.
#[test]
#[timeout(30000)]
fn uf_fallback_wrong_constructor_with_matching_payload_rejects() {
    let mut encoder = AYEncoder::new();

    // Pre-declare `c` as Sort::Int to force UF fallback path.
    let c_term = encoder
        .get_or_declare_var("c", Sort::Int)
        .expect("should declare c as Int");

    // match c { Red(42) => 1, _ => 0 }
    let match_result = match_expr(
        var("c"),
        vec![
            (
                Pattern::Constructor {
                    name: "Red".to_string(),
                    inner: Some(Box::new(Pattern::Literal(int(42)))),
                },
                int(1),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let match_term = encoder
        .encode_pure(&match_result)
        .expect("UF fallback match should encode");

    // Assert c is Blue (wrong constructor), but payload coincidentally matches.
    // First declare Blue as a constructor too (via a separate match encoding).
    let blue_match = match_expr(
        var("c"),
        vec![
            (
                Pattern::Constructor {
                    name: "Blue".to_string(),
                    inner: Some(Box::new(Pattern::Literal(int(0)))),
                },
                int(99),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );
    // Encoding this match creates the is_blue and payload_blue UFs.
    let _ = encoder.encode_pure(&blue_match);

    // Assert is_blue(c) AND NOT is_red(c).
    let is_blue = encoder
        .decls()
        .get_spec_func("is_blue")
        .cloned()
        .expect("is_blue should exist");
    let is_red = encoder
        .decls()
        .get_spec_func("is_red")
        .cloned()
        .expect("is_red should exist");
    let is_blue_term = encoder.solver.apply(&is_blue, &[c_term]);
    encoder.solver.assert_term(is_blue_term);
    let is_red_term = encoder.solver.apply(&is_red, &[c_term]);
    let not_red = encoder.solver.not(is_red_term);
    encoder.solver.assert_term(not_red);

    // c is Blue, not Red. The Red(42) arm should not match → wildcard → 0.
    // Assert match == 1 → should be UNSAT.
    let one = encoder.solver.int_const(1);
    let eq_one = encoder.solver.eq(match_term, one);
    encoder.solver.assert_term(eq_one);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "UF fallback: Blue value should NOT match Red(42) arm even if payloads share a value, got: {result:?}"
    );
}

// ── Regression: Loop preservation vacuity guard ──
//
// The function/mut-borrow verification paths use a two-phase vacuity guard
// (solver_tail.rs:142-156): after inner-scope UNSAT, pop the negated
// postcondition and re-solve the base context. If the base alone is UNSAT,
// the proof was vacuous and the result is demoted to Unknown.
//
// #2440 extends the same two-phase pattern to loop verification. This test
// keeps the contradictory-invariant regression pinned so preservation cannot
// silently return a vacuous Verified again.

/// Loop preservation with contradictory invariants must NOT return Verified.
///
/// invariant: `x > 0 AND x < 0` (contradictory)
/// body_effect: `x_next = x + 1` (irrelevant — base is UNSAT)
///
/// The vacuity guard (#2440) detects that the base assertions are UNSAT
/// without the negated postcondition and demotes to Unknown(vacuous).
#[test]
#[timeout(30000)]
fn loop_preservation_contradictory_invariant_vacuity_gap() {
    use std::collections::HashMap;

    use crate::{verify_loop_invariant, LoopVerificationContext, VerificationResult};

    // x > 0 AND x < 0 — contradictory, makes the base context UNSAT
    let contradictory_invariant = binop(gt(var("x"), int(0)), BinOp::And, lt(var("x"), int(0)));
    let invariants = vec![contradictory_invariant];
    let loop_condition = PureExpr::Bool(true);
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), binop(var("x"), BinOp::Add, int(1)));
    let empty_effect = HashMap::new();
    let pre_loop = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &[], // requires
        &[], // ensures
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_effect, &empty_effect),
        &pre_loop,
    )
    .with_loop_condition(&loop_condition);

    let result = verify_loop_invariant(&ctx).expect("loop encoding should not hard-error");

    // Vacuity guard (#2440): contradictory invariants are detected by
    // re-solving the per-slice base after popping only the negated goal scope.
    assert!(
        matches!(result.preservation, VerificationResult::Unknown(..)),
        "Contradictory invariants should produce Unknown(vacuous) in loop preservation \
         (#2440 vacuity guard). Got: {:?}",
        result.preservation
    );
    // Verify the message mentions vacuity specifically.
    if let VerificationResult::Unknown(reason) = &result.preservation {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("vacuous"),
            "Unknown reason should mention vacuity, got: {msg}"
        );
    }
}
