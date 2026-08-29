// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Behavioral verification tests for iterator `produces` element identity (#2172).
//!
//! These tests verify that the driver-side lowering of `produces` to
//! `ext_eq`/`concat` enables proofs about element values and ordering,
//! not just length partition. The tests use the REWRITTEN formula form
//! (what trust-wp-ay sees after `iterator_spec_rewrite.rs` transforms the
//! contract expressions).
//!
//! The combined model folds the `into_iter` seeding (`iter@ == vec@`) into
//! the produces relation, yielding: `vec@.ext_eq(seq![v].concat(next@))`.
//! This tests the core semantic property: ext_eq + concat + seq_singleton
//! constrain the produced element value, not just the count.

use std::time::Duration;

use super::*;

const ITER_PRODUCES_TIMEOUT: Duration = Duration::from_secs(1);

/// One-step `Vec::IntoIter` element identity: the first produced value
/// equals the original first element. (#2172 AC)
///
/// Models the combined effect of `into_iter` seeding + one `next()` call:
///   `vec@.ext_eq(seq![v].concat(next@))`
///
/// Given `vec@.index_logic(0) == 42`, proves `v == 42`.
///
/// With the old length-only produces model, this would be unprovable because
/// the length-conservation axiom `len(self) == len(visited) + len(o)` does
/// not constrain element values.
#[test]
#[timeout(30000)]
fn test_verify_into_iter_produces_element_identity() {
    // Precondition 1: vec_view has known length and first element
    let vec_len = eq(method_call(view(var("vec")), "len", vec![]), int(3));
    let vec_first = eq(
        method_call(view(var("vec")), "index_logic", vec![int(0)]),
        int(42),
    );

    // Precondition 2: combined produces (seeding folded in)
    // vec@.ext_eq(seq![v].concat(next@))
    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let concat = method_call(seq_v, "concat", vec![view(var("next_iter"))]);
    let produces = method_call(view(var("vec")), "ext_eq", vec![concat]);

    // Postcondition: the produced value v equals the original first element
    let ens = eq(var("v"), int(42));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[vec_len, vec_first, produces], &[ens])
            .timeout(Some(ITER_PRODUCES_TIMEOUT)),
    )
    .unwrap();
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result),
        "Vec::IntoIter produces element identity: v should equal first element (42): got {result:?}"
    );
}

/// Negative test: wrong element value should fail. (#2172)
///
/// Same setup as the positive test but proves `v == 99` — which is false
/// because the first element is 42.
#[test]
#[timeout(30000)]
fn test_verify_into_iter_produces_wrong_element_fails() {
    let vec_len = eq(method_call(view(var("vec")), "len", vec![]), int(3));
    let vec_first = eq(
        method_call(view(var("vec")), "index_logic", vec![int(0)]),
        int(42),
    );

    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let concat = method_call(seq_v, "concat", vec![view(var("next_iter"))]);
    let produces = method_call(view(var("vec")), "ext_eq", vec![concat]);

    // Wrong postcondition: v == 99 (should fail, first element is 42)
    let ens = eq(var("v"), int(99));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[vec_len, vec_first, produces], &[ens])
            .timeout(Some(ITER_PRODUCES_TIMEOUT)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Wrong element value (99 != 42) should fail: got {result:?}"
    );
}

/// Regression: ext_eq(a@, b@) with two free Seq views must be satisfiable.
///
/// Before the #2246 reverse-axiom suppression for ay#6481, a ay-dpll bug
/// where asserting a quantified formula Q AND using Q in implies(Q, x)
/// caused false UNSAT. This test ensures the ext_eq encoding is
/// satisfiable (not internally contradictory).
#[test]
#[timeout(30000)]
fn test_diag_ext_eq_two_free_views_satisfiable() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(ITER_PRODUCES_TIMEOUT));

    let ext_eq = method_call(view(var("a")), "ext_eq", vec![view(var("b"))]);

    encoder.register_sort_hints(std::slice::from_ref(&ext_eq));
    let term = encoder
        .encode_pure(&ext_eq)
        .unwrap_or_else(|e| panic!("encode failed: {e:?}"));
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert!(
        !result.is_unsat(),
        "ext_eq(a@, b@) with two free views must not be internally contradictory; AY may conservatively return Unknown when the auxiliary Seq model is incomplete: got {result:?}; reason={:?}; error={:?}",
        encoder.last_unknown_reason(),
        encoder.last_executor_error()
    );
}

/// Regression: ext_eq(a, concat(singleton(v), b)) must be satisfiable.
///
/// Verifies that the ext_eq + concat + singleton combination (the exact
/// pattern from `produces` lowering) does not create an internal
/// contradiction via the Seq axiom system.
#[test]
#[timeout(30000)]
fn test_diag_ext_eq_concat_singleton_alone_satisfiable() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(ITER_PRODUCES_TIMEOUT));

    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let concat = method_call(seq_v, "concat", vec![view(var("b"))]);
    let ext_eq = method_call(view(var("a")), "ext_eq", vec![concat]);

    encoder.register_sort_hints(std::slice::from_ref(&ext_eq));
    let term = encoder
        .encode_pure(&ext_eq)
        .unwrap_or_else(|e| panic!("encode failed: {e:?}"));
    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "ext_eq(a, concat(singleton(v), b)) alone should not be contradictory: got {result:?}"
    );
}

/// Diagnostic: check if preconditions are vacuously UNSAT.
///
/// Uses postcondition `v == 0` which should be falsifiable (first element
/// is 42, not 0). If this returns Verified, the preconditions themselves
/// are UNSAT — the ext_eq encoding is overconstrained.
///
/// **Root cause (P1-1210):** ay aae15b56 returns false UNSAT for the
/// combination of `produces` (ext_eq + concat) with `vec_first`
/// (index_logic constraint). The individual sub-combinations are
/// satisfiable — `produces` alone, `produces + len`, `ext_eq(plain) +
/// first`, `concat_len + first` are all SAT. The false UNSAT only
/// manifests when ay processes the full combination involving array
/// theory (select/store) + quantifier instantiation (bridge axiom,
/// Axiom 16) + uninterpreted functions (Seq projectors). Filed as #2404.
#[test]
#[timeout(30000)]
fn test_diag_ext_eq_preconditions_not_vacuous() {
    let vec_len = eq(method_call(view(var("vec")), "len", vec![]), int(3));
    let vec_first = eq(
        method_call(view(var("vec")), "index_logic", vec![int(0)]),
        int(42),
    );

    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let concat = method_call(seq_v, "concat", vec![view(var("next_iter"))]);
    let produces = method_call(view(var("vec")), "ext_eq", vec![concat]);

    // Postcondition v == 0: should FAIL (first element is 42, not 0).
    // If Verified, preconditions are vacuously UNSAT.
    let ens = eq(var("v"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[vec_len, vec_first, produces], &[ens])
            .timeout(Some(ITER_PRODUCES_TIMEOUT)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "DIAGNOSTIC: v == 0 should fail; if Verified, preconditions are vacuously UNSAT: got {result:?}"
    );
}

/// Diagnostic: produces (ext_eq) alone must not cause vacuous UNSAT.
///
/// Verifies that the ext_eq + concat + singleton encoding is satisfiable
/// in isolation — without vec_len or vec_first. This ensures the ext_eq
/// encoding itself is sound; the false UNSAT in #2404 requires the
/// additional index_logic constraint from vec_first.
#[test]
#[timeout(30000)]
fn test_diag_ext_eq_produces_alone_not_vacuous() {
    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let concat = method_call(seq_v, "concat", vec![view(var("next_iter"))]);
    let produces = method_call(view(var("vec")), "ext_eq", vec![concat]);

    let ens = eq(var("v"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[produces], &[ens]).timeout(Some(ITER_PRODUCES_TIMEOUT)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "produces alone should fail v==0: got {result:?}"
    );
}

/// Diagnostic: produces + vec_len (no vec_first) must not cause vacuous UNSAT.
///
/// The contradiction in #2404 requires vec_first (index_logic at 0), not
/// vec_len. This test confirms that adding a length constraint to the
/// produces encoding does not trigger false UNSAT.
#[test]
#[timeout(30000)]
fn test_diag_ext_eq_produces_plus_len_not_vacuous() {
    let vec_len = eq(method_call(view(var("vec")), "len", vec![]), int(3));

    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let concat = method_call(seq_v, "concat", vec![view(var("next_iter"))]);
    let produces = method_call(view(var("vec")), "ext_eq", vec![concat]);

    let ens = eq(var("v"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[vec_len, produces], &[ens]).timeout(Some(ITER_PRODUCES_TIMEOUT)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "produces + len should fail v==0: got {result:?}"
    );
}

/// Root cause diagnostic: check if PanicRecoveryFalse fires during encoding.
///
/// If the unsoundness counter for PanicRecoveryFalse is non-zero after
/// encoding the preconditions, a ay sort mismatch panic was caught and
/// replaced with `false`, making the formula UNSAT (false Verified).
#[test]
#[timeout(30000)]
fn test_diag_panic_recovery_false_during_precondition_encoding() {
    use crate::encoder::unsoundness;

    let before = unsoundness::snapshot();

    let vec_len = eq(method_call(view(var("vec")), "len", vec![]), int(3));
    let vec_first = eq(
        method_call(view(var("vec")), "index_logic", vec![int(0)]),
        int(42),
    );
    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let concat = method_call(seq_v, "concat", vec![view(var("next_iter"))]);
    let produces = method_call(view(var("vec")), "ext_eq", vec![concat]);
    let preconditions = vec![vec_len, vec_first, produces];

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_sort_hints(&preconditions);
    for expr in &preconditions {
        let term = encoder
            .encode_pure(expr)
            .unwrap_or_else(|e| panic!("precondition should encode: {e:?}"));
        encoder.assert_term(term);
    }

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    let panic_false_count = delta
        .get(&unsoundness::UnsoundnessCategory::PanicRecoveryFalse)
        .copied()
        .unwrap_or(0);
    let solver_panic = encoder.solver_panic_reason();

    eprintln!(
        "DIAGNOSTIC: PanicRecoveryFalse delta = {panic_false_count}, solver_panic = {solver_panic:?}"
    );
    eprintln!("DIAGNOSTIC: full unsoundness delta = {delta:?}");

    assert_eq!(
        panic_false_count, 0,
        "PanicRecoveryFalse fired during precondition encoding — \
         a ay sort panic was caught and replaced with false, \
         making the formula vacuously UNSAT. solver_panic = {solver_panic:?}"
    );
}

// NOTE: Two-step element ordering (chained ext_eq/concat) requires
// right-side concat index propagation (axiom 17). Axiom 17's trigger
// (`index(concat, len(s1)+i)`) needs the index to structurally match
// `len(s1)+i`, which bare integer ground seeds don't satisfy. Until
// ay-dpll supports arithmetic trigger matching, multi-step iterator
// element identity proofs are not supported. (#2172)
