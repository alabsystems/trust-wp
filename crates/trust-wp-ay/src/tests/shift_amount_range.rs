// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Machine-int shift-amount range safety obligations (ledger int-shift-full).
//!
//! The driver wraps the amount operand of a machine-int `<<`/`>>` in the
//! `__trust_wp_shift_amount_in_range_{bits}` marker.
//! `collect_shift_amount_range_obligation` collects `0 <= amount < bits` as a
//! proof obligation (not a solver assumption) through the same channel as the
//! `divisor != 0` obligations (#1629), so an unproven shift amount causes
//! verification failure (SAT = counterexample with an over-wide amount).
//! Mirrors `div_mod_zero.rs`.

use std::sync::Arc;

use ntest::timeout;

use super::{super::*, helpers::*};

/// Build the driver's shift-amount-in-range marker for a `bits`-wide shifted
/// operand.
fn in_range_marker(bits: u32, amount: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: format!("__trust_wp_shift_amount_in_range_{bits}"),
        args: vec![amount],
    }
}

/// `x >> amount` with the amount wrapped in the in-range marker, as the
/// driver emits for a machine-int shift.
fn shr_marked(bits: u32, value: PureExpr, amount: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(value),
        BinOp::Shr,
        Arc::new(in_range_marker(bits, amount)),
    )
}

/// At the encoding level (no postcondition negation), shift-range obligations
/// are collected but NOT asserted as solver assumptions. Setting n=8 for an
/// 8-bit shift is therefore satisfiable; the obligation is checked later by
/// the verification layer, exactly like `divisor != 0`.
#[test]
#[timeout(30000)]
fn test_shift_obligation_collected_not_assumed() {
    let mut encoder = AYEncoder::new();
    let expr = shr_marked(8, var("x"), var("n"));
    let _term = encoder
        .encode_pure(&expr)
        .expect("x >> marker(n) should encode without error");

    assert_eq!(
        encoder.division_obligations_for_test().len(),
        1,
        "a symbolic shift amount should collect exactly one range obligation"
    );

    let n = *encoder
        .vars_for_test()
        .get("n")
        .expect("n must be declared after encoding the marked shift");
    let eight = encoder.solver.int_const(8);
    let n_eq_eight = encoder.solver.eq(n, eight);
    encoder.assert_term(n_eq_eight);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "n=8 must be satisfiable at encoding level — obligation is deferred to verification"
    );
}

/// A literal amount already inside `[0, bits)` needs no obligation: the range
/// is discharged syntactically.
#[test]
#[timeout(30000)]
fn test_shift_in_range_literal_amount_collects_no_obligation() {
    let mut encoder = AYEncoder::new();
    let expr = shr_marked(8, var("x"), int(3));
    let _term = encoder
        .encode_pure(&expr)
        .expect("x >> marker(3) should encode without error");

    assert!(
        encoder.division_obligations_for_test().is_empty(),
        "an in-range literal amount must not collect a range obligation"
    );
}

/// A literal amount at/above the width still collects the (unsatisfiable)
/// obligation — the int-shift-full shape `1u8 >> 8`.
#[test]
#[timeout(30000)]
fn test_shift_over_wide_literal_amount_collects_obligation() {
    let mut encoder = AYEncoder::new();
    let expr = shr_marked(8, int(1), int(8));
    let _term = encoder
        .encode_pure(&expr)
        .expect("1 >> marker(8) should encode without error");

    assert_eq!(
        encoder.division_obligations_for_test().len(),
        1,
        "an over-wide literal amount must collect the range obligation"
    );
}

/// The obligation is path-guarded: a shift inside a dead branch does not
/// constrain the amount (mirrors the dead-branch division test).
#[test]
#[timeout(30000)]
fn test_shift_obligation_guarded_on_dead_branch() {
    let mut encoder = AYEncoder::new();
    let expr = ite(bool_expr(false), shr_marked(8, var("x"), var("n")), int(7));
    let term = encoder
        .encode_pure(&expr)
        .expect("ite(false, x >> marker(n), 7) should encode without error");

    let n = *encoder
        .vars_for_test()
        .get("n")
        .expect("n must be declared in dead-branch shift encoding");
    let eight = encoder.solver.int_const(8);
    let seven = encoder.solver.int_const(7);
    let n_eq_eight = encoder.solver.eq(n, eight);
    let term_eq_seven = encoder.solver.eq(term, seven);
    encoder.assert_term(n_eq_eight);
    encoder.assert_term(term_eq_seven);
    // Assert the collected obligations the way the verification layer would
    // conjoin them: under the false path guard they must be inert.
    let obligations = encoder.take_division_obligations();
    for obligation in obligations {
        encoder.assert_term(obligation);
    }

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "shift-range obligation must be path-guarded inside dead branches, got: {result:?}"
    );
}

/// End-to-end RED: an unconstrained symbolic amount prevents verification.
///
/// Models `#[ensures(true)] fn f(x: u8, n: u8) -> u8 {{ x >> n }}` — no
/// precondition bounds `n`, so the range obligation is unproven and the
/// verifier must return Failed with a counterexample (n >= 8).
#[test]
#[timeout(30000)]
fn test_verify_shift_unconstrained_amount_not_verified() {
    let ensures = [bool_expr(true)];
    let body = shr_marked(8, var("x"), var("n"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "shift by unconstrained n must fail with a counterexample, got: {result:?}"
    );
}

/// End-to-end RED, the exact int-shift-full shape: an over-wide LITERAL
/// amount with an EMPTY postcondition set must fail. This pins the pipeline's
/// empty-ensures path: body side obligations must be proved even when there
/// is no user postcondition (previously the empty-obligation-set shortcut
/// returned Verified without consulting them).
#[test]
#[timeout(30000)]
fn test_verify_over_wide_literal_shift_with_empty_ensures_not_verified() {
    let body = shr_marked(8, int(1), int(8));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[]).return_expr(Some(&body)));
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "1u8 >> 8 with an empty postcondition set must fail, got: {result:?}"
    );
}

/// End-to-end GREEN: preconditions pinning the amount into range verify.
///
/// Models `#[requires(n@ < 8)] fn f(x: u8, n: u8) -> u8 {{ x >> n }}` (the
/// driver additionally supplies `n >= 0` from the unsigned parameter range).
#[test]
#[timeout(30000)]
fn test_verify_shift_with_range_preconditions_succeeds() {
    let requires = [ge(var("n"), int(0)), lt(var("n"), int(8))];
    let ensures = [bool_expr(true)];
    let body = shr_marked(8, var("x"), var("n"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "shift with in-range preconditions must verify, got: {result:?}"
    );
}

/// End-to-end GREEN: an in-range literal amount with an empty postcondition
/// set keeps the historical empty-obligation-set Verified result — no
/// obligation is collected, so the trivial-goal substitution stays inert.
#[test]
#[timeout(30000)]
fn test_verify_in_range_literal_shift_with_empty_ensures_succeeds() {
    let body = shr_marked(8, var("x"), int(3));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[]).return_expr(Some(&body)));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "x >> 3 with an empty postcondition set must stay verified, got: {result:?}"
    );
}

/// GUARDED-ITE result-binding lane regression (the bits.rs `empty` false
/// counterexample): a shift living in the ELSE branch of the body ITE, with
/// the amount provably in range ONLY under the else condition, must VERIFY.
///
/// `assert_guarded_result_branch_equality` re-encodes each branch body
/// outside `encode_pure_impl`'s Ite traversal; before the path-condition
/// fix its obligation was collected UNGUARDED, so the solver "failed" the
/// range check at `n == 0` — a branch the model never takes.
#[test]
#[timeout(30000)]
fn test_verify_ite_else_branch_obligation_is_branch_guarded() {
    let requires = [ge(var("n"), int(0)), le(var("n"), int(8))];
    let ensures = [bool_expr(true)];
    // if n == 0 { 0 } else { x >> ((n - 1) as amount) } — for n in [1, 8]
    // the amount n-1 is in [0, 7]; at n == 0 the shift is never executed.
    let body = ite(
        eq(var("n"), int(0)),
        int(0),
        shr_marked(8, var("x"), sub(var("n"), int(1))),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    );
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "else-branch shift with branch-guarded in-range amount must verify, got: {result:?}"
    );
}

/// RED companion: the branch guard must not swallow the obligation — with no
/// range facts on `n`, the same else-branch shift stays unproven (n == 9
/// reaches the shift with amount 8).
#[test]
#[timeout(30000)]
fn test_verify_ite_else_branch_unguarded_amount_still_fails() {
    let ensures = [bool_expr(true)];
    let body = ite(
        eq(var("n"), int(0)),
        int(0),
        shr_marked(8, var("x"), sub(var("n"), int(1))),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "an unbounded else-branch amount must still fail, got: {result:?}"
    );
}

/// BV-SORTED amount (bitwise_proof BV encodings): the range obligation is
/// emitted NATIVELY in the BV theory — `bvult amount, bits` on the amount
/// term itself, with no Int-sort round-trip and no fresh conversion aux.
/// An in-range BV amount satisfies it; an over-wide BV amount refutes it.
#[test]
#[timeout(30000)]
fn test_bv_sorted_amount_collects_native_bv_obligation() {
    let mut encoder = AYEncoder::new();
    let vars_before = encoder.vars_for_test().len();
    let amount = encoder.solver.bv_var("bv_amount", 8);
    let returned = encoder.collect_shift_amount_range_obligation_for_test(amount, 8);
    assert_eq!(
        returned, amount,
        "the marker must stay the identity on a BV-sorted amount (no coercion)"
    );
    assert_eq!(
        encoder.vars_for_test().len(),
        vars_before,
        "no bridge/aux variable may be introduced for a BV-sorted amount"
    );

    let obligations = encoder.take_division_obligations();
    assert_eq!(
        obligations.len(),
        1,
        "a symbolic BV amount must collect exactly one range obligation"
    );
    encoder.assert_term(obligations[0]);

    // In range: amount == 3 satisfies bvult(amount, 8).
    encoder.push_scope().expect("push scope");
    let three = encoder.solver.bv_const_u64(3, 8);
    let eq_three = encoder.solver.eq(amount, three);
    encoder.assert_term(eq_three);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "an in-range BV amount must satisfy the native range check"
    );
    encoder.pop_scope().expect("pop scope");

    // Over-wide: amount == 8 refutes bvult(amount, 8). The encoder's mixed
    // Logic::All lane is not DECISIVE on this pure-BV UNSAT (it may return
    // Unknown), but it must never accept a model: Sat here would mean the
    // obligation degenerated (dropped, or bridged through an unconstrained
    // aux). The decisive over-wide REJECTION in a pure QF_BV solver is
    // pinned by `bitwise_bv_proof_general::tests::
    // marker_with_over_wide_amount_fails_natively` and the
    // `should_fail_bitwise_over_wide` fixture.
    let eight = encoder.solver.bv_const_u64(8, 8);
    let eq_eight = encoder.solver.eq(amount, eight);
    encoder.assert_term(eq_eight);
    let over_wide = encoder.check_sat();
    assert!(
        !matches!(over_wide, SolveResult::Sat),
        "an over-wide BV amount must never satisfy the native range check, got: {over_wide:?}"
    );
}

/// ASSUMPTION-position suppression (bitwalker `poke` proof_assert shape):
/// a marker inside a REQUIRES fact re-states an already-verified body path
/// (`length < 64 ==> !(value >= 1 << length)`), so it must NOT collect an
/// unguarded range obligation — the VC has to verify even though `length`
/// may legally equal the width (requires only bounds `length <= 64`).
#[test]
#[timeout(30000)]
fn test_verify_marker_in_requires_fact_collects_no_obligation() {
    let shift = PureExpr::BinOp(
        Arc::new(int(1)),
        BinOp::Shl,
        Arc::new(in_range_marker(64, var("length"))),
    );
    let requires = [
        binop(var("length"), BinOp::Le, int(64)),
        implies(lt(var("length"), int(64)), not(ge(var("value"), shift))),
    ];
    let ensures = [bool_expr(true)];
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "a shift marker inside a requires fact must not fail the VC at length == 64, got: {result:?}"
    );
}
