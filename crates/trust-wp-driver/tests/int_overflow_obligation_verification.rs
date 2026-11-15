// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for machine-integer arithmetic panic obligations.
//!
//! Creusot compiles with `-Coverflow-checks=off` and models `+ - *`, signed
//! negation, `/` and `%` as prelude PROGRAM functions whose preconditions are
//! the overflow / division goals (`prelude-generator/int.in.coma`). Each RED
//! fixture below would verify (or never be examined) if those goals were not
//! trust-wp obligations (D-18); each GREEN fixture discharges them.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/int_overflow_obligation_tests");
    nested_cargo("check")
        .current_dir(fixture_dir("int_overflow_obligation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        // Verify the fixture crate only (the driver's primary-package mode):
        // the `trust-wp-std` dependency is not under test here.
        .env("CARGO_TRUST_WP", "1")
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for int_overflow_obligation fixture")
}

fn assert_fails(bin: &str, failing_fn: &str, obligation_fragment: &str) {
    let output = run_fixture(bin);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "expected verification failure for {bin}; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    // A refutation whose evidence is not a validated counterexample model is
    // reported as `unknown (refutation withheld: ...)` rather than `FAILED`
    // (D-28). The run is still a rejection — it exits non-zero and counts
    // the item under `errors` — so both spellings satisfy this test.
    assert!(
        stderr.contains(&format!("{failing_fn} FAILED"))
            || (stderr.contains(&format!("{failing_fn} unknown"))
                && stderr.contains("refutation withheld")),
        "expected {failing_fn} to fail or to withhold its refutation; stderr: {stderr}",
    );
    // When a refutation is withheld (D-28) the reason is inserted INSIDE the
    // parenthesised qualifier — `(loop call obligations: refutation withheld:
    // ...)` — so a fragment written with its closing paren does not match.
    // Accept the open form too.
    let obligation_open = obligation_fragment
        .strip_suffix(')')
        .unwrap_or(obligation_fragment);
    assert!(
        stderr.contains(obligation_fragment) || stderr.contains(obligation_open),
        "expected {failing_fn} to fail on the arithmetic obligation `{obligation_fragment}`; \
         stderr: {stderr}",
    );
}

/// Like [`assert_fails`] for a closure of `parent`: the closure's index is
/// not part of the claim (spec type-checking expansions add closures to the
/// parent body), only that a closure of `parent` fails on the obligation.
fn assert_closure_fails(bin: &str, parent: &str, obligation_fragment: &str) {
    let output = run_fixture(bin);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "expected verification failure for {bin}; stderr: {stderr}",
    );
    let prefix = format!("trust-wp: {parent}::{{closure#");
    let mut lines = stderr.lines().peekable();
    let mut found = false;
    while let Some(line) = lines.next() {
        if line.starts_with(&prefix) && line.contains("FAILED") {
            let mut block = String::new();
            while let Some(next) = lines.peek() {
                if next.starts_with("trust-wp: ") {
                    break;
                }
                block.push_str(lines.next().unwrap_or_default());
                block.push('\n');
            }
            if block.contains(obligation_fragment) {
                found = true;
            }
        }
    }
    assert!(
        found,
        "expected a closure of {parent} to fail on `{obligation_fragment}`; stderr: {stderr}",
    );
}

/// A panicking program must never be reported `verified`, whether the
/// verdict is FAILED or an inconclusive `unknown`.
fn assert_not_verified(bin: &str, function: &str) -> String {
    let output = run_fixture(bin);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        !output.status.success(),
        "expected {bin} not to verify; stderr: {stderr}",
    );
    assert!(
        !stderr.contains(&format!("{function} verified")),
        "{function} must not be reported verified; stderr: {stderr}",
    );
    assert!(
        stderr.contains(&format!("trust-wp: {function} FAILED"))
            || stderr.contains(&format!("trust-wp: {function} unknown")),
        "expected a FAILED or unknown verdict for {function}; stderr: {stderr}",
    );
    stderr
}

fn assert_verifies(bin: &str, expected_verified: usize) {
    let output = run_fixture(bin);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "expected {bin} to verify; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    assert!(
        stderr.contains(&format!("{expected_verified} verified, 0 failed, 0 errors")),
        "expected {expected_verified} verified functions for {bin}; stderr: {stderr}",
    );
}

#[test]
#[timeout(240_000)]
fn unsigned_add_overflow_should_fail() {
    assert_fails("should_fail_add_u8", "add_one", "((x + 1) <= 255)");
}

#[test]
#[timeout(240_000)]
fn signed_sub_overflow_should_fail() {
    assert_fails("should_fail_sub_i8", "dec", "(-128 <= (x - 1))");
}

#[test]
#[timeout(240_000)]
fn unsigned_mul_overflow_should_fail() {
    assert_fails("should_fail_mul_u8", "dbl", "((x * 2) <= 255)");
}

#[test]
#[timeout(240_000)]
fn signed_negation_overflow_should_fail() {
    assert_fails("should_fail_neg_i8", "negate", "(x != -128)");
}

#[test]
#[timeout(240_000)]
fn signed_division_min_by_minus_one_should_fail() {
    assert_fails(
        "should_fail_div_signed",
        "quot",
        "!((a == -128) && (b == -1))",
    );
}

#[test]
#[timeout(240_000)]
fn division_by_zero_should_fail() {
    assert_fails("should_fail_div_zero", "quot0", "(b != 0)");
}

/// The MIR `Assert(DivisionByZero)` owes `b != 0` at its OWN program point,
/// not only where the quotient reaches the goal.
///
/// `should_fail_div_zero` returns the quotient, so trust-wp-ay's independent
/// encoder-side divisor obligation refutes it as well; it therefore does not
/// gate the driver-side lane. Discarding the quotient leaves the assert's own
/// obligation as the only thing that can reject the program (D-18).
#[test]
#[timeout(240_000)]
fn division_by_zero_with_discarded_quotient_should_fail() {
    assert_fails(
        "should_fail_div_zero_discarded",
        "quot0_discarded",
        "(b != 0)",
    );
}

/// The `%` twin of [`division_by_zero_with_discarded_quotient_should_fail`]:
/// `Assert(RemainderByZero)` owes the same `b != 0`.
#[test]
#[timeout(240_000)]
fn remainder_by_zero_with_discarded_remainder_should_fail() {
    assert_fails(
        "should_fail_rem_zero_discarded",
        "rem0_discarded",
        "(b != 0)",
    );
}

#[test]
#[timeout(240_000)]
fn unbounded_loop_counter_should_fail() {
    assert_fails("should_fail_loop_unbounded", "count", "j");
}

#[test]
#[timeout(240_000)]
fn inline_const_overflow_should_fail() {
    assert_fails(
        "should_fail_inline_const",
        "succ_const",
        "((N + 1) <= 4294967295)",
    );
}

#[test]
#[timeout(240_000)]
fn contract_free_inline_const_overflow_should_fail() {
    assert_fails(
        "should_fail_inline_const_contractless",
        "f",
        "((N + 1) <= 4294967295)",
    );
}

#[test]
#[timeout(240_000)]
fn contract_free_add_overflow_should_fail() {
    assert_fails(
        "should_fail_contractless_add",
        "bump",
        "((x + 1) <= 4294967295)",
    );
}

#[test]
#[timeout(240_000)]
fn post_loop_add_without_invariant_should_fail() {
    assert_fails("should_fail_post_loop_stale", "after_loop", "<=");
}

#[test]
#[timeout(240_000)]
fn reassigned_param_before_annotated_loop_should_fail() {
    assert_fails(
        "should_fail_param_reassigned",
        "shifted",
        "(loop call obligations)",
    );
}

#[test]
#[timeout(240_000)]
fn write_through_mut_ref_then_add_should_fail() {
    // `v + 1` reads `v` after `*r = y` stored through a local `&mut`. That
    // lane binds `v` to the pointee's ENTRY value, so since 4be31657 a
    // returned read of it pushes a fail-closed `false` instead of the stale
    // `0` this fixture was written against, and a refutation over a goal set
    // carrying that marker is withheld (D-27). What the fixture guards is
    // that the obligation is never discharged from `v == 0`: `through_ref` is
    // not verified, and the withheld reason names the marker. When the
    // return lane models the store, the refutation on `v + 1 <= 255`
    // (`y == 255`) is what this test must see again, through `assert_fails`.
    let output = run_fixture("should_fail_mut_ref_write");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "expected verification failure; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("through_ref verified"),
        "the obligation over the stored value must not be discharged; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "through_ref unknown (refutation withheld: goal set carries a fail-closed `false`"
        ),
        "expected the return lane's fail-closed marker to withhold the refutation; \
         stderr: {stderr}"
    );
}

#[test]
#[timeout(240_000)]
fn guarded_arithmetic_should_verify() {
    assert_verifies("should_verify", 9);
}

#[test]
#[timeout(240_000)]
fn bounded_loop_counter_should_verify() {
    assert_verifies("should_verify_loop", 1);
}

#[test]
#[timeout(240_000)]
fn in_range_inline_const_should_verify() {
    assert_verifies("should_verify_inline_const", 1);
}

#[test]
#[timeout(240_000)]
fn loop_written_param_is_not_read_at_entry_value_should_fail() {
    assert_fails(
        "should_fail_param_carried",
        "bump",
        "(loop call obligations)",
    );
}

#[test]
#[timeout(240_000)]
fn earlier_loop_write_is_not_stale_in_later_loop_should_fail() {
    assert_fails("should_fail_seq_loop_stale", "two_loops", "<=");
}

#[test]
#[timeout(240_000)]
fn pre_loop_join_is_not_one_branch_value_should_fail() {
    assert_fails("should_fail_branch_preloop", "joined", "<=");
}

#[test]
#[timeout(240_000)]
fn write_through_field_then_add_is_rejected() {
    let output = run_fixture("should_fail_field_write");
    assert!(
        !output.status.success(),
        "expected should_fail_field_write to be rejected; stderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(
        !String::from_utf8_lossy(&output.stderr).contains("through_field verified"),
        "through_field must not verify",
    );
}

#[test]
#[timeout(240_000)]
fn conservative_region_walks_should_verify() {
    assert_verifies("should_verify_regions", 3);
}

#[test]
#[timeout(240_000)]
fn stable_locals_read_at_two_points_are_not_conflated_should_fail() {
    assert_fails(
        "should_fail_conflate_post",
        "conflate_post",
        "(0 <= (__trust_wp_arith_havoc_",
    );
}

#[test]
#[timeout(240_000)]
fn conflated_locals_in_loop_without_invariant_should_fail() {
    assert_fails(
        "should_fail_conflate_loop",
        "conflate_loop",
        "(0 <= (__trust_wp_arith_havoc_",
    );
}

#[test]
#[timeout(240_000)]
fn conflated_locals_contract_free_should_fail() {
    assert_fails(
        "should_fail_conflate_contractless",
        "conflate_contractless",
        "(0 <= (__trust_wp_arith_havoc_",
    );
}

#[test]
#[timeout(240_000)]
fn contract_free_assert_is_never_verified() {
    assert_not_verified("should_fail_assert_contractless", "assert_contractless");
}

#[test]
#[timeout(240_000)]
fn reference_add_forwarding_impl_should_fail() {
    assert_fails("should_fail_ref_add", "ref_add", "((*x + 1) <= 255)");
}

#[test]
#[timeout(240_000)]
fn reference_sub_forwarding_impl_should_fail() {
    assert_fails("should_fail_ref_sub", "ref_sub", "(0 <= (*a - *b))");
}

#[test]
#[timeout(240_000)]
fn add_assign_through_mut_ref_is_never_verified() {
    assert_not_verified("should_fail_ref_add_assign", "ref_add_assign");
}

#[test]
#[timeout(240_000)]
fn second_add_assign_through_mut_ref_is_never_verified() {
    assert_not_verified("should_fail_ref_add_assign_twice", "ref_add_assign_twice");
}

#[test]
#[timeout(240_000)]
fn closure_body_overflow_should_fail() {
    assert_closure_fails("should_fail_closure_add", "closure_add", "((x + 1) <= 255)");
}

#[test]
#[timeout(240_000)]
fn closure_body_overflow_is_its_own_goal_should_fail() {
    assert_closure_fails(
        "should_fail_closure_body_only",
        "closure_body_only",
        "((x + 1) <= 255)",
    );
}

#[test]
#[timeout(240_000)]
fn second_overflow_twins_should_verify() {
    assert_verifies("should_verify_overflow_v2", 6);
}

#[test]
#[timeout(240_000)]
fn closure_body_twin_should_verify() {
    let output = run_fixture("should_verify_closure_body");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("closure_guarded_ok::{closure#0} verified"),
        "expected the closure body to verify; stderr: {stderr}",
    );
}

/// A contract-free body's index bounds check is a charged goal (D-95): in
/// bounds on every path it verifies, not capped as an unchecked panic site...
#[test]
#[timeout(240_000)]
fn clause_free_body_with_discharged_bounds_check_should_verify() {
    let output = run_fixture("should_verify_index_contractless");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stderr.contains("trust-wp: index_guarded verified"),
        "expected index_guarded to verify; stderr: {stderr}",
    );
}

/// A contract-free body's `assert!` whose panic arm the switch lane charged:
/// the assertion holds on every path, so the charged edge leaves the
/// clause-free cap and the body verifies (its twin
/// `should_fail_assert_contractless` is never verified).
#[test]
#[timeout(240_000)]
fn clause_free_body_with_discharged_assert_should_verify() {
    let output = run_fixture("should_verify_assert_contractless");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stderr.contains("trust-wp: assert_guarded verified"),
        "expected assert_guarded to verify; stderr: {stderr}",
    );
}

/// ...and one index past the end on a path the guard admits is refuted on the
/// bounds goal itself.
#[test]
#[timeout(240_000)]
fn clause_free_body_with_out_of_bounds_index_should_fail() {
    assert_fails(
        "should_fail_index_contractless",
        "index_unguarded",
        "(i < 4)",
    );
}

#[test]
#[timeout(240_000)]
fn explicit_path_add_call_should_fail() {
    assert_fails(
        "should_fail_explicit_add",
        "explicit_add",
        "((x + 1) <= 255)",
    );
}

#[test]
#[timeout(240_000)]
fn method_syntax_add_call_should_fail() {
    assert_fails("should_fail_method_add", "method_add", "((x + 1) <= 255)");
}

#[test]
#[timeout(240_000)]
fn explicit_add_assign_call_should_fail() {
    assert_fails(
        "should_fail_explicit_add_assign",
        "explicit_add_assign",
        "((x + 1) <= 255)",
    );
}

#[test]
#[timeout(240_000)]
fn reference_shift_forwarding_impl_should_fail() {
    assert_fails("should_fail_shl_ref", "shl_ref", "(*s < 8)");
}

#[test]
#[timeout(240_000)]
fn reference_neg_forwarding_impl_should_fail() {
    assert_fails("should_fail_neg_ref", "neg_ref", "(*x != -128)");
}

#[test]
#[timeout(240_000)]
fn operator_call_twins_should_verify() {
    assert_verifies("should_verify_operator_calls", 3);
}

/// The guarded negation must never be rejected. On the frozen ay its
/// unsat answer is withheld as `unknown (proof-trusted)` (the same backend
/// certification gap as syntax/02_operators), so either verdict is allowed.
#[test]
#[timeout(240_000)]
fn reference_neg_twin_is_never_rejected() {
    let output = run_fixture("should_verify_neg_ref");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("neg_ref_ok FAILED"),
        "the guarded negation must not fail; stderr: {stderr}",
    );
    assert!(
        stderr.contains("neg_ref_ok verified")
            || stderr.contains("neg_ref_ok unknown (proof-trusted)"),
        "expected verified or the proof-trusted unknown; stderr: {stderr}",
    );
}

/// Two `Cell::get` reads around a `Cell::set` are two values: a write through
/// interior mutability (`&Cell<u8>`) is a write, so `b - a` is never proved.
#[test]
#[timeout(240_000)]
fn interior_mutability_reads_are_not_conflated() {
    assert_not_verified("should_fail_cell_nc2", "cell_nc2");
}

/// GREEN twin: arithmetic that holds for any two reads of the cell. On the
/// frozen ay the unsat answer may be withheld as `unknown (proof-trusted)`.
#[test]
#[timeout(240_000)]
fn interior_mutability_twin_is_never_rejected() {
    let output = run_fixture("should_verify_cell_twin");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("cell_twin FAILED"),
        "the two-read arithmetic must not fail; stderr: {stderr}",
    );
    assert!(
        stderr.contains("cell_twin verified")
            || stderr.contains("cell_twin unknown (proof-trusted)"),
        "expected verified or the proof-trusted unknown; stderr: {stderr}",
    );
}

/// A contract-free body calling a std method that panics inside its own
/// body (`Vec::remove` on an empty vector) is capped, naming the call.
#[test]
#[timeout(240_000)]
fn contract_free_unchecked_callee_is_partial() {
    let stderr = assert_not_verified("should_fail_vec_remove", "vr");
    // Either the partial cap naming the call, or (since the Vec::remove spec
    // carries its `index < len` precondition) a FAILED verdict on
    // exactly that precondition.
    assert!(
        (stderr.contains("vr unknown (partial: panic paths unchecked (")
            && stderr.contains("call to "))
            || (stderr.contains("trust-wp: vr FAILED") && stderr.contains("(0@ < v@.len())")),
        "expected the partial verdict naming the call or the remove precondition failure; \
         stderr: {stderr}",
    );
}

/// GREEN twin: a checked callee whose precondition is discharged and a total
/// core integer method leave a contract-free body creditable.
#[test]
#[timeout(240_000)]
fn contract_free_checked_callee_twin_should_verify() {
    let output = run_fixture("should_verify_checked_callee");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("checked_callee FAILED") && !stderr.contains("partial: panic paths"),
        "the checked callee and total method must not fail or cap; stderr: {stderr}",
    );
    assert!(
        stderr.contains("checked_callee verified")
            || stderr.contains("checked_callee unknown (proof-trusted)"),
        "expected verified or the proof-trusted unknown; stderr: {stderr}",
    );
}

/// Drop glue running a panicking `Drop` impl caps a contract-free body.
#[test]
#[timeout(240_000)]
fn contract_free_drop_glue_is_partial() {
    let stderr = assert_not_verified("should_fail_dropper", "dropper");
    // Either the partial cap naming the drop, or a FAILED verdict: the drop
    // glue of an uncontracted `Drop` impl owes its own obligation, and the GREEN
    // twin without drop glue (`no_drop_glue_twin_should_verify`) verifies, so
    // the failure is the drop's.
    assert!(
        (stderr.contains("dropper unknown (partial: panic paths unchecked (")
            && stderr.contains("drop of D"))
            || stderr.contains("trust-wp: dropper FAILED")
            // D-28: an unvalidated refutation is withheld rather than printed as
            // FAILED. Still a rejection (non-zero exit, counted under errors).
            || (stderr.contains("trust-wp: dropper unknown")
                && stderr.contains("refutation withheld")),
        "expected the partial verdict naming the drop, a FAILED verdict, or a withheld refutation; stderr: {stderr}",
    );
}

/// GREEN twin: a local without drop glue.
#[test]
#[timeout(240_000)]
fn no_drop_glue_twin_should_verify() {
    assert_verifies("should_verify_no_drop_glue", 1);
}

/// An operator-trait method called through a fn pointer owes the operation's
/// obligation.
#[test]
#[timeout(240_000)]
fn fn_pointer_operator_call_should_fail() {
    assert_fails("should_fail_fnptr_add", "fnptr", "((x + 1) <= 255)");
}

/// GREEN twin: the fn-pointer call's obligation is discharged by `requires`.
#[test]
#[timeout(240_000)]
fn fn_pointer_operator_call_twin_should_verify() {
    assert_verifies("should_verify_fnptr_add", 1);
}

/// `Iterator::sum` into an integer is an overflow-checked fold.
#[test]
#[timeout(240_000)]
fn integer_sum_is_never_verified() {
    assert_not_verified("should_fail_sum", "sum");
}

/// GREEN twin: `len` is not an overflow-checked fold.
#[test]
#[timeout(240_000)]
fn len_twin_should_verify() {
    assert_verifies("should_verify_len_twin", 1);
}
