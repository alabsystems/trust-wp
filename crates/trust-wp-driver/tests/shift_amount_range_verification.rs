// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for the machine-int shift-amount range obligation
//! (ledger int-shift-full).
//!
//! These tests verify that:
//! 1. An over-wide literal shift (`1u8 >> 8`) FAILS verification — the
//!    historical false accept: the shift encoding emitted no
//!    shift-amount-in-range obligation, so the over-wide shift verified.
//! 2. A symbolic shift amount with no range guard FAILS verification.
//! 3. Well-formed shifts (in-range literal, `amt & (BITS - 1)` mask,
//!    `#[requires]`-guarded amount) still VERIFY.

use std::{path::Path, process::Command};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/shift_amount_range_tests");
    Command::new("cargo")
        .current_dir(fixture_dir("shift_amount_range"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for shift_amount_range fixture")
}

/// RED: the int-shift-full shape. `1u8 >> 8` must fail verification via the
/// shift-amount-in-range obligation even though the postcondition is `true`.
#[test]
#[timeout(240_000)]
fn shift_over_wide_literal_should_fail() {
    let output = run_fixture("should_fail_over_wide");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "expected verification failure for 1u8 >> 8; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    assert!(
        stderr.contains("shr_full FAILED"),
        "expected shr_full to fail via the shift-amount range obligation; stderr: {stderr}",
    );
}

/// RED: a symbolic amount with no range guard must fail verification
/// (counterexample: n >= 8).
#[test]
#[timeout(240_000)]
fn shift_unguarded_symbolic_amount_should_fail() {
    let output = run_fixture("should_fail_unguarded");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "expected verification failure for x >> n with unguarded n; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    assert!(
        stderr.contains("shr_unguarded FAILED"),
        "expected shr_unguarded to fail via the shift-amount range obligation; stderr: {stderr}",
    );
}

/// RED (BV mode): an over-wide shift under `#[bitwise_proof]` must FAIL.
///
/// The fixture's postcondition (`x >> n <= x`) is VALID, so the only
/// refutable conjunct is the shift-amount range obligation — emitted as a
/// native BV check in the QF_BV proof lane. This pins that BV mode keeps
/// the SAME soundness check as the Int lane (a marker treated as a pure
/// identity in the BV encoding would falsely verify). The Int-lane RED
/// battery does not cover BV mode.
#[test]
#[timeout(240_000)]
fn shift_bitwise_proof_over_wide_should_fail() {
    let output = run_fixture("should_fail_bitwise_over_wide");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "expected verification failure for bitwise_proof x >> n with unguarded n; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    assert!(
        stderr.contains("shr_bitwise FAILED"),
        "expected shr_bitwise to fail via the BV-mode shift-amount range obligation; stderr: {stderr}",
    );
}

/// GREEN (BV mode): guarded and masked shifts under `#[bitwise_proof]`
/// must verify — the BV-native range check must not reject well-formed
/// shifts (bits.rs regression class: `empty`/`set_bit` degraded when the
/// obligation dragged Int-encoded terms into the BV lane).
#[test]
#[timeout(240_000)]
fn shift_bitwise_proof_well_formed_should_verify() {
    let output = run_fixture("should_verify_bitwise");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "expected verification success for well-formed bitwise_proof shifts; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    for verified_fn in ["shr_bitwise_guarded", "shr_bitwise_masked"] {
        assert!(
            stderr.contains(&format!("{verified_fn} verified")),
            "expected {verified_fn} to verify; stderr: {stderr}",
        );
    }
}

/// GREEN: in-range literal, masked, and precondition-guarded shifts must all
/// still verify — the new obligation must not reject well-formed shifts.
#[test]
#[timeout(240_000)]
fn shift_well_formed_should_verify() {
    let output = run_fixture("should_verify");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "expected verification success for well-formed shifts; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    for verified_fn in ["shr_literal", "shl_masked", "shr_guarded"] {
        assert!(
            stderr.contains(&format!("{verified_fn} verified")),
            "expected {verified_fn} to verify; stderr: {stderr}",
        );
    }
}
