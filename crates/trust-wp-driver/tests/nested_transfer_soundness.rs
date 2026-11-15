// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Soundness regression tests for the nested-reborrow transfer encoding
//! (rusthorn `inc_max_3` class).
//!
//! The block extractor synthesizes per-path body write facts for rebindable
//! `&mut T` parameter slots using collapsed naming (`Deref(p)` for both the
//! entry and the post-write state). On paths where no transfer-call
//! substitution fired, those facts degenerate to contradictions like
//! `*ma == *ma + 2`, which — asserted as branch-guarded premises — negate
//! REACHABLE path conditions and let postconditions that are false on those
//! paths verify vacuously. `apply_nested_transfer_resolutions` strips
//! those body facts (the exact expiry resolutions carry the per-path write
//! semantics instead).
//!
//! * `should_fail`: false exactly on the no-swap path — must FAIL (verifies
//!   vacuously if the collapsed body facts are kept).
//! * `should_verify`: the reference `inc_max_3` — must keep verifying from
//!   the expiry resolutions alone (completeness pin for the strip).

use ntest::timeout;
use trust_wp_test_utils::{
    fixture_dir, nested_cargo, trust_wp_rustc_fixture_target_dir, trust_wp_rustc_path,
};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir = trust_wp_rustc_fixture_target_dir("nested_transfer_soundness_tests");
    nested_cargo("check")
        .current_dir(fixture_dir("nested_transfer_soundness"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for nested-transfer soundness fixture")
}

#[test]
#[timeout(300_000)]
fn contradictory_collapsed_body_fact_does_not_false_verify() {
    let output = run_fixture("should_fail");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "should_fail fixture must NOT verify (reachable-path-false postcondition); \
         stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    assert!(
        stderr.contains("entry_order_claim FAILED"),
        "expected entry_order_claim postcondition failure; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("entry_order_claim verified"),
        "entry_order_claim must not verify; stderr: {stderr}"
    );
}

/// The crate does not pass as a whole, and that is the fixture's `main`, not
/// `inc_max_3`: `main` owes `inc_max_3`'s precondition, so it is a
/// verification target (D-71), and the call's credit states `^` of the
/// constant each local holds, which the final-collapse guard's
/// constant-carrier arm refuses (D-14). The cost is that caller's verdict;
/// the caller is committed as the xfail control
/// `constant_initialized_locals_lent_to_prophecy_callee_control.rs`.
#[test]
#[timeout(300_000)]
fn inc_max_3_still_verifies_from_expiry_resolutions() {
    let output = run_fixture("should_verify");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("inc_max_3 verified"),
        "expected inc_max_3 verification; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    assert!(
        stderr.contains("trust-wp: main error: unsupported formula: final-collapse refused")
            && stderr.contains("`^Int(3)` applies a prophecy to a constant carrier"),
        "expected main's call to be refused on the constant carrier; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 1 verified, 0 failed, 1 errors, 1 trusted"),
        "expected inc_max_3 as the one credit beside main's refusal; stderr: {stderr}"
    );
    assert!(
        !output.status.success(),
        "a refused caller fails the crate; stderr: {stderr}"
    );
}
