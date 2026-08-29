// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Soundness regression tests for the nested-reborrow transfer encoding
//! (rusthorn `inc_max_3` class; adjudicated 2026-07-22).
//!
//! The block extractor synthesizes per-path body write facts for rebindable
//! `&mut T` parameter slots using collapsed naming (`Deref(p)` for both the
//! entry and the post-write state). On paths where no transfer-call
//! substitution fired, those facts degenerate to contradictions like
//! `*ma == *ma + 2`, which — asserted as branch-guarded premises — negate
//! REACHABLE path conditions and let postconditions that are false on those
//! paths verify vacuously. `apply_nested_transfer_resolutions` now strips
//! those body facts (the exact expiry resolutions carry the per-path write
//! semantics instead).
//!
//! * `should_fail`: false exactly on the no-swap path — must FAIL (falsely
//!   verified before the fix).
//! * `should_verify`: the reference `inc_max_3` — must keep verifying from
//!   the expiry resolutions alone (completeness pin for the strip).

use std::process::Command;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_fixture_target_dir, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir = trust_wp_rustc_fixture_target_dir("nested_transfer_soundness_tests");
    Command::new("cargo")
        .current_dir(fixture_dir("nested_transfer_soundness"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for nested-transfer soundness fixture")
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

#[test]
#[timeout(300_000)]
fn inc_max_3_still_verifies_from_expiry_resolutions() {
    let output = run_fixture("should_verify");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "inc_max_3 fixture should verify; stdout: {}\nstderr: {stderr}",
        String::from_utf8_lossy(&output.stdout),
    );
    assert!(
        stderr.contains("inc_max_3 verified"),
        "expected inc_max_3 verification; stderr: {stderr}"
    );
}
