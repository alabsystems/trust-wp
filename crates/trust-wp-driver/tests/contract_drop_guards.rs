// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::OnceLock,
};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_path};

fn fixture_target_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/contract_drop_guard_tests")
}

/// Pre-warm the fixture's dependency cache so individual bin checks are fast.
///
/// Without this, three concurrent tests each try to cold-compile all trust-wp
/// deps into the same target directory, fighting over cargo's file lock and
/// often exceeding the per-test timeout in multi-worker environments.
fn warm_fixture_deps() {
    static ONCE: OnceLock<()> = OnceLock::new();
    ONCE.get_or_init(|| {
        // Build the lib target to cache all shared dependencies.
        // Status is intentionally ignored — the lib may have parse errors,
        // but the dependency artifacts will still be cached for bin targets.
        let _ = Command::new("cargo")
            .current_dir(fixture_dir("contract_drop_guards"))
            .env("CARGO_TARGET_DIR", fixture_target_dir())
            .env("RUSTC_WRAPPER", trust_wp_rustc_path())
            .args(["check", "--quiet", "--lib"])
            .status();
    });
}

fn run_fixture(bin: &str) -> std::process::Output {
    warm_fixture_deps();
    Command::new("cargo")
        .current_dir(fixture_dir("contract_drop_guards"))
        .env("CARGO_TARGET_DIR", fixture_target_dir())
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for contract drop guard fixture")
}

#[test]
#[timeout(300_000)]
fn dropped_requires_clause_rejects_function() {
    let output = run_fixture("requires_dropped");
    let stderr = String::from_utf8_lossy(&output.stderr);

    // trust-wp-rustc returns exit code 2 for unparseable contracts, which causes
    // cargo check to fail. This is correct: malformed contracts should not silently
    // compile. The important thing is that the right diagnostics are emitted.
    assert!(
        !output.status.success(),
        "fixture with malformed requires should fail (exit non-zero); stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("failed to parse requires"),
        "expected parse failure for malformed requires clause; stderr: {stderr}"
    );
    assert!(
        stderr.contains("has unparseable requires clause(s)"),
        "expected dropped requires diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("skipping verification to prevent unsound results"),
        "expected skip-verification safety diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 0 verified, 0 failed, 1 errors"),
        "expected malformed requires fixture to be rejected without verification; stderr: {stderr}"
    );
}

/// After #1513, char literal `'a'` parses as `Int(97)` — a valid integer variant
/// measure. The variant IS accepted but verification fails because the constant
/// `97` does not decrease at the recursive call site. This is correct behavior:
/// variants are integer expressions, and `Int(97)` is a valid (if useless) integer.
#[test]
#[timeout(300_000)]
fn dropped_variant_clause_rejects_function() {
    let output = run_fixture("variant_dropped");
    let stderr = String::from_utf8_lossy(&output.stderr);

    // trust-wp-rustc returns exit code 1 for verification failure, which causes
    // cargo check to fail. The variant `'a'` (= Int(97)) is accepted as a constant
    // integer measure, but verification correctly detects it does not decrease.
    assert!(
        !output.status.success(),
        "fixture with non-decreasing variant should fail verification; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("FAILED") && stderr.contains("variant decrease"),
        "expected variant decrease failure for constant variant measure; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 0 verified, 1 failed, 0 errors"),
        "expected verification failure (not parse error) for constant variant; stderr: {stderr}"
    );
}

/// Regression test for #1132: per-loop invariant parse errors were silently
/// dropped, bypassing the dropped-clause safety guard from #802.
#[test]
#[timeout(300_000)]
fn dropped_per_loop_invariant_clause_rejects_function() {
    let output = run_fixture("per_loop_invariant_dropped");
    let stderr = String::from_utf8_lossy(&output.stderr);

    // trust-wp-rustc returns exit code 2 for unparseable contracts, which causes
    // cargo check to fail. Same as dropped_requires: malformed contracts are errors.
    assert!(
        !output.status.success(),
        "fixture with malformed invariant should fail (exit non-zero); stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("failed to parse") && stderr.contains("invariant"),
        "expected parse failure for malformed per-loop invariant clause; stderr: {stderr}"
    );
    assert!(
        stderr.contains("has unparseable invariant clause(s)"),
        "expected dropped invariant diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("skipping verification to prevent unsound results"),
        "expected skip-verification safety diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 0 verified, 0 failed, 1 errors"),
        "expected malformed per-loop invariant fixture to be rejected without verification; stderr: {stderr}"
    );
}
