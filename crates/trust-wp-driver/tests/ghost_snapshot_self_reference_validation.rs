// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for Snapshot self-reference rejection (#2686 / bug/436_2).

use std::{path::Path, process::Command};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/ghost_snapshot_self_reference_validation_tests");
    Command::new("cargo")
        .current_dir(fixture_dir("ghost_snapshot_self_reference_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for snapshot self-reference fixture")
}

#[test]
#[timeout(120_000)]
fn ghost_snapshot_self_reference_validation_should_fail() {
    let output = run_fixture("should_fail");
    assert!(
        !output.status.success(),
        "expected snapshot self-reference failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("snapshot self-reference"),
        "missing snapshot self-reference diagnostic; stderr: {stderr}",
    );
    assert!(
        stderr.contains("BadDirect") || stderr.contains("BadOption") || stderr.contains("BadEnum"),
        "missing rejecting type name; stderr: {stderr}",
    );

    let has_verification_output = stderr.lines().any(|line| {
        line.contains("trust-wp:") && (line.contains("verified") || line.contains("FAILED"))
    });
    assert!(
        !has_verification_output,
        "verification should not run after snapshot self-reference rejection; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_snapshot_self_reference_validation_should_pass() {
    let output = run_fixture("should_pass");
    assert!(
        output.status.success(),
        "expected non-recursive snapshot shapes to compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("snapshot self-reference"),
        "allowed snapshot shapes must not emit self-reference errors; stderr: {stderr}",
    );
}
