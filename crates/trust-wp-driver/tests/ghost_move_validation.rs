// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/ghost_move_validation_tests");
    nested_cargo("check")
        .current_dir(fixture_dir("ghost_move_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for ghost move fixture")
}

#[test]
#[timeout(120_000)]
fn ghost_move_validation_should_fail() {
    let output = run_fixture("should_fail");
    assert!(
        !output.status.success(),
        "expected ghost validation failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("cannot move non-ghost value in ghost block"),
        "missing expected error message; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_move_validation_should_pass() {
    let output = run_fixture("should_pass");
    assert!(
        output.status.success(),
        "expected ghost validation success; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
#[timeout(120_000)]
fn ghost_move_validation_user_ghost_should_fail() {
    let output = run_fixture("should_fail_user_ghost");
    assert!(
        !output.status.success(),
        "expected ghost validation failure for user-defined Ghost type; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("cannot move non-ghost value in ghost block"),
        "missing expected error message for user-defined Ghost type; stderr: {stderr}",
    );
}

/// Regression test for #1981: user-defined `#[derive(Copy, Clone)]` types
/// must not be rejected by ghost move validation.
#[test]
#[timeout(120_000)]
fn ghost_move_validation_user_copy_should_pass() {
    let output = run_fixture("should_pass_user_copy");
    assert!(
        output.status.success(),
        "expected ghost validation success for user-defined Copy type; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
