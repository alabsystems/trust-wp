// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/ghost_loop_validation_tests");
    nested_cargo("check")
        .current_dir(fixture_dir("ghost_loop_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for ghost loop fixture")
}

#[test]
#[timeout(120_000)]
fn ghost_loop_validation_should_fail_for_non_terminating_loop() {
    let output = run_fixture("should_fail");
    assert!(
        !output.status.success(),
        "expected ghost loop validation failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("non-terminating `loop {}` in ghost block requires #[variant(...)]"),
        "missing ghost loop validation error message; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_loop_validation_should_pass_for_while_loop() {
    let output = run_fixture("should_pass");
    assert!(
        output.status.success(),
        "expected ghost loop validation success; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
