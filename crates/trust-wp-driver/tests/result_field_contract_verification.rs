// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{path::Path, process::Command};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/result_field_contract_tests");
    Command::new("cargo")
        .current_dir(fixture_dir("result_field_contract"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for result-field contract fixture")
}

#[test]
#[timeout(120_000)]
fn ensures_on_result_struct_field_verifies() {
    let output = run_fixture("should_verify");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "fixture should compile and verify; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("trust-wp: 1 verified, 0 failed, 0 errors"),
        "expected successful contract verification summary; stderr: {stderr}"
    );
}
