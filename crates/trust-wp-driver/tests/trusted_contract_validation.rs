// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for trusted contract reference validation.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(format!(
        "../../target/trusted_contract_validation_tests_verify_{bin}"
    ));
    nested_cargo("check")
        .current_dir(fixture_dir("trusted_contract_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for trusted contract validation fixture")
}

#[test]
#[timeout(120_000)]
fn trusted_contract_validation_rejects_ghost_function_reference() {
    let output = run_fixture("should_fail_ghost_ref");
    assert!(
        !output.status.success(),
        "expected trusted contract ghost-reference failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("trusted contract validation"),
        "missing trusted contract validation diagnostic; stderr: {stderr}",
    );
    assert!(
        stderr.contains("ghost function") && stderr.contains("faux"),
        "missing referenced ghost function in diagnostic; stderr: {stderr}",
    );
    assert!(
        !stderr.contains("trusted_bad trusted (skipped)"),
        "invalid trusted contract must fail before trusted skip; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn trusted_contract_validation_allows_scalar_contract() {
    let output = run_fixture("should_pass_trusted_scalar_contract");
    assert!(
        output.status.success(),
        "expected scalar trusted contract to compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("trusted contract validation"),
        "valid trusted contract must not emit validation error; stderr: {stderr}",
    );
}
