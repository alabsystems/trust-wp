// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for Creusot-compatible `Tokens::new` placement rules.

use std::{path::Path, process::Command};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/tokens_new_validation_tests");
    Command::new("cargo")
        .current_dir(fixture_dir("tokens_new_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for Tokens::new fixture")
}

#[test]
#[timeout(120_000)]
fn tokens_new_allows_single_main_call() {
    let output = run_fixture("should_pass_main");
    assert!(
        output.status.success(),
        "expected single Tokens::new in main to compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
#[timeout(120_000)]
fn tokens_new_rejects_non_main_call() {
    let output = run_fixture("should_fail_not_main");
    assert!(
        !output.status.success(),
        "expected Tokens::new outside main to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Tokens::new may only be called in the entry main function"),
        "missing non-main Tokens::new diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn tokens_new_rejects_loop_call() {
    let output = run_fixture("should_fail_loop");
    assert!(
        !output.status.success(),
        "expected Tokens::new in loop to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Tokens::new may not be called inside a loop"),
        "missing loop Tokens::new diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn tokens_new_rejects_second_call() {
    let output = run_fixture("should_fail_twice");
    assert!(
        !output.status.success(),
        "expected second Tokens::new to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Tokens::new may be called at most once"),
        "missing duplicate Tokens::new diagnostic; stderr: {stderr}",
    );
}
