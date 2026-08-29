// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for Creusot-compatible purity/admissibility validation.

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/purity_validation_tests");
    Command::new(cargo_path())
        .current_dir(fixture_dir("purity_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for purity validation fixture")
}

fn cargo_path() -> PathBuf {
    if let Some(path) = std::env::var_os("CARGO") {
        return PathBuf::from(path);
    }

    if let Some(home) = std::env::var_os("HOME") {
        let path = Path::new(&home).join(".cargo/bin/cargo");
        if path.exists() {
            return path;
        }
    }

    PathBuf::from("cargo")
}

#[test]
#[timeout(120_000)]
fn purity_validation_rejects_program_logic_call() {
    let output = run_fixture("should_fail_program_logic_call");
    assert!(
        !output.status.success(),
        "expected program logic call to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("called logic function"),
        "missing program logic call diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn purity_validation_rejects_logic_surface_gaps() {
    let output = run_fixture("should_fail_logic_surface");
    assert!(
        !output.status.success(),
        "expected logic surface fixture to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    for expected in [
        "The `dead` term can only be used",
        "Cannot divide primitive integers in logic",
        "cannot calculate the remainder of primitive integers in logic",
        "Pattern matching literals on Int are unsupported",
        "no IndexLogic implementation found",
        "Forbidden constructor or field access of opaque type",
        "Cannot make a less-visible logic function transparent",
    ] {
        assert!(
            stderr.contains(expected),
            "missing `{expected}` diagnostic; stderr: {stderr}",
        );
    }
}

#[test]
#[timeout(120_000)]
fn purity_validation_rejects_raw_pointer_deref() {
    let output = run_fixture("should_fail_raw_pointer_deref");
    assert!(
        !output.status.success(),
        "expected raw pointer deref to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Dereference of a raw pointer is forbidden"),
        "missing raw pointer deref diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn purity_validation_allows_forbidden_text_in_comments_strings_and_non_int_match() {
    let output = run_fixture("should_pass_text_noise");
    assert!(
        output.status.success(),
        "expected text-noise fixture to pass; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
