// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for Creusot-compatible purity/admissibility validation.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/purity_validation_tests");
    nested_cargo("check")
        .current_dir(fixture_dir("purity_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for purity validation fixture")
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
        "Pattern matching literals on Int are unsupported",
        "Forbidden constructor or field access of opaque type",
        "Cannot make a less-visible logic function transparent",
    ] {
        assert!(
            stderr.contains(expected),
            "missing `{expected}` diagnostic; stderr: {stderr}",
        );
    }
}

/// The logic-surface gaps that are TYPE errors of the specification are
/// reported by rustc through the contract type-check vehicle, before the
/// driver runs, in Creusot's wording: Creusot's `DivLogic`/`RemLogic` exist
/// for `Int` only, and `a[i]` in logic is an `IndexLogic` method call whose
/// absence is an E0599 naming the trait (Creusot lowers it to
/// `__creusot_index_logic_stub`, the same shape).
#[test]
#[timeout(120_000)]
fn purity_validation_rejects_logic_surface_type_errors() {
    let output = run_fixture("should_fail_logic_surface_types");
    assert!(
        !output.status.success(),
        "expected logic surface type-error fixture to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    for expected in [
        "Cannot divide primitive integers in logic",
        "cannot calculate the remainder of primitive integers in logic",
        "error[E0599]",
        "`Bag: trust_wp::logic::ops::IndexLogic<_>`",
    ] {
        assert!(
            stderr.contains(expected),
            "missing `{expected}` diagnostic; stderr: {stderr}",
        );
    }
    // trust-wp's own verdict lines only: targo's lane banner says
    // "UNVERIFIED" and "explicit-unverified" of the nested command.
    assert!(
        !stderr.lines().any(|line| line.starts_with("trust-wp:")
            && line.contains("verified")
            && !line.contains(" 0 verified")),
        "a fixture that fails to type-check must verify nothing; stderr: {stderr}"
    );
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
