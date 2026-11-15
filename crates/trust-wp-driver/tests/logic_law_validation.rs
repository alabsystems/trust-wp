// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for Creusot-compatible trait/impl law mode validation.

use std::{
    fs,
    path::Path,
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time should be after unix epoch")
        .as_nanos();
    let target_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/logic_law_validation_tests")
        .join(format!("{bin}-{}-{unique}", std::process::id()));
    let output = nested_cargo("check")
        .current_dir(fixture_dir("logic_law_validation"))
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for logic law validation fixture");
    let _ = fs::remove_dir_all(&target_dir);
    output
}

#[test]
#[timeout(120_000)]
fn law_mode_validation_allows_matching_trait_impl_modes() {
    let output = run_fixture("should_pass_match");
    assert!(
        output.status.success(),
        "expected matching trait/impl law modes to compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
#[timeout(120_000)]
fn law_mode_validation_rejects_mismatched_trait_impl_modes() {
    let output = run_fixture("should_fail_mismatch");
    assert!(
        !output.status.success(),
        "expected mismatched trait/impl law modes to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Expected `la` to be a `#[logic(law)]`"),
        "missing expected-law diagnostic; stderr: {stderr}",
    );
    assert!(
        stderr.contains("Method `lo` should not be a `#[logic(law)]`"),
        "missing unexpected-law diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn law_mode_validation_rejects_impl_added_prophetic_mode() {
    // Strict guard (Phase 2, creusot tests/should_fail/logic_prophetic_impl.rs):
    // an impl MUST NOT upgrade from the trait's default-opaque `#[logic]` mode
    // directly to `#[logic(prophetic)]`. Creusot rejects this with
    // "Expected `f` to be a logic function as specified by the trait
    // declaration" because the trait's opaque declaration does not authorize
    // prophetic-mode bodies. The impl must instead use `open`, `open(self)`,
    // or match the trait's mode. The previously-lenient acceptance was a
    // false-accept closed by Phase 2; this test enforces the rejection.
    let output = run_fixture("should_fail_prophetic_impl");
    assert!(
        !output.status.success(),
        "expected impl-added prophetic mode to be rejected; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr
            .contains("Expected `f` to be a logic function as specified by the trait declaration"),
        "missing prophetic-impl rejection diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn law_mode_validation_rejects_sealed_trait_default_override() {
    let output = run_fixture("should_fail_sealed_default");
    assert!(
        !output.status.success(),
        "expected sealed trait default override to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("This trait method overrides a sealed implementation"),
        "missing sealed override diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn law_mode_validation_rejects_law_method_generics_and_where_clauses() {
    let output = run_fixture("should_fail_law_generics");
    assert!(
        !output.status.success(),
        "expected law generic/where fixture to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    let count = stderr
        .matches("Laws cannot have additional generic parameters or trait constraints")
        .count();
    assert_eq!(
        count, 2,
        "expected one diagnostic for the generic law and one for the where-clause law; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn law_mode_validation_lenient_trait_logic_implemented_by_plain_fn() {
    // Lenient mode: impl may omit #[logic] when the trait declares it.
    // The impl inherits logic-mode dispatch from the trait declaration.
    let output = run_fixture("should_fail_trait_logic_plain_impl");
    assert!(
        output.status.success(),
        "lenient mode should accept trait-logic/plain-impl; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("Expected `f` to be a `#[logic]`"),
        "lenient mode should not emit expected-logic diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn law_mode_validation_rejects_logic_fn_implementing_plain_trait_method() {
    // Creusot's `can_implement`: a logic function cannot implement a program
    // trait method. The code that runs for the call is the logic function's
    // erased body, and no program body owes the trait method's contract
    // (trait_logic_impl_of_program_method_granted.rs).
    let output = run_fixture("should_fail_plain_trait_logic_impl");
    assert!(
        !output.status.success(),
        "a logic impl of a program trait method must be refused; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "Expected `f` to be a program function as specified by the trait declaration"
        ),
        "missing program-function refusal; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn law_mode_validation_rejects_macro_emitted_sealed_trait_default_override() {
    let output = run_fixture("should_fail_macro_sealed_default");
    assert!(
        !output.status.success(),
        "expected macro sealed trait default override to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("This trait method overrides a sealed implementation"),
        "missing macro sealed override diagnostic; stderr: {stderr}",
    );
}
