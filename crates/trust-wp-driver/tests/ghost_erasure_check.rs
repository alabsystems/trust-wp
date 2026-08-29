// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the MIR-level ghost erasure soundness check (#1768).
//!
//! Compiles fixture code through trust-wp-rustc and verifies that:
//! - `should_pass` compiles without erasure check violations
//! - `should_pass_ghost_return` allows Ghost<T> in ordinary signatures
//! - `should_fail_switchint` still trips the real control-flow leak check
//! - `should_fail_program_context` rejects direct runtime Ghost API use
//! - focused program-context fixtures reject explicit create/deref/mutate/extract
//! - `should_fail_non_ghost_call` rejects non-ghost program calls in ghost context
//! - `should_fail_erasure_attribute_mismatch` rejects invalid `#[erasure]`
//! - `should_fail_permission_identity` rejects unvalidated ghost permission use

use std::{path::Path, process::Command};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/ghost_erasure_check_tests");
    Command::new("cargo")
        .current_dir(fixture_dir("ghost_erasure_check"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for ghost erasure fixture")
}

fn assert_fixture_fails_with(bin: &str, expected: &str) {
    let output = run_fixture(bin);
    assert!(
        !output.status.success(),
        "expected {bin} to fail; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(expected),
        "missing `{expected}` diagnostic for {bin}; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_allows_ghost_return_signature() {
    let output = run_fixture("should_pass_ghost_return");
    assert!(
        output.status.success(),
        "expected ghost-return fixture to compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_pass() {
    let output = run_fixture("should_pass");
    assert!(
        output.status.success(),
        "expected ghost erasure check success; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// Regression: `snapshot! { stmt; }` (statement-form, discarded result)
/// must allow `#[logic]` calls inside its body and must not trigger the
/// program-context ghost extraction / ghost API diagnostics.  The macro
/// lowers to a block whose tail is `Snapshot::<()>::new_phantom()` instead
/// of a `Snapshot::capture(...)` call, so the validator must recognise the
/// pattern explicitly and bump `snapshot_capture_depth` while walking the
/// captured body. (#9)
#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_pass_snapshot_stmt_form_with_logic_call() {
    let output = run_fixture("should_pass_snapshot_stmt_logic");
    assert!(
        output.status.success(),
        "expected snapshot stmt-form with #[logic] call to pass ghost erasure check;          stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_switchint_ghost_branch() {
    let output = run_fixture("should_fail_switchint");
    assert!(
        !output.status.success(),
        "expected ghost erasure check failure for ghost-controlled branch; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("cannot dereference a ghost value in program context"),
        "missing program-context ghost deref error; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_program_context_ghost_api() {
    let output = run_fixture("should_fail_program_context");
    assert!(
        !output.status.success(),
        "expected program-context ghost API failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("cannot create a ghost variable in program context"),
        "missing Ghost::new program-context error; stderr: {stderr}",
    );
    assert!(
        stderr.contains("cannot dereference a ghost value in program context"),
        "missing Ghost deref program-context error; stderr: {stderr}",
    );
    assert!(
        stderr.contains("cannot extract a ghost value in program context"),
        "missing Ghost extraction program-context error; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_explicit_program_context_create() {
    assert_fixture_fails_with(
        "should_fail_program_context_create",
        "cannot create a ghost variable in program context",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_explicit_program_context_deref() {
    assert_fixture_fails_with(
        "should_fail_program_context_deref",
        "cannot dereference a ghost value in program context",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_explicit_program_context_mutate() {
    assert_fixture_fails_with(
        "should_fail_program_context_mutate",
        "cannot dereference a ghost value in program context",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_explicit_program_context_into_inner() {
    assert_fixture_fails_with(
        "should_fail_program_context_into_inner",
        "cannot extract a ghost value in program context",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_non_ghost_call_in_ghost_context() {
    let output = run_fixture("should_fail_non_ghost_call");
    assert!(
        !output.status.success(),
        "expected non-ghost call in ghost context failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("called non-ghost function") && stderr.contains("ghost context"),
        "missing non-ghost call diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_erasure_attribute_mismatch() {
    let output = run_fixture("should_fail_erasure_attribute_mismatch");
    assert!(
        !output.status.success(),
        "expected erasure attribute mismatch failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("failed #[erasure] check"),
        "missing erasure mismatch diagnostic; stderr: {stderr}",
    );
    assert!(
        stderr.contains("bar3"),
        "missing generic erasure equivalence site; stderr: {stderr}",
    );
    assert!(
        stderr.contains("add2"),
        "missing argument erasure equivalence site; stderr: {stderr}",
    );
    assert!(
        stderr.contains("#[erasure] target must have a body"),
        "missing erasure target body diagnostic; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_erasure_check_should_fail_on_permission_identity() {
    let output = run_fixture("should_fail_permission_identity");
    assert!(
        !output.status.success(),
        "expected permission identity failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("permission identity"),
        "missing permission identity diagnostic; stderr: {stderr}",
    );
    assert!(
        stderr.contains("not produced together") || stderr.contains("identity mismatch"),
        "missing permission identity detail; stderr: {stderr}",
    );
    for diagnostic_snippet in [
        "cell.borrow(perm)",
        "cell.borrow(ghost!(&*wrong_owner))",
        "local_cell.borrow(unknown_permission)",
        "cell.borrow_mut(wrong_permission)",
        "cell.take(ghost!(&mut **wrong_owner))",
        "cell.borrow(helper_wrong)",
        "cell.borrow(tuple_wrong)",
        "Perm::as_ref(ptr, perm)",
        "Perm::as_ref(ptr, ghost!(&**wrong_owner))",
        "Perm::as_mut(ptr as *mut i32, wrong_permission)",
    ] {
        assert!(
            stderr.contains(diagnostic_snippet),
            "missing permission identity diagnostic for {diagnostic_snippet}; stderr: {stderr}",
        );
    }
}

/// `#[erasure(target)]` functions are the ghost-bearing implementation half of
/// an erasure pair and legitimately receive both a runtime resource and its
/// ghost permission as inputs — the same-origin witness lives on the caller
/// (the erased target), not in the function body. The permission identity
/// heuristic must skip these functions or the `Perm::as_ref(x, own)` and
/// `Perm::as_mut(x, own)` patterns in
/// `reference/creusot/tests/should_succeed/specification/erasure.rs` cannot
/// even reach the body-equivalence check.
///
/// The fixture also tickles the body-equivalence layer (a separate check
/// that compares the erasure body against the target body), which is
/// known to be stricter than Creusot's. This test only asserts that the
/// *permission identity* diagnostic is no longer raised; the
/// body-equivalence layer is out of scope here.
#[test]
#[timeout(120_000)]
fn ghost_erasure_check_allows_permission_identity_in_erasure_fn() {
    let output = run_fixture("should_pass_erasure_permission_identity");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("permission identity"),
        "no permission identity diagnostic expected for erasure-tagged fn; \
         stderr: {stderr}",
    );
}
