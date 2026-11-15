// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression: a borrow-checked operand type still carries inference regions
//! (`'?N`). `interior_mutable_ref_arg_positions` asked rustc's `Freeze` query
//! with such a type as the key while resolving an extern-spec call on a
//! `Box<dyn Fn>` receiver, and the query system panicked hashing the region
//! ("region variables should not be hashed"). The function then got no verdict.
//!
//! The fixture's contract is false (the boxed closure divides by `x`, which may
//! be 0), so the run must end in a VERIFIER rejection with zero panics.

use ntest::timeout;
use trust_wp_test_utils::{
    fixture_dir, nested_cargo, trust_wp_rustc_fixture_target_dir, trust_wp_rustc_path,
};

#[test]
#[timeout(300_000)]
fn box_dyn_fn_extern_spec_call_reaches_a_verdict_without_panicking() {
    let target_dir = trust_wp_rustc_fixture_target_dir("revar_is_freeze_tests");
    let output = nested_cargo("check")
        .current_dir(fixture_dir("revar_is_freeze"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        // Hermetic: verify only the fixture crate, never its dependencies.
        .env("CARGO_TRUST_WP", "1")
        // Query keys are stable-hashed only when the dep graph is on: without
        // incremental compilation the ReVar key is never hashed and the bug
        // does not reproduce (the Creusot harness and cargo's dev profile both
        // compile incrementally).
        .env("CARGO_INCREMENTAL", "1")
        .args(["--quiet", "--bin", "box_dyn_fn"])
        .output()
        .expect("failed to run targo check for the revar_is_freeze fixture");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !stderr.contains("region variables should not be hashed"),
        "the Freeze query must not be keyed on inference regions; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("panicked"),
        "bd must reach a verdict, not a panic; stderr: {stderr}"
    );
    assert!(
        !output.status.success(),
        "bd's contract is false (10 / 0 when x == 0) and must be rejected; stderr: {stderr}"
    );
    assert!(
        stderr.contains("bd FAILED"),
        "expected the verifier to reject bd; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("bd verified"),
        "bd must not verify; stderr: {stderr}"
    );
}
