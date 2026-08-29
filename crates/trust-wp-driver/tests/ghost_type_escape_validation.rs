// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for ghost-type escape signature validation (#2686).
//!
//! Covers the recovered should-fail compat shapes from
//! `generic_deref_ghost.rs` / `generic_deref_snap.rs` and nearby
//! signatures that must remain accepted. The check is body-level: ghost
//! parameters are legal proof authority unless ghost-derived data reaches a
//! runtime return or branch.

use std::{path::Path, process::Command};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/ghost_type_escape_tests");
    Command::new("cargo")
        .current_dir(fixture_dir("ghost_type_escape_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for ghost type escape fixture")
}

#[test]
#[timeout(120_000)]
fn ghost_type_escape_validation_should_fail_on_non_ghost_return() {
    let output = run_fixture("should_fail");
    assert!(
        !output.status.success(),
        "expected ghost type escape failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("ghost type escape"),
        "missing ghost type escape diagnostic; stderr: {stderr}",
    );
    assert!(
        stderr.contains("bad_ghost_escape"),
        "missing Ghost<T> rejection site; stderr: {stderr}",
    );
    assert!(
        stderr.contains("bad_snapshot_escape"),
        "missing Snapshot<T> rejection site; stderr: {stderr}",
    );
    assert!(
        stderr.contains("bad_ghost_ref_escape"),
        "missing Ghost<&T> rejection site; stderr: {stderr}",
    );
    assert!(
        stderr.contains("bad_ghost_ref_escape_with_runtime_source"),
        "missing Ghost<&T> rejection with non-ghost source site; stderr: {stderr}",
    );
    assert!(
        stderr.contains("returns non-ghost type `i32`"),
        "missing non-ghost return detail; stderr: {stderr}",
    );

    let has_verification_output = stderr.lines().any(|line| {
        line.contains("trust-wp:") && (line.contains("verified") || line.contains("FAILED"))
    });
    assert!(
        !has_verification_output,
        "verification should not run after signature rejection; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_type_escape_validation_should_pass_for_allowed_signatures() {
    let output = run_fixture("should_pass");
    assert!(
        output.status.success(),
        "expected allowed ghost signatures to compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("ghost type escape"),
        "allowed signature fixture must not emit ghost type escape errors; stderr: {stderr}",
    );
}
