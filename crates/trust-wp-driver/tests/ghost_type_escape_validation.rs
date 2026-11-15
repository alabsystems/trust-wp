// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for ghost-type escape signature validation (#2686).
//!
//! Covers the recovered should-fail compat shapes from
//! `generic_deref_ghost.rs` / `generic_deref_snap.rs` and nearby
//! signatures that must remain accepted. The check is body-level: ghost
//! parameters are legal proof authority unless ghost-derived data reaches a
//! runtime return or branch. The compat shapes reach the ghost's `Deref`
//! through a generic bound, which runs at run time and panics, so the
//! program-context ghost validator refuses each call before this check
//! runs (D-193); the should-fail half asserts that refusal at every site.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/ghost_type_escape_tests");
    nested_cargo("check")
        .current_dir(fixture_dir("ghost_type_escape_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for ghost type escape fixture")
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

    // One refusal per `deref_wrap` call, named by the ghost type whose
    // `Deref` the call's bound runs: `bad_ghost_escape`,
    // `bad_ghost_deref_in_unit_fn` and `bad_ghost_deref_in_check_ghost_fn`
    // on `Ghost<i32>`, `bad_snapshot_escape` on `Snapshot<i32>`, and the two
    // `bad_ghost_ref_escape*` on `Ghost<&i32>`.
    let stderr = String::from_utf8_lossy(&output.stderr);
    let refusals = |ghost_ty: &str| {
        stderr
            .lines()
            .filter(|line| {
                line.contains(&format!("{ghost_ty} as Deref>` runs outside ghost!(...)"))
                    && line.contains("where its run-time body is not the logical operation")
            })
            .count()
    };
    assert_eq!(
        refusals("Ghost<i32>"),
        3,
        "expected the Ghost<i32> deref refused in bad_ghost_escape, \
         bad_ghost_deref_in_unit_fn and bad_ghost_deref_in_check_ghost_fn; stderr: {stderr}",
    );
    assert_eq!(
        refusals("Snapshot<i32>"),
        1,
        "expected the Snapshot<i32> deref refused in bad_snapshot_escape; stderr: {stderr}",
    );
    assert_eq!(
        refusals("Ghost<&i32>"),
        2,
        "expected the Ghost<&i32> deref refused in both bad_ghost_ref_escape sites; \
         stderr: {stderr}",
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
