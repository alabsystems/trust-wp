// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #2325: in-ghost `snapshot!` bindings immediately
//! preceding an in-ghost `proof_assert!` must keep the proof assertions verified.
//!
//! Root cause: `__trust_wp_tuple0()` sort inference fell through to `Sort::Int`
//! instead of `unit_sort()`, firing `SortFallbackToIntFromLogicFn` (a demoting
//! unsoundness category) and causing all proof_asserts in the function to be
//! demoted from Verified to Unknown.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::trust_wp_rustc_path;

fn run_fixture() -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-ghost-snapshot-subst-{}-{unique}",
        std::process::id()
    ));
    let src_dir = fixture_dir.join("src");
    fs::create_dir_all(&src_dir).expect("failed to create temp fixture directory");

    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("failed to resolve workspace root");
    let trust_wp_path = workspace_root.join("crates/trust-wp");
    let trust_wp_std_path = workspace_root.join("crates/trust-wp-std");

    fs::write(
        fixture_dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"ghost-snapshot-subst-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\ntrust_wp_std = {{ package = \"trust-wp-std\", path = \"{}\" }}\n",
            trust_wp_path.display(),
            trust_wp_std_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    // Native trust-wp driver fixture for the #2325 lane:
    // ghost block → snapshot binding → proof_assert on the snapshot.
    //
    // Direct driver fixtures reject writes to non-ghost outer locals inside
    // `ghost!`, so this uses a local `Snapshot<T>` binding rather than the
    // creusot-compat assignment form. The exercised sort path is the same:
    // `snapshot!` lowers through a unit-typed helper path that must infer
    // `__trust_wp_tuple0()` as `unit_sort()` rather than `Sort::Int`.
    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use trust_wp::*;

#[ensures(true)]
fn snapshot_in_ghost_then_proof_assert() {
    let _ = ghost! {
        let g_mut: Snapshot<i32> = snapshot!(3i32);
        proof_assert!(g_mut@ == 3);

        let g_next: Snapshot<i32> = snapshot!(4i32);
        proof_assert!(g_next@ == 4);
    };
}

fn main() {
    snapshot_in_ghost_then_proof_assert();
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/ghost_snapshot_subst_tests");

    let output = Command::new("cargo")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet"])
        .output()
        .expect("failed to run cargo check for ghost snapshot fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn in_ghost_snapshot_binding_then_proof_assert_verifies() {
    let output = run_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    // The proof_assert inside the ghost block must produce output.
    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );

    // The in-ghost proof_asserts must verify (not be demoted to unknown/failure).
    assert!(
        !stderr.contains("proof_assert") || !stderr.contains("FAILED"),
        "in-ghost snapshot proof_assert must not fail; stderr: {stderr}"
    );

    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "expected both in-ghost proof_asserts to verify; stderr: {stderr}"
    );

    // The enclosing function currently demotes for an unrelated opaque-call
    // assumption, so this test scopes itself to the proof_assert lane.
    assert!(
        !stderr.contains("sort_fallback_to_int_from_logic_fn"),
        "unit tuple sort inference must not trigger sort fallback demotion; stderr: {stderr}"
    );

    // Regression for #2333: the `Resolve::resolve` spec-only panic stub lowers
    // to `Call { target: None }` in MIR. The primary extractor must treat this
    // as a dead-end bail, not emit an UnsupportedTerminator warning.
    assert!(
        !stderr.contains("Call terminator has no continuation target"),
        "diverging call must not emit UnsupportedTerminator warning (#2333); stderr: {stderr}"
    );
}
