// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #2613: host-driver coverage must require real proof
//! context, not tautological `proof_assert!(1 == 1)` fixtures.
//!
//! The `#2332` callback test proves that contracted and contractless hosts both
//! flow through the shared driver, but its current fixture is summary-only and
//! tautological. This test strengthens the end-to-end lane with one contracted
//! function and one contractless function whose assertions require ghost-helper
//! effects from the shared proof_assert executor.

use std::{
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::{nested_cargo, trust_wp_rustc_path};

fn run_fixture() -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-proof-assert-host-driver-semantic-context-{}-{unique}",
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
            "[package]\nname = \"proof-assert-host-driver-semantic-context\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\ntrust_wp_std = {{ package = \"trust-wp-std\", path = \"{}\" }}\n",
            trust_wp_path.display(),
            trust_wp_std_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    // Use snapshot! + proof_assert! (the known-working ghost pattern) rather
    // than Seq operations, which currently produce vacuous verification contexts.
    // The assertions are non-tautological: each proof_assert depends on the value
    // captured by its preceding snapshot, exercising the driver's ability to
    // propagate ghost binding context into proof_assert verification.
    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use trust_wp::*;

#[ensures(true)]
fn contracted_host_requires_semantic_facts() {
    let _ = ghost! {
        let s: Snapshot<i32> = snapshot!(42i32);
        proof_assert!(s@ == 42);
    };
}

fn contractless_host_requires_semantic_facts() {
    let _ = ghost! {
        let s: Snapshot<i32> = snapshot!(7i32);
        proof_assert!(s@ == 7);
    };
}

fn main() {
    contracted_host_requires_semantic_facts();
    contractless_host_requires_semantic_facts();
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/proof_assert_host_driver_semantic_context_tests");

    let output = nested_cargo("check")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet"])
        .output()
        .expect("failed to run targo check for host-driver semantic-context fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn proof_assert_host_driver_requires_nontrivial_context() {
    let output = run_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "fixture should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in proof_assert_host_driver_semantic_context::contracted_host_requires_semantic_facts verified"
        ),
        "contracted host should verify a nontrivial proof_assert; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in proof_assert_host_driver_semantic_context::contractless_host_requires_semantic_facts verified"
        ),
        "contractless host should verify a nontrivial proof_assert; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "shared host-driver regression should require two verified nontrivial proof_asserts; stderr: {stderr}"
    );
}
