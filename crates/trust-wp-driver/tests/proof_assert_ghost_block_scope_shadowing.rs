// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #994: substitutions from a dead ghost-block local must
//! not leak into a later ghost block that reuses the same source name.

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
        "trust-wp-ghost-block-scope-shadowing-{}-{unique}",
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
            "[package]\nname = \"ghost-block-scope-shadowing-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\ntrust_wp_std = {{ package = \"trust-wp-std\", path = \"{}\" }}\n",
            trust_wp_path.display(),
            trust_wp_std_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use trust_wp::*;

#[ensures(true)]
fn ghost_block_scope_shadowing() {
    let _ = ghost! {
        let x = 1i32;
        let alias_first_block_only = x + 1;
        proof_assert!(alias_first_block_only == 2);
    };

    let _ = ghost! {
        let x = 2i32;
        proof_assert!(x == 2);
    };
}

fn main() {
    ghost_block_scope_shadowing();
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/ghost_block_scope_shadowing");

    let output = nested_cargo("check")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify --verbose")
        .args(["--quiet"])
        .output()
        .expect("failed to run targo check for ghost block scope fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn later_ghost_block_does_not_inherit_dead_local_aliases() {
    let output = run_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "expected both proof_asserts to verify; stderr: {stderr}"
    );

    let last_segment = stderr
        .split("trust-wp: verifying proof_assert")
        .filter(|segment| !segment.trim().is_empty())
        .last()
        .expect("expected at least one proof_assert segment");

    assert!(
        !last_segment.contains("alias_first_block_only"),
        "dead first-block alias leaked into later proof_assert scope; final segment: {last_segment}"
    );
}
