// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #2299: unit-returning `snapshot! { ... }` blocks must
//! preserve leading lemma calls so their postconditions remain visible.

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
        "trust-wp-snapshot-block-lemma-{}-{unique}",
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
            "[package]\nname = \"snapshot-block-lemma-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\ntrust_wp_std = {{ package = \"trust-wp-std\", path = \"{}\" }}\n",
            trust_wp_path.display(),
            trust_wp_std_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use trust_wp::*;

pub enum Tree {
    Node(Box<Tree>, Box<Tree>),
    Leaf,
}

#[logic(open)]
pub fn tree_size(tree: &Tree) -> Int {
    pearlite! {
        match tree {
            Tree::Node(left, right) => 1 + tree_size(left) + tree_size(right),
            Tree::Leaf => 0,
        }
    }
}

impl Tree {
    #[allow(dead_code)]
    #[trusted]
    #[ensures(tree_size(self) >= 0)]
    fn lemma_size_nonneg(&self) {
        let _ = self;
    }
}

#[ensures(true)]
fn snapshot_method_lemma_feeds_proof_assert(t: &Tree) {
    let _snap: Snapshot<()> = snapshot! {
        t.lemma_size_nonneg();
    };
    proof_assert!(tree_size(t) >= 0);
}

#[ensures(tree_size(t) >= 0)]
fn function_contract_from_snapshot_method_lemma(t: &Tree) {
    let _snap: Snapshot<()> = snapshot! {
        t.lemma_size_nonneg();
    };
}

fn main() {
    let t = Tree::Leaf;
    snapshot_method_lemma_feeds_proof_assert(&t);
    function_contract_from_snapshot_method_lemma(&t);
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/snapshot_block_method_lemma_tests");

    let output = Command::new("cargo")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet"])
        .output()
        .expect("failed to run cargo check for snapshot fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn snapshot_block_method_lemma_verifies() {
    let output = run_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("snapshot_method_lemma_feeds_proof_assert verified"),
        "snapshot-fed proof_assert should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: function_contract_from_snapshot_method_lemma verified"),
        "snapshot-fed lemma call should propagate to enclosing function verification; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 2 verified, 0 failed, 0 errors"),
        "expected exact contract summary (2 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary (1 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should verify successfully; stderr: {stderr}"
    );
}
