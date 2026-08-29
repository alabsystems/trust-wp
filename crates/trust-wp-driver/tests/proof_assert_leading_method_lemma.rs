// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #2299: leading lemma calls inside `proof_assert!`
//! must feed both the proof_assert VC and the enclosing function contract.

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
        "trust-wp-proof-assert-leading-lemma-{}-{unique}",
        std::process::id()
    ));
    let src_dir = fixture_dir.join("src");
    fs::create_dir_all(&src_dir).expect("failed to create temp fixture directory");

    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("failed to resolve workspace root");
    let trust_wp_path = workspace_root.join("crates/trust-wp");

    fs::write(
        fixture_dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"proof-assert-leading-lemma-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\n",
            trust_wp_path.display()
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
fn proof_assert_leading_method_lemma(t: &Tree) {
    proof_assert! {
        t.lemma_size_nonneg();
        tree_size(t) >= 0
    };
}

#[ensures(tree_size(t) >= 0)]
fn function_contract_from_leading_method_lemma(t: &Tree) {
    proof_assert! {
        t.lemma_size_nonneg();
        true
    };
}

fn main() {
    let t = Tree::Leaf;
    proof_assert_leading_method_lemma(&t);
    function_contract_from_leading_method_lemma(&t);
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/proof_assert_tests_verify_leading_lemma");

    let output = Command::new("cargo")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet"])
        .output()
        .expect("failed to run cargo check for proof_assert fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn proof_assert_leading_method_lemma_verify() {
    let output = run_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in ")
            && stderr.contains("proof_assert_leading_method_lemma verified"),
        "leading lemma call should verify inside proof_assert; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: function_contract_from_leading_method_lemma verified"),
        "leading lemma call should propagate to enclosing function verification; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 2 verified, 0 failed, 0 errors"),
        "expected exact contract summary (2 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary (2 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
    assert!(
        stderr.contains("2 assumed"),
        "trusted leading lemma calls should remain visible as assumptions; stderr: {stderr}"
    );
    assert!(
        !output.status.success(),
        "fixture has trusted proof_assert assumptions and should not be a clean proof; stderr: {stderr}"
    );
}
