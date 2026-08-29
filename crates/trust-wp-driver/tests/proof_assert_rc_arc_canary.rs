// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #976: the Rc/Arc proof-assert canary from
//! `arc_and_rc.rs` must verify through the live proof-assert path.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::trust_wp_rustc_path;

#[allow(clippy::too_many_lines)]
fn run_fixture() -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-proof-assert-rc-arc-{}-{unique}",
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
            "[package]\nname = \"proof_assert_rc_arc_canary_fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\n",
            trust_wp_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use std::{rc::Rc, sync::Arc};

use trust_wp::proof_assert;

fn rc_deref_view() {
    let rc = Rc::new(1);
    proof_assert!(*rc@ == 1i32);
}

fn rc_as_ref_view() {
    let rc = Rc::new(1);
    let inner = rc.as_ref();
    proof_assert!(inner@ == 1);
}

fn rc_eq_clone() {
    let rc = Rc::new(1);
    let rc2 = rc.clone();
    proof_assert!(rc == rc2);
}

fn rc_ptr_eq_clone() {
    let rc = Rc::new(1);
    let rc2 = rc.clone();
    let b = Rc::ptr_eq(&rc, &rc2);
    proof_assert!(b);
}

fn rc_ptr_eq_distinct() {
    let rc = Rc::new(1);
    let rc3 = Rc::new(2);
    let b2 = Rc::ptr_eq(&rc, &rc3);
    proof_assert!(!b2);
}

fn arc_deref_view() {
    let arc = Arc::new(1);
    proof_assert!(*arc@ == 1i32);
}

fn arc_as_ref_view() {
    let arc = Arc::new(1);
    let inner = arc.as_ref();
    proof_assert!(inner@ == 1);
}

fn arc_eq_clone() {
    let arc = Arc::new(1);
    let arc2 = arc.clone();
    proof_assert!(arc == arc2);
}

fn arc_ptr_eq_clone() {
    let arc = Arc::new(1);
    let arc2 = arc.clone();
    let b = Arc::ptr_eq(&arc, &arc2);
    proof_assert!(b);
}

fn arc_ptr_eq_distinct() {
    let arc = Arc::new(1);
    let arc3 = Arc::new(2);
    let b2 = Arc::ptr_eq(&arc, &arc3);
    proof_assert!(!b2);
}

fn main() {
    rc_deref_view();
    rc_as_ref_view();
    rc_eq_clone();
    rc_ptr_eq_clone();
    rc_ptr_eq_distinct();
    arc_deref_view();
    arc_as_ref_view();
    arc_eq_clone();
    arc_ptr_eq_clone();
    arc_ptr_eq_distinct();
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/proof_assert_tests_verify_rc_arc");

    let output = Command::new("cargo")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet"])
        .output()
        .expect("failed to run cargo check for Rc/Arc proof_assert fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn proof_assert_rc_arc_canary_verify() {
    let output = run_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr
            .contains("proof_assert in proof_assert_rc_arc_canary_fixture::rc_deref_view verified"),
        "expected rc_deref_view proof_assert to verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in proof_assert_rc_arc_canary_fixture::arc_ptr_eq_distinct verified"
        ),
        "expected arc_ptr_eq_distinct proof_assert to verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in proof_assert_rc_arc_canary_fixture::rc_eq_clone verified"),
        "expected rc_eq_clone proof_assert to verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 10 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary for the Rc/Arc canary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "Rc/Arc proof_assert fixture should verify successfully; stderr: {stderr}"
    );
}
