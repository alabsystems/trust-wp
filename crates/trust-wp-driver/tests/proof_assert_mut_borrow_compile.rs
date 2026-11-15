// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for #2586: `proof_assert!` marker closures must not trigger
//! borrowck errors for live mutable-borrow patterns from `bug/final_borrows.rs`.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Output,
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::{nested_cargo, trust_wp_rustc_path};

fn run_mut_borrow_fixture() -> Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-proof-assert-mut-borrow-{}-{unique}",
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
            "[package]\nname = \"proof-assert-mut-borrow-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\ntrust_wp_std = {{ package = \"trust-wp-std\", path = \"{}\" }}\n",
            trust_wp_path.display(),
            trust_wp_std_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(
        src_dir.join("lib.rs"),
        r#"#![allow(unexpected_cfgs)]
#![allow(unused_variables)]

use trust_wp::*;

#[ensures(true)]
pub fn box_reborrow_direct<T>(mut x: Box<T>) {
    let borrow: &mut T = &mut *x;
    proof_assert! {
        *borrow == *x
    }
}

pub fn shared_borrow_no_gen<T>(bor: &mut T) {
    let b1 = &mut *bor;
    let _shared = &bor;
    proof_assert!(b1 == bor);
}

pub fn inspect_no_gen<T>(x: &mut Option<T>) {
    let r = &mut *x;

    if matches!(x, Some(_)) {
        return;
    }
    proof_assert!(r == x);
}

pub fn place_mention_no_gen<T>(x: &mut Option<T>) {
    let _r = &mut *x;
    let _ = x;
    proof_assert!(_r == x);
}

pub fn shallow_borrow_no_gen(x: &mut Option<i32>) {
    let _r = &mut *x;
    match *x {
        Some(ref inner) if *inner == 2 => {
            proof_assert!(_r == x);
        }
        _ => {}
    }
}

#[ensures(true)]
pub fn write_inner_borrow<'a>(x: &mut &'a mut i32, b: &'a mut i32, value: i32) {
    let r = &mut **x;
    let snap = snapshot!(&mut **x);
    *x = b;
    **x = value;
    proof_assert!(r == *snap);
}
"#,
    )
    .expect("failed to write temp lib.rs");

    let target_dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/proof_assert_tests_verify_mut_borrow");

    let output = nested_cargo("check")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet"])
        .output()
        .expect("failed to run targo check for mut-borrow fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn proof_assert_mut_borrow_patterns_compile_and_verify() {
    let output = run_mut_borrow_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    // The crate's one refused assertion (`write_inner_borrow`, below) fails
    // the build; rustc itself must report no error.
    assert!(
        output.status.success() || !stderr.contains("error["),
        "fixture should compile without borrowck regression; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("error[E0499]")
            && !stderr.contains("error[E0502]")
            && !stderr.contains("error[E0503]"),
        "proof_assert marker must not reintroduce borrowck errors; stderr: {stderr}"
    );

    for fn_path in [
        "proof_assert_mut_borrow_fixture::box_reborrow_direct",
        "proof_assert_mut_borrow_fixture::shared_borrow_no_gen",
        "proof_assert_mut_borrow_fixture::inspect_no_gen",
        "proof_assert_mut_borrow_fixture::place_mention_no_gen",
        "proof_assert_mut_borrow_fixture::shallow_borrow_no_gen",
    ] {
        assert!(
            stderr.contains(&format!("proof_assert in {fn_path} verified")),
            "expected verified proof_assert output for {fn_path}; stderr: {stderr}"
        );
    }
    // `write_inner_borrow` reads the borrow `r` after `**x = value` writes
    // through `x`, whose alias class `r` (a reborrow of `**x`) is in. Which
    // memory that store reaches depends on the redirect `*x = b` before it,
    // which the alias analysis does not follow, so the assertion reads `r`
    // at a state the lane does not know and is refused (D-185): a TRUE
    // assertion, not credited and not refuted.
    assert!(
        stderr.contains(
            "proof_assert in proof_assert_mut_borrow_fixture::write_inner_borrow error: stale \
             read refused (fail-closed)"
        ),
        "expected write_inner_borrow's read of `r` refused as stale (D-185); stderr: {stderr}"
    );

    let proof_assert_summary = stderr
        .lines()
        .find(|line| line.starts_with("trust-wp: proof_assert:"))
        .expect("expected proof_assert summary line");
    assert!(
        proof_assert_summary.contains("0 failed, 1 errors"),
        "expected proof_assert summary with no failures and the one refusal; stderr: {stderr}"
    );
    assert!(
        !stderr.lines().any(|line| {
            line.contains("proof_assert in proof_assert_mut_borrow_fixture::")
                && line.contains(" FAILED")
        }),
        "proof_assert marker fixture should not have proof_assert failures; stderr: {stderr}"
    );
}
