// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration test for #1646: proof_assert named-field rewrite wiring.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::trust_wp_rustc_path;

fn run_named_field_rewrite_fixture() -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-proof-assert-named-field-{}-{unique}",
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
            "[package]\nname = \"proof-assert-named-field-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\n",
            trust_wp_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use trust_wp::{proof_assert, requires};

struct Pair {
    value: i32,
    other: i32,
}

#[requires(__trust_wp_tuple_get_0(p) == 10)]
fn named_field_assertion_rewrite(p: Pair) {
    proof_assert!(p.value == 10);
}

#[requires(p.value == 10)]
fn named_field_precondition_rewrite(p: Pair) {
    proof_assert!(__trust_wp_tuple_get_0(p) == 10);
}

fn named_field_generic_arg_rewrite(opt: Option<Pair>) {
    if let Some(p) = opt {
        proof_assert!(p.value == __trust_wp_tuple_get_0(p));
    }
}

fn main() {
    named_field_assertion_rewrite(Pair {
        value: 10,
        other: 0,
    });
    named_field_precondition_rewrite(Pair {
        value: 10,
        other: 1,
    });
    named_field_generic_arg_rewrite(Some(Pair {
        value: 3,
        other: 7,
    }));
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/proof_assert_tests_verify_named_field");

    let output = Command::new("cargo")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet"])
        .output()
        .expect("failed to run cargo check for named-field rewrite fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn proof_assert_named_field_rewrite_verify() {
    let output = run_named_field_rewrite_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Primary assertion: the fixture must compile.
    // Before #1670 fix, `proof_assert!(p.value ...)` produced E0425 scope errors
    // because field names after `.` and function call names were incorrectly
    // captured as free variables in the probe closure.
    assert!(
        output.status.success(),
        "fixture should compile without scope errors; stderr: {stderr}"
    );

    // Contract verification: functions with #[requires] should be found and verified
    assert!(
        stderr.contains("named_field_assertion_rewrite"),
        "expected named_field_assertion_rewrite in verification output; stderr: {stderr}"
    );
    assert!(
        stderr.contains("named_field_precondition_rewrite"),
        "expected named_field_precondition_rewrite in verification output; stderr: {stderr}"
    );
    assert!(
        stderr.contains("verified"),
        "expected at least one function to verify; stderr: {stderr}"
    );
}

fn run_point_mov_fixture() -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-point-mov-named-adt-{}-{unique}",
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
            "[package]\nname = \"point-mov-named-adt-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\n",
            trust_wp_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use trust_wp::requires;

#[derive(Clone, Copy)]
struct Point {
    x: i32,
    y: i32,
}

impl Point {
    #[doc(hidden)]
    #[doc = "trust-wp:ensures:result.x == self.x + p.0"]
    #[doc = "trust-wp:ensures:result.y == self.y + p.1"]
    fn mov(self, p: (i32, i32)) -> Point {
        Point {
            x: self.x + p.0,
            y: self.y + p.1,
        }
    }
}

#[requires(true)]
fn use_mov(p: Point) {
    let _ = p.mov((1, 2));
}

fn main() {
    use_mov(Point { x: 0, y: 0 });
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/proof_assert_tests_point_mov");

    let output = Command::new("cargo")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet"])
        .output()
        .expect("failed to run cargo check for point-mov fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn point_mov_named_adt_field_extraction_compiles() {
    let output = run_point_mov_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "fixture should compile without extraction errors; stderr: {stderr}"
    );
    assert!(
        stderr.contains("Point::mov"),
        "expected Point::mov in verification output; stderr: {stderr}"
    );
    assert!(
        stderr.contains("verified"),
        "expected the Point::mov fixture to verify; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("missing local expression for _4"),
        "Point::mov should not hit the missing-local extraction gap; stderr: {stderr}"
    );
}
