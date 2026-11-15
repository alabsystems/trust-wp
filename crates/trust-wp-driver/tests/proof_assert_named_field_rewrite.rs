// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration test for #1646: proof_assert named-field rewrite wiring.

use std::{
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::{nested_cargo, trust_wp_rustc_path};

/// The named-field fixture in the user-facing spelling: every field access is
/// written `p.value`. The driver's MIR extraction spells that projection
/// `__trust_wp_tuple_get_0(p)` internally, and the rewrite under test (#1370,
/// #1670) is what makes the two meet in the solver.
const NAMED_FIELD_FIXTURE: &str = r#"#![allow(unexpected_cfgs)]

use trust_wp::{proof_assert, requires};

struct Pair {
    value: i32,
    other: i32,
}

#[requires(p.value == 10)]
fn named_field_assertion_rewrite(p: Pair) {
    proof_assert!(p.value == 10);
}

#[requires(p.value == 10)]
fn named_field_precondition_rewrite(p: Pair) {
    proof_assert!(p.value == 10 && p.other == p.other);
}

fn named_field_generic_arg_rewrite(opt: Option<Pair>) {
    if let Some(p) = opt {
        proof_assert!(p.value == p.value);
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
"#;

/// The same fixture with the driver's INTERNAL projection spelling written
/// by hand in specification text. `__trust_wp_*` is a namespace the
/// verifier synthesizes names in; a source identifier there could stand for
/// a synthesized symbol, so the frontend refuses it
/// (`creusot_frontend_checks::validate_reserved_binding_names`).
const RESERVED_SPELLING_FIXTURE: &str = r#"#![allow(unexpected_cfgs)]

use trust_wp::{proof_assert, requires};

struct Pair {
    value: i32,
    other: i32,
}

#[requires(__trust_wp_tuple_get_0(p) == 10)]
fn named_field_assertion_rewrite(p: Pair) {
    proof_assert!(p.value == 10);
}

fn main() {
    named_field_assertion_rewrite(Pair {
        value: 10,
        other: 0,
    });
}
"#;

fn run_named_field_rewrite_fixture(main_rs: &str, target_subdir: &str) -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    // The clock alone does not separate two tests of this binary that start
    // together (macOS reads it in microseconds), and a shared directory runs
    // one test over the other's `main.rs`; the target name is per test.
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-proof-assert-named-field-{target_subdir}-{}-{unique}",
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

    fs::write(src_dir.join("main.rs"), main_rs).expect("failed to write temp main.rs");

    let target_dir: PathBuf =
        Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../target/{target_subdir}"));

    let output = nested_cargo("check")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet"])
        .output()
        .expect("failed to run targo check for named-field rewrite fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn proof_assert_named_field_rewrite_verify() {
    let output = run_named_field_rewrite_fixture(
        NAMED_FIELD_FIXTURE,
        "proof_assert_tests_verify_named_field",
    );
    let stderr = trust_wp_test_utils::fixture_stderr(&output);

    // Primary assertion: the fixture must compile.
    // Before #1670 fix, `proof_assert!(p.value ...)` produced E0425 scope errors
    // because field names after `.` and function call names were incorrectly
    // captured as free variables in the probe closure.
    assert!(
        !stderr.contains("error[E"),
        "fixture should compile without scope errors; stderr: {stderr}"
    );

    // The crate does not pass as a whole, and that is `main`: it owes its
    // callees' preconditions, so it is a verification target (D-71), and its
    // call to the contract-free `named_field_generic_arg_rewrite` owes
    // `requires(false)` (the opaque-call lane), whose refutation is withheld
    // (D-27). The cost is main's verdict; the xfail control for a caller of a
    // local contract-free callee is s80_contractless_mut_callee_control.rs.
    assert!(
        stderr.contains("trust-wp: main unknown (refutation withheld"),
        "expected main's verdict withheld on the opaque call; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 2 verified, 0 failed, 1 errors")
            && stderr.contains("trust-wp: proof_assert: 3 verified, 0 failed, 0 errors"),
        "expected both contracts and all three assertions credited; stderr: {stderr}"
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

/// A specification that spells the driver's internal projection by hand is
/// refused, with the reason, and verifies nothing. The contract type-check
/// vehicle leaves the reserved spelling untyped on purpose so that this
/// refusal — not an E0425 — is what the user reads.
#[test]
#[timeout(120_000)]
fn reserved_projection_spelling_in_a_spec_is_refused() {
    let output = run_named_field_rewrite_fixture(
        RESERVED_SPELLING_FIXTURE,
        "proof_assert_tests_reserved_spelling",
    );
    let stderr = trust_wp_test_utils::fixture_stderr(&output);

    assert!(
        !output.status.success(),
        "a spec written in the `__trust_wp_` namespace must not compile; stderr: {stderr}"
    );
    assert!(
        stderr.contains("specification identifier `__trust_wp_tuple_get_0` lies in a namespace the verifier synthesizes names in"),
        "expected the reserved-namespace refusal; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("E0425"),
        "the reserved spelling is refused by the frontend, not by name resolution; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("verified ✓"),
        "a refused crate verifies nothing; stderr: {stderr}"
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
    #[doc = "trust-wp:requires:self.x@ + p.0@ <= i32::MAX@ && self.x@ + p.0@ >= i32::MIN@"]
    #[doc = "trust-wp:requires:self.y@ + p.1@ <= i32::MAX@ && self.y@ + p.1@ >= i32::MIN@"]
    #[doc = "trust-wp:ensures:result.x@ == self.x@ + p.0@"]
    #[doc = "trust-wp:ensures:result.y@ == self.y@ + p.1@"]
    fn mov(self, p: (i32, i32)) -> Point {
        Point {
            x: self.x + p.0,
            y: self.y + p.1,
        }
    }
}

#[requires(p.x@ + 1 <= i32::MAX@ && p.x@ + 1 >= i32::MIN@ && p.y@ + 2 <= i32::MAX@ && p.y@ + 2 >= i32::MIN@)]
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

    let output = nested_cargo("check")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet"])
        .output()
        .expect("failed to run targo check for point-mov fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn point_mov_named_adt_field_extraction_compiles() {
    let output = run_point_mov_fixture();
    let stderr = trust_wp_test_utils::fixture_stderr(&output);

    assert!(
        !stderr.contains("error[E"),
        "fixture should compile without extraction errors; stderr: {stderr}"
    );
    assert!(
        stderr.contains("Point::mov verified ✓"),
        "expected Point::mov itself to verify (not merely its caller); stderr: {stderr}"
    );
    assert!(
        stderr.contains("use_mov verified ✓"),
        "expected use_mov to verify; stderr: {stderr}"
    );
    // The crate does not pass as a whole, and that is `main`: it owes
    // `use_mov`'s precondition (D-71), whose `p.x` is placed by the name table
    // of `main`'s own signature, which names no `Point`, so the obligation is
    // stated over an accessor nothing constrains and is refuted. A named field
    // is placed by one signature's table in every lane until every lane places
    // it by the receiver's type (D-170); the cost is this caller's verdict, a
    // refutation of a TRUE call, and its xfail control is
    // call_site_named_field_unmapped_control.rs.
    assert!(
        stderr.contains("trust-wp: main FAILED")
            && stderr.contains("trust-wp: 2 verified, 1 failed, 0 errors"),
        "expected main's call to be refuted on the unplaced field (D-170); stderr: {stderr}"
    );
    assert!(
        !stderr.contains("missing local expression for _4"),
        "Point::mov should not hit the missing-local extraction gap; stderr: {stderr}"
    );
}
