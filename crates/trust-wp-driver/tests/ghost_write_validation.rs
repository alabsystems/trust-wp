// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> std::process::Output {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/ghost_write_validation_tests");
    nested_cargo("check")
        .current_dir(fixture_dir("ghost_write_validation"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for ghost write fixture")
}

#[test]
#[timeout(120_000)]
fn ghost_write_validation_should_fail() {
    let output = run_fixture("should_fail");
    assert!(
        !output.status.success(),
        "expected ghost validation failure; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("cannot write to non-ghost variable in ghost block"),
        "missing direct write error message; stderr: {stderr}",
    );
    assert!(
        stderr.contains("cannot write to field/index of non-ghost variable in ghost block"),
        "missing field/index write error message; stderr: {stderr}",
    );
    assert!(
        stderr.contains("outer.push(1)"),
        "missing mutating-method-call diagnostic for outer.push; stderr: {stderr}",
    );
    assert!(
        stderr.contains("swap(&mut a, &mut b)"),
        "missing mutable-reference escape diagnostic for swap; stderr: {stderr}",
    );
    assert!(
        stderr.contains("let alias = &mut outer"),
        "missing mutable-reference alias diagnostic for local alias to outer; stderr: {stderr}",
    );
    assert!(
        stderr.contains("let alias1 = &mut outer"),
        "missing mutable-reference alias-chain diagnostic for local alias chain to outer; stderr: {stderr}",
    );
    assert!(
        stderr.contains("cell.set(1)"),
        "missing interior-mutability diagnostic for Cell::set; stderr: {stderr}",
    );
    assert!(
        stderr.contains("ref_cell.borrow_mut()"),
        "missing interior-mutability capability-escape diagnostic for RefCell::borrow_mut; stderr: {stderr}",
    );

    // #1877 AC #2: ghost validation errors must halt compilation BEFORE
    // the verification phase runs. All verification output uses "trust-wp: "
    // prefix (e.g., "trust-wp: foo verified ✓", "trust-wp: foo FAILED ✗").
    // Ghost validation errors use rustc's span_err which produces
    // "error: cannot write to ..." messages without the "trust-wp: " prefix.
    let has_verification_output = stderr.lines().any(|line| {
        line.contains("trust-wp:") && (line.contains("verified") || line.contains("FAILED"))
    });
    assert!(
        !has_verification_output,
        "verification should not run when ghost validation errors halt compilation; stderr: {stderr}",
    );
}

#[test]
#[timeout(120_000)]
fn ghost_write_validation_should_pass() {
    let output = run_fixture("should_pass");
    assert!(
        output.status.success(),
        "expected ghost validation success; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
