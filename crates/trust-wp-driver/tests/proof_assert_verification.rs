// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for `proof_assert!` verification.
//!
//! These tests verify that:
//! 1. `proof_assert!(expr)` succeeds when `expr` follows from preconditions
//! 2. `proof_assert!(expr)` fails when `expr` doesn't follow from preconditions

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{Mutex, OnceLock},
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, trust_wp_rustc_fixture_target_dir, trust_wp_rustc_path};

fn proof_assert_fixture_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn run_fixture_with_trust_wp_args(bin: &str, trust_wp_args: Option<&str>) -> std::process::Output {
    let _fixture_guard = proof_assert_fixture_lock()
        .lock()
        .expect("proof_assert fixture lock poisoned");

    // Use separate target dirs for verify vs non-verify runs (#902).
    // TRUST_WP_ARGS is read by trust-wp-rustc at compile time but is invisible to
    // cargo's fingerprinting, so verify and non-verify invocations of the same
    // fixture binary must not share a cargo cache.
    let suffix = if trust_wp_args.is_some() {
        "verify"
    } else {
        "nocheck"
    };
    let target_dir = trust_wp_rustc_fixture_target_dir(&format!("proof_assert_tests_{suffix}"));

    let mut cmd = Command::new("cargo");
    cmd.current_dir(fixture_dir("proof_assert"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path());

    if let Some(args) = trust_wp_args {
        cmd.env("TRUST_WP_ARGS", args);
    }

    cmd.args(["check", "--quiet", "--bin", bin])
        .output()
        .expect("failed to run cargo check for proof_assert fixture")
}

fn run_fixture(bin: &str, verify: bool) -> std::process::Output {
    let trust_wp_args = if verify { Some("--verify") } else { None };
    run_fixture_with_trust_wp_args(bin, trust_wp_args)
}

fn assert_proof_assert_rejected(stderr: &str, fn_path: &str) {
    let failed_line = format!("proof_assert in {fn_path} FAILED");
    let unknown_line = format!("proof_assert in {fn_path} unknown");
    assert!(
        stderr.contains(&failed_line) || stderr.contains(&unknown_line),
        "expected proof_assert rejection ({failed_line} or {unknown_line}); stderr: {stderr}"
    );
}

fn assert_single_rejection_summary(stderr: &str) {
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified, 1 failed, 0 errors")
            || stderr.contains("trust-wp: proof_assert: 0 verified, 0 failed, 1 errors"),
        "expected single rejection summary (failed or unknown); stderr: {stderr}"
    );
}

fn run_inline_quantifier_fixture() -> std::process::Output {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    let fixture_dir = std::env::temp_dir().join(format!(
        "trust-wp-proof-assert-quantifier-{}-{unique}",
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
            "[package]\nname = \"proof-assert-inline-fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\ntrust_wp = {{ package = \"trust-wp\", path = \"{}\" }}\n",
            trust_wp_path.display()
        ),
    )
    .expect("failed to write temp Cargo.toml");

    fs::write(
        src_dir.join("main.rs"),
        r#"#![allow(unexpected_cfgs)]

use trust_wp::proof_assert;

fn quantifier_syntax_verify() {
    proof_assert!(forall<x: i32> x >= 0 ==> x >= 0);
    proof_assert!(exists<y: i32> y == y);
}

fn main() {
    quantifier_syntax_verify();
}
"#,
    )
    .expect("failed to write temp main.rs");

    let target_dir: PathBuf = trust_wp_rustc_fixture_target_dir("proof_assert_tests_verify_inline");

    let output = Command::new("cargo")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["check", "--quiet"])
        .output()
        .expect("failed to run cargo check for inline quantifier fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(120_000)]
fn proof_assert_should_verify() {
    let output = run_fixture("should_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Check that proof_assert verification ran
    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );

    // Assert specific function verification results (not just absence of FAILED)
    assert!(
        stderr.contains("proof_assert in should_verify::positive_implies_non_negative verified"),
        "positive_implies_non_negative should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in should_verify::and_implies_left verified"),
        "and_implies_left should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in should_verify::sum_is_non_negative verified"),
        "sum_is_non_negative should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 3 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary (3 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
}

/// Regression for #1279: proof_assert must accept and verify
/// Creusot quantifier/implication syntax.
#[test]
#[timeout(120_000)]
fn proof_assert_quantifier_syntax_verify() {
    let output = run_inline_quantifier_fixture();
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in proof_assert_inline_fixture::quantifier_syntax_verify verified"
        ),
        "quantifier implication assertion should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "expected 2 verified, 0 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

#[test]
#[timeout(120_000)]
fn proof_assert_should_fail() {
    let output = run_fixture("should_fail", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Check that proof_assert verification ran and found a failure
    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );

    // Assert the specific function failed with a counterexample
    assert!(
        stderr.contains("proof_assert in should_fail::non_negative_does_not_imply_positive FAILED"),
        "non_negative_does_not_imply_positive must fail (x >= 0 does not imply x > 0); stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified, 1 failed, 0 errors"),
        "expected exact proof_assert summary (0 verified, 1 failed, 0 errors); stderr: {stderr}"
    );
}

/// Regression for #1424: repeated writes to the same projected path must
/// invalidate earlier projected-write assumptions (last-write-wins).
///
/// Before the fix, extraction retained both `pair.0 == 5` and `pair.0 == 7`,
/// allowing `proof_assert!(pair.0@ == 5)` to verify vacuously.
#[test]
#[timeout(120_000)]
fn proof_assert_contradictory_projected_writes_should_fail() {
    let output = run_fixture("contradictory_projected_writes_should_fail", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert_proof_assert_rejected(
        &stderr,
        "contradictory_projected_writes_should_fail::contradictory_projected_writes_should_fail",
    );
    assert_single_rejection_summary(&stderr);
}

/// Regression: whole-local reassignment must invalidate older projected-write
/// assumptions from the same base local.
///
/// Sequence under test:
/// - `pair.0 = 5` (projected-write fact)
/// - `pair = (7,)` (whole-local overwrite)
/// - `proof_assert!(pair.0@ == 5)` must fail.
#[test]
#[timeout(120_000)]
fn proof_assert_projected_write_then_whole_reassign_should_fail() {
    let output = run_fixture("projected_write_then_whole_reassign_should_fail", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert_proof_assert_rejected(
        &stderr,
        "projected_write_then_whole_reassign_should_fail::projected_write_then_whole_reassign_should_fail",
    );
    assert_single_rejection_summary(&stderr);
}

/// Regression test for #1450 AC2: non-constant whole-local reassignment must
/// clear stale projected-write facts. Uses a function parameter (symbolic value)
/// to exercise the soundness-critical path where constant folding doesn't mask
/// the stale fact.
#[test]
#[timeout(120_000)]
fn proof_assert_stale_projected_write_symbolic_reassign_should_fail() {
    let output = run_fixture("stale_projected_write_symbolic_reassign_should_fail", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert_proof_assert_rejected(
        &stderr,
        "stale_projected_write_symbolic_reassign_should_fail::stale_projected_write_symbolic_reassign",
    );
    assert_single_rejection_summary(&stderr);
}

/// Regression for #1500: assigning a parent projected path (for example `pair.0`)
/// must invalidate stale nested-path facts (for example `pair.0.1`).
#[test]
#[timeout(120_000)]
fn proof_assert_projected_substruct_overwrite_should_fail() {
    let output = run_fixture("projected_substruct_overwrite_should_fail", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert_proof_assert_rejected(
        &stderr,
        "projected_substruct_overwrite_should_fail::projected_substruct_overwrite_should_fail",
    );
    assert_single_rejection_summary(&stderr);
}

/// Regression test for #815: branch-local call assumptions must not leak globally
/// and call preconditions must be enforced in proof_assert path.
///
/// This fixture contains two functions that SHOULD FAIL verification:
/// 1. `branch_unsound`: postcondition leaks from if-branch to global scope
/// 2. `precondition_unsound`: postcondition assumed without proving precondition
///
/// Both functions should FAIL verification.
#[test]
#[timeout(120_000)]
fn proof_assert_soundness_815_branch_leak() {
    let output = run_fixture("soundness_815_branch_leak", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Check that proof_assert verification ran
    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );

    // branch_unsound: x > 0 only holds inside the if-branch
    assert!(
        stderr.contains("proof_assert in soundness_815_branch_leak::branch_unsound FAILED"),
        "branch-local assumption leak must fail; stderr: {stderr}"
    );
    // precondition_unsound: id_pos requires x > 0, not proven at call site
    assert!(
        stderr.contains("proof_assert in soundness_815_branch_leak::precondition_unsound FAILED"),
        "missing call precondition must fail; stderr: {stderr}"
    );
    // Require exact proof_assert summary for this fixture to avoid
    // false positives from partial matches.
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified, 2 failed, 0 errors"),
        "expected exact proof_assert summary (0 verified, 2 failed, 0 errors); stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; proof_assert failures are asserted through the proof_assert summary; stderr: {stderr}"
    );
}

/// Regression test for #816: bool-returning call specs must not ICE.
///
/// When a function returns bool and has predicate-style ensures, the
/// proof_assert path previously panicked with
/// `BUG: mk_eq expects same sort, got Int = Bool`.
///
/// Fixed in 82c9f53b: sort annotation propagation from MIR type info.
#[test]
#[timeout(120_000)]
fn proof_assert_soundness_816_bool_ice() {
    let output = run_fixture("soundness_816_bool_ice", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Must not crash with sort mismatch ICE (#816, fixed in 82c9f53b).
    assert!(
        !stderr.contains("panicked") && !stderr.contains("BUG: mk_eq"),
        "fixture must not crash with sort mismatch; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile without ICE (#816); stderr: {stderr}"
    );
    // This fixture may either verify or fail depending on surrounding call-spec
    // reasoning, but it must report a concrete verification outcome.
    let verified_line = "proof_assert in soundness_816_bool_ice::bool_call_no_crash verified";
    let failed_line = "proof_assert in soundness_816_bool_ice::bool_call_no_crash FAILED";
    assert!(
        stderr.contains(verified_line) || stderr.contains(failed_line),
        "expected concrete proof_assert outcome for bool_call_no_crash; stderr: {stderr}"
    );
    let verified_summary = "trust-wp: proof_assert: 1 verified, 0 failed, 0 errors";
    let failed_summary = "trust-wp: proof_assert: 0 verified, 1 failed, 0 errors";
    assert!(
        stderr.contains(verified_summary) || stderr.contains(failed_summary),
        "expected exact proof_assert summary (verified or failed, zero errors); stderr: {stderr}"
    );
}

/// Soundness test for #817 AC1: branch-scoped call assumptions.
///
/// Tests that call postconditions are correctly scoped to the branch
/// in which the call occurs:
/// - `branch_scoped_verify`: proof_assert INSIDE branch should verify
/// - `branch_scoped_fail`: proof_assert OUTSIDE branch should fail
#[test]
#[timeout(120_000)]
fn proof_assert_callspec_branch_scope() {
    let output = run_fixture("callspec_branch_scope", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    // The within-branch assertion should verify (path condition + call spec).
    assert!(
        stderr.contains("proof_assert in callspec_branch_scope::branch_scoped_verify verified"),
        "branch-scoped call assumption should verify within branch; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("trust-wp: branch_scoped_verify FAILED"),
        "branch-scoped proof_assert fixture must not introduce a function-level failure; stderr: {stderr}"
    );
    // The post-branch assertion should fail (assumption must not leak).
    assert!(
        stderr.contains("proof_assert in callspec_branch_scope::branch_scoped_fail FAILED"),
        "post-branch assertion without assumption must fail; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 1 failed, 0 errors"),
        "expected 1 verified, 1 failed; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; proof_assert failure is asserted through the proof_assert summary; stderr: {stderr}"
    );
}

/// Soundness test for #817 AC2: callee precondition obligations.
///
/// Tests that calling a function with a `requires` clause generates
/// a proper obligation:
/// - `precondition_met_verify`: precondition satisfied, assertion verifies
/// - `precondition_violated_fail`: precondition violated, assertion fails
#[test]
#[timeout(120_000)]
fn proof_assert_callspec_precondition_obligation() {
    let output = run_fixture("callspec_precondition_obligation", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in callspec_precondition_obligation::precondition_met_verify verified"
        ),
        "call with met precondition should verify; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("trust-wp: positive_identity unknown"),
        "callee helper should verify cleanly so this fixture only exercises proof_assert verdicts; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in callspec_precondition_obligation::precondition_violated_fail FAILED"
        ),
        "call with violated precondition should fail; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 1 failed, 0 errors"),
        "expected 1 verified, 1 failed; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; proof_assert failure is asserted through the proof_assert summary; stderr: {stderr}"
    );
}

/// Regression test for #927: nested branch obligations from both ITE arms
/// must be enforced with branch guards, not treated as global assumptions.
#[test]
#[timeout(120_000)]
fn proof_assert_callspec_multibranch_obligation() {
    let output = run_fixture("callspec_multibranch_obligation", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in callspec_multibranch_obligation::multibranch_obligation_unsound FAILED"
        ),
        "multi-branch obligation gap must fail verification; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified, 1 failed, 0 errors"),
        "expected 0 verified, 1 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; proof_assert failure is asserted through the proof_assert summary; stderr: {stderr}"
    );
}

/// Soundness test for #817 AC3: bool-returning call specs in proof_assert path.
///
/// Tests that functions returning bool with predicate-style ensures
/// produce correct verification results (not just absence of crash):
/// - `bool_call_verify`: precondition met, assertion verifies
/// - `bool_call_fail`: precondition violated, assertion fails
#[test]
#[timeout(120_000)]
fn proof_assert_callspec_bool_return() {
    let output = run_fixture("callspec_bool_return", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    // Must not crash (extends #816 regression coverage).
    assert!(
        !stderr.contains("panicked") && !stderr.contains("BUG: mk_eq"),
        "must not crash with sort mismatch; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in callspec_bool_return::bool_call_verify verified"),
        "bool call with met precondition should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in callspec_bool_return::bool_call_fail FAILED"),
        "bool call with violated precondition should fail; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 1 failed, 0 errors"),
        "expected 1 verified, 1 failed; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; proof_assert failure is asserted through the proof_assert summary; stderr: {stderr}"
    );
}

/// Program-point regression for #746:
/// proof_assert extraction must stop at the assertion span so unsupported
/// tail MIR does not block call-spec reasoning before the assertion.
#[test]
#[timeout(120_000)]
fn proof_assert_callspec_before_unsupported_tail() {
    let output = run_fixture("callspec_before_unsupported_tail", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in callspec_before_unsupported_tail::callspec_before_unsupported_tail verified"),
        "proof_assert should verify using call spec before unsupported tail MIR; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected 1 verified, 0 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #746: scoped extraction must tolerate diverging panic branches
/// before the proof_assert program point.
#[test]
#[timeout(120_000)]
fn proof_assert_diverging_branch_before_assert() {
    let output = run_fixture("diverging_branch_before_assert", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in diverging_branch_before_assert::diverging_branch_before_assert verified"),
        "proof_assert should verify past diverging branch; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected 1 verified, 0 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// AC3 for #746: proof_assert inside `if let Some(b) = Some(true)` block.
///
/// The MIR uses discriminant reads and downcast projections for if-let patterns.
/// The extraction pipeline handles this via:
/// - Explicit `Rvalue::Discriminant` translation to a pure discriminant method call
/// - SwitchInt fallback as a backup when discriminant locals are unavailable
/// - Downcast projection as no-op in expression model
/// - Field(0) identity passthrough for scalar values
#[test]
#[timeout(120_000)]
fn proof_assert_if_let_some_verify() {
    let output = run_fixture("if_let_some_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in if_let_some_verify::if_let_some_verify verified"),
        "proof_assert inside if-let Some block should verify; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("unknown method call: discriminant"),
        "discriminant method call should be encodable; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected 1 verified, 0 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// AC for #1457: match-arm discriminant guards must flow to proof_assert.
#[test]
#[timeout(120_000)]
fn proof_assert_match_arm_discriminant_verify() {
    let output = run_fixture("match_arm_discriminant_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in match_arm_discriminant_verify::match_arm_discriminant_verify verified"
        ),
        "proof_assert inside match true arm should verify with discriminant guard; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected 1 verified, 0 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// AC1 for #746: proof_assert after mutable dereference assignment.
///
/// Tests that `*a = 1; proof_assert!(*a > 0)` verifies when the extraction
/// pipeline tracks deref writes and the substitution system maps `*a` to
/// the written value.
#[test]
#[timeout(120_000)]
fn proof_assert_deref_assign_verify() {
    let output = run_fixture("deref_assign_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in deref_assign_verify::set_and_check verified"),
        "proof_assert after deref assignment should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected 1 verified, 0 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #746: projected deref writes through call-returned tuples
/// must flow into source-name substitutions at proof_assert program points.
#[test]
#[timeout(120_000)]
fn proof_assert_projected_deref_write_verify() {
    let output = run_fixture("projected_deref_write_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in projected_deref_write_verify::projected_deref_write_verify verified"
        ),
        "projected deref write proof_asserts should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "expected 2 verified, 0 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #746: MIR extraction must handle runtime assert!() macros
/// that appear between function calls and proof_assert!() in the MIR.
///
/// Runtime `assert!()` macro generates a bool SwitchInt with a panic branch
/// in MIR. The extraction pipeline handles this in cutoff mode by filtering
/// branches via cutoff-reachability: the panic arm is unreachable (diverges),
/// so only the success arm is followed.
#[test]
#[timeout(120_000)]
fn proof_assert_runtime_assert_before_proof_assert() {
    let output = run_fixture("runtime_assert_before_proof_assert", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    // Both assertions should verify:
    // 1. After call with postcondition + runtime assert
    assert!(
        stderr.contains("proof_assert in runtime_assert_before_proof_assert::assert_between_call_and_proof_assert verified"),
        "proof_assert after runtime assert + call should verify; stderr: {stderr}"
    );
    // 2. After let-binding + runtime assert
    assert!(
        stderr.contains(
            "proof_assert in runtime_assert_before_proof_assert::assert_after_let_binding verified"
        ),
        "proof_assert after let + runtime assert should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "expected 2 verified, 0 failed; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #928: projected assignments (tuple field writes like `_3.0 = _4`)
/// must not overwrite the whole local in the expression map. Before the fix,
/// `extract_from_block_with_context` would replace `local_exprs[_3]` with just
/// the RHS expression, losing the tuple/struct context.
#[test]
#[timeout(120_000)]
fn proof_assert_tuple_field_assign_verify() {
    let output = run_fixture("tuple_field_assign_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in tuple_field_assign_verify::scalar_after_tuple_field_write verified"
        ),
        "proof_assert after tuple field write should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected 1 verified, 0 failed; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #1180: proof_assert path must apply closure enrichment
/// to quantifier goals using `postcondition_mut`.
#[test]
#[timeout(120_000)]
fn proof_assert_closure_quantifier_enrichment() {
    let output =
        run_fixture_with_trust_wp_args("closure_quantifier_enrichment", Some("--verify --verbose"));
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in closure_quantifier_enrichment::proof_assert_closure_quantifier_enrichment verified"
        ),
        "expected proof_assert to verify after closure quantifier enrichment; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected exact proof_assert success summary; stderr: {stderr}"
    );
    assert!(
        stderr.contains("closure existential enrichment(s) applied"),
        "expected proof_assert closure existential enrichment to run; stderr: {stderr}"
    );
    assert!(
        stderr.contains("closure forall-goal enrichment(s) applied"),
        "expected proof_assert closure forall-goal enrichment to run; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #1190: closure-body proof_assert checks that depend on
/// mutable captures must use post-assignment substitutions.
#[test]
#[timeout(120_000)]
fn proof_assert_closure_mutation_capture_verify() {
    let output = run_fixture("closure_mutation_capture_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in closure_mutation_capture_verify::mutable_capture::{closure#0} verified"
        ),
        "mutable closure body assertions should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in closure_mutation_capture_verify::captures_and_call::{closure#0} verified"),
        "called closure body assertions should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 4 verified, 0 failed, 0 errors"),
        "expected 4 verified, 0 failed summary; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #1445: multi-field projected writes should verify.
///
/// Writes to distinct tuple fields (`pair.0 = 1; pair.1 = 2`) must produce
/// separate LetAssume facts that are both visible at the proof_assert point.
#[test]
#[timeout(120_000)]
fn proof_assert_multi_field_projected_writes_should_eventually_verify() {
    let output = run_fixture("multi_field_projected_writes_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in multi_field_projected_writes_verify::multi_field_projected_writes_verify verified"
        ),
        "multi-field projected writes should verify with per-field assumptions; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary (1 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
}

/// Regression for #1515: projected-write facts must survive both call and
/// match/switch block boundaries before reaching proof_assert.
#[test]
#[timeout(120_000)]
fn proof_assert_projected_write_call_match_verify() {
    let output = run_fixture("projected_write_call_match_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in projected_write_call_match_verify::projected_write_call_match_verify verified"
        ),
        "projected write fact should survive call + match before proof_assert; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary (1 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
}

#[test]
#[timeout(120_000)]
fn proof_assert_detection_without_verify() {
    // Even without --verify, proof assertions should be detected in verbose mode
    let output = run_fixture("should_verify", false);
    // Without --verify, the assertions are just detected, not verified
    // This test ensures the detection phase works without crashing
    assert!(
        output.status.success(),
        "expected fixture to compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Layer 2 (#1489): after a direct FnMut closure call, capture state
/// updates must be visible to the caller's `proof_assert!`. The name
/// substitution path maps the capture variable (`x`) to its post-call
/// value (`Final(x)`) so `x == 11` is correctly encoded as `x_final == 11`.
#[test]
#[timeout(120_000)]
fn proof_assert_closure_caller_capture_verify() {
    let output = run_fixture("closure_caller_capture_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr
            .contains("proof_assert in closure_caller_capture_verify::direct_fnmut_call verified"),
        "caller proof_assert after direct FnMut call should verify; stderr: {stderr}"
    );
    assert!(
        !stderr
            .contains("proof_assert in closure_caller_capture_verify::direct_fnmut_call unknown"),
        "proof_assert should not be unknown; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in closure_caller_capture_verify::direct_fnmut_two_calls verified"
        ),
        "caller proof_assert after two direct FnMut calls should verify; stderr: {stderr}"
    );
    assert!(
        !stderr.contains(
            "proof_assert in closure_caller_capture_verify::direct_fnmut_two_calls unknown"
        ),
        "two-call proof_assert should not be unknown; stderr: {stderr}"
    );
    assert!(
        stderr
            .contains("proof_assert in closure_caller_capture_verify::test_fnmut_mirror verified"),
        "test_fnmut_mirror (u32 + view) should verify; stderr: {stderr}"
    );
    assert!(
        !stderr
            .contains("proof_assert in closure_caller_capture_verify::test_fnmut_mirror unknown"),
        "test_fnmut_mirror should not be unknown; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 3 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary (3 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #1264: by-value `self` methods (like Option::ok_or) must
/// resolve `*self` in std spec postconditions within proof_assert blocks.
#[test]
#[timeout(120_000)]
fn proof_assert_by_value_self_verify() {
    let output = run_fixture("by_value_self_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("unresolved symbolic names"),
        "by-value self should not produce unresolved symbolic names (#1264); stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert in by_value_self_verify::by_value_self_ok_or verified"),
        "by-value self ok_or proof_assert should verify (#1264); stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary; stderr: {stderr}"
    );
}

/// Regression for #2209 / #1581: `Perm::disjoint_lemma` must keep the wrapped
/// ghost permission locals connected to the disjointness fact seen by
/// subsequent proof_asserts.
#[test]
#[timeout(120_000)]
fn proof_assert_ghost_perm_disjoint_verify() {
    let output = run_fixture("ghost_perm_disjoint_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr
            .contains("proof_assert in ghost_perm_disjoint_verify::perm_disjoint_verify verified"),
        "wrapped Perm disjointness proof_asserts should verify; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "expected exact proof_assert summary (2 verified, 0 failed, 0 errors); stderr: {stderr}"
    );
}

/// Regression for #2533: ghost tuple mutation must advance proof_assert
/// substitutions to the post-state instead of collapsing through the
/// pre-mutation tuple literal.
#[test]
#[timeout(120_000)]
fn proof_assert_ghost_tuple_mutation_post_state_verify() {
    let output = run_fixture("ghost_tuple_mutation_post_state_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "ghost tuple mutation should verify both proof_asserts; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("call_assumption[3]: (2 == 4)"),
        "ghost tuple mutation must not emit stale pre-mutation call assumption; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("assertion_after_sub: (2 == 4)"),
        "ghost tuple mutation must not substitute the stale tuple literal into the assertion; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("vacuous proof"),
        "ghost tuple mutation should verify non-vacuously; stderr: {stderr}"
    );
}

/// Canary for #2616: ghost Seq push_back should now verify through the
/// proof_assert path without falling back to the vacuous-proof demotion.
#[test]
#[timeout(120_000)]
fn proof_assert_seq_push_back_ghost_vacuity_canary() {
    let output = run_fixture("seq_push_back_ghost_vacuity", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in seq_push_back_ghost_vacuity::seq_push_back_ghost_vacuity verified"
        ),
        "ghost Seq reproducer should now verify; stderr: {stderr}"
    );
    assert!(
        !stderr
            .contains("vacuous proof: base assertions are UNSAT without the negated postcondition"),
        "ghost Seq reproducer should no longer demote to vacuous proof; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 1 verified, 0 failed, 0 errors"),
        "ghost Seq reproducer should report a successful proof_assert summary; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("sort_fallback_to_int"),
        "ghost Seq reproducer should stay beyond the older #2326 sort-fallback lane; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "ghost Seq canary should now succeed; stderr: {stderr}"
    );
}

/// Regression for the resolve_drop class: a proof_assert reading a local
/// AFTER a write through a (plain or boxed) mutable borrow of it must see the
/// POST-write value. Before the fix, the cutoff-time substitution map kept the
/// entry-time binding (`x -> 12`) alongside the writeback (`x == 13`),
/// manufacturing UNSAT base premises — a vacuous "proof" the vacuity guard
/// then rejected as an error.
#[test]
#[timeout(120_000)]
fn proof_assert_deref_write_local_current_value_verify() {
    let output = run_fixture("deref_write_local_current_value_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains(
            "proof_assert in deref_write_local_current_value_verify::plain_borrow_write verified"
        ),
        "plain &mut chain should verify post-write value; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in deref_write_local_current_value_verify::boxed_borrow_write verified"
        ),
        "Box<&mut _> chain should verify post-write value; stderr: {stderr}"
    );
    assert!(
        !stderr
            .contains("vacuous proof: base assertions are UNSAT without the negated postcondition"),
        "deref-write locals must not manufacture vacuous premises; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 2 verified, 0 failed, 0 errors"),
        "expected exactly 2 verified proof_asserts; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile and verify; stderr: {stderr}"
    );
}
