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
    sync::{Mutex, OnceLock},
    time::{SystemTime, UNIX_EPOCH},
};

use ntest::timeout;
use trust_wp_test_utils::{
    fixture_dir, nested_cargo, trust_wp_rustc_fixture_target_dir, trust_wp_rustc_path,
};

/// Every test here runs the one fixture crate in one target dir, one at a
/// time, and a test's `#[timeout]` runs from its start: it includes the wait
/// for this lock and, for whichever test takes it first, the cold build of
/// the fixture's dependencies. Budgets sized for one fixture run timed out
/// behind the queue on a loaded machine, whichever tests happened to wait
/// longest, so each budget covers the whole queue instead.
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

    let mut cmd = nested_cargo("check");
    cmd.current_dir(fixture_dir("proof_assert"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path());

    if let Some(args) = trust_wp_args {
        cmd.env("TRUST_WP_ARGS", args);
    }

    cmd.args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for proof_assert fixture")
}

fn run_fixture(bin: &str, verify: bool) -> std::process::Output {
    let trust_wp_args = if verify { Some("--verify") } else { None };
    run_fixture_with_trust_wp_args(bin, trust_wp_args)
}

/// The assertion at `fn_path` is not proved, whatever the word: `FAILED`,
/// `unknown`, or `inconclusive` (an unproved assertion in a contract-free
/// body, #2700).
fn assert_proof_assert_rejected(stderr: &str, fn_path: &str) {
    let words = ["FAILED", "unknown", "inconclusive"];
    assert!(
        words
            .iter()
            .any(|word| stderr.contains(&format!("proof_assert in {fn_path} {word}"))),
        "expected proof_assert rejection (proof_assert in {fn_path} FAILED, unknown or \
         inconclusive); stderr: {stderr}"
    );
    assert!(
        !stderr.contains(&format!("proof_assert in {fn_path} verified")),
        "the assertion must not be proved; stderr: {stderr}"
    );
}

/// A refuted `proof_assert!` is a goal of the function it sits in (D-87):
/// each function in `owners` is FAILED and never credited, and a
/// function-level FAILED fails the crate. The fixtures below predate D-87 and
/// asserted a clean exit beside a refuted assertion.
fn assert_owners_failed(output: &std::process::Output, stderr: &str, owners: &[&str]) {
    for owner in owners {
        assert!(
            stderr.contains(&format!("trust-wp: {owner} FAILED")),
            "the function owning a refuted assertion must be FAILED: {owner}; stderr: {stderr}"
        );
        assert!(
            !stderr.contains(&format!("trust-wp: {owner} verified")),
            "the function owning a refuted assertion must not be credited: {owner}; stderr: {stderr}"
        );
    }
    assert!(
        !stderr.contains("panicked"),
        "the failure is a verdict, not a crash; stderr: {stderr}"
    );
    assert!(
        !output.status.success(),
        "a function-level FAILED fails the crate; stderr: {stderr}"
    );
}

fn assert_single_rejection_summary(stderr: &str) {
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified, 1 failed, 0 errors")
            || stderr.contains("trust-wp: proof_assert: 0 verified, 0 failed, 1 errors")
            || stderr
                .contains("trust-wp: proof_assert: 0 verified, 0 failed, 0 errors, 1 inconclusive"),
        "expected single rejection summary (failed, unknown or inconclusive); stderr: {stderr}"
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

    let output = nested_cargo("check")
        .current_dir(&fixture_dir)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet"])
        .output()
        .expect("failed to run targo check for inline quantifier fixture");
    let _ = fs::remove_dir_all(&fixture_dir);
    output
}

#[test]
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
    // A refuted assertion is a goal of the function it sits in (D-87).
    assert_owners_failed(
        &output,
        &stderr,
        &["branch_unsound", "precondition_unsound"],
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
#[timeout(600_000)]
fn proof_assert_soundness_816_bool_ice() {
    let output = run_fixture("soundness_816_bool_ice", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Must not crash with sort mismatch ICE (#816, fixed in 82c9f53b).
    assert!(
        !stderr.contains("panicked") && !stderr.contains("BUG: mk_eq"),
        "fixture must not crash with sort mismatch; stderr: {stderr}"
    );
    // `flag` is unconstrained and `id_bool(flag)` requires it, so the call's
    // `ensures(flag)` may not be assumed (#815): `proof_assert!(flag)` is
    // refuted. A `verified` here would be the #815 leak, which this test
    // accepted beside the refutation until D-87 made the verdict exact.
    assert!(
        stderr.contains("proof_assert in soundness_816_bool_ice::bool_call_no_crash FAILED"),
        "an unconstrained flag refutes the assertion; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified, 1 failed, 0 errors"),
        "expected exact proof_assert summary (0 verified, 1 failed, 0 errors); stderr: {stderr}"
    );
    assert_owners_failed(&output, &stderr, &["bool_call_no_crash"]);
}

/// Soundness test for #817 AC1: branch-scoped call assumptions.
///
/// Tests that call postconditions are correctly scoped to the branch
/// in which the call occurs:
/// - `branch_scoped_verify`: proof_assert INSIDE branch should verify
/// - `branch_scoped_fail`: proof_assert OUTSIDE branch should fail
#[test]
#[timeout(600_000)]
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
    // A refuted assertion is a goal of the function it sits in (D-87): the
    // function that owns it is FAILED, never credited, while the function
    // whose assertion held keeps its credit.
    assert!(
        stderr.contains("trust-wp: branch_scoped_fail FAILED \u{2717} (proof_assert)"),
        "the function owning the refuted assertion must be FAILED; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("trust-wp: branch_scoped_fail verified"),
        "the function owning the refuted assertion must not be credited; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: branch_scoped_verify verified \u{2713}"),
        "the function whose assertion held keeps its credit; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("panicked"),
        "the failure is a verdict, not a crash; stderr: {stderr}"
    );
    assert!(
        !output.status.success(),
        "a function-level FAILED fails the crate; stderr: {stderr}"
    );
}

/// Soundness test for #817 AC2: callee precondition obligations.
///
/// Tests that calling a function with a `requires` clause generates
/// a proper obligation:
/// - `precondition_met_verify`: precondition satisfied, assertion verifies
/// - `precondition_violated_fail`: precondition violated, assertion fails
#[test]
#[timeout(600_000)]
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
        stderr.contains("trust-wp: precondition_met_verify verified"),
        "the function whose assertion held keeps its credit; stderr: {stderr}"
    );
    assert_owners_failed(&output, &stderr, &["precondition_violated_fail"]);
}

/// Regression test for #927: nested branch obligations from both ITE arms
/// must be enforced with branch guards, not treated as global assumptions.
#[test]
#[timeout(600_000)]
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
    assert_owners_failed(&output, &stderr, &["multibranch_obligation_unsound"]);
}

/// Soundness test for #817 AC3: bool-returning call specs in proof_assert path.
///
/// Tests that functions returning bool with predicate-style ensures
/// produce correct verification results (not just absence of crash):
/// - `bool_call_verify`: precondition met, assertion verifies
/// - `bool_call_fail`: precondition violated, assertion fails
#[test]
#[timeout(600_000)]
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
        stderr.contains("trust-wp: bool_call_verify verified"),
        "the function whose assertion held keeps its credit; stderr: {stderr}"
    );
    assert_owners_failed(&output, &stderr, &["bool_call_fail"]);
}

/// Program-point regression for #746:
/// proof_assert extraction must stop at the assertion span so unsupported
/// tail MIR does not block call-spec reasoning before the assertion.
#[test]
#[timeout(600_000)]
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
    // The summary is not asserted as an exact count: the same proof_assert is
    // reported once per lane that discharges it, and the fixture's helper
    // `identity_positive` legitimately verifies as well. What matters is that
    // nothing in the run failed or errored.
    assert!(
        !stderr.contains("proof_assert in callspec_before_unsupported_tail::callspec_before_unsupported_tail FAILED")
            && !stderr.contains("proof_assert in callspec_before_unsupported_tail::callspec_before_unsupported_tail unknown"),
        "proof_assert must not be rejected in any lane; stderr: {stderr}"
    );
    let summary = stderr
        .lines()
        .find(|line| line.starts_with("trust-wp: proof_assert: "))
        .unwrap_or_default();
    assert!(
        summary.contains(" 0 failed, 0 errors"),
        "expected a proof_assert summary with 0 failed, 0 errors; got `{summary}`; stderr: {stderr}"
    );
    assert!(
        output.status.success(),
        "fixture should compile; stderr: {stderr}"
    );
}

/// Regression for #746: scoped extraction must tolerate diverging panic branches
/// before the proof_assert program point.
#[test]
#[timeout(600_000)]
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
    // The `panic!` arm is reachable (nothing constrains `flag`), and a
    // contract-free body owes its abort obligations (D-71): the function is
    // FAILED while the assertion past the diverging arm holds.
    assert_owners_failed(&output, &stderr, &["diverging_branch_before_assert"]);
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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

/// #746 carried a projected deref write through a call-returned tuple
/// (`*p.0 = 10` of `p = swap_refs((&mut a, &mut b))`) into `b`'s value. Two
/// rules now meet here. The callee states the swap by comparing the `&mut`s
/// its tuple parameter holds whole, which D-181 refuses: its own lane read the
/// comparison over current values while every call read it as which borrow
/// the result holds (tuple_param_held_mut_whole_swap_claimed_unswapped). And
/// the borrows reach the callee in a tuple it is handed by value, so each
/// assertion reading `a` or `b` after the hand-off is refused (D-129), these
/// true ones included. tuple_param_held_mut_whole_swap_control is the xfail
/// that names the price: no assertion is credited.
#[test]
#[timeout(600_000)]
fn proof_assert_projected_deref_write_through_a_whole_held_mut_claim_is_refused() {
    let output = run_fixture("projected_deref_write_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    for name in ["b", "a"] {
        assert!(
            stderr.contains(&format!(
                "proof_assert in projected_deref_write_verify::projected_deref_write_verify error: \
                 stale read refused (fail-closed): `{name}`"
            )),
            "the read of `{name}` after the holder's hand-off should be refused; stderr: {stderr}"
        );
    }
    assert!(
        stderr.contains(
            "swap_refs: ensures `result == (x.1, x.0)` is refused: `x` holds a `&mut` without \
             being one, and a postcondition reads that `&mut` only through `*`, `^` or `@`"
        ),
        "the whole comparison of the held `&mut`s should be refused (D-181); stderr: {stderr}"
    );
    assert!(
        !stderr.contains(
            "proof_assert in projected_deref_write_verify::projected_deref_write_verify verified"
        ),
        "no assertion may be credited; stderr: {stderr}"
    );
    assert!(
        !output.status.success(),
        "a refused clause fails the run; stderr: {stderr}"
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
#[timeout(600_000)]
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
    // The `assert!` arm is charged unreachable by the switch lane and
    // discharged, and the body is loop-free with exact values, so the
    // clause-free cap reads the charged edge as dead and lets `verified`
    // stand (D-142; the adversarial control is
    // `contract_free_assert_provable_control`).
    assert!(
        stderr.contains("trust-wp: assert_after_let_binding verified"),
        "a contract-free body's charged, discharged assert! is not capped (D-142); \
         stderr: {stderr}"
    );
    // Here the charge `y > 0` is proved from `identity_positive`'s
    // postcondition, a premise that is not an entry fact, so no edge counts
    // as dead and the cap stands although the assertion verifies (D-143's
    // named price).
    assert!(
        stderr.contains(
            "trust-wp: assert_between_call_and_proof_assert unknown (partial: panic paths unchecked (panic call))"
        ),
        "a charge proved from a callee postcondition proves no edge dead (D-143); \
         stderr: {stderr}"
    );
    assert!(
        !stderr.contains(" FAILED") && !stderr.contains("panicked"),
        "a provable assert! is never refuted; stderr: {stderr}"
    );
}

/// Regression for #928: projected assignments (tuple field writes like `_3.0 = _4`)
/// must not overwrite the whole local in the expression map. Before the fix,
/// `extract_from_block_with_context` would replace `local_exprs[_3]` with just
/// the RHS expression, losing the tuple/struct context.
#[test]
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
fn proof_assert_closure_mutation_capture_verify() {
    let output = run_fixture("closure_mutation_capture_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "proof_assert in closure_mutation_capture_verify::mutable_capture::{closure#1} verified"
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
    // The hosts own verdicts of their own, and neither is a pass. Each owes its
    // closure's precondition (D-71), which `mutable_capture` discharges over
    // the captured constant; its call enters the closure through
    // `FnMut::call_mut`, whose body the panic account does not read at a call
    // (D-104), so its verdict is partial. `captures_and_call` hands a closure
    // that writes a captured `&mut` to a trusted callee that runs it where no
    // lane sees the write, and its verdict is withdrawn (D-118).
    assert!(
        stderr.contains(
            "trust-wp: mutable_capture unknown (partial: panic paths unchecked (call to std::ops::FnMut::call_mut))"
        ),
        "expected mutable_capture's precondition discharged and its verdict partial (D-104); stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: captures_and_call error: verdict withdrawn"),
        "expected captures_and_call's verdict withdrawn (D-118); stderr: {stderr}"
    );
    assert!(
        !stderr.contains("FAILED"),
        "no host call of a closure should be refuted; stderr: {stderr}"
    );
}

/// Regression for #1445: multi-field projected writes should verify.
///
/// Writes to distinct tuple fields (`pair.0 = 1; pair.1 = 2`) must produce
/// separate LetAssume facts that are both visible at the proof_assert point.
#[test]
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
#[timeout(600_000)]
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
    // `main` is a clause-free caller of the three functions above, and each of
    // their bodies calls an `FnMut` closure. A `FnMut::call_mut` site enters no
    // body for the clause-free panic account (D-104), so those bodies are not
    // clean, `main` is capped at `unknown` and the run is not clean. Every
    // function this test is about verifies.
    assert!(
        stderr.contains(
            "trust-wp: main unknown (partial: panic paths unchecked (call to \
             direct_fnmut_call (unchecked panic paths in direct_fnmut_call)"
        ),
        "main should be capped by D-104's `FnMut` exclusion; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 6 verified, 0 failed, 1 errors"),
        "only `main` should go unverified; stderr: {stderr}"
    );
}

/// Regression for #1264: by-value `self` methods (like Option::ok_or) must
/// resolve `*self` in std spec postconditions within proof_assert blocks.
#[test]
#[timeout(600_000)]
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
#[timeout(600_000)]
fn proof_assert_ghost_perm_disjoint_verify() {
    let output = run_fixture("ghost_perm_disjoint_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // The lemma's `&mut own1` goes through `DerefMut::deref_mut` on the ghost
    // handle, and the write flows back to `own1`: K1's forwarding quarantine
    // is gone, and D-8 names this program's corpus spelling, the compat row
    // ghost/disjoint_raw_ptr.rs, in the price of deleting it. Over
    // trust_wp_std's `Perm` the premises each assertion is read under are
    // unsatisfiable on their own, and the vacuity guard refuses both rather
    // than credit them. The pin keeps that neither assertion is credited and
    // neither is refuted; the TRUE program is the xfail control
    // perm_disjoint_lemma_through_ghost_deref_mut_control.rs.
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified, 0 failed, 2 errors")
            && stderr
                .matches("perm_disjoint_verify unknown (vacuous proof")
                .count()
                == 2,
        "expected both Perm disjointness assertions refused as vacuous; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("FAILED"),
        "no Perm disjointness assertion should be refuted; stderr: {stderr}"
    );
}

/// Regression for #2533: ghost tuple mutation must advance proof_assert
/// substitutions to the post-state instead of collapsing through the
/// pre-mutation tuple literal.
#[test]
#[timeout(600_000)]
fn proof_assert_ghost_tuple_mutation_post_state_verify() {
    let output = run_fixture("ghost_tuple_mutation_post_state_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // The write `p.0 = 4` goes through `DerefMut::deref_mut` and flows back
    // to `p` as the final value of the constant the tuple was built from,
    // which the final-collapse guard's constant-carrier arm refuses (D-14).
    // That is the price D-8 names for deleting K1's `deref_mut` forwarding
    // quarantine: the assertions had verified on the stale entry value.
    // The xfail control is ghost_tuple_field_write_through_deref_mut_control.rs.
    // What #2533 pins still holds: no stale pre-mutation literal, no vacuity.
    assert!(
        stderr.contains("proof_assert"),
        "expected proof_assert output in stderr; stderr: {stderr}"
    );
    assert!(
        stderr.contains("final-collapse refused (fail-closed): `^Int(2)` applies a prophecy to a constant carrier")
            && stderr.contains("trust-wp: proof_assert: 0 verified, 0 failed, 2 errors"),
        "both assertions refused on the constant carrier, neither credited; stderr: {stderr}"
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
#[timeout(600_000)]
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

/// The resolve_drop class: a proof_assert reading a local AFTER a write
/// through a (plain or boxed) mutable borrow of it. A TRUE assertion there is
/// owed the POST-write value; while the lane cannot state it without a
/// contradiction or a havoc, the assertion must be refused, never credited
/// and never refuted.
#[test]
#[timeout(600_000)]
fn proof_assert_deref_write_local_current_value_verify() {
    let output = run_fixture("deref_write_local_current_value_verify", true);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // The plain chain is not credited: `*b += 1` is recorded for the borrow
    // chain as the raw `x + 1`, which the name lane reads at the post-write
    // binding, so the premises state `x == 12 + 1` beside `x == (12 + 1) + 1`
    // and the vacuity guard refuses the assertion. Handing the handlers the
    // governed write's resolved value removes that contradiction only on paths
    // where `x` has a binding of its own, and on a path where `x` is still the
    // parameter's entry symbol the contradiction stays and is then path-local,
    // which the guard does not see (D-171). The cost is this TRUE assertion;
    // its xfail control is deref_write_through_local_borrow_post_write_value_control.rs.
    assert!(
        stderr.contains(
            "proof_assert in deref_write_local_current_value_verify::plain_borrow_write unknown (vacuous proof"
        ),
        "plain &mut chain: expected the doubled write refused as vacuous (D-171); stderr: {stderr}"
    );
    // The `Box<&mut _>` chain is not credited: `Box::new(&mut x)` hands the
    // borrow into a container, the lane havocs `x` there, and nothing carries
    // the write through the boxed borrow back to it, so the assertion ends
    // `unknown`. That is the residual gap
    // s48v4_box_new_handback_deref_control.rs is the xfail control for; the
    // pin is that it is not credited and not vacuous.
    assert!(
        stderr.contains(
            "proof_assert in deref_write_local_current_value_verify::boxed_borrow_write unknown"
        ),
        "Box<&mut _> chain: expected the handback gap's `unknown`; stderr: {stderr}"
    );
    assert!(
        !stderr.contains(
            "proof_assert in deref_write_local_current_value_verify::boxed_borrow_write unknown (vacuous proof"
        ),
        "Box<&mut _> chain: the handback gap must not manufacture vacuous premises; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified, 0 failed, 2 errors"),
        "expected neither chain's assertion credited and neither refuted; stderr: {stderr}"
    );
}

/// A `proof_assert!` in a loop body reads a local the loop writes later in
/// the body (`y = 5` after the assertion) or carries as its counter: at the
/// head of an arbitrary iteration it holds the value the back edge carried
/// in, not the first iteration's. Both assertions are false (n = 2 reads
/// `y == 5`, `v == 1` on the second iteration) and must not be credited
/// (D-187).
#[test]
#[timeout(600_000)]
fn proof_assert_in_loop_body_reads_a_local_the_body_writes_later() {
    let output = run_fixture("loop_body_local_written_later", true);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_proof_assert_rejected(&stderr, "loop_body_local_written_later::written_later");
    assert_proof_assert_rejected(&stderr, "loop_body_local_written_later::counter_copy");
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified"),
        "no assertion of the fixture may be credited; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("panicked"),
        "the rejection is a verdict, not a crash; stderr: {stderr}"
    );
}

/// A `proof_assert!` in a loop placed before the loop's own test (a `loop`
/// whose break test follows it, a `while` condition block) runs on the
/// iteration whose test fails too: with n = 0 both assertions read i = 0.
/// The loop condition must not be assumed there (D-188).
#[test]
#[timeout(600_000)]
fn proof_assert_before_a_loops_test_is_not_proved_from_that_test() {
    let output = run_fixture("assert_before_loop_test", true);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_proof_assert_rejected(&stderr, "assert_before_loop_test::before_break_test");
    assert_proof_assert_rejected(&stderr, "assert_before_loop_test::in_while_condition_block");
    assert!(
        stderr.contains("trust-wp: proof_assert: 0 verified"),
        "no assertion of the fixture may be credited; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("panicked"),
        "the rejection is a verdict, not a crash; stderr: {stderr}"
    );
}
