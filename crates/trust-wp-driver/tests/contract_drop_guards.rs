// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    path::{Path, PathBuf},
    sync::OnceLock,
};

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn fixture_target_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/contract_drop_guard_tests")
}

/// Pre-warm the fixture's dependency cache so individual bin checks are fast.
///
/// Without this, three concurrent tests each try to cold-compile all trust-wp
/// deps into the same target directory, fighting over cargo's file lock and
/// often exceeding the per-test timeout in multi-worker environments.
fn warm_fixture_deps() {
    static ONCE: OnceLock<()> = OnceLock::new();
    ONCE.get_or_init(|| {
        // Build the lib target to cache all shared dependencies.
        // Status is intentionally ignored — the lib may have parse errors,
        // but the dependency artifacts will still be cached for bin targets.
        let _ = nested_cargo("check")
            .current_dir(fixture_dir("contract_drop_guards"))
            .env("CARGO_TARGET_DIR", fixture_target_dir())
            .env("RUSTC_WRAPPER", trust_wp_rustc_path())
            .args(["--quiet", "--lib"])
            .status();
    });
}

fn run_fixture(bin: &str) -> std::process::Output {
    warm_fixture_deps();
    nested_cargo("check")
        .current_dir(fixture_dir("contract_drop_guards"))
        .env("CARGO_TARGET_DIR", fixture_target_dir())
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for contract drop guard fixture")
}

#[test]
#[timeout(300_000)]
fn dropped_requires_clause_rejects_function() {
    let output = run_fixture("requires_dropped");
    let stderr = String::from_utf8_lossy(&output.stderr);

    // trust-wp-rustc returns exit code 2 for unparseable contracts, which causes
    // cargo check to fail. This is correct: malformed contracts should not silently
    // compile. The important thing is that the right diagnostics are emitted.
    assert!(
        !output.status.success(),
        "fixture with malformed requires should fail (exit non-zero); stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("failed to parse requires"),
        "expected parse failure for malformed requires clause; stderr: {stderr}"
    );
    assert!(
        stderr.contains("has unparseable requires clause(s)"),
        "expected dropped requires diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("skipping verification to prevent unsound results"),
        "expected skip-verification safety diagnostic; stderr: {stderr}"
    );
    // `main` calls the malformed function, so it owes that callee's
    // precondition (a contract-free body with a contracted callee is a target,
    // D-71): the same unparseable clause, refused there too. Nothing verifies.
    assert!(
        stderr.contains("trust-wp: main error: unsupported formula"),
        "expected main's owed callee precondition to be refused; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 0 verified, 0 failed, 2 errors"),
        "expected malformed requires fixture to be rejected without verification; stderr: {stderr}"
    );
}

/// A `char` is not a well-founded variant measure. Creusot's `WellFounded`
/// (`creusot-std/src/logic/well_founded.rs`) is implemented for `Int`, the
/// machine integers, references, boxes, `()` and tuples of those — never for
/// `char` — so `#[variant('a')]` is a TYPE error of the specification, and
/// the contract type-check vehicle (`trust-wp-macros/src/spec_tc`,
/// `variant_check<T: WellFounded>`) reports it as one. The rejection is
/// unchanged; its reason moved from a verification failure (the driver's
/// parser reads `'a'` as `Int(97)`, a constant that never decreases) to the
/// type error rustc reports before the driver runs.
#[test]
#[timeout(300_000)]
fn dropped_variant_clause_rejects_function() {
    let output = run_fixture("variant_dropped");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "fixture with a `char` variant measure must not compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("E0277") && stderr.contains("WellFounded"),
        "expected the `char: WellFounded` type error for a `char` variant measure; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("verified ✓") && !stderr.contains("trust-wp: 1 verified"),
        "a fixture that fails to type-check must verify nothing; stderr: {stderr}"
    );
}

/// Regression test for #1132: per-loop invariant parse errors were silently
/// dropped, bypassing the dropped-clause safety guard from #802.
#[test]
#[timeout(300_000)]
fn dropped_per_loop_invariant_clause_rejects_function() {
    let output = run_fixture("per_loop_invariant_dropped");
    let stderr = String::from_utf8_lossy(&output.stderr);

    // trust-wp-rustc returns exit code 2 for unparseable contracts, which causes
    // cargo check to fail. Same as dropped_requires: malformed contracts are errors.
    assert!(
        !output.status.success(),
        "fixture with malformed invariant should fail (exit non-zero); stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("failed to parse") && stderr.contains("invariant"),
        "expected parse failure for malformed per-loop invariant clause; stderr: {stderr}"
    );
    assert!(
        stderr.contains("has unparseable invariant clause(s)"),
        "expected dropped invariant diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("skipping verification to prevent unsound results"),
        "expected skip-verification safety diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 0 verified, 0 failed, 1 errors"),
        "expected malformed per-loop invariant fixture to be rejected without verification; stderr: {stderr}"
    );
}

/// THE PROPERTY CAMPAIGN COMMIT 192a2e73 LEFT UNGUARDED.
///
/// That commit moved `dropped_variant_clause_rejects_function` from asserting a
/// verification failure to asserting rustc's `char: WellFounded` E0277, and the
/// move is correct — `#[variant('a')]` is a type error of the specification and
/// creusot-std really does not implement `WellFounded` for `char`. What it left
/// behind is this: nothing else in the workspace supplied a variant measure that
/// TYPE-CHECKS and is then refuted.
///
/// `i32: WellFounded`, so `spec_tc` accepts `#[variant(0i32)]`, the driver runs,
/// and the decrease obligation is really posed and really fails. Every assertion
/// below is a POSITIVE string only the intended path can produce; none is the
/// vacuous "did not say verified" negative, which any compile error satisfies.
#[test]
#[timeout(300_000)]
fn non_decreasing_variant_fails_verification() {
    let output = run_fixture("variant_non_decreasing");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "a constant variant measure must not verify; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("FAILED ✗ (variant decrease)"),
        "expected the variant-decrease obligation to be posed and refuted; stderr: {stderr}"
    );
    assert!(
        stderr.contains("variant does not decrease at recursive call site"),
        "expected the variant-decrease reason; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 0 verified, 1 failed, 0 errors"),
        "the fixture must be VERIFIED and refuted, not skipped as an error; stderr: {stderr}"
    );
}

/// The parser-refuses-a-well-typed-variant path: `variants_dropped` in
/// `callbacks::parsing::clauses::has_dropped_clauses`.
///
/// `match n { 0 => 0, _ => n }` is a well-typed `i32` expression, so the
/// specification type-check accepts it and nothing rejects it before the driver.
/// `parse_contract` then refuses it (Pearlite does not match integer literals),
/// the clause is dropped, and the function must be REFUSED rather than verified
/// without its measure. If this arm regressed, a `#[check(terminates)]` function
/// whose `#[variant]` was dropped would be verified with no decrease obligation
/// at all — an exit-0 false accept.
#[test]
#[timeout(300_000)]
fn parser_refused_variant_rejects_function() {
    let output = run_fixture("variant_parse_refused");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "a function whose variant the parser refuses must not compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("failed to parse variant"),
        "expected the variant parse failure; stderr: {stderr}"
    );
    assert!(
        stderr.contains("Pattern matching literals on Int are unsupported by Pearlite"),
        "expected the Pearlite int-literal-pattern refusal, i.e. the clause reached \
         the contract parser and was refused there; stderr: {stderr}"
    );
    assert!(
        stderr.contains("has unparseable variant clause(s)"),
        "expected the dropped-variant diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("skipping verification to prevent unsound results"),
        "expected the skip-verification safety diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 0 verified, 0 failed, 1 errors"),
        "a dropped variant must yield zero verified functions; stderr: {stderr}"
    );
}

/// The per-loop arm of the same path.
///
/// `failed to parse per-loop variant` is emitted ONLY by
/// `parse_clause_inputs`'s `per_loop_variants` branch, so that string is what
/// makes this bin cover the loop lane rather than repeating the function-level
/// one. Note what is measured and what is NOT: because
/// `discovery::collect_loop_contract_attrs` also `extend_unique`s every loop
/// variant into the function's FLAT `variants` list, a refused loop variant
/// always sets `variants_dropped` as well, so `has_dropped_clauses` reports
/// "variant" and its `per_loop_variants_dropped && !variants_dropped` label is
/// not reachable from this (or any) user-surface input. This bin therefore
/// guards the per-loop PARSE arm, and the flat arm covers the drop decision.
#[test]
#[timeout(300_000)]
fn dropped_per_loop_variant_clause_rejects_function() {
    let output = run_fixture("per_loop_variant_dropped");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "a loop whose variant the parser refuses must not compile; stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        stderr,
    );
    assert!(
        stderr.contains("failed to parse per-loop variant"),
        "expected the PER-LOOP variant parse failure specifically; stderr: {stderr}"
    );
    assert!(
        stderr.contains("has unparseable variant clause(s)"),
        "expected the dropped-variant diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("skipping verification to prevent unsound results"),
        "expected the skip-verification safety diagnostic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: 0 verified, 0 failed, 1 errors"),
        "a dropped per-loop variant must yield zero verified functions; stderr: {stderr}"
    );
}
