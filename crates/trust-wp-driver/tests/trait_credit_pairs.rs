// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Isolating pairs for the trait-contract credit withdrawal (D-86, D-94).
//!
//! Each pair is one program run twice, differing in the single value an impl
//! returns. The refuted run must withdraw the credits resting on the impl; the
//! honoured run must keep them. The adversarial corpus can gate only the first
//! half: a run in which any impl fails is a rejection whatever else it keeps,
//! and its runner does not flag a TRUE credit that was withdrawn. These tests
//! gate both halves on the driver's own output.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

/// Run one fixture bin in its own target dir, cleaning the fixture package
/// first: Cargo's fingerprint does not cover the wrapper's contents, so a warm
/// target dir would replay an earlier driver's output.
fn run_fixture(bin: &str) -> String {
    let target_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(format!("../../target/trait_credit_pairs_tests_{bin}"));
    let clean = nested_cargo("clean")
        .current_dir(fixture_dir("trait_credit_pairs"))
        .env("CARGO_TARGET_DIR", &target_dir)
        .args(["--quiet", "-p", "trait-credit-pairs-fixture"])
        .status()
        .expect("failed to run targo clean for the trait credit fixture");
    assert!(
        clean.success(),
        "targo clean failed for the trait credit fixture"
    );
    let output = nested_cargo("check")
        .current_dir(fixture_dir("trait_credit_pairs"))
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        // Hermetic: verify only the fixture crate, never its dependencies.
        .env("CARGO_TRUST_WP", "1")
        .args(["--quiet", "--bin", bin])
        .output()
        .expect("failed to run targo check for the trait credit fixture");
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn verified(stderr: &str, item: &str) -> bool {
    stderr.contains(&format!("trust-wp: {item} verified"))
}

fn withdrawn(stderr: &str, item: &str) -> bool {
    stderr.contains(&format!("trust-wp: {item} error: verdict withdrawn"))
}

/// Credited and never taken back.
fn stands(stderr: &str, item: &str) -> bool {
    verified(stderr, item) && !withdrawn(stderr, item)
}

/// `<W as Rd>::rd` refutes `Rd::rd` in both runs. A call the resolver pins to
/// `<V as Rd>::rd` (`V.rd()`, `self.rd()` inside `impl V`) rests on V's impl
/// alone, and so does a caller of such a call.
#[test]
#[timeout(300_000)]
fn a_call_pinned_to_an_honouring_impl_keeps_its_credit() {
    let stderr = run_fixture("pinned_honoured");
    for item in ["go_vd", "V::m", "go_vm"] {
        assert!(
            stands(&stderr, item),
            "`{item}` rests only on V's impl, which honours the contract; stderr: {stderr}"
        );
    }
    // Every call that may run W's impl is withdrawn: pinned to it, generic,
    // or through a generic function the walk does not instantiate.
    for item in ["go_wd", "gen_read", "go_v"] {
        assert!(
            !stands(&stderr, item),
            "`{item}` may run W's impl and must not keep its credit; stderr: {stderr}"
        );
    }
    assert!(
        stderr.contains(
            "trust-wp: go_wd error: verdict withdrawn - it assumed trait method contract \
             `Rd::rd` where `<W as Rd>::rd` runs"
        ),
        "the pinned withdrawal must name the impl it rests on; stderr: {stderr}"
    );
}

/// The twin: V's impl refutes the contract too, and every credit pinned to it
/// is withdrawn.
#[test]
#[timeout(300_000)]
fn a_call_pinned_to_a_refuting_impl_is_withdrawn() {
    let stderr = run_fixture("pinned_refuted");
    for item in ["go_vd", "V::m", "go_vm", "go_wd", "gen_read", "go_v"] {
        assert!(
            !stands(&stderr, item),
            "`{item}` rests on a refuted impl and must not keep its credit; stderr: {stderr}"
        );
    }
    assert!(
        stderr.contains(
            "trust-wp: go_vd error: verdict withdrawn - it assumed trait method contract \
             `Rd::rd` where `<V as Rd>::rd` runs"
        ),
        "the pinned withdrawal must name V's impl; stderr: {stderr}"
    );
}

/// A `verified*` credit is counted in `verified_with_axiom_deps`, not in
/// `verified`; it rests on a trait grant like any other credit.
#[test]
#[timeout(300_000)]
fn a_verified_star_credit_on_an_honoured_grant_stands() {
    let stderr = run_fixture("axiom_dep_honoured");
    assert!(
        stderr.contains("trust-wp: go_star verified*"),
        "control: `go_star` is credited `verified*`; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("verdict withdrawn"),
        "control: a discharged contract withdraws nothing; stderr: {stderr}"
    );
    assert!(
        stderr.contains("1 verified* (unproven axiom deps)"),
        "control: the summary counts the `verified*` credit; stderr: {stderr}"
    );
}

#[test]
#[timeout(300_000)]
fn a_verified_star_credit_on_a_refuted_grant_is_withdrawn_from_its_own_counter() {
    let stderr = run_fixture("axiom_dep_refuted");
    assert!(
        stderr.contains("trust-wp: go_star verified*"),
        "`go_star` is first credited `verified*`; stderr: {stderr}"
    );
    assert!(
        withdrawn(&stderr, "go_star"),
        "`go_star` rests on `gen_read`'s refuted grant; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("verified* (unproven axiom deps)"),
        "the withdrawn credit must leave the `verified*` count; stderr: {stderr}"
    );
}
