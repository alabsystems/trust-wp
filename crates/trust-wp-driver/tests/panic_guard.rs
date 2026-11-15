// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The main verification loop's fail-closed panic guard (#1975).
//!
//! `verify_contracts` wraps each item in `catch_unwind` so that one panicking
//! function does not abort the crate. That containment is only sound because
//! the panic is RECORDED — `counters.panics` is the single trace a panicked
//! item leaves, and it is what makes the run exit non-zero.
//!
//! A refactor that keeps the `catch_unwind` and drops the handler turns every
//! crashed proof into a silent pass: a crate-level FALSE ACCEPT. These tests
//! exist so that such a refactor fails here instead of shipping. Each asserts
//! against a CONTROL run of the same fixture with the injection off, so a
//! rejection for an unrelated reason cannot be mistaken for the guard working.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

/// Run one fixture bin, optionally with the guard's fault injection armed.
///
/// `probe` names the item whose verification must panic; `None` is the
/// control run. Each (bin, mode) pair gets its own target dir so the control
/// and the injected run cannot share a cached verdict.
///
/// The fixture package is cleaned first. Cargo's fingerprint covers the
/// RUSTC_WRAPPER *path* but not the wrapper's contents, and it does not see
/// `TRUST_WP_PROBE_PANIC` at all, so a second run in a warm target directory
/// replays the first run's captured output and exit status verbatim. That
/// would make this test report on a driver that is no longer installed —
/// exactly the failure mode it exists to catch. Dependencies stay cached, so
/// only the fixture crate is recompiled.
fn run_fixture(bin: &str, probe: Option<&str>) -> std::process::Output {
    let mode = if probe.is_some() { "probe" } else { "control" };
    let target_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(format!("../../target/panic_guard_tests_{bin}_{mode}"));
    let wrapper = trust_wp_rustc_path();
    let clean = nested_cargo("clean")
        .current_dir(fixture_dir("panic_guard"))
        .env("CARGO_TARGET_DIR", &target_dir)
        .args(["--quiet", "-p", "panic-guard-fixture"])
        .status()
        .expect("failed to run targo clean for the panic guard fixture");
    assert!(
        clean.success(),
        "targo clean failed for the panic guard fixture"
    );
    let mut cmd = nested_cargo("check");
    cmd.current_dir(fixture_dir("panic_guard"))
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("RUSTC_WRAPPER", wrapper)
        .env("TRUST_WP_ARGS", "--verify")
        // Hermetic: verify only the fixture crate, never its dependencies.
        .env("CARGO_TRUST_WP", "1")
        .args(["--quiet", "--bin", bin]);
    match probe {
        Some(item) => cmd.env("TRUST_WP_PROBE_PANIC", item),
        None => cmd.env_remove("TRUST_WP_PROBE_PANIC"),
    };
    cmd.output()
        .expect("failed to run targo check for the panic guard fixture")
}

/// CONTROL: with nothing injected the fixture verifies and the crate exits 0.
///
/// This is what makes the injected runs below evidence: they start from an
/// accepted crate, so the rejection they assert can only come from the panic.
#[test]
#[timeout(300_000)]
fn the_fixture_verifies_when_nothing_panics() {
    let output = run_fixture("panicking_item", None);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "control: the fixture must verify with no injection; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: panic_guard_target verified"),
        "control: the target item must verify; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("panicked during verification"),
        "control: nothing may panic without the injection; stderr: {stderr}"
    );
}

/// A panicked item must be COUNTED, REPORTED, and must force a non-zero exit.
///
/// Deleting the `if let Err(..)` handler in `verify_contracts` while keeping
/// the `catch_unwind` fails all three assertions at once: the run prints no
/// panic line, reports "0 errors", and exits 0.
#[test]
#[timeout(300_000)]
fn a_panicked_item_is_reported_and_rejects_the_crate() {
    let output = run_fixture("panicking_item", Some("panic_guard_target"));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "a panicked item must not leave the crate accepted; stderr: {stderr}"
    );
    assert!(
        stderr.contains("trust-wp: panic_guard_target panicked during verification"),
        "the panic must be reported against the item that panicked; stderr: {stderr}"
    );
    assert!(
        stderr.contains("(continuing with remaining functions)"),
        "the guard must say it contained the panic; stderr: {stderr}"
    );
    assert!(
        stderr.contains("1 panicked"),
        "counters.panics must reach the summary; stderr: {stderr}"
    );
    // Containment is the other half of the guard: the panic must not cost the
    // verdicts of the items that did not panic.
    assert!(
        stderr.contains("trust-wp: panic_guard_bystander verified"),
        "verification must continue with the remaining functions; stderr: {stderr}"
    );
    assert!(
        !stderr.contains("trust-wp: panic_guard_target verified"),
        "a panicked item must never also be credited; stderr: {stderr}"
    );
}

/// The trait-credit join must see the panic too.
///
/// The impl inherits its trait contract verbatim, so its refinement goal is
/// the tautology `P => P` and only the BODY obligation discharges the trait
/// contract for `gen_read`'s generic call site. When the body never finishes,
/// the caller's grant rests on nothing and must be withdrawn.
///
/// Before the guard was restored this ran the other way: the panic left no
/// counter, `end_item`'s `panicked during body verification` branch could not
/// fire, and the crate exited 0 with "2 verified".
///
/// `go` took no trait grant of its own; it calls `gen_read`, and a credit that
/// rests on a withdrawn one is withdrawn by the same walk.
#[test]
#[timeout(300_000)]
fn a_panicked_impl_body_does_not_discharge_the_trait_contract_it_inherited() {
    let output = run_fixture("panicking_trait_impl", Some("<W as Rd>::rd"));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "a panicked impl body must not leave the crate accepted; stderr: {stderr}"
    );
    assert!(
        stderr.contains("panicked during verification"),
        "the impl body's panic must be reported; stderr: {stderr}"
    );
    assert!(
        stderr.contains("verdict withdrawn - it assumed trait method contract `Rd::rd`"),
        "the generic caller's trait grant must be withdrawn; stderr: {stderr}"
    );
    assert!(
        stderr.contains("panicked during body verification"),
        "the withdrawal must name the panic as its reason; stderr: {stderr}"
    );
    assert!(
        stderr.contains(
            "trust-wp: go error: verdict withdrawn - through `gen_read`, it assumed trait \
             method contract `Rd::rd`"
        ),
        "a caller one ordinary call away from the withdrawn grant must be withdrawn too; \
         stderr: {stderr}"
    );
}

/// CONTROL for the trait fixture: with nothing injected the impl body
/// discharges the contract it inherited, and neither the generic caller nor
/// the caller one call away from it is withdrawn. Together with the injected
/// run above this is the isolating pair for the transitive withdrawal: the
/// same program, differing only in whether the impl's obligation was paid.
#[test]
#[timeout(300_000)]
fn a_discharged_trait_contract_withdraws_nothing() {
    let output = run_fixture("panicking_trait_impl", None);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "control: the trait fixture must verify with no injection; stderr: {stderr}"
    );
    for item in ["gen_read", "go"] {
        assert!(
            stderr.contains(&format!("trust-wp: {item} verified")),
            "control: `{item}` must verify; stderr: {stderr}"
        );
    }
    assert!(
        !stderr.contains("verdict withdrawn"),
        "control: a discharged contract must withdraw nothing; stderr: {stderr}"
    );
}
