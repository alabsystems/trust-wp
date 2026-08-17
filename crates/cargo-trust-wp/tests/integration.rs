// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the `targo-trust-wp` command and its
//! `cargo-trust-wp` compatibility alias.
//!
//! These tests verify the cargo subcommand behavior including:
//! - Help output
//! - Version output
//! - Argument parsing
//!
//! Note: Full end-to-end tests with trust-wp-rustc require a nightly toolchain
//! and the trust-wp-driver binary built, so those tests are run separately.

use std::process::Command;

use ntest::timeout;
use trust_wp_test_utils::cargo_trust_wp_bin;

const CARGO_TRUST_WP_VERSION: &str = env!("CARGO_PKG_VERSION");

fn targo_trust_wp_bin() -> &'static str {
    env!("CARGO_BIN_EXE_targo-trust-wp")
}

#[test]
#[timeout(10000)]
fn test_help_flag() {
    let output = Command::new(cargo_trust_wp_bin())
        .arg("--help")
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--help should succeed; stderr: {stderr}"
    );
    assert!(
        stdout.contains("targo-trust-wp"),
        "missing primary 'targo-trust-wp' name in help; stdout: {stdout}"
    );
    assert!(
        stdout.contains("back-compat alias: cargo trust-wp"),
        "missing cargo compatibility alias in help; stdout: {stdout}"
    );
    assert!(
        stdout.contains("USAGE"),
        "missing 'USAGE' in help; stdout: {stdout}"
    );
    assert!(
        stdout.contains("-v, -vv, --verbose"),
        "missing verbose alias line in help; stdout: {stdout}"
    );
    assert!(
        !stdout.contains("Very verbose output"),
        "help should not advertise a fake second verbosity tier; stdout: {stdout}"
    );
    assert!(
        stdout.contains("--emit-smt"),
        "missing '--emit-smt' in help; stdout: {stdout}"
    );
    assert!(
        stdout.contains("--track <level>"),
        "missing split-form '--track <level>' in help; stdout: {stdout}"
    );
    assert!(
        stdout.contains("TRUST_WP_LOG=<target>=<level>[,...]"),
        "missing TRUST_WP_LOG help block; stdout: {stdout}"
    );
    assert!(
        stdout.contains("targets: callbacks, mir_analysis, encoder, verify, memory_model"),
        "missing log target alias list; stdout: {stdout}"
    );
    assert!(
        stdout.contains("EXIT CODES"),
        "missing 'EXIT CODES' in help; stdout: {stdout}"
    );
    assert!(
        stderr.is_empty(),
        "--help should write help text to stdout only; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_short_help_flag() {
    let output = Command::new(cargo_trust_wp_bin())
        .arg("-h")
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "-h should succeed; stderr: {stderr}"
    );
    assert!(
        stdout.contains("USAGE"),
        "missing 'USAGE' in -h output; stdout: {stdout}"
    );
    assert!(
        stderr.is_empty(),
        "-h should write help text to stdout only; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_version_flag() {
    let output = Command::new(cargo_trust_wp_bin())
        .arg("--version")
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--version should succeed; stderr: {stderr}"
    );
    assert!(
        stdout.contains("cargo-trust-wp"),
        "missing 'cargo-trust-wp' in version; stdout: {stdout}"
    );
    assert!(
        stdout.contains(CARGO_TRUST_WP_VERSION),
        "missing version number in --version; stdout: {stdout}"
    );
    assert!(
        stderr.is_empty(),
        "--version should write version text to stdout only; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_primary_version_flag() {
    let output = Command::new(targo_trust_wp_bin())
        .arg("--version")
        .output()
        .expect("failed to execute targo-trust-wp");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--version should succeed; stderr: {stderr}"
    );
    assert!(
        stdout.contains("targo-trust-wp"),
        "missing 'targo-trust-wp' in primary version output; stdout: {stdout}"
    );
    assert!(
        stdout.contains(CARGO_TRUST_WP_VERSION),
        "missing version number in primary --version; stdout: {stdout}"
    );
    assert!(
        stderr.is_empty(),
        "--version should write version text to stdout only; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_short_version_flag() {
    let output = Command::new(cargo_trust_wp_bin())
        .arg("-V")
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "-V should succeed; stderr: {stderr}"
    );
    assert!(
        stdout.contains(CARGO_TRUST_WP_VERSION),
        "missing version number in -V; stdout: {stdout}"
    );
    assert!(
        stderr.is_empty(),
        "-V should write version text to stdout only; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_timeout_missing_value_is_parse_error() {
    let output = Command::new(cargo_trust_wp_bin())
        .arg("--timeout")
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(3),
        "--timeout without value should exit with code 3 (parse error); stderr: {stderr}"
    );
    assert!(
        stderr.contains("--timeout requires a value"),
        "missing diagnostic for --timeout; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_filter_missing_value_is_parse_error() {
    let output = Command::new(cargo_trust_wp_bin())
        .arg("--filter")
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(3),
        "--filter without value should exit with code 3 (parse error); stderr: {stderr}"
    );
    assert!(
        stderr.contains("--filter requires a value"),
        "missing diagnostic for --filter; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_timeout_with_value_does_not_error() {
    // --timeout with a value should not produce a parse error.
    // It will fail for other reasons (no trust-wp-rustc) but NOT with exit code 3.
    let output = Command::new(cargo_trust_wp_bin())
        .args(["--timeout", "120", "--help"])
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--timeout 120 --help should succeed; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_filter_with_value_does_not_error() {
    // --filter with a value should not produce a parse error.
    let output = Command::new(cargo_trust_wp_bin())
        .args(["--filter", "my_func", "--help"])
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--filter my_func --help should succeed; stderr: {stderr}"
    );
}

#[test]
#[timeout(10000)]
fn test_trust_wp_subcommand_arg_is_stripped() {
    // When invoked as `cargo trust-wp --help`, cargo passes "trust-wp" as first arg
    let output = Command::new(cargo_trust_wp_bin())
        .args(["trust-wp", "--help"])
        .output()
        .expect("failed to execute cargo-trust-wp");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "'trust-wp --help' should succeed; stderr: {stderr}"
    );
    assert!(
        stdout.contains("USAGE"),
        "missing 'USAGE' in trust-wp --help; stdout: {stdout}"
    );
    assert!(
        stderr.is_empty(),
        "'trust-wp --help' should write help text to stdout only; stderr: {stderr}"
    );
}
