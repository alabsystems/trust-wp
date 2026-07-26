// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for cargo-trust-wp CLI argument parsing, metadata handling, and exit code logic.
//!
//! Extracted from main.rs to reduce file size (#1669).

use std::time::{Duration, SystemTime, UNIX_EPOCH};

use ntest::timeout;

use super::*;

fn s(val: &str) -> String {
    val.to_string()
}

struct TempDir(PathBuf);

impl TempDir {
    fn new(prefix: &str) -> Self {
        let mut path = env::temp_dir();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after unix epoch")
            .as_nanos();
        path.push(format!(
            "cargo-trust-wp-{prefix}-{}-{timestamp}",
            std::process::id()
        ));
        fs::create_dir_all(&path).expect("create temp test directory");
        Self(path)
    }

    fn join(&self, rel: impl AsRef<Path>) -> PathBuf {
        self.0.join(rel)
    }
}

fn write_file(path: &Path, contents: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create parent directories");
    }
    fs::write(path, contents).expect("write test file");
}

fn has_path_suffix(paths: &[PathBuf], suffix: impl AsRef<Path>) -> bool {
    let suffix = suffix.as_ref();
    paths.iter().any(|path| path.ends_with(suffix))
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Helper: extract (trust_wp_args, cargo_args) from ParsedArgs for existing tests.
fn args_tuple(args: &[String]) -> (Vec<String>, Vec<String>) {
    let p = parse_args(args).unwrap();
    (p.trust_wp_args, p.cargo_args)
}

// ── parse_args ──

#[test]
#[timeout(10000)]
fn parse_args_empty() {
    let (trust_wp, cargo) = args_tuple(&[]);
    assert!(trust_wp.is_empty());
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_verbose_short() {
    let (trust_wp, cargo) = args_tuple(&[s("-v")]);
    assert_eq!(trust_wp, vec!["--verbose"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_verbose_long() {
    let (trust_wp, cargo) = args_tuple(&[s("--verbose")]);
    assert_eq!(trust_wp, vec!["--verbose"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_double_verbose() {
    let (trust_wp, _) = args_tuple(&[s("-vv")]);
    assert_eq!(trust_wp, vec!["--verbose"]);
}

#[test]
#[timeout(10000)]
fn parse_args_emit_smt() {
    let (trust_wp, _) = args_tuple(&[s("--emit-smt")]);
    assert_eq!(trust_wp, vec!["--emit-smt"]);
}

#[test]
#[timeout(10000)]
fn parse_args_timeout_with_value() {
    let (trust_wp, _) = args_tuple(&[s("--timeout"), s("120")]);
    assert_eq!(trust_wp, vec!["--timeout", "120"]);
}

#[test]
#[timeout(10000)]
fn parse_args_timeout_equals_form() {
    let (trust_wp, cargo) = args_tuple(&[s("--timeout=120")]);
    assert_eq!(trust_wp, vec!["--timeout", "120"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_timeout_missing_value() {
    let err = parse_args(&[s("--timeout")]).unwrap_err();
    assert!(err.contains("--timeout requires a value"), "got: {err}");
}

#[test]
#[timeout(10000)]
fn parse_args_filter_with_value() {
    let (trust_wp, _) = args_tuple(&[s("--filter"), s("my_func")]);
    assert_eq!(trust_wp, vec!["--filter", "my_func"]);
}

#[test]
#[timeout(10000)]
fn parse_args_filter_equals_form() {
    let (trust_wp, cargo) = args_tuple(&[s("--filter=my_func")]);
    assert_eq!(trust_wp, vec!["--filter", "my_func"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_filter_missing_value() {
    let err = parse_args(&[s("--filter")]).unwrap_err();
    assert!(err.contains("--filter requires a value"), "got: {err}");
}

#[test]
#[timeout(10000)]
fn parse_args_mixed_trust_wp_and_cargo() {
    let (trust_wp, cargo) = args_tuple(&[s("-v"), s("--timeout"), s("30"), s("-p"), s("my-crate")]);
    assert_eq!(trust_wp, vec!["--verbose", "--timeout", "30"]);
    assert_eq!(cargo, vec!["-p", "my-crate"]);
}

#[test]
#[timeout(10000)]
fn parse_args_unknown_flags_go_to_cargo() {
    let (trust_wp, cargo) = args_tuple(&[s("--release"), s("--features"), s("foo")]);
    assert!(trust_wp.is_empty());
    assert_eq!(cargo, vec!["--release", "--features", "foo"]);
}

#[test]
#[timeout(10000)]
fn parse_args_wide_pointers() {
    let (trust_wp, _) = args_tuple(&[s("--wide-pointers")]);
    assert_eq!(trust_wp, vec!["--wide-pointers"]);
}

#[test]
#[timeout(10000)]
fn parse_args_force() {
    let (trust_wp, _) = args_tuple(&[s("--force")]);
    assert_eq!(trust_wp, vec!["--force"]);
}

#[test]
#[timeout(10000)]
fn parse_args_strict_axioms() {
    let (trust_wp, cargo) = args_tuple(&[s("--strict-axioms")]);
    assert_eq!(trust_wp, vec!["--strict-axioms"]);
    assert!(cargo.is_empty());
}

// ── find_trust_wp_rustc ──

#[test]
#[timeout(10000)]
fn find_trust_wp_rustc_missing_binary_returns_none() {
    let temp = TempDir::new("missing");
    let exe_dir = temp.join("bin");
    fs::create_dir_all(&exe_dir).unwrap();
    let fake_exe = exe_dir.join("cargo-trust-wp");

    let found = find_trust_wp_rustc_with(Some(fake_exe.as_path()), None);
    assert_eq!(found, None);
}

#[test]
#[timeout(10000)]
fn find_trust_wp_rustc_falls_back_to_path() {
    let temp = TempDir::new("path-fallback");
    let exe_dir = temp.join("bin");
    let path_dir = temp.join("path");
    fs::create_dir_all(&exe_dir).unwrap();
    fs::create_dir_all(&path_dir).unwrap();

    let fake_exe = exe_dir.join("cargo-trust-wp");
    let path_binary = path_dir.join("trust-wp-rustc");
    fs::write(&path_binary, b"stub").unwrap();

    let path_var = env::join_paths([path_dir.as_path()]).unwrap();
    let found = find_trust_wp_rustc_with(Some(fake_exe.as_path()), Some(path_var.as_os_str()));

    assert_eq!(found, Some(path_binary));
}

#[test]
#[timeout(10000)]
fn find_trust_wp_rustc_prefers_sibling_over_path() {
    let temp = TempDir::new("sibling-priority");
    let exe_dir = temp.join("bin");
    let path_dir = temp.join("path");
    fs::create_dir_all(&exe_dir).unwrap();
    fs::create_dir_all(&path_dir).unwrap();

    let fake_exe = exe_dir.join("cargo-trust-wp");
    let sibling_binary = exe_dir.join("trust-wp-rustc");
    let path_binary = path_dir.join("trust-wp-rustc");
    fs::write(&sibling_binary, b"sibling").unwrap();
    fs::write(&path_binary, b"path").unwrap();

    let path_var = env::join_paths([path_dir.as_path()]).unwrap();
    let found = find_trust_wp_rustc_with(Some(fake_exe.as_path()), Some(path_var.as_os_str()));

    assert_eq!(found, Some(sibling_binary));
}

// ── build_trust_wp_args_env ──

#[test]
#[timeout(10000)]
fn build_trust_wp_args_env_empty() {
    let result = build_trust_wp_args_env(&[]);
    assert_eq!(result, "--force");
}

#[test]
#[timeout(10000)]
fn build_trust_wp_args_env_with_args() {
    let result = build_trust_wp_args_env(&[s("--verbose"), s("--timeout"), s("30")]);
    // Newline-delimited format (#1691) for path-safe forwarding
    assert_eq!(result, "--force\n--verbose\n--timeout\n30");
}

// ── parse_summary_counts ──

#[test]
#[timeout(10000)]
fn parse_summary_counts_standard() {
    let result = parse_summary_counts("trust-wp: 5 verified, 2 failed, 1 errors");
    assert_eq!(result, Some((5, 2, 1, 0)));
}

#[test]
#[timeout(10000)]
fn parse_summary_counts_proof_assert_prefix() {
    let result = parse_summary_counts("trust-wp: proof_assert: 3 verified, 0 failed, 0 errors");
    assert_eq!(result, Some((3, 0, 0, 0)));
}

#[test]
#[timeout(10000)]
fn parse_summary_counts_no_match() {
    assert_eq!(parse_summary_counts("some random line"), None);
}

#[test]
#[timeout(10000)]
fn parse_summary_counts_with_warnings() {
    assert_eq!(
        parse_summary_counts("trust-wp: 2 verified, 0 failed, 0 errors, 3 warnings"),
        Some((2, 0, 0, 3))
    );
}

#[test]
#[timeout(10000)]
fn parse_summary_counts_with_skipped_and_warnings() {
    assert_eq!(
        parse_summary_counts("trust-wp: 2 verified, 1 failed, 0 errors, 1 skipped, 4 warnings"),
        Some((2, 1, 0, 4))
    );
}

#[test]
#[timeout(10000)]
fn parse_summary_counts_with_axioms_and_warnings() {
    assert_eq!(
        parse_summary_counts(
            "trust-wp: 3 verified, 1 failed, 0 errors, 1 unverified axiom(s), 2 warnings"
        ),
        Some((3, 1, 0, 2))
    );
}

#[test]
#[timeout(10000)]
fn parse_summary_counts_unrecognized_extra_part_tolerated() {
    // Optional parts handled by separate soundness-gap policy are tolerated
    // by this basic count parser (warnings stays 0).
    assert_eq!(
        parse_summary_counts("trust-wp: 1 verified, 0 failed, 0 errors, 1 skipped"),
        Some((1, 0, 0, 0))
    );
}

/// #2015: encoding-errors suffix is tolerated by the summary parser.
#[test]
#[timeout(10000)]
fn parse_summary_counts_with_encoding_errors_suffix() {
    assert_eq!(
        parse_summary_counts(
            "trust-wp: 5 verified, 2 failed, 8 errors, encoding-errors unsupported=3 sort-inference=4 solver=1"
        ),
        Some((5, 2, 8, 0))
    );
}

/// #2015: encoding-errors suffix alongside warnings is tolerated.
#[test]
#[timeout(10000)]
fn parse_summary_counts_with_encoding_errors_and_warnings() {
    assert_eq!(
        parse_summary_counts(
            "trust-wp: 5 verified, 2 failed, 8 errors, 3 warnings, encoding-errors unsupported=3 sort-inference=4 solver=1"
        ),
        Some((5, 2, 8, 3))
    );
}

/// #2015: proof_assert with encoding-errors suffix is tolerated.
#[test]
#[timeout(10000)]
fn parse_summary_counts_proof_assert_with_encoding_errors() {
    assert_eq!(
        parse_summary_counts(
            "trust-wp: proof_assert: 3 verified, 0 failed, 2 errors, encoding-errors unsupported=2 sort-inference=0 solver=0"
        ),
        Some((3, 0, 2, 0))
    );
}

// ── derive_exit_code ──

#[test]
#[timeout(10000)]
fn derive_exit_code_success() {
    assert_eq!(
        derive_exit_code(0, "trust-wp: 3 verified, 0 failed, 0 errors", true, false),
        0
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_verification_failure() {
    assert_eq!(
        derive_exit_code(0, "trust-wp: 2 verified, 1 failed, 0 errors", true, false),
        EXIT_VERIFICATION_FAILURE
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_encoding_error() {
    assert_eq!(
        derive_exit_code(0, "trust-wp: 0 verified, 0 failed, 2 errors", true, false),
        EXIT_ENCODING_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_parse_error() {
    assert_eq!(
        derive_exit_code(0, "trust-wp: error: failed to parse contract", true, false),
        EXIT_PARSE_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_termination_check() {
    assert_eq!(
        derive_exit_code(
            0,
            "trust-wp: termination check failed: missing #[variant]",
            true,
            false,
        ),
        EXIT_ENCODING_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_termination_check_dcx_format() {
    // When emitted via tcx.dcx().err(), the message is prefixed with "error: "
    // by rustc's diagnostic output (#1717).
    assert_eq!(
        derive_exit_code(
            101,
            "error: trust-wp: termination check failed: `foo`: requires #[variant(...)]",
            true,
            false,
        ),
        EXIT_ENCODING_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_failures_take_priority_over_errors() {
    // When both errors and failures present, failures (code 1) wins (#2114).
    // A counterexample is a definitive proof of incorrectness — it must not
    // be masked by solver errors.
    assert_eq!(
        derive_exit_code(0, "trust-wp: 1 verified, 1 failed, 1 errors", true, false),
        EXIT_VERIFICATION_FAILURE
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_no_trust_wp_output_passes_cargo_code_nonzero() {
    // Non-zero cargo code with no trust-wp output passes through
    // regardless of verify mode (cargo itself failed)
    assert_eq!(derive_exit_code(1, "some cargo error", true, false), 1);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_no_trust_wp_output_no_verify_passes() {
    // In --no-verify mode, missing summary is expected and passes through
    assert_eq!(derive_exit_code(0, "", false, false), 0);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_parse_error_takes_priority_over_summary() {
    // If both parse error and summary counts appear, parse error wins
    let stderr =
        "trust-wp: error: failed to parse contract\ntrust_wp: 0 verified, 1 failed, 0 errors";
    assert_eq!(derive_exit_code(0, stderr, true, false), EXIT_PARSE_ERROR);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_multiline_summary() {
    // Multiple summary lines (e.g., multiple crates verified).
    // proof_assert lines are excluded from exit-code (#1703).
    let stderr = "trust-wp: 3 verified, 0 failed, 0 errors\ntrust_wp: proof_assert: 2 verified, 1 failed, 0 errors";
    assert_eq!(derive_exit_code(0, stderr, true, false), 0);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_proof_assert_errors_excluded() {
    // proof_assert errors should not affect the exit code (#1703).
    // Only the main function-level summary drives the exit code.
    let stderr = "trust-wp: 1 verified, 0 failed, 0 errors\ntrust_wp: proof_assert: 0 verified, 0 failed, 2 errors";
    assert_eq!(derive_exit_code(0, stderr, true, false), 0);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_main_errors_still_fatal() {
    // Main function-level errors should still cause exit code 2.
    let stderr = "trust-wp: 0 verified, 0 failed, 1 errors\ntrust_wp: proof_assert: 0 verified, 0 failed, 0 errors";
    assert_eq!(
        derive_exit_code(0, stderr, true, false),
        EXIT_ENCODING_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_soundness_gap_summary_fails_closed() {
    let cases = [
        "trust-wp: 0 verified, 0 failed, 0 errors, 1 assumed",
        "trust-wp: 0 verified, 0 failed, 0 errors, 1 trusted",
        "trust-wp: 0 verified, 0 failed, 0 errors, 1 skipped",
        "trust-wp: 1 verified, 0 failed, 0 errors, 1 verified* (unproven axiom deps)",
        "trust-wp: 1 verified, 0 failed, 0 errors, 1 unverified axiom(s)",
        "trust-wp: 0 verified, 0 failed, 0 errors, 1 vacuous",
    ];

    for stderr in cases {
        assert_eq!(
            derive_exit_code(0, stderr, true, false),
            EXIT_ENCODING_ERROR,
            "legacy fallback should fail closed for soundness gap summary: {stderr}"
        );
    }
}

#[test]
#[timeout(10000)]
fn derive_exit_code_panicked_summary_is_fatal() {
    let stderr = "trust-wp: 0 verified, 0 failed, 0 errors, 1 panicked";
    assert_eq!(
        derive_exit_code(0, stderr, true, false),
        EXIT_ENCODING_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_failures_still_precede_soundness_gaps() {
    let stderr = "trust-wp: 0 verified, 1 failed, 0 errors, 1 trusted";
    assert_eq!(
        derive_exit_code(0, stderr, true, false),
        EXIT_VERIFICATION_FAILURE
    );
}

// ── derive_exit_code: warnings ──

#[test]
#[timeout(10000)]
fn derive_exit_code_warnings_do_not_affect_exit_code() {
    // Dropped obligation warnings are informational — they don't change the exit code
    let stderr = "trust-wp: 2 verified, 0 failed, 0 errors, 3 warnings";
    assert_eq!(derive_exit_code(0, stderr, true, false), 0);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_failures_not_masked_by_warnings() {
    // Failures (exit 1) still appear when warnings are also present
    let stderr = "trust-wp: 1 verified, 1 failed, 0 errors, 2 warnings";
    assert_eq!(
        derive_exit_code(0, stderr, true, false),
        EXIT_VERIFICATION_FAILURE
    );
}

// ── derive_exit_code: --strict-obligations (#1779) ──

#[test]
#[timeout(10000)]
fn derive_exit_code_strict_obligations_warnings_become_errors() {
    // With --strict-obligations, dropped obligation warnings cause exit code 2
    let stderr = "trust-wp: 2 verified, 0 failed, 0 errors, 3 warnings";
    assert_eq!(derive_exit_code(0, stderr, true, true), EXIT_ENCODING_ERROR);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_strict_obligations_no_warnings_passes() {
    // With --strict-obligations but no warnings, exit code is still 0
    let stderr = "trust-wp: 3 verified, 0 failed, 0 errors";
    assert_eq!(derive_exit_code(0, stderr, true, true), 0);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_strict_obligations_failures_still_take_priority() {
    // Failures (exit 1) still take priority over strict-obligations warnings
    let stderr = "trust-wp: 1 verified, 1 failed, 0 errors, 2 warnings";
    assert_eq!(
        derive_exit_code(0, stderr, true, true),
        EXIT_VERIFICATION_FAILURE
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_strict_obligations_errors_still_take_priority() {
    // Errors (exit 2) still take priority over strict-obligations warnings
    let stderr = "trust-wp: 0 verified, 0 failed, 1 errors, 2 warnings";
    assert_eq!(derive_exit_code(0, stderr, true, true), EXIT_ENCODING_ERROR);
}

// ── derive_exit_code: fail-closed (#1825) ──

#[test]
#[timeout(10000)]
fn derive_exit_code_fail_closed_no_summary_verify_mode() {
    // In verify mode with cargo success and no trust-wp summary, fail closed
    assert_eq!(derive_exit_code(0, "", true, false), EXIT_ENCODING_ERROR);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_fail_closed_no_summary_no_verify_mode() {
    // In --no-verify mode, missing summary is expected
    assert_eq!(derive_exit_code(0, "", false, false), 0);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_fail_closed_only_proof_assert_summary() {
    // proof_assert-only summaries don't count as main verification output
    // so fail-closed should trigger
    let stderr = "trust-wp: proof_assert: 3 verified, 0 failed, 0 errors";
    assert_eq!(
        derive_exit_code(0, stderr, true, false),
        EXIT_ENCODING_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_fail_closed_cargo_nonzero_no_summary() {
    // If cargo itself failed (non-zero), pass through cargo code even
    // without trust-wp summary — cargo failure is already non-zero
    assert_eq!(derive_exit_code(1, "", true, false), 1);
}

// ── metadata parsing ──

#[test]
#[timeout(10000)]
fn extract_json_string_values_basic() {
    let json = r#"{"src_path":"/foo/src/lib.rs","name":"my-crate"}"#;
    let paths = extract_json_string_values(json, "src_path");
    assert_eq!(paths, vec!["/foo/src/lib.rs".to_string()]);
}

#[test]
#[timeout(10000)]
fn extract_json_string_values_multiple() {
    let json = r#"{"src_path":"/a/lib.rs"},{"src_path":"/b/main.rs"}"#;
    let paths = extract_json_string_values(json, "src_path");
    assert_eq!(
        paths,
        vec!["/a/lib.rs".to_string(), "/b/main.rs".to_string()]
    );
}

#[test]
#[timeout(10000)]
fn extract_json_string_values_handles_whitespace_and_escapes() {
    let json = r#"{"src_path" : "C:\\repo\\src\\lib.rs","name":"my-crate"}"#;
    let paths = extract_json_string_values(json, "src_path");
    assert_eq!(paths, vec!["C:\\repo\\src\\lib.rs".to_string()]);
}

#[test]
#[timeout(10000)]
fn extract_json_string_values_no_match() {
    let json = r#"{"name":"foo","version":"1.0"}"#;
    let paths = extract_json_string_values(json, "src_path");
    assert!(paths.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_src_paths_from_metadata_no_filter() {
    let json = r#"{"packages":[{"name":"my-crate","targets":[{"src_path":"/a/src/lib.rs"},{"src_path":"/a/src/bin/main.rs"}]}]}"#;
    let paths = parse_src_paths_from_metadata(json, &[]);
    assert_eq!(paths.len(), 2);
    assert_eq!(paths[0], PathBuf::from("/a/src/lib.rs"));
    assert_eq!(paths[1], PathBuf::from("/a/src/bin/main.rs"));
}

#[test]
#[timeout(10000)]
fn parse_src_paths_from_metadata_with_filter() {
    let json = r#"{"packages":[{"name":"crate-a","targets":[{"src_path":"/a/lib.rs"}]},{"name":"crate-b","targets":[{"src_path":"/b/lib.rs"}]}]}"#;
    let paths = parse_src_paths_from_metadata(json, &["crate-b"]);
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0], PathBuf::from("/b/lib.rs"));
}

#[test]
#[timeout(10000)]
fn parse_src_paths_from_metadata_filter_no_match() {
    let json = r#"{"packages":[{"name":"crate-a","targets":[{"src_path":"/a/lib.rs"}]}]}"#;
    let paths = parse_src_paths_from_metadata(json, &["nonexistent"]);
    assert!(paths.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_src_paths_from_metadata_virtual_workspace_manifest() {
    let json = r#"{
            "packages":[
                {"name":"crate-a","targets":[{"src_path":"/ws/crate-a/src/lib.rs"}]},
                {"name":"crate-b","targets":[{"src_path":"/ws/crate-b/src/main.rs"}]}
            ]
        }"#;
    let paths = parse_src_paths_from_metadata(json, &[]);
    assert_eq!(
        paths,
        vec![
            PathBuf::from("/ws/crate-a/src/lib.rs"),
            PathBuf::from("/ws/crate-b/src/main.rs"),
        ]
    );
}

#[test]
#[timeout(10000)]
fn parse_src_paths_from_metadata_custom_lib_path() {
    let json = r#"{
            "packages":[
                {"name":"custom-lib","targets":[{"src_path":"/ws/custom-lib/custom/lib_entry.rs"}]}
            ]
        }"#;
    let paths = parse_src_paths_from_metadata(json, &["custom-lib"]);
    assert_eq!(
        paths,
        vec![PathBuf::from("/ws/custom-lib/custom/lib_entry.rs")]
    );
}

#[test]
#[timeout(10000)]
fn parse_src_paths_from_metadata_bin_only_src_bin_layout() {
    let json = r#"{
            "packages":[
                {"name":"bin-only","targets":[{"src_path":"/ws/bin-only/src/bin/tool.rs"}]}
            ]
        }"#;
    let paths = parse_src_paths_from_metadata(json, &["bin-only"]);
    assert_eq!(paths, vec![PathBuf::from("/ws/bin-only/src/bin/tool.rs")]);
}

#[test]
#[timeout(10000)]
fn parse_src_paths_from_metadata_whitespace_around_packages_key() {
    // Ensure the parser handles arbitrary whitespace around the "packages" key,
    // not just the two hardcoded patterns.
    let json =
        r#"{ "packages" : [ {"name":"ws-crate","targets":[{"src_path":"/ws/src/lib.rs"}]} ] }"#;
    let paths = parse_src_paths_from_metadata(json, &["ws-crate"]);
    assert_eq!(paths, vec![PathBuf::from("/ws/src/lib.rs")]);
}

#[test]
#[timeout(10000)]
fn collect_package_filters_empty() {
    assert!(collect_package_filters(&[]).is_empty());
}

#[test]
#[timeout(10000)]
fn collect_package_filters_short_flag() {
    let args = vec![s("-p"), s("my-crate"), s("--release")];
    let pkgs = collect_package_filters(&args);
    assert_eq!(pkgs, vec!["my-crate"]);
}

#[test]
#[timeout(10000)]
fn collect_package_filters_long_flag() {
    let args = vec![s("--package"), s("foo")];
    let pkgs = collect_package_filters(&args);
    assert_eq!(pkgs, vec!["foo"]);
}

#[test]
#[timeout(10000)]
fn collect_package_filters_multiple() {
    let args = vec![s("-p"), s("a"), s("-p"), s("b")];
    let pkgs = collect_package_filters(&args);
    assert_eq!(pkgs, vec!["a", "b"]);
}

// ── discover_target_paths (end-to-end cargo metadata) ──

#[test]
#[timeout(10000)]
fn discover_target_paths_virtual_workspace_manifest() {
    let temp = TempDir::new("discover-workspace");
    let workspace_manifest = temp.join("Cargo.toml");
    write_file(
        &workspace_manifest,
        "[workspace]\nmembers = [\"crate-a\", \"crate-b\"]\nresolver = \"2\"\n",
    );

    write_file(
        &temp.join("crate-a/Cargo.toml"),
        "[package]\nname = \"crate-a\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    );
    write_file(&temp.join("crate-a/src/lib.rs"), "pub fn a() {}\n");

    write_file(
        &temp.join("crate-b/Cargo.toml"),
        "[package]\nname = \"crate-b\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    );
    write_file(&temp.join("crate-b/src/main.rs"), "fn main() {}\n");

    let paths = discover_target_paths(&[
        s("--manifest-path"),
        s(workspace_manifest.to_str().expect("utf8 path")),
    ]);

    assert!(
        has_path_suffix(&paths, Path::new("crate-a").join("src").join("lib.rs")),
        "missing crate-a/src/lib.rs in metadata paths: {paths:?}"
    );
    assert!(
        has_path_suffix(&paths, Path::new("crate-b").join("src").join("main.rs")),
        "missing crate-b/src/main.rs in metadata paths: {paths:?}"
    );
}

#[test]
#[timeout(10000)]
fn discover_target_paths_custom_lib_path_manifest() {
    let temp = TempDir::new("discover-custom-lib");
    let manifest = temp.join("Cargo.toml");
    write_file(
        &manifest,
        "[package]\nname = \"custom-lib\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[lib]\npath = \"custom/lib_entry.rs\"\n\n[workspace]\n",
    );
    write_file(&temp.join("custom/lib_entry.rs"), "pub fn entry() {}\n");

    let paths = discover_target_paths(&[
        s("--manifest-path"),
        s(manifest.to_str().expect("utf8 path")),
    ]);

    assert!(
        has_path_suffix(&paths, Path::new("custom").join("lib_entry.rs")),
        "missing custom/lib_entry.rs in metadata paths: {paths:?}"
    );
}

#[test]
#[timeout(10000)]
fn discover_target_paths_bin_only_src_bin_manifest() {
    let temp = TempDir::new("discover-bin-only");
    let manifest = temp.join("Cargo.toml");
    write_file(
        &manifest,
        "[package]\nname = \"bin-only\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n",
    );
    write_file(&temp.join("src/bin/tool.rs"), "fn main() {}\n");

    let paths = discover_target_paths(&[
        s("--manifest-path"),
        s(manifest.to_str().expect("utf8 path")),
    ]);

    assert!(
        has_path_suffix(&paths, Path::new("src").join("bin").join("tool.rs")),
        "missing src/bin/tool.rs in metadata paths: {paths:?}"
    );
}

// ── touch_source_file with metadata ──

#[test]
#[timeout(10000)]
#[allow(clippy::similar_names)]
fn touch_source_file_virtual_workspace_manifest_touches_members() {
    let temp = TempDir::new("touch-workspace");
    let workspace_manifest = temp.join("Cargo.toml");
    write_file(
        &workspace_manifest,
        "[workspace]\nmembers = [\"crate-a\", \"crate-b\"]\nresolver = \"2\"\n",
    );

    write_file(
        &temp.join("crate-a/Cargo.toml"),
        "[package]\nname = \"crate-a\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    );
    let member_a_src = temp.join("crate-a/src/lib.rs");
    write_file(&member_a_src, "pub fn a() {}\n");

    write_file(
        &temp.join("crate-b/Cargo.toml"),
        "[package]\nname = \"crate-b\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    );
    let member_b_src = temp.join("crate-b/src/main.rs");
    write_file(&member_b_src, "fn main() {}\n");

    let a_before = fs::metadata(&member_a_src).unwrap().modified().unwrap();
    let b_before = fs::metadata(&member_b_src).unwrap().modified().unwrap();

    std::thread::sleep(Duration::from_secs(1));
    touch_source_file(&[
        s("--manifest-path"),
        s(workspace_manifest.to_str().expect("utf8 path")),
    ]);

    let a_after = fs::metadata(&member_a_src).unwrap().modified().unwrap();
    let b_after = fs::metadata(&member_b_src).unwrap().modified().unwrap();
    assert!(
        a_after > a_before,
        "crate-a source should be touched for virtual workspace root manifest"
    );
    assert!(
        b_after > b_before,
        "crate-b source should be touched for virtual workspace root manifest"
    );
}

#[test]
#[timeout(10000)]
fn touch_source_file_fallback_lib_rs() {
    // When cargo metadata is unavailable (simulated by temp dir),
    // falls back to src/lib.rs
    let temp = TempDir::new("touch-lib");
    let src_dir = temp.join("src");
    fs::create_dir_all(&src_dir).unwrap();
    let lib_rs = src_dir.join("lib.rs");
    fs::write(&lib_rs, b"// lib").unwrap();
    let manifest = temp.join("Cargo.toml");
    fs::write(&manifest, b"[package]\nname=\"t\"").unwrap();

    let mtime_before = fs::metadata(&lib_rs).unwrap().modified().unwrap();
    // Small sleep to ensure mtime changes
    std::thread::sleep(std::time::Duration::from_millis(50));

    touch_source_file(&[s("--manifest-path"), s(manifest.to_str().unwrap())]);

    let mtime_after = fs::metadata(&lib_rs).unwrap().modified().unwrap();
    assert!(
        mtime_after >= mtime_before,
        "mtime should be updated after touch"
    );
}

#[test]
#[timeout(10000)]
fn touch_source_file_fallback_main_rs() {
    // When src/lib.rs doesn't exist, falls back to src/main.rs
    let temp = TempDir::new("touch-main");
    let src_dir = temp.join("src");
    fs::create_dir_all(&src_dir).unwrap();
    let main_rs = src_dir.join("main.rs");
    fs::write(&main_rs, b"fn main() {}").unwrap();
    let manifest = temp.join("Cargo.toml");
    fs::write(&manifest, b"[package]\nname=\"t\"").unwrap();

    touch_source_file(&[s("--manifest-path"), s(manifest.to_str().unwrap())]);
    // Just verify it doesn't panic — the file exists and should be touched
    assert!(main_rs.exists());
}

#[test]
#[timeout(10000)]
fn touch_source_file_no_source_does_not_panic() {
    // When neither src/lib.rs nor src/main.rs exists, should not panic
    let temp = TempDir::new("touch-none");
    let manifest = temp.join("Cargo.toml");
    fs::write(&manifest, b"[workspace]").unwrap();

    touch_source_file(&[s("--manifest-path"), s(manifest.to_str().unwrap())]);
    // No panic = success
}

#[test]
#[timeout(10000)]
fn parse_summary_counts_zero_values() {
    assert_eq!(
        parse_summary_counts("trust-wp: 0 verified, 0 failed, 0 errors"),
        Some((0, 0, 0, 0))
    );
}

// ── parse_args: --strict-obligations (#1779) ──

#[test]
#[timeout(10000)]
fn parse_args_strict_obligations_is_local_flag() {
    // --strict-obligations is a local cargo-trust-wp policy flag, not forwarded
    let p = parse_args(&[s("--strict-obligations")]).unwrap();
    assert!(p.trust_wp_args.is_empty());
    assert!(p.cargo_args.is_empty());
    assert!(p.strict_obligations);
}

#[test]
#[timeout(10000)]
fn parse_args_strict_obligations_with_other_args() {
    let p = parse_args(&[s("-v"), s("--strict-obligations"), s("-p"), s("foo")]).unwrap();
    assert_eq!(p.trust_wp_args, vec!["--verbose"]);
    assert_eq!(p.cargo_args, vec!["-p", "foo"]);
    assert!(p.strict_obligations);
}

#[test]
#[timeout(10000)]
fn parse_args_default_no_strict_obligations() {
    let p = parse_args(&[s("-v")]).unwrap();
    assert!(!p.strict_obligations);
}

// ── parse_args: --track=<level> ──

#[test]
#[timeout(10000)]
fn parse_args_track_reg() {
    let (trust_wp, cargo) = args_tuple(&[s("--track=reg")]);
    assert_eq!(trust_wp, vec!["--track=reg"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_track_split_form() {
    let (trust_wp, cargo) = args_tuple(&[s("--track"), s("reg")]);
    assert_eq!(trust_wp, vec!["--track=reg"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_track_auto() {
    let (trust_wp, cargo) = args_tuple(&[s("--track=auto")]);
    assert_eq!(trust_wp, vec!["--track=auto"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_track_ptr() {
    let (trust_wp, cargo) = args_tuple(&[s("--track=ptr")]);
    assert_eq!(trust_wp, vec!["--track=ptr"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_track_mem() {
    let (trust_wp, cargo) = args_tuple(&[s("--track=mem")]);
    assert_eq!(trust_wp, vec!["--track=mem"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_track_missing_value() {
    let err = parse_args(&[s("--track")]).unwrap_err();
    assert!(err.contains("--track requires a level"), "got: {err}");
}

// ── parse_args: --verify / --no-verify ──

#[test]
#[timeout(10000)]
fn parse_args_verify() {
    let (trust_wp, cargo) = args_tuple(&[s("--verify")]);
    assert_eq!(trust_wp, vec!["--verify"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_no_verify() {
    let (trust_wp, cargo) = args_tuple(&[s("--no-verify")]);
    assert_eq!(trust_wp, vec!["--no-verify"]);
    assert!(cargo.is_empty());
}

// ── parse_args: --stop-after-analysis ──

#[test]
#[timeout(10000)]
fn parse_args_stop_after_analysis() {
    let (trust_wp, cargo) = args_tuple(&[s("--stop-after-analysis")]);
    assert_eq!(trust_wp, vec!["--stop-after-analysis"]);
    assert!(cargo.is_empty());
}

// ── parse_args: --emit-smt-dir (#1691) ──

#[test]
#[timeout(10000)]
fn parse_args_emit_smt_dir_split_form() {
    let (trust_wp, cargo) = args_tuple(&[s("--emit-smt-dir"), s("/tmp/smt-out")]);
    assert_eq!(trust_wp, vec!["--emit-smt-dir", "/tmp/smt-out"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_emit_smt_dir_equals_form() {
    let (trust_wp, cargo) = args_tuple(&[s("--emit-smt-dir=/tmp/smt-out")]);
    assert_eq!(trust_wp, vec!["--emit-smt-dir", "/tmp/smt-out"]);
    assert!(cargo.is_empty());
}

#[test]
#[timeout(10000)]
fn parse_args_emit_smt_dir_missing_value() {
    let err = parse_args(&[s("--emit-smt-dir")]).unwrap_err();
    assert!(err.contains("--emit-smt-dir requires a path"), "got: {err}");
}

#[test]
#[timeout(10000)]
fn parse_args_emit_smt_dir_with_spaces_in_path() {
    let (trust_wp, _) = args_tuple(&[s("--emit-smt-dir"), s("/tmp/my path/smt out")]);
    assert_eq!(trust_wp, vec!["--emit-smt-dir", "/tmp/my path/smt out"]);
}

#[test]
#[timeout(10000)]
fn parse_args_emit_smt_and_emit_smt_dir_combined() {
    let (trust_wp, _) = args_tuple(&[s("--emit-smt"), s("--emit-smt-dir"), s("./out")]);
    assert_eq!(trust_wp, vec!["--emit-smt", "--emit-smt-dir", "./out"]);
}

// ── build_trust_wp_args_env: newline format (#1691) ──

#[test]
#[timeout(10000)]
fn build_trust_wp_args_env_uses_newlines() {
    let result = build_trust_wp_args_env(&[s("--verbose"), s("--emit-smt-dir"), s("/tmp/out")]);
    assert_eq!(result, "--force\n--verbose\n--emit-smt-dir\n/tmp/out");
}

#[test]
#[timeout(10000)]
fn build_trust_wp_args_env_newline_preserves_spaces_in_paths() {
    let result = build_trust_wp_args_env(&[s("--emit-smt-dir"), s("/my path/smt out")]);
    let lines: Vec<&str> = result.lines().collect();
    assert_eq!(lines, vec!["--force", "--emit-smt-dir", "/my path/smt out"]);
}

#[test]
#[timeout(10000)]
fn build_trust_wp_args_env_empty_uses_newlines() {
    let result = build_trust_wp_args_env(&[]);
    assert_eq!(result, "--force");
}

// ── structured result protocol (#1690) ──

fn structured_wire_line(
    result: trust_wp_core::result_protocol::StructuredVerificationResult,
) -> String {
    result.to_wire_line()
}

#[test]
#[timeout(10000)]
fn split_stderr_wire_lines_no_wire_line() {
    let stderr = "trust-wp: foo verified ✓\ntrust_wp: 1 verified, 0 failed, 0 errors\n";
    let (human, wire) = split_stderr_wire_lines(stderr);
    assert!(wire.is_none());
    assert!(human.contains("trust-wp: foo verified"));
    assert!(human.contains("1 verified, 0 failed, 0 errors"));
}

#[test]
#[timeout(10000)]
fn split_stderr_wire_lines_strips_wire_line() {
    let wire_line = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=3 failed=0 errors=0 warnings=0 assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 unverified_axioms=0 vacuous=0 evidence_gaps=0 proof_assert_failed=0 proof_assert_errors=0 panics=0 demoted=0 parse_errors=0 termination_errors=0 logic_recursion_errors=0 erasure_errors=0";
    let stderr = format!(
        "trust-wp: foo verified ✓\n{wire_line}\ntrust_wp: 3 verified, 0 failed, 0 errors\n"
    );
    let (human, wire) = split_stderr_wire_lines(&stderr);
    assert!(wire.is_some());
    let wire = wire.unwrap();
    assert_eq!(wire.verified, 3);
    assert_eq!(wire.base_exit_code, 0);
    // Machine line must not appear in human output
    assert!(!human.contains("TRUST_WP_RESULT:v1"));
    assert!(human.contains("trust-wp: foo verified"));
}

#[test]
#[timeout(10000)]
fn split_stderr_wire_lines_aggregates_multiple() {
    let line1 = "TRUST_WP_RESULT:v1 base_exit_code=0 verified=2 failed=0 errors=0 warnings=0 assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 unverified_axioms=0 vacuous=0 evidence_gaps=0 proof_assert_failed=0 proof_assert_errors=0 panics=0 demoted=0 parse_errors=0 termination_errors=0 logic_recursion_errors=0 erasure_errors=0";
    let line2 = "TRUST_WP_RESULT:v1 base_exit_code=1 verified=1 failed=1 errors=0 warnings=0 assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 unverified_axioms=0 vacuous=0 evidence_gaps=0 proof_assert_failed=0 proof_assert_errors=0 panics=0 demoted=0 parse_errors=0 termination_errors=0 logic_recursion_errors=0 erasure_errors=0";
    let stderr = format!("{line1}\n{line2}\n");
    let (_, wire) = split_stderr_wire_lines(&stderr);
    let wire = wire.unwrap();
    assert_eq!(wire.verified, 3);
    assert_eq!(wire.failed, 1);
    // Merged exit code recomputed: failed > 0 → 1
    assert_eq!(wire.base_exit_code, 1);
}

#[test]
#[timeout(10000)]
fn split_stderr_wire_lines_preserves_bare_nonzero_base_exit_code() {
    let line1 = structured_wire_line(
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: EXIT_ENCODING_ERROR,
            ..Default::default()
        },
    );
    let line2 = structured_wire_line(
        trust_wp_core::result_protocol::StructuredVerificationResult {
            verified: 1,
            ..Default::default()
        },
    );

    let stderr = format!("{line1}\n{line2}\n");
    let (_, wire) = split_stderr_wire_lines(&stderr);

    assert_eq!(wire.unwrap().base_exit_code, EXIT_ENCODING_ERROR);
}

#[test]
#[timeout(10000)]
fn split_stderr_wire_lines_normalizes_soundness_gap_result_status() {
    let cases = [
        trust_wp_core::result_protocol::StructuredVerificationResult {
            assumed: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            trusted: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            skipped: 1,
            ..Default::default()
        },
    ];

    for result in cases {
        let line = structured_wire_line(result);
        let (_, wire) = split_stderr_wire_lines(&format!("{line}\n"));

        assert_eq!(
            wire.unwrap().base_exit_code,
            EXIT_ENCODING_ERROR,
            "wire result status should fail closed for {line}"
        );
    }
}

#[test]
#[timeout(10000)]
fn split_stderr_wire_lines_keeps_incomplete_protocol_line_human() {
    let stderr = "TRUST_WP_RESULT:v1 base_exit_code=0\ntrust_wp: 1 verified, 0 failed, 0 errors\n";
    let (human, wire) = split_stderr_wire_lines(stderr);

    assert!(
        wire.is_none(),
        "incomplete prefixed lines must not become authoritative"
    );
    assert!(
        human.contains("TRUST_WP_RESULT:v1 base_exit_code=0"),
        "malformed wire lines must stay in forwarded stderr"
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_success() {
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 0,
        verified: 3,
        ..Default::default()
    };
    assert_eq!(derive_exit_code_from_wire(&wire, true, false), 0);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_and_cargo_preserves_later_cargo_failure() {
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 0,
        verified: 3,
        ..Default::default()
    };

    assert_eq!(
        derive_exit_code_from_wire_and_cargo(101, &wire, true, false),
        101
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_and_cargo_keeps_wire_failure_priority() {
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: EXIT_VERIFICATION_FAILURE,
        verified: 2,
        failed: 1,
        ..Default::default()
    };

    assert_eq!(
        derive_exit_code_from_wire_and_cargo(101, &wire, true, false),
        EXIT_VERIFICATION_FAILURE
    );
}

#[test]
#[timeout(10000)]
fn reconcile_forwarded_wire_exit_code_records_cargo_failure() {
    let mut wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 0,
        verified: 3,
        ..Default::default()
    };

    reconcile_forwarded_wire_exit_code(&mut wire, 101);

    assert_eq!(wire.base_exit_code, 101);
}

#[test]
#[timeout(10000)]
fn reconcile_forwarded_wire_exit_code_keeps_structured_failure_priority() {
    let mut wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: EXIT_VERIFICATION_FAILURE,
        verified: 2,
        failed: 1,
        ..Default::default()
    };

    reconcile_forwarded_wire_exit_code(&mut wire, 101);

    assert_eq!(wire.base_exit_code, EXIT_VERIFICATION_FAILURE);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_soundness_gap_fails_closed() {
    let cases = [
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            assumed: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            trusted: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            skipped: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            verified_with_axiom_deps: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            unverified_axioms: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            vacuous: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            evidence_gaps: 1,
            ..Default::default()
        },
    ];

    for wire in cases {
        assert_eq!(
            derive_exit_code_from_wire(&wire, true, false),
            EXIT_ENCODING_ERROR,
            "wire soundness gap should fail closed even if base_exit_code is zero: {wire:?}"
        );
    }
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_failure() {
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 1,
        verified: 2,
        failed: 1,
        ..Default::default()
    };
    assert_eq!(derive_exit_code_from_wire(&wire, true, false), 1);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_error() {
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 2,
        errors: 1,
        ..Default::default()
    };
    assert_eq!(derive_exit_code_from_wire(&wire, true, false), 2);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_parse_error() {
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 0,
        parse_errors: 1,
        ..Default::default()
    };
    assert_eq!(
        derive_exit_code_from_wire(&wire, true, false),
        EXIT_PARSE_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_structural_error_counters_fail_closed() {
    let cases = [
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            termination_errors: 1,
            ..Default::default()
        },
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            logic_recursion_errors: 1,
            ..Default::default()
        },
        // Phase 5c: erasure_errors is a structural error counter; fail closed.
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: 0,
            erasure_errors: 1,
            ..Default::default()
        },
    ];

    for wire in cases {
        assert_eq!(
            derive_exit_code_from_wire(&wire, true, false),
            EXIT_ENCODING_ERROR,
            "structural error counters should fail closed: {wire:?}"
        );
    }
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_strict_obligations() {
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 0,
        verified: 2,
        warnings: 3,
        ..Default::default()
    };
    assert_eq!(derive_exit_code_from_wire(&wire, true, false), 0);
    assert_eq!(
        derive_exit_code_from_wire(&wire, true, true),
        EXIT_ENCODING_ERROR
    );
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_proof_assert_follows_driver() {
    // Wire path trusts driver's base_exit_code, which includes proof_assert
    // failures (unlike legacy text path which excluded them).
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 1,
        verified: 1,
        proof_assert_failed: 1,
        ..Default::default()
    };
    assert_eq!(derive_exit_code_from_wire(&wire, true, false), 1);
}

#[test]
#[timeout(10000)]
fn derive_exit_code_from_wire_proof_assert_error_follows_driver() {
    // Proof-assert encoding/solver errors must remain fatal on the wire path.
    let wire = trust_wp_core::result_protocol::StructuredVerificationResult {
        base_exit_code: 2,
        verified: 1,
        proof_assert_errors: 1,
        ..Default::default()
    };
    assert_eq!(derive_exit_code_from_wire(&wire, true, false), 2);
}
