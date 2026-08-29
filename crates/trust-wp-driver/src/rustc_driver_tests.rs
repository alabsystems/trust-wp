// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for trust-wp-rustc CLI option parsing.
//!
//! Extracted from rustc_driver.rs to stay within file size limits (#1691).

use callbacks::TrackLevel;

use super::*;

#[test]
fn test_parse_track_level_auto() {
    let opts = parse_opts_vec(&["--track=auto".to_string()]);
    assert_eq!(opts.track_level, TrackLevel::Auto);
}

#[test]
fn test_parse_track_level_reg() {
    let opts = parse_opts_vec(&["--track=reg".to_string()]);
    assert_eq!(opts.track_level, TrackLevel::Reg);
}

#[test]
fn test_parse_track_level_ptr() {
    let opts = parse_opts_vec(&["--track=ptr".to_string()]);
    assert_eq!(opts.track_level, TrackLevel::Ptr);
}

#[test]
fn test_parse_track_level_mem() {
    let opts = parse_opts_vec(&["--track=mem".to_string()]);
    assert_eq!(opts.track_level, TrackLevel::Mem);
}

#[test]
fn test_parse_track_level_unknown_fallback() {
    // Unknown track level should fall back to Auto
    let opts = parse_opts_vec(&["--track=foo".to_string()]);
    assert_eq!(opts.track_level, TrackLevel::Auto);
}

#[test]
fn test_parse_wide_pointers() {
    let opts = parse_opts_vec(&["--wide-pointers".to_string()]);
    assert!(opts.wide_pointers);

    // Default should be false
    let opts = parse_opts_vec(&[]);
    assert!(!opts.wide_pointers);
}

#[test]
fn test_parse_track_with_other_opts() {
    let opts = parse_opts_vec(&[
        "--verbose".to_string(),
        "--track=mem".to_string(),
        "--wide-pointers".to_string(),
        "--emit-smt".to_string(),
    ]);
    assert!(opts.verbose);
    assert_eq!(opts.track_level, TrackLevel::Mem);
    assert!(opts.wide_pointers);
    assert!(opts.emit_smt);
}

#[test]
fn test_parse_track_default_is_auto() {
    // When no --track is specified, default should be Auto
    let opts = parse_opts_vec(&["--verbose".to_string()]);
    assert_eq!(opts.track_level, TrackLevel::Auto);
}

#[test]
fn test_parse_strict_axioms() {
    let opts = parse_opts_vec(&["--strict-axioms".to_string()]);
    assert!(opts.strict_axioms);

    // Default should be false
    let opts = parse_opts_vec(&[]);
    assert!(!opts.strict_axioms);
}

#[test]
fn test_parse_strict_trust_default_on() {
    // Phase 1 soundness gate (#20): default ON, no flags required.
    let opts = parse_opts_vec(&[]);
    assert!(
        opts.strict_trust,
        "strict_trust must default to true (Phase 1 soundness gate)"
    );
}

#[test]
fn test_parse_strict_trust_explicit() {
    let opts = parse_opts_vec(&["--strict-trust".to_string()]);
    assert!(opts.strict_trust, "--strict-trust must set strict_trust");
}

#[test]
fn test_parse_no_strict_trust_is_ignored() {
    let opts = parse_opts_vec(&["--no-strict-trust".to_string()]);
    assert!(
        opts.strict_trust,
        "the deprecated flag must not disable proof authority"
    );
}

#[test]
fn test_parse_strict_trust_then_no_cannot_override() {
    let opts = parse_opts_vec(&[
        "--strict-trust".to_string(),
        "--no-strict-trust".to_string(),
    ]);
    assert!(opts.strict_trust);
}

#[test]
fn test_parse_opts_string_with_track() {
    // Test parse_opts_string path (used by TRUST_WP_ARGS env var)
    let opts = parse_opts_string("--verbose --track=ptr --wide-pointers");
    assert!(opts.verbose);
    assert_eq!(opts.track_level, TrackLevel::Ptr);
    assert!(opts.wide_pointers);
}

#[test]
fn test_no_verify_alone_skips_verification() {
    let opts = parse_opts_vec(&["--no-verify".to_string()]);
    assert!(!opts.verify, "--no-verify alone must disable verification");
}

#[test]
fn test_no_verify_with_emit_smt_skips_verification() {
    let opts = parse_opts_vec(&["--no-verify".to_string(), "--emit-smt".to_string()]);
    assert!(
        !opts.verify,
        "--no-verify --emit-smt must disable verification"
    );
}

#[test]
fn test_default_enables_verification() {
    let opts = parse_opts_vec(&[]);
    assert!(opts.verify, "default (no flags) must enable verification");
}

#[test]
fn test_verify_with_emit_smt_enables_verification() {
    let opts = parse_opts_vec(&["--verify".to_string(), "--emit-smt".to_string()]);
    assert!(opts.verify, "--verify --emit-smt must enable verification");
}

#[test]
fn test_emit_smt_alone_disables_verification() {
    let opts = parse_opts_vec(&["--emit-smt".to_string()]);
    assert!(!opts.verify, "--emit-smt alone must disable verification");
}

#[test]
fn test_is_rustc_path_bare_name() {
    assert!(is_rustc_path("rustc"));
    assert!(is_rustc_path("trustc"));
    assert!(!is_rustc_path("cargo"));
    assert!(!is_rustc_path("gcc"));
}

#[test]
fn test_is_rustc_path_full_path() {
    // Unix paths
    assert!(is_rustc_path("/usr/bin/rustc"));
    assert!(is_rustc_path(
        "/home/user/.rustup/toolchains/nightly/bin/rustc"
    ));
    assert!(is_rustc_path("/path/to/rustc"));
    assert!(is_rustc_path("/path/to/trustc"));

    // Windows paths
    assert!(is_rustc_path(
        "C:\\Users\\user\\.rustup\\toolchains\\nightly\\bin\\rustc.exe"
    ));
    assert!(is_rustc_path("C:\\Program Files\\Rust\\bin\\rustc"));
    assert!(is_rustc_path("C:\\Program Files\\Trust\\bin\\trustc.exe"));
}

#[test]
fn test_is_rustc_path_case_insensitive() {
    assert!(is_rustc_path("RUSTC"));
    assert!(is_rustc_path("Rustc"));
    assert!(is_rustc_path("/path/to/RUSTC"));
    assert!(is_rustc_path("rustc.EXE"));
    assert!(is_rustc_path("TRUSTC"));
    assert!(is_rustc_path("/path/to/Trustc"));
    assert!(is_rustc_path("trustc.EXE"));
}

#[test]
fn test_is_rustc_path_negative_cases() {
    // Should not match trust-wp-rustc
    assert!(!is_rustc_path("trust-wp-rustc"));
    assert!(!is_rustc_path("/path/to/trust-wp-rustc"));
    assert!(!is_rustc_path("trust-wp-trustc"));
    assert!(!is_rustc_path("/path/to/trust-wp-trustc"));

    // Should not match non-rustc binaries
    assert!(!is_rustc_path("cargo"));
    assert!(!is_rustc_path("/usr/bin/cargo"));
    assert!(!is_rustc_path("-"));
    assert!(!is_rustc_path("--crate-name"));
}

// ── --emit-smt-dir parsing (#1691) ──

#[test]
fn test_parse_emit_smt_dir_split() {
    let opts = parse_opts_vec(&["--emit-smt-dir".to_string(), "/tmp/smt-out".to_string()]);
    assert_eq!(
        opts.emit_smt_dir.as_deref(),
        Some(std::path::Path::new("/tmp/smt-out"))
    );
}

#[test]
fn test_parse_emit_smt_dir_equals() {
    let opts = parse_opts_vec(&["--emit-smt-dir=/tmp/smt-out".to_string()]);
    assert_eq!(
        opts.emit_smt_dir.as_deref(),
        Some(std::path::Path::new("/tmp/smt-out"))
    );
}

#[test]
fn test_parse_emit_smt_dir_default_none() {
    let opts = parse_opts_vec(&["--verbose".to_string()]);
    assert!(opts.emit_smt_dir.is_none());
}

#[test]
fn test_parse_emit_smt_dir_follows_emit_only_default() {
    // --emit-smt-dir without --verify should disable verification
    let opts = parse_opts_vec(&["--emit-smt-dir".to_string(), "/tmp/out".to_string()]);
    assert!(
        !opts.verify,
        "--emit-smt-dir alone must disable verification"
    );
}

#[test]
fn test_parse_emit_smt_dir_with_verify_enables_verification() {
    let opts = parse_opts_vec(&[
        "--emit-smt-dir".to_string(),
        "/tmp/out".to_string(),
        "--verify".to_string(),
    ]);
    assert!(
        opts.verify,
        "--emit-smt-dir --verify must enable verification"
    );
}

// ── newline-safe parse_opts_string (#1691) ──

#[test]
fn test_parse_opts_string_newline_format() {
    let opts = parse_opts_string("--force\n--verbose\n--emit-smt-dir\n/tmp/smt out");
    assert!(opts.force_callbacks);
    assert!(opts.verbose);
    assert_eq!(
        opts.emit_smt_dir.as_deref(),
        Some(std::path::Path::new("/tmp/smt out"))
    );
}

#[test]
fn test_parse_opts_string_legacy_whitespace_format() {
    // Legacy format without newlines should still work
    let opts = parse_opts_string("--force --verbose --emit-smt");
    assert!(opts.force_callbacks);
    assert!(opts.verbose);
    assert!(opts.emit_smt);
}

#[test]
fn test_parse_help_request_from_option_lane() {
    let request = parse_trust_wp_request_vec(&["--help".to_string()]);
    assert!(request.help_requested);
}

#[test]
fn test_parse_help_request_from_trust_wp_args_env() {
    let request = parse_trust_wp_request_string("--help");
    assert!(request.help_requested);
}

#[test]
fn test_render_trust_wp_help_mentions_logging_aliases() {
    let help = render_trust_wp_help();
    assert!(help.contains("TRUST_WP_LOG=<target>=<level>[,...]"));
    assert!(help.contains("callbacks"));
}

#[test]
fn test_parse_opts_string_newline_ignores_empty_lines() {
    let opts = parse_opts_string("--force\n\n--verbose\n");
    assert!(opts.force_callbacks);
    assert!(opts.verbose);
}

#[test]
fn test_solver_stack_defaults_pinned() {
    // Pin the exact env names/values ay reads (env-read-only knobs in
    // ay-dpll's executor). A typo here would silently disable the certified
    // composed stack, so the full table is asserted verbatim.
    //
    // AY_DT_LAZY_AUFLIA_INCR is intentionally ABSENT: ay 0.7 hard-clamped
    // the incremental lazy-DT lane and by v0.13.0 the var has zero read
    // sites (see the DEFAULT_SOLVER_STACK doc). Do not restore it without
    // a read site — test_solver_stack_vars_have_read_sites_in_linked_ay
    // enforces that for every entry.
    assert_eq!(
        DEFAULT_SOLVER_STACK,
        &[
            ("AY_DT_LAZY_AUFLIA", "1"),
            ("AY_DT_LAZY_AUFLIA_EAGER", "1"),
            ("AY_DT_CERT", "on"),
            ("AY_DT_CERT_BRIDGE_ROUTE", "1"),
        ]
    );
}

/// ROT GUARD: every `DEFAULT_SOLVER_STACK` var must have a read site in the
/// linked ay source tree.
///
/// These are env-read-only knobs: ay consults them at their use sites and
/// there is no registration or error for an unknown var, so when ay deletes
/// a read site the stack entry rots into a silent no-op. That happened
/// across ay 0.5 -> 0.7 (`AY_DT_LAZY_AUFLIA_INCR` removed,
/// `AY_DT_CERT_BRIDGE_ROUTE` demoted to its shadow/audit lane) and was only
/// caught by a manual delta scout.
///
/// Same guard style as the `cert.*` accounting pin in
/// `callbacks/reporting.rs` (`linked_ay_publishes_process_cumulative_cert_
/// accounting`, 148d743): a name-level pin of a linked-ay assumption that
/// fails loudly when the linked ay changes. Retire-on-signal: when this
/// fails, the fix is to remove or replace the dead stack entry (or update
/// the dep-path parsing if the ay link itself moved) — never to relax the
/// guard.
#[test]
fn test_solver_stack_vars_have_read_sites_in_linked_ay() {
    // Resolve the linked ay-dpll source tree from the workspace manifest's
    // path dependency, so the guard follows the actual link rather than a
    // hardcoded sibling-checkout assumption.
    let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("workspace root two levels above crates/trust-wp-driver");
    let manifest_path = workspace_root.join("Cargo.toml");
    let manifest = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|e| panic!("read workspace manifest {}: {e}", manifest_path.display()));
    let dep_line = manifest
        .lines()
        .find(|line| {
            let t = line.trim_start();
            t.starts_with("ay-dpll") && t.contains("path")
        })
        .expect("workspace manifest declares an ay-dpll path dependency");
    let rel_path = dep_line
        .split('"')
        .nth(1)
        .expect("ay-dpll dependency line carries a quoted path");
    let ay_dpll_src = workspace_root.join(rel_path).join("src");
    assert!(
        ay_dpll_src.is_dir(),
        "linked ay-dpll source tree not found at {} — the ay link moved; \
         update the dep-path parsing in this guard",
        ay_dpll_src.display()
    );

    // Collect non-test .rs sources. Test-only occurrences (ay's own
    // ScopedEnvVar test scaffolding, the `executor_tests` tree) are not read
    // sites — a var read only by ay's tests is still a production no-op.
    fn collect_non_test_rs(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(dir).expect("read ay-dpll src dir") {
            let entry = entry.expect("read ay-dpll src dir entry");
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().into_owned();
            if path.is_dir() {
                if name == "tests" || name.ends_with("_tests") {
                    continue;
                }
                collect_non_test_rs(&path, out);
            } else if name.ends_with(".rs")
                && !name.ends_with("_tests.rs")
                && !name.starts_with("test_")
                && name != "tests.rs"
            {
                out.push(path);
            }
        }
    }
    let mut sources = Vec::new();
    collect_non_test_rs(&ay_dpll_src, &mut sources);
    assert!(
        sources.len() > 100,
        "implausibly few non-test .rs files ({}) under {} — guard is \
         scanning the wrong tree",
        sources.len(),
        ay_dpll_src.display()
    );

    for (var, _) in DEFAULT_SOLVER_STACK {
        // A read site references the var name as a string literal
        // (`std::env::var("...")` / `var_os("...")`).
        let needle = format!("\"{var}\"");
        let read_site = sources.iter().find(|path| {
            std::fs::read_to_string(path)
                .map(|src| src.contains(&needle))
                .unwrap_or(false)
        });
        assert!(
            read_site.is_some(),
            "DEFAULT_SOLVER_STACK sets {var} but the linked ay source tree \
             ({}) has no non-test read site for it — the entry is a silent \
             no-op (this is how AY_DT_LAZY_AUFLIA_INCR rotted across ay \
             0.5 -> 0.7). Remove the entry or fix its name; do not relax \
             this guard",
            ay_dpll_src.display()
        );
    }
}

#[test]
fn test_solver_stack_defaults_apply_all_when_absent() {
    // Nothing pre-set: every default is planned, in table order.
    let plan = solver_stack_defaults_to_apply(|_| false);
    assert_eq!(plan, DEFAULT_SOLVER_STACK.to_vec());
}

#[test]
fn test_solver_stack_defaults_respect_preset_values() {
    // A var already present in the environment must never be overridden —
    // regardless of its value. This is the override contract: an explicit
    // disabling value (e.g. AY_DT_CERT=off, AY_DT_LAZY_AUFLIA=0) is
    // "present" just the same, so it wins over the default.
    let plan = solver_stack_defaults_to_apply(|name| name == "AY_DT_CERT");
    assert!(plan.iter().all(|(name, _)| *name != "AY_DT_CERT"));
    assert_eq!(plan.len(), DEFAULT_SOLVER_STACK.len() - 1);
}

#[test]
fn test_solver_stack_defaults_noop_when_all_preset() {
    // Fully user-configured environment: the planner is a no-op.
    let plan = solver_stack_defaults_to_apply(|_| true);
    assert!(plan.is_empty());
}
