// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub
)]

//! Cargo trust-wp - Cargo subcommand for trust-wp verification
//!
//! This binary is invoked as `cargo trust-wp` and sets up the environment
//! to run trust-wp verification on the current project. It discovers the
//! `trust-wp-rustc` binary, sets `RUSTC_WRAPPER`, and forwards CLI options
//! to the trust-wp driver via the `TRUST_WP_ARGS` environment variable.
//!
//! Usage:
//!   `cargo trust-wp [OPTIONS] [CARGO_OPTS]`
//!
//! Options:
//!   `-v`, `-vv`, `--verbose`    Show detailed verification progress
//!   `--emit-smt`                Output SMT-LIB2 queries to stdout (for debugging)
//!   `--emit-smt-dir <path>`     Write per-function .smt2 files with source comments
//!   `--force`                   Run trust-wp analysis even without trust-wp dependency
//!   `--timeout <secs>`          Per-function verification timeout (default: 60)
//!   `--filter <name>`           Only verify functions matching pattern
//!   `--track <level>`           Set memory tracking level (auto, reg, ptr, mem)
//!   `--wide-pointers`           Enable wide pointer support (unimplemented)
//!   `--strict-axioms`           Treat unverified axioms as errors
//!   `--strict-trust`            Reject proofs with trust/hole steps (default ON)
//!   `--no-strict-trust`         Disable the strict-trust gate
//!   `--strict-obligations`      Treat dropped obligations as errors (exit 2)
//!   `--verify`                  Enable verification (default unless `--emit-smt`)
//!   `--no-verify`               Skip verification
//!   `--stop-after-analysis`     Stop after MIR analysis (no verification)
//!   `-h`, `--help`              Print help information
//!   `-V`, `--version`           Print version information
//!
//! Exit codes: 0 = verified, 1 = verification failure, 2 = encoding/solver
//! error, 3 = parse error, 101 = internal error (panic).

use std::{
    env,
    ffi::OsStr,
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    process::{exit, Command, ExitCode},
};

use trust_wp_core::tracing_init::{init_trust_wp_tracing, trust_wp_log_help};

/// Exit code for verification failures
const EXIT_VERIFICATION_FAILURE: i32 = 1;
/// Exit code for encoding or solver errors
const EXIT_ENCODING_ERROR: i32 = 2;
/// Exit code for parse errors
const EXIT_PARSE_ERROR: i32 = 3;

fn main() -> ExitCode {
    // cargo passes "trust-wp" as first arg when invoked as "cargo trust-wp"
    // Skip the binary name and "trust-wp" to get actual options
    let args: Vec<String> = env::args().skip(1).collect();

    // Filter out "trust-wp" if present (cargo subcommand convention)
    let args: Vec<String> = if args.first().is_some_and(|a| a == "trust-wp") {
        args.into_iter().skip(1).collect()
    } else {
        args
    };

    init_trust_wp_tracing(verbose_requested(&args));

    // Handle help
    if args.iter().any(|a| a == "-h" || a == "--help") {
        print_help();
        return ExitCode::SUCCESS;
    }

    // Handle version
    if args.iter().any(|a| a == "-V" || a == "--version") {
        print_version();
        return ExitCode::SUCCESS;
    }

    // Parse trust-wp-specific options
    let parsed = match parse_args(&args) {
        Ok(p) => p,
        Err(msg) => {
            eprintln!("error: {msg}");
            // EXIT_PARSE_ERROR is 3, fits in u8
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            return ExitCode::from(EXIT_PARSE_ERROR as u8);
        }
    };
    let trust_wp_args = parsed.trust_wp_args;
    let cargo_args = parsed.cargo_args;
    let strict_obligations = parsed.strict_obligations;

    // Find trust-wp-rustc binary
    let trust_wp_rustc = find_trust_wp_rustc().unwrap_or_else(|| {
        eprintln!("error: Could not find trust-wp-rustc binary.");
        eprintln!("       Make sure trust-wp-driver is installed and in PATH.");
        exit(EXIT_ENCODING_ERROR);
    });

    // Build TRUST_WP_ARGS for the wrapper
    let trust_wp_args_env = build_trust_wp_args_env(&trust_wp_args);

    // Touch source file to invalidate cargo's cache and force recompilation.
    // This ensures trust-wp-rustc runs even when dependencies are cached.
    touch_source_file(&cargo_args);

    // Run cargo check with trust-wp-rustc as RUSTC_WRAPPER.
    // CARGO_TRUST_WP signals to trust-wp-rustc that it's invoked via cargo-trust-wp,
    // so it can skip analysis for dependency crates (only primary package).
    // TRUST_WP_RESULT_PROTOCOL requests structured wire-line output (#1690).
    let output = Command::new("cargo")
        .arg("check")
        .args(&cargo_args)
        .env("RUSTC_WRAPPER", &trust_wp_rustc)
        .env("TRUST_WP_ARGS", &trust_wp_args_env)
        .env("CARGO_TRUST_WP", "1")
        .env(trust_wp_core::result_protocol::RESULT_PROTOCOL_ENV, "1")
        .output()
        .unwrap_or_else(|e| {
            eprintln!("error: Failed to run cargo: {e}");
            exit(EXIT_ENCODING_ERROR);
        });

    let cargo_code = output.status.code().unwrap_or(EXIT_ENCODING_ERROR);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let verify_mode = !trust_wp_args.iter().any(|a| a == "--no-verify");

    // Split stderr: forward human lines, collect wire lines (#1690).
    let (human_stderr, mut wire_result) = split_stderr_wire_lines(&stderr);

    let exit_code = if let Some(ref wire) = wire_result {
        // Wire-first path: trust the driver's structured result
        derive_exit_code_from_wire_and_cargo(cargo_code, wire, verify_mode, strict_obligations)
    } else {
        // Legacy fallback: parse human-readable summary text
        derive_exit_code(cargo_code, &stderr, verify_mode, strict_obligations)
    };
    if let Some(ref mut wire) = wire_result {
        reconcile_forwarded_wire_exit_code(wire, exit_code);
    }
    forward_split_output(&output.stdout, &human_stderr, wire_result.as_ref());

    // Exit codes are small integers (0-3) that fit in u8
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    ExitCode::from(exit_code as u8)
}

fn verbose_requested(args: &[String]) -> bool {
    args.iter()
        .any(|arg| matches!(arg.as_str(), "-v" | "-vv" | "--verbose"))
}

/// Parse arguments into trust-wp options and cargo options.
/// Parsed CLI arguments for cargo-trust-wp.
#[derive(Debug)]
struct ParsedArgs {
    /// Arguments forwarded to trust-wp-rustc via TRUST_WP_ARGS.
    trust_wp_args: Vec<String>,
    /// Arguments forwarded to cargo.
    cargo_args: Vec<String>,
    /// Local policy flag: treat warnings as errors.
    /// Set by `--strict-obligations`. Not forwarded to trust-wp-rustc. (#1779)
    strict_obligations: bool,
}

fn parse_args(args: &[String]) -> Result<ParsedArgs, String> {
    let mut trust_wp_args = Vec::new();
    let mut cargo_args = Vec::new();
    let mut strict_obligations = false;

    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        match arg.as_str() {
            "-v" | "--verbose" | "-vv" => trust_wp_args.push("--verbose".to_string()),
            "--emit-smt" => trust_wp_args.push("--emit-smt".to_string()),
            // Per-function SMT file emission (#1691): split and = forms
            "--emit-smt-dir" => {
                if i + 1 < args.len() {
                    trust_wp_args.push("--emit-smt-dir".to_string());
                    trust_wp_args.push(args[i + 1].clone());
                    i += 1;
                } else {
                    return Err(
                        "--emit-smt-dir requires a path (e.g., --emit-smt-dir ./smt-out)"
                            .to_string(),
                    );
                }
            }
            _ if arg.starts_with("--emit-smt-dir=") => {
                trust_wp_args.push("--emit-smt-dir".to_string());
                trust_wp_args.push(arg[15..].to_string());
            }
            "--force" => trust_wp_args.push("--force".to_string()),
            "--timeout" => {
                if i + 1 < args.len() {
                    trust_wp_args.push("--timeout".to_string());
                    trust_wp_args.push(args[i + 1].clone());
                    i += 1;
                } else {
                    return Err("--timeout requires a value (e.g., --timeout 60)".to_string());
                }
            }
            _ if arg.starts_with("--timeout=") => {
                trust_wp_args.push("--timeout".to_string());
                trust_wp_args.push(arg[10..].to_string());
            }
            "--filter" => {
                if i + 1 < args.len() {
                    trust_wp_args.push("--filter".to_string());
                    trust_wp_args.push(args[i + 1].clone());
                    i += 1;
                } else {
                    return Err(
                        "--filter requires a value (e.g., --filter my_function)".to_string()
                    );
                }
            }
            _ if arg.starts_with("--filter=") => {
                trust_wp_args.push("--filter".to_string());
                trust_wp_args.push(arg[9..].to_string());
            }
            // Route --wide-pointers to trust-wp-rustc (not yet supported, shows proper error)
            "--wide-pointers" => trust_wp_args.push("--wide-pointers".to_string()),
            // Treat unverified logic function postconditions as errors (#1490)
            "--strict-axioms" => trust_wp_args.push("--strict-axioms".to_string()),
            // Phase 1 soundness gate (#20): default is ON in the driver.
            // Forward the explicit forms so callers can opt out via
            // --no-strict-trust or affirm via --strict-trust.
            "--strict-trust" => trust_wp_args.push("--strict-trust".to_string()),
            "--no-strict-trust" => trust_wp_args.push("--no-strict-trust".to_string()),
            // Local policy flag: treat dropped obligation warnings as errors (#1779).
            // Not forwarded to trust-wp-rustc — this is a cargo-trust-wp exit-code policy.
            "--strict-obligations" => strict_obligations = true,
            // Track level: normalize split form to the driver's = form.
            "--track" => {
                if i + 1 < args.len() {
                    trust_wp_args.push(format!("--track={}", args[i + 1]));
                    i += 1;
                } else {
                    return Err("--track requires a level (e.g., --track reg)".to_string());
                }
            }
            // Track level: forward --track=<level> to trust-wp-rustc
            _ if arg.starts_with("--track=") => trust_wp_args.push(arg.clone()),
            // Verification control: forward to trust-wp-rustc
            "--verify" => trust_wp_args.push("--verify".to_string()),
            "--no-verify" => trust_wp_args.push("--no-verify".to_string()),
            // Analysis-only mode: forward to trust-wp-rustc
            "--stop-after-analysis" => trust_wp_args.push("--stop-after-analysis".to_string()),
            // Pass everything else to cargo
            _ => cargo_args.push(arg.clone()),
        }
        i += 1;
    }

    Ok(ParsedArgs {
        trust_wp_args,
        cargo_args,
        strict_obligations,
    })
}

/// Build the `TRUST_WP_ARGS` environment variable value.
///
/// Uses newline-delimited format so path-valued flags (like `--emit-smt-dir`)
/// can contain spaces without being split incorrectly. The driver's
/// `parse_opts_string` detects newlines and splits on lines; without newlines
/// it falls back to whitespace splitting for backward compatibility. (#1691)
fn build_trust_wp_args_env(args: &[String]) -> String {
    // Always include --force to ensure trust-wp analysis runs
    let mut all_args = vec!["--force".to_string()];
    all_args.extend(args.iter().cloned());
    all_args.join("\n")
}

/// Find the trust-wp-rustc binary.
fn find_trust_wp_rustc() -> Option<PathBuf> {
    let current_exe = env::current_exe().ok();
    let path_var = env::var_os("PATH");
    find_trust_wp_rustc_with(current_exe.as_deref(), path_var.as_deref())
}

fn find_trust_wp_rustc_with(
    current_exe: Option<&Path>,
    path_var: Option<&OsStr>,
) -> Option<PathBuf> {
    // 1. Check next to this binary (cargo-trust-wp)
    if let Some(parent) = current_exe.and_then(Path::parent) {
        let sibling = parent.join("trust-wp-rustc");
        if sibling.exists() {
            return Some(sibling);
        }
    }

    // 2. Check in PATH
    which_in_path_with("trust-wp-rustc", path_var)
}

fn which_in_path_with(name: &str, path_var: Option<&OsStr>) -> Option<PathBuf> {
    let path_var = path_var?;
    for dir in env::split_paths(path_var) {
        let candidate = dir.join(name);
        if candidate.exists() {
            return Some(candidate);
        }
        // Also check with .exe on Windows
        #[cfg(windows)]
        {
            let candidate_exe = dir.join(format!("{}.exe", name));
            if candidate_exe.exists() {
                return Some(candidate_exe);
            }
        }
    }
    None
}

/// Touch source files to force recompilation via cargo metadata target discovery.
///
/// Uses `cargo metadata --no-deps` to discover all target source paths for the
/// selected package(s), then touches each one to invalidate cargo's mtime cache.
/// This ensures `RUSTC_WRAPPER` (trust-wp-rustc) is invoked even when artifacts
/// are cached.
///
/// Falls back to hardcoded `src/lib.rs` / `src/main.rs` when metadata is
/// unavailable (e.g., minimal environments without cargo in PATH).
///
/// Fixes: #1825 (cache invalidation misses custom/virtual manifests)
fn touch_source_file(cargo_args: &[String]) {
    let metadata_paths = discover_target_paths(cargo_args);
    if !metadata_paths.is_empty() {
        for path in &metadata_paths {
            touch_file(path);
        }
        return;
    }

    // Fallback: hardcoded paths for environments where cargo metadata fails
    let manifest_path = cargo_args
        .iter()
        .position(|a| a == "--manifest-path")
        .and_then(|i| cargo_args.get(i + 1))
        .map_or_else(|| PathBuf::from("Cargo.toml"), PathBuf::from);

    let manifest_dir = manifest_path
        .parent()
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);

    let fallback_candidates = [
        manifest_dir.join("src/lib.rs"),
        manifest_dir.join("src/main.rs"),
    ];

    for source in &fallback_candidates {
        if source.exists() {
            touch_file(source);
            return;
        }
    }
}

/// Touch a file by rewriting its contents to update mtime.
fn touch_file(path: &Path) {
    if path.exists() {
        if let Ok(content) = fs::read(path) {
            let _ = fs::write(path, content);
        }
    }
}

/// Discover target source paths from `cargo metadata --no-deps`.
///
/// Respects `--manifest-path` and `-p`/`--package` from cargo args.
/// Returns source paths for all targets (lib, bin, example, etc.) of
/// the selected packages.
fn discover_target_paths(cargo_args: &[String]) -> Vec<PathBuf> {
    let mut cmd = Command::new("cargo");
    cmd.arg("metadata")
        .arg("--no-deps")
        .arg("--format-version=1");

    // Forward --manifest-path if present
    if let Some(pos) = cargo_args.iter().position(|a| a == "--manifest-path") {
        if let Some(path) = cargo_args.get(pos + 1) {
            cmd.arg("--manifest-path").arg(path);
        }
    }

    let output = match cmd.output() {
        Ok(o) if o.status.success() => o,
        _ => return Vec::new(),
    };

    let Ok(stdout) = std::str::from_utf8(&output.stdout) else {
        return Vec::new();
    };

    // Collect -p/--package filters from cargo args
    let selected_packages: Vec<&str> = collect_package_filters(cargo_args);

    parse_src_paths_from_metadata(stdout, &selected_packages)
}

/// Collect `-p <pkg>` and `--package <pkg>` values from cargo args.
fn collect_package_filters(cargo_args: &[String]) -> Vec<&str> {
    let mut packages = Vec::new();
    let mut i = 0;
    while i < cargo_args.len() {
        match cargo_args[i].as_str() {
            "-p" | "--package" => {
                if let Some(pkg) = cargo_args.get(i + 1) {
                    packages.push(pkg.as_str());
                    i += 1;
                }
            }
            _ => {}
        }
        i += 1;
    }
    packages
}

/// Parse `src_path` values from cargo metadata JSON without serde.
///
/// Extracts `"src_path":"<path>"` from each target entry. When
/// `selected_packages` is non-empty, only returns paths from matching
/// packages (by `"name":"<pkg>"` in the enclosing package object).
fn parse_src_paths_from_metadata(json: &str, selected_packages: &[&str]) -> Vec<PathBuf> {
    let mut paths = Vec::new();

    // cargo metadata JSON structure (simplified):
    //   { "packages": [ { "name": "...", "targets": [ { "src_path": "..." } ] } ] }
    //
    // We do lightweight extraction: find each "src_path" value and, when
    // package filtering is active, match the nearest preceding "name" field.
    // This avoids a serde_json dependency for a single use case.

    // If no package filter, collect all src_path values
    if selected_packages.is_empty() {
        for src_path in extract_json_string_values(json, "src_path") {
            paths.push(PathBuf::from(src_path));
        }
    } else {
        // With package filter: walk package objects
        for (pkg_name, pkg_src_paths) in extract_package_src_paths(json) {
            if selected_packages.contains(&pkg_name.as_str()) {
                for src_path in pkg_src_paths {
                    paths.push(PathBuf::from(src_path));
                }
            }
        }
    }

    paths
}

/// Extract all values for a given JSON string key (e.g., `"src_path":"value"`).
///
/// Handles optional whitespace around `:` and decodes JSON string escapes.
fn extract_json_string_values(json: &str, key: &str) -> Vec<String> {
    let key_pattern = format!("\"{key}\"");
    let mut values = Vec::new();
    let mut search_from = 0;

    while let Some(start) = json[search_from..].find(&key_pattern) {
        let mut cursor = search_from + start + key_pattern.len();

        while let Some(ch) = json[cursor..].chars().next() {
            if ch.is_whitespace() {
                cursor += ch.len_utf8();
            } else {
                break;
            }
        }

        if !json[cursor..].starts_with(':') {
            search_from = cursor;
            continue;
        }
        cursor += 1;

        while let Some(ch) = json[cursor..].chars().next() {
            if ch.is_whitespace() {
                cursor += ch.len_utf8();
            } else {
                break;
            }
        }

        if !json[cursor..].starts_with('"') {
            search_from = cursor;
            continue;
        }
        cursor += 1;

        let value_tail = &json[cursor..];
        let mut escaped = false;
        let mut value_end = None;
        for (idx, ch) in value_tail.char_indices() {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => {
                    value_end = Some(idx);
                    break;
                }
                _ => {}
            }
        }

        let Some(end) = value_end else {
            break;
        };

        let raw_value = &value_tail[..end];
        let decoded =
            decode_json_string_literal(raw_value).unwrap_or_else(|| raw_value.to_string());
        values.push(decoded);

        search_from = cursor + end + 1;
    }

    values
}

fn decode_json_string_literal(raw: &str) -> Option<String> {
    let mut out = String::with_capacity(raw.len());
    let mut chars = raw.chars();

    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }

        let esc = chars.next()?;
        match esc {
            '"' => out.push('"'),
            '\\' => out.push('\\'),
            '/' => out.push('/'),
            'b' => out.push('\u{0008}'),
            'f' => out.push('\u{000c}'),
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            'u' => {
                let mut hex = String::with_capacity(4);
                for _ in 0..4 {
                    hex.push(chars.next()?);
                }
                let code = u32::from_str_radix(&hex, 16).ok()?;
                out.push(char::from_u32(code)?);
            }
            _ => return None,
        }
    }

    Some(out)
}

/// Extract `(package_name, [src_paths])` pairs from cargo metadata JSON.
///
/// Walks the `"packages"` array and for each package, extracts its `"name"`
/// and all `"src_path"` values from its `"targets"` array.
fn extract_package_src_paths(json: &str) -> Vec<(String, Vec<String>)> {
    // Find the "packages" array with arbitrary whitespace around `:` and `[`.
    // Matches the same tolerance as extract_json_string_values.
    let Some(offset) = find_json_array_start(json, "packages") else {
        return Vec::new();
    };

    extract_packages_from_offset(json, offset)
}

/// Find the start of a JSON array value for a given key, tolerating whitespace.
///
/// Returns the byte offset of the key pattern start (before `"key"`), or `None`.
fn find_json_array_start(json: &str, key: &str) -> Option<usize> {
    let key_pattern = format!("\"{key}\"");
    let mut search_from = 0;

    while let Some(start) = json[search_from..].find(&key_pattern) {
        let abs_start = search_from + start;
        let mut cursor = abs_start + key_pattern.len();

        // Skip whitespace after key
        while json[cursor..].starts_with(|c: char| c.is_whitespace()) {
            cursor += json[cursor..].chars().next().map_or(0, char::len_utf8);
        }

        // Expect colon
        if !json[cursor..].starts_with(':') {
            search_from = cursor;
            continue;
        }
        cursor += 1;

        // Skip whitespace after colon
        while json[cursor..].starts_with(|c: char| c.is_whitespace()) {
            cursor += json[cursor..].chars().next().map_or(0, char::len_utf8);
        }

        // Expect array opening bracket
        if json[cursor..].starts_with('[') {
            return Some(abs_start);
        }

        search_from = cursor;
    }

    None
}

fn extract_packages_from_offset(json: &str, packages_start: usize) -> Vec<(String, Vec<String>)> {
    let mut result = Vec::new();

    // Find each package object by looking for "name" fields followed by "targets"
    // containing "src_path" fields. We use brace depth tracking.
    let slice = &json[packages_start..];

    // Find opening bracket of packages array
    let Some(arr_start) = slice.find('[') else {
        return result;
    };
    let arr_slice = &slice[arr_start + 1..];

    // Split by package objects: each starts with { and ends with matching }
    let mut depth = 0;
    let mut pkg_start = None;

    for (i, ch) in arr_slice.char_indices() {
        match ch {
            '{' => {
                if depth == 0 {
                    pkg_start = Some(i);
                }
                depth += 1;
            }
            '}' => {
                depth -= 1;
                if depth == 0 {
                    if let Some(start) = pkg_start {
                        let pkg_json = &arr_slice[start..=i];
                        // Extract name and src_paths from this package object
                        let names = extract_json_string_values(pkg_json, "name");
                        let src_paths = extract_json_string_values(pkg_json, "src_path");
                        if let Some(name) = names.first() {
                            result.push((name.clone(), src_paths));
                        }
                    }
                    pkg_start = None;
                }
            }
            ']' if depth == 0 => break,
            _ => {}
        }
    }

    result
}

/// Split stderr into human-readable text and parsed wire result (#1690).
///
/// Machine lines matching the wire prefix are parsed and aggregated.
/// All other lines are collected as human stderr for forwarding.
fn split_stderr_wire_lines(
    stderr: &str,
) -> (
    String,
    Option<trust_wp_core::result_protocol::StructuredVerificationResult>,
) {
    use trust_wp_core::result_protocol::{StructuredVerificationResult, WIRE_PREFIX};

    let mut human_lines = Vec::new();
    let mut aggregated: Option<StructuredVerificationResult> = None;

    for line in stderr.lines() {
        if line.starts_with(WIRE_PREFIX) {
            if let Some(mut parsed) = StructuredVerificationResult::from_wire_line(line) {
                parsed.normalize_exit_code();
                match aggregated.as_mut() {
                    Some(existing) => existing.merge(&parsed),
                    None => aggregated = Some(parsed),
                }
                continue;
            }
        }
        human_lines.push(line);
    }

    // Reconstruct human stderr with line endings
    let human = if human_lines.is_empty() {
        String::new()
    } else {
        let mut s = human_lines.join("\n");
        // Preserve trailing newline if original had one
        if stderr.ends_with('\n') {
            s.push('\n');
        }
        s
    };

    (human, aggregated)
}

/// Forward stdout and filtered human stderr to the user.
///
/// When a wire result is present, re-emits the aggregated wire line to stderr
/// so downstream harness consumers can parse structured telemetry (#2641).
fn forward_split_output(
    stdout: &[u8],
    human_stderr: &str,
    wire_result: Option<&trust_wp_core::result_protocol::StructuredVerificationResult>,
) {
    let _ = io::stdout().write_all(stdout);
    let _ = io::stderr().write_all(human_stderr.as_bytes());
    // Re-emit the aggregated wire line so harness/CI consumers can parse it.
    if let Some(wire) = wire_result {
        let _ = io::stderr().write_all(wire.to_wire_line().as_bytes());
        let _ = io::stderr().write_all(b"\n");
    }
}

/// Derive exit code from the structured wire result (#1690).
///
/// Trusts the driver's `base_exit_code` and applies wrapper-only policy
/// (`--strict-obligations` warning promotion).
fn derive_exit_code_from_wire(
    wire: &trust_wp_core::result_protocol::StructuredVerificationResult,
    _verify_mode: bool,
    strict_obligations: bool,
) -> i32 {
    let wire_exit_code = wire.effective_exit_code();
    if wire_exit_code != 0 {
        return wire_exit_code;
    }

    // --strict-obligations: treat warnings as errors (wrapper-local policy)
    if strict_obligations && wire.warnings > 0 {
        return EXIT_ENCODING_ERROR;
    }

    0
}

fn derive_exit_code_from_wire_and_cargo(
    cargo_code: i32,
    wire: &trust_wp_core::result_protocol::StructuredVerificationResult,
    verify_mode: bool,
    strict_obligations: bool,
) -> i32 {
    let wire_exit_code = derive_exit_code_from_wire(wire, verify_mode, strict_obligations);
    if wire_exit_code != 0 {
        return wire_exit_code;
    }

    if cargo_code != 0 {
        return cargo_code;
    }

    0
}

fn reconcile_forwarded_wire_exit_code(
    wire: &mut trust_wp_core::result_protocol::StructuredVerificationResult,
    exit_code: i32,
) {
    if exit_code != 0 && wire.effective_exit_code() == 0 {
        wire.base_exit_code = exit_code;
    }
}

/// Summary line counts: (verified, failed, errors, warnings).
///
/// The warnings field captures the "N warnings" suffix that the driver
/// appends when contract clause parse errors occur during preparation.
/// Additional optional parts are tolerated here; the legacy text fallback
/// scans them separately for fail-closed soundness-gap policy.
fn parse_summary_counts(line: &str) -> Option<(u64, u64, u64, u64)> {
    let summary = line
        .strip_prefix("trust-wp: proof_assert: ")
        .or_else(|| line.strip_prefix("trust-wp: "))?;

    let mut parts = summary.split(", ");
    let verified = parts.next()?.strip_suffix(" verified")?.parse().ok()?;
    let failed = parts.next()?.strip_suffix(" failed")?.parse().ok()?;
    let errors = parts.next()?.strip_suffix(" errors")?.parse().ok()?;

    let mut warnings: u64 = 0;
    for part in parts {
        if let Some(w) = part.strip_suffix(" warnings") {
            warnings = w.parse().ok()?;
        }
        // Other optional parts (skipped, unverified axioms) are tolerated
    }

    Some((verified, failed, errors, warnings))
}

fn parse_summary_prefix(line: &str) -> Option<&str> {
    line.strip_prefix("trust-wp: proof_assert: ")
        .or_else(|| line.strip_prefix("trust-wp: "))
}

fn parse_positive_suffix_count(part: &str, suffix: &str) -> Option<u64> {
    let count = part.strip_suffix(suffix)?.parse().ok()?;
    (count > 0).then_some(count)
}

fn summary_has_soundness_gap(line: &str) -> bool {
    let Some(summary) = parse_summary_prefix(line) else {
        return false;
    };

    for part in summary.split(", ").skip(3) {
        if parse_positive_suffix_count(part, " assumed").is_some()
            || parse_positive_suffix_count(part, " trusted").is_some()
            || parse_positive_suffix_count(part, " skipped").is_some()
            || parse_positive_suffix_count(part, " verified* (unproven axiom deps)").is_some()
            || parse_positive_suffix_count(part, " unverified axiom(s)").is_some()
            || parse_positive_suffix_count(part, " vacuous").is_some()
        {
            return true;
        }
    }

    false
}

fn summary_has_panics(line: &str) -> bool {
    let Some(summary) = parse_summary_prefix(line) else {
        return false;
    };

    summary
        .split(", ")
        .skip(3)
        .any(|part| parse_positive_suffix_count(part, " panicked").is_some())
}

fn derive_exit_code(
    cargo_code: i32,
    stderr: &str,
    verify_mode: bool,
    strict_obligations: bool,
) -> i32 {
    if stderr
        .lines()
        .any(|line| line.contains("trust-wp: error: failed to parse"))
    {
        return EXIT_PARSE_ERROR;
    }

    // Structural termination errors (e.g., missing #[variant]) are reported
    // via tcx.dcx().err() as "error: trust-wp: termination check failed: ..."
    // and map to exit code 2 (#208, #1717).
    if stderr
        .lines()
        .any(|line| line.contains("trust-wp: termination check failed"))
    {
        return EXIT_ENCODING_ERROR;
    }

    let mut has_failed = false;
    let mut has_errors = false;
    let mut has_warnings = false;
    let mut has_soundness_gap = false;
    let mut has_summary = false;

    for line in stderr.lines() {
        // Exclude proof_assert summary from exit-code calculation (#1703).
        // proof_assert verification is a separate pass — its errors (e.g.,
        // quantifier-unhandled for complex generic types) should not cause the
        // overall verification to fail when the main function contracts verify.
        if line.starts_with("trust-wp: proof_assert:") {
            continue;
        }
        let Some((_, failed, errors, warnings)) = parse_summary_counts(line) else {
            continue;
        };
        has_summary = true;
        has_failed |= failed > 0;
        has_errors |= errors > 0 || summary_has_panics(line);
        has_warnings |= warnings > 0;
        has_soundness_gap |= summary_has_soundness_gap(line);
    }

    // Priority: failures > errors (matches trust-wp-rustc reporting.rs:125-145).
    // A verification failure (counterexample found) is a definitive proof that
    // code is wrong — it must not be masked by solver errors (#2114).
    if has_failed {
        return EXIT_VERIFICATION_FAILURE;
    }
    if has_errors {
        return EXIT_ENCODING_ERROR;
    }
    if has_soundness_gap {
        return EXIT_ENCODING_ERROR;
    }
    // --strict-obligations: treat warnings as encoding errors for CI gating.
    // Without this flag, warnings are informational only. (#1657, #1779)
    if strict_obligations && has_warnings {
        return EXIT_ENCODING_ERROR;
    }

    // Fail-closed gate (#1825): if verification mode is active and cargo
    // succeeded but trust-wp-rustc never emitted a summary line, the wrapper
    // was likely never invoked (cached artifacts). Return an encoding error
    // rather than silently passing through a non-verified success.
    if verify_mode && cargo_code == 0 && !has_summary {
        tracing::error!(
            "cargo-trust-wp: no verification summary detected. \
             trust-wp-rustc may not have been invoked (cached build artifacts). \
             Re-run with `cargo clean` or check your manifest layout."
        );
        return EXIT_ENCODING_ERROR;
    }

    cargo_code
}

fn print_help() {
    println!("{}", render_help());
}

fn render_help() -> String {
    format!(
        r"cargo-trust-wp - Deductive verification for Rust

USAGE:
    cargo trust-wp [OPTIONS] [CARGO_OPTS]

OPTIONS:
    -v, -vv, --verbose Show detailed verification progress
    --emit-smt         Output SMT-LIB2 queries to stdout (for debugging)
    --emit-smt-dir <path>  Write per-function .smt2 files with source comments
    --force            Run trust-wp analysis even without trust-wp dependency
    --timeout <secs>   Per-function verification timeout (default: 60)
    --filter <name>    Only verify functions matching pattern
    --track <level>    Set memory tracking level (auto, reg, ptr, mem)
    --wide-pointers    Enable wide pointer support [UNIMPLEMENTED]
    --strict-axioms    Treat unverified axioms as errors
    --strict-trust     Reject UNSAT proofs with trust/hole/fallback steps
                       (Phase 1 soundness gate; default ON)
    --no-strict-trust  Disable the strict-trust gate (legacy permissive mode)
    --strict-obligations  Treat dropped obligations as errors (exit code 2)
    --verify           Enable verification (default unless --emit-smt)
    --no-verify        Skip verification
    --stop-after-analysis  Stop after MIR analysis (no verification)
    -h, --help         Print help information
    -V, --version      Print version information

{}

EXIT CODES:
    0    All functions verified successfully
    1    At least one verification failure
    2    Encoding error or solver error
    3    Parse error in contracts
    101  Internal error (panic)

EXAMPLES:
    # Verify all annotated functions in the current project
    cargo trust-wp

    # Verbose output
    cargo trust-wp -v

    # Only verify specific functions
    cargo trust-wp --filter increment

    # Debug: emit SMT queries
    cargo trust-wp --emit-smt

CONTRACT SYNTAX:
    Use Creusot-compatible proc-macro attributes:

    use trust_wp::{{ensures, requires}};

    #[requires(x > 0)]
    #[ensures(result > x)]
    fn increment(x: i32) -> i32 {{
        x + 1
    }}

See https://github.com/alabsystems/trust-wp for documentation.",
        trust_wp_log_help()
    )
}

fn print_version() {
    println!(
        "cargo-trust-wp {} ({})",
        env!("CARGO_PKG_VERSION"),
        env!("CARGO_PKG_REPOSITORY")
    );
}

#[cfg(test)]
mod tests;
