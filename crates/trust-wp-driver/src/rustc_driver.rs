// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! trust-wp Rustc Driver - MIR extraction via rustc integration
//!
//! This binary wraps rustc to intercept MIR for verification.
//! Usage: `trust-wp-rustc [RUSTC_OPTIONS] -- [TRUST_WP_OPTIONS]`
//!
//! The driver:
//! 1. Parses trust-wp-specific args from `--` separator or `TRUST_WP_ARGS` env var
//! 2. Runs `rustc_driver::run_compiler` with `TrustWpCallbacks`
//! 3. Extracts MIR for functions with contract attributes
//!
//! This pattern follows Creusot's approach (see reference/creusot/creusot-rustc/).

#![feature(rustc_private)]
#![feature(box_patterns)]
// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; these lints are not actionable for trust-wp's public surface.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unused_crate_dependencies,
    unreachable_pub,
    // `tcx.get_all_attrs` deprecation: trust-wp reads custom proof-marker attrs
    // (not parsed built-ins) — the use the deprecation note explicitly sanctions.
    deprecated
)]
// Allow pedantic warnings not covered by lib.rs crate-level allows
#![allow(clippy::doc_markdown)] // Technical terms don't need backticks
// Explicit closures are clearer.
#![allow(clippy::redundant_closure_for_method_calls)]
// Existing rustc-private extraction code carries pedantic cleanup debt. Keep
// the allow list explicit so broad `-D warnings` can still catch new categories.
#![allow(
    clippy::cast_possible_truncation,
    clippy::collapsible_if,
    clippy::collapsible_match,
    clippy::doc_overindented_list_items,
    clippy::explicit_iter_loop,
    clippy::for_kv_map,
    clippy::format_push_string,
    clippy::if_not_else,
    clippy::if_same_then_else,
    clippy::implicit_clone,
    clippy::manual_let_else,
    clippy::map_entry,
    clippy::map_unwrap_or,
    clippy::needless_borrow,
    clippy::needless_pass_by_value,
    clippy::needless_pub_self,
    clippy::only_used_in_recursion,
    clippy::option_option,
    clippy::question_mark,
    clippy::ref_option,
    clippy::similar_names,
    clippy::single_char_add_str,
    clippy::single_match_else,
    clippy::struct_excessive_bools,
    clippy::struct_field_names,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::trivially_copy_pass_by_ref,
    clippy::type_complexity,
    clippy::unnecessary_find_map,
    clippy::unnecessary_lazy_evaluations,
    clippy::unnecessary_semicolon,
    clippy::unnecessary_wraps,
    clippy::unnested_or_patterns,
    clippy::unreadable_literal,
    clippy::useless_format,
    clippy::useless_vec,
    clippy::vec_init_then_push
)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

// rustc_abi is needed for mir_analysis (Size, FieldIdx, AllocRange types)
// Used in production for promoted constant allocation reading (#1572) and in tests.
extern crate rustc_abi;
// rustc_index provides MixedBitSet, IndexVec, and the newtype_index! macro
// used by the not_final_places backward dataflow analysis (#2150).
extern crate rustc_index;
// rustc_mir_dataflow provides the Analysis trait, Backward direction, GenKill,
// and ResultsCursor used by not_final_places (#2150).
extern crate rustc_mir_dataflow;

#[macro_use]
extern crate log;

mod assoc_const_paths;
mod attr_utils;
mod callbacks;
mod contracts;
// The REAL kernel lane (design §9 P(−1)): driver obligation formulas →
// clean_kernel goals, graded through the frozen interface. Observation only.
#[cfg(feature = "clean-kernel")]
mod formula_kernel_lane;
mod ghost;
mod logic;
mod mir_analysis;
mod proof_assert;
mod result_protocol_state;

use std::env;

use callbacks::{DefaultCallbacks, TrustWpCallbacks, TrustWpOptions};
use rustc_driver::run_compiler;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};
use trust_wp_core::tracing_init::{init_trust_wp_tracing, trust_wp_log_help};

const BUG_REPORT_URL: &str = "https://github.com/alabsystems/trust-wp/issues/new";

/// Rustc args that activate features needed by trust-wp.
///
/// These are injected via `-Zcrate-attr` to enable custom tool attributes
/// without requiring the user to add `#![feature(register_tool)]` manually.
const TRUST_WP_RUSTC_ARGS: &[&str] = &[
    "-Zcrate-attr=feature(register_tool)",
    "-Zcrate-attr=register_tool(trust_wp)",
    "-Zcrate-attr=feature(stmt_expr_attributes)",
    // Allow by-value self in trait methods without requiring Self: Sized.
    // Needed for Creusot compat: #[logic] trait methods use `self` by value.
    "-Zcrate-attr=feature(unsized_fn_params)",
    "--allow=internal_features",
    // The `feature(...)` gates above are injected by trust-wp, not written by
    // the user, so a file that happens not to exercise one must not be warned
    // that *it* declared an unused feature. Without this, every contract file
    // that uses no statement-expression attribute prints
    // "feature `stmt_expr_attributes` is declared but not used".
    "--allow=unused_features",
    "--cfg",
    "trust_wp",
];

#[derive(Debug, Clone, Default)]
struct ParsedTrustWpRequest {
    options: TrustWpOptions,
    help_requested: bool,
}

fn main() {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());

    // Set backtrace to minimal by default (verification tools crash often during development)
    if std::env::var_os("RUST_BACKTRACE").is_none() {
        // Item-level env_mutation allow (NOT a blanket): this is a one-shot,
        // process-startup default at the top of `main`, before any threads are
        // spawned and with nothing to restore. It cannot route through the
        // test-only code and there is no save/restore to guard. The
        // single-threaded-startup invariant is what makes the mutation sound.
        // The canonical Trust review gate promotes the Trust toolchain's
        // `env_mutation` lint to deny; stock rustc doesn't know it, hence
        // `unknown_lints`.
        // SAFETY: single-threaded at this point
        #[allow(unknown_lints, env_mutation)]
        unsafe {
            std::env::set_var("RUST_BACKTRACE", "0");
        }
    }

    // Default-enable the certified composed solver stack (set-if-absent).
    // Same single-threaded-startup invariant as the RUST_BACKTRACE default
    // above: we are at the top of `main`, before rustc spawns the compiler
    // thread and before any trust-wp-ay solver thread exists, so the env
    // mutation cannot race a concurrent `getenv`.
    apply_default_solver_stack();

    rustc_driver::install_ice_hook(BUG_REPORT_URL, |_| ());
    rustc_driver::init_rustc_env_logger(&handler);

    run_trust_wp_driver();
}

/// The certified default configuration of the ay solver backend.
///
/// The composed lazy-DT + certified-model stack was certified flag-ON:
/// should_fail 99/99 with 0 false accepts RAW, and the full should_succeed
/// sweep pass-set-equal to the previous defaults (band churn only;
/// bitvectors/bitwalker passes). That certification promoted this stack to
/// the production default (originally against ay 0.5.0, 153665fb9).
///
/// ay reads these knobs from the environment at their use sites (there is
/// no programmatic config API for them), so the default is installed as
/// set-if-absent env initialization here in the driver, before any solver
/// thread exists. A var already present in the environment — with ANY
/// value, including a disabling one such as `AY_DT_CERT=off` or
/// `AY_DT_LAZY_AUFLIA=0` — is never overridden, so explicit user
/// configuration always wins.
///
/// Because these are env-read-only knobs, an entry here can rot into a
/// silent no-op when the linked ay deletes its read site — that happened
/// once across the ay 0.5 -> 0.7 move (`AY_DT_LAZY_AUFLIA_INCR`, removed
/// below). `test_solver_stack_vars_have_read_sites_in_linked_ay` pins every
/// entry to a live read site in the linked ay source tree; when it fails,
/// the linked ay changed — remove or fix the entry, don't relax the test.
///
/// Per-entry status verified at ay v0.13.0 (dd4de9e94e) and re-verified at
/// v0.15.0-77 (f9fda8ddca) — identical sites at both:
///
/// * `AY_DT_LAZY_AUFLIA` — live (`ay-dpll/src/executor/theories/euf/dt.rs`,
///   two gates).
/// * `AY_DT_LAZY_AUFLIA_EAGER` — live (same module, eager-arm gate).
/// * `AY_DT_CERT` — live (`ay-dpll/src/executor/mbqi.rs` `dt_cert_mode`,
///   tri-state off/shadow/on; also `executor/check_sat.rs`).
/// * `AY_DT_CERT_BRIDGE_ROUTE` — live but DEMOTED since ay 0.7
///   (`a786a5cd5` "certify quantified model publication"): the
///   authoritative Sat grant was deleted for a model-authority defect (the
///   granted Sat was backed by a model other than the published one). At
///   0.13.0 the flag still gates the W1 bridge-route classification/audit
///   lane (`mbqi.rs` `dt_cert_bridge_route_enabled`) — observed firing
///   live on `rusthorn/inc_some_list` (`[BRIDGE-ROUTE] would-claim ...` /
///   `decline: selector-bridge completion is not representable in the
///   published model`) — but every grant is withheld until selector-lambda
///   interpretations can be represented exactly in the published model.
///   Kept: the audit lane is the signal that tells us when the grant
///   returns, and unset/off remains byte-identical everywhere.
///
/// Removed entry (do not restore without a read site):
///
/// * `AY_DT_LAZY_AUFLIA_INCR` — DEAD. ay 0.7 hard-clamped the incremental
///   lazy-DT lane (`try_solve_dt_auflia_lazy_maybe_incremental` returns
///   `Ok(None)` on any live incremental session: the optional oracle rolled
///   its TermStore back after an inner UNSAT, recycling TermIds under the
///   mandatory authored-scope proof), and by v0.13.0 the env var itself has
///   ZERO read sites in the ay tree (re-verified at v0.15.0-77). Setting it
///   was a silent no-op.
const DEFAULT_SOLVER_STACK: &[(&str, &str)] = &[
    ("AY_DT_LAZY_AUFLIA", "1"),
    ("AY_DT_LAZY_AUFLIA_EAGER", "1"),
    ("AY_DT_CERT", "on"),
    ("AY_DT_CERT_BRIDGE_ROUTE", "1"),
];

/// Which `DEFAULT_SOLVER_STACK` vars should be set, given `is_present`.
///
/// Pure planning half of the set-if-absent default, split out so the
/// override-preservation contract is unit-testable without mutating the
/// process environment: any var reported present is excluded from the plan.
fn solver_stack_defaults_to_apply(
    is_present: impl Fn(&str) -> bool,
) -> Vec<(&'static str, &'static str)> {
    DEFAULT_SOLVER_STACK
        .iter()
        .copied()
        .filter(|(name, _)| !is_present(name))
        .collect()
}

/// Install the certified solver stack as set-if-absent env defaults.
///
/// Must be called from single-threaded process startup (see the call site
/// in `main` for the thread-safety reasoning); the same item-level
/// `env_mutation` rationale as the RUST_BACKTRACE default applies.
fn apply_default_solver_stack() {
    let to_apply = solver_stack_defaults_to_apply(|name| std::env::var_os(name).is_some());

    for (name, value) in &to_apply {
        // SAFETY: single-threaded at this point (top of `main`)
        #[allow(unknown_lints, env_mutation)]
        unsafe {
            std::env::set_var(name, value);
        }
    }

    // Introspection line. Tracing is not initialized this early in `main`,
    // so gate a plain stderr line on TRUST_WP_DEBUG directly; the format
    // matches the `[TRUST_WP_DEBUG]` tracing idiom (stderr, no
    // target/level/time) used across trust-wp-ay.
    if std::env::var_os("TRUST_WP_DEBUG").is_some() {
        let applied: Vec<&str> = to_apply.iter().map(|(name, _)| *name).collect();
        eprintln!(
            "[TRUST_WP_DEBUG] solver stack defaults: lazy-DT AUFLIA lanes + DT cert \
             bridge-route (set-if-absent; applied: {applied:?})"
        );
    }
}

/// Parse arguments and run the trust-wp driver.
///
/// Arguments can be passed in two ways:
/// 1. Command line: `trust-wp-rustc [RUSTC_ARGS] -- [TRUST_WP_ARGS]`
/// 2. Environment: `TRUST_WP_ARGS="-v" trust-wp-rustc [RUSTC_ARGS]`
///
/// When invoked via `RUSTC_WRAPPER`, cargo passes args as:
///   `$RUSTC_WRAPPER $RUSTC [rustc args...]`
/// We detect this by checking if `args[1]` looks like a rustc path and strip it.
fn run_trust_wp_driver() {
    let mut args: Vec<String> = env::args().collect();

    // Handle RUSTC_WRAPPER mode: cargo passes the real rustc path as first arg
    // after the wrapper name. Detect and strip it.
    // Pattern: ["trust-wp-rustc", "/path/to/rustc", "-", ...]
    let wrapper_mode = if args.len() >= 2 && is_rustc_path(&args[1]) {
        let rustc_path = args[1].clone();
        args.remove(1);
        args[0] = rustc_path;
        true
    } else {
        false
    };

    // Parse trust-wp options from environment or -- separator
    let request = parse_trust_wp_options(&mut args);
    init_trust_wp_tracing(request.as_ref().is_some_and(|r| r.options.verbose));

    if request.as_ref().is_some_and(|r| r.help_requested) {
        print!("{}", render_trust_wp_help());
        return;
    }

    if wrapper_mode {
        info!(
            "trust-wp-rustc: RUSTC_WRAPPER mode detected, using rustc path: {}",
            args[0]
        );
    }
    info!("trust-wp-rustc: args={args:?}");

    // Check if this crate uses trust-wp contracts or --force was specified.
    // Cargo passes external crate dependencies as `--extern trust_wp=<rmeta>`,
    // so we match on the crate-name form `trust_wp=` (underscore). The
    // hyphenated form `trust-wp=` never appears in rustc args — that was a
    // pre-rename leftover that silently disabled trust-wp analysis on every
    // fixture and caused logic-law mismatch checks to be skipped.
    let has_trust_wp = args.iter().any(|arg| {
        arg == "trust_wp"
            || arg.contains("trust_wp=")
            || arg == "trust_wp_std"
            || arg.contains("trust_wp_std=")
    });

    let force_callbacks = request.as_ref().is_some_and(|r| r.options.force_callbacks);

    // When invoked via `cargo trust-wp` (sets CARGO_TRUST_WP=1), only run trust-wp
    // analysis on the primary package — not on dependency crates. Cargo sets
    // CARGO_PRIMARY_PACKAGE=1 for the user's target crate. This follows
    // Creusot's pattern (CARGO_CREUSOT + CARGO_PRIMARY_PACKAGE).
    // Direct `trust-wp-rustc file.rs -- --force` still works because
    // CARGO_TRUST_WP is not set for direct invocations. (#534)
    let via_cargo_trust_wp = env::var("CARGO_TRUST_WP").is_ok();
    let is_primary = env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    // Under `cargo trust-wp`, only verify the primary package. Dependency
    // crates that themselves depend on `trust_wp`/`trust_wp_std` (e.g.
    // `trust-wp-std` itself, which uses `#[requires]`/`#[trusted]`) would
    // otherwise emit their own structured result wire-line containing
    // `trusted` markers. cargo-trust-wp aggregates wire-lines across all
    // crates, so dep emissions inflate `trusted`/`skipped` counts on the
    // aggregated wire and force `base_exit_code=2` even when the target
    // crate verifies cleanly. Gating on `is_primary` keeps dep compilation
    // free of trust-wp processing under cargo-trust-wp mode, which matches
    // the documented "only primary package" semantics (see comment above).
    let run_trust_wp = if via_cargo_trust_wp {
        // cargo trust-wp: only verify the primary package, never deps.
        is_primary && (has_trust_wp || force_callbacks)
    } else {
        // Direct invocation: honor `has_trust_wp` and `--force` regardless
        // of CARGO_PRIMARY_PACKAGE (which isn't set for direct calls).
        has_trust_wp || force_callbacks
    };

    // In RUSTC_WRAPPER mode the embedded rustc driver computes its sysroot from
    // THIS binary's location (e.g. `target/release/trust-wp-rustc`), which is not
    // a toolchain layout, so std/core fail to resolve ("can't find crate for
    // std", "the <host> target may not be installed"). cargo doesn't pass
    // `--sysroot`, and this bit HOST build-scripts/proc-macros especially (the
    // compat-harness warmup hit exit 101 here). Resolve the sysroot from the real
    // rustc cargo handed us (now `args[0]`) and inject it when absent.
    if wrapper_mode
        && !args
            .iter()
            .any(|a| a == "--sysroot" || a.starts_with("--sysroot="))
    {
        if let Some(sysroot) = resolve_wrapped_sysroot(&args[0]) {
            args.push("--sysroot".to_string());
            args.push(sysroot);
        }
    }

    // trust-wp-rustc IS the verifier: disable the Trust compiler's built-in
    // `trust_verify` MIR pass on every compile we wrap. The channel="trust"
    // toolchain runs that pass batteries-on by default — on the target crate AND
    // every dependency (memchr, serde, syn, …). For trust-wp it is redundant
    // (TrustWpCallbacks does the real verification via ay) and harmful: it is
    // slow on the full dep stack and ICEs on some third-party deps — exactly the
    // E0463/vcgen-depth failures the workspace's own `.cargo/config.toml`
    // `-Ztrust-verify=off` rustflag exists for. Without it the compat-harness
    // warmup panics (exit 101) and every test pays a multi-minute dep-verify cost
    // (90s timeouts). Inject it once for both the verify and passthrough paths.
    let has_trust_verify_off = args.iter().enumerate().any(|(i, a)| {
        a == "-Ztrust-verify=off"
            || (a == "-Z" && args.get(i + 1).map(String::as_str) == Some("trust-verify=off"))
    });
    if !has_trust_verify_off {
        args.push("-Ztrust-verify=off".to_string());
    }

    if run_trust_wp {
        let opts = request.map(|r| r.options).unwrap_or_default();
        info!(
            "trust-wp-rustc: Running with contract analysis (force={force_callbacks}, primary={is_primary})",
        );

        // Inject trust-wp-required rustc args for tool attribute registration
        inject_trust_wp_args(&mut args);

        run_compiler(&args, &mut TrustWpCallbacks::new(opts));
    } else {
        // No trust-wp contracts, or this is a dependency crate in cargo-trust-wp mode
        if via_cargo_trust_wp {
            info!("trust-wp-rustc: Skipping analysis for dependency crate");
        } else {
            info!("trust-wp-rustc: No trust-wp dependency, running default rustc");
        }
        run_compiler(&args, &mut DefaultCallbacks);
    }
}

/// Resolve the sysroot to inject from the wrapped rustc path (`<sysroot>/bin/rustc`).
///
/// Computes `dirname(dirname(rustc))` and accepts it when it looks like a real
/// sysroot (`lib/rustlib` present) — a path computation with NO subprocess. The
/// previous `rustc --print sysroot` spawned a child process on EVERY wrapped
/// rustc invocation, which raced under cargo's parallel build-script compiles
/// and intermittently produced `can't find crate for std` / warmup exit 101.
/// Falls back to `--print sysroot` only when the path layout is unexpected.
fn resolve_wrapped_sysroot(rustc: &str) -> Option<String> {
    let path = std::path::Path::new(rustc);
    if let Some(root) = path.parent().and_then(std::path::Path::parent) {
        if root.join("lib").join("rustlib").is_dir() {
            return Some(root.to_string_lossy().into_owned());
        }
    }
    let out = std::process::Command::new(rustc)
        .args(["--print", "sysroot"])
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
    (!sysroot.is_empty()).then_some(sysroot)
}

/// Parse trust-wp-specific options from args or environment.
fn parse_trust_wp_options(args: &mut Vec<String>) -> Option<ParsedTrustWpRequest> {
    // Try environment variable first
    if let Ok(env_args) = std::env::var("TRUST_WP_ARGS") {
        return Some(parse_trust_wp_request_string(&env_args));
    }

    // Look for -- separator
    if let Some(pos) = args.iter().rposition(|arg| arg == "--") {
        // split_off(pos) moves args[pos..] into trust_wp_args
        // trust_wp_args = ["--", "-v", "--force", ...]
        // args is now truncated to args[..pos]
        let trust_wp_args: Vec<String> = args.split_off(pos);

        // Parse everything after the "--" (skip trust_wp_args[0] which is "--")
        return Some(parse_trust_wp_request_vec(&trust_wp_args[1..]));
    }

    None
}

/// Inject trust-wp-required args into the rustc command line.
///
/// These enable the `#[trust_wp::...]` tool attributes without requiring
/// manual feature flags in user code.
fn inject_trust_wp_args(args: &mut Vec<String>) {
    // Insert after the binary name but before other args
    for (i, arg) in TRUST_WP_RUSTC_ARGS.iter().enumerate() {
        args.insert(1 + i, arg.to_string());
    }
}

#[cfg(test)]
fn parse_opts_string(s: &str) -> TrustWpOptions {
    parse_trust_wp_request_string(s).options
}

fn parse_trust_wp_request_string(s: &str) -> ParsedTrustWpRequest {
    // If the env value contains newlines, split on lines (newline-safe format
    // from cargo-trust-wp #1691). Otherwise keep the legacy whitespace fallback
    // for direct `TRUST_WP_ARGS="--verbose --emit-smt"` usage.
    let parts: Vec<String> = if s.contains('\n') {
        s.lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(String::from)
            .collect()
    } else {
        s.split_whitespace().map(String::from).collect()
    };
    parse_trust_wp_request_vec(&parts)
}

#[cfg(test)]
fn parse_opts_vec(args: &[String]) -> TrustWpOptions {
    parse_trust_wp_request_vec(args).options
}

fn parse_trust_wp_request_vec(args: &[String]) -> ParsedTrustWpRequest {
    use callbacks::TrackLevel;

    let mut request = ParsedTrustWpRequest::default();
    let mut verify_explicit = false;
    let mut args_iter = args.iter().peekable();

    while let Some(arg) = args_iter.next() {
        match arg.as_str() {
            "-v" | "--verbose" => request.options.verbose = true,
            "-h" | "--help" => request.help_requested = true,
            "--stop-after-analysis" => request.options.stop_after_analysis = true,
            "--force" => request.options.force_callbacks = true,
            "--emit-smt" => request.options.emit_smt = true,
            "--verify" => {
                request.options.verify = true;
                verify_explicit = true;
            }
            "--no-verify" => {
                request.options.verify = false;
                verify_explicit = true;
            }
            // Track level options (Phase 1 of #275)
            "--track=auto" => request.options.track_level = TrackLevel::Auto,
            "--track=reg" => request.options.track_level = TrackLevel::Reg,
            "--track=ptr" => request.options.track_level = TrackLevel::Ptr,
            "--track=mem" => request.options.track_level = TrackLevel::Mem,
            "--wide-pointers" => request.options.wide_pointers = true,
            "--strict-axioms" => request.options.strict_axioms = true,
            "--strict-trust" => request.options.strict_trust = true,
            "--no-strict-trust" => {
                // Compatibility-only spelling. Proof authority is mandatory;
                // a command-line flag must never turn an untrusted or absent
                // certificate into a successful verification result.
                warn!("--no-strict-trust is deprecated and ignored");
                request.options.strict_trust = true;
            }
            // Per-function SMT file emission directory (#1691)
            "--emit-smt-dir" => match args_iter.next() {
                Some(p) => {
                    request.options.emit_smt_dir = Some(std::path::PathBuf::from(p.as_str()));
                }
                None => warn!("--emit-smt-dir requires a path argument"),
            },
            _ if arg.starts_with("--emit-smt-dir=") => {
                request.options.emit_smt_dir = Some(std::path::PathBuf::from(&arg[15..]));
            }
            "--filter" => match args_iter.next() {
                Some(pattern) => request.options.filter_pattern = Some(pattern.clone()),
                None => warn!("--filter requires a pattern argument"),
            },
            _ if arg.starts_with("--filter=") => {
                request.options.filter_pattern = Some(arg[9..].to_string());
            }
            "--timeout" => match args_iter.next().map(|v| v.parse::<u64>()) {
                Some(Ok(secs)) => request.options.timeout_secs = Some(secs),
                Some(Err(_)) => warn!("--timeout requires a numeric argument"),
                None => warn!("--timeout requires a numeric argument"),
            },
            _ if arg.starts_with("--timeout=") => match arg[10..].parse::<u64>() {
                Ok(secs) => request.options.timeout_secs = Some(secs),
                Err(_) => warn!("--timeout requires a numeric value, got '{}'", &arg[10..]),
            },
            _ if arg.starts_with("--track=") => {
                warn!(
                    "Unknown track level '{}', using auto. Valid: auto, reg, ptr, mem",
                    &arg[8..]
                );
                request.options.track_level = TrackLevel::Auto;
            }
            _ => {
                warn!("Unknown trust-wp option: {arg}");
            }
        }
    }

    // Default: enable verification unless user explicitly passed --no-verify
    // or an emit mode is requested without --verify
    let emit_only = request.options.emit_smt || request.options.emit_smt_dir.is_some();
    if !verify_explicit && !emit_only {
        request.options.verify = true;
    }

    request
}

fn render_trust_wp_help() -> String {
    format!(
        "trust-wp-rustc - trust-wp rustc driver

USAGE:
    trust-wp-rustc [RUSTC_OPTIONS] -- [TRUST_WP_OPTIONS]
    TRUST_WP_ARGS=\"<TRUST_WP_OPTIONS>\" trust-wp-rustc [RUSTC_OPTIONS]

TRUST_WP OPTIONS:
    -v, --verbose      Show detailed verification progress
    --stop-after-analysis
                       Stop the compiler after MIR analysis. Contracts are
                       still verified; nothing is code-generated. Use
                       --no-verify to skip verification itself.
    --force            Run trust-wp analysis even without trust-wp dependency
    --emit-smt         Output SMT-LIB2 queries to stdout
    --emit-smt-dir <path>
                       Write per-function .smt2 files with source comments
    --filter <name>    Only verify functions matching pattern
    --timeout <secs>   Per-function verification timeout (default: 60)
    --track=<level>    Set memory tracking level (auto, reg, ptr, mem)
    --wide-pointers    Enable wide pointer support [UNIMPLEMENTED]
    --strict-axioms    Treat unverified axioms as errors
    --strict-trust     Require independently replayed proof authority [default]
    --no-strict-trust  Deprecated compatibility spelling; ignored
    --verify           Enable verification (default unless emit-only)
    --no-verify        Skip verification
    -h, --help         Print this trust-wp option help

{}
",
        trust_wp_log_help()
    )
}

/// Check if an argument looks like a path to a Rust/Trust compiler binary.
///
/// When cargo uses `RUSTC_WRAPPER`, it passes the real rustc path as the
/// first argument after the wrapper. We need to detect this to strip it.
///
/// We match:
/// - Bare `rustc`/`trustc` names, with an optional `.exe` suffix
/// - Paths whose final component is `rustc` or `trustc`
///
/// We do NOT match wrapper binaries like "trust-wp-rustc" or "clippy-driver".
fn is_rustc_path(arg: &str) -> bool {
    let arg_lower = arg.to_lowercase();
    let compiler_name = arg_lower
        .rsplit(['/', '\\'])
        .next()
        .unwrap_or(arg_lower.as_str());

    matches!(
        compiler_name,
        "rustc" | "rustc.exe" | "trustc" | "trustc.exe"
    )
}

#[cfg(test)]
#[path = "rustc_driver_tests.rs"]
mod tests;
