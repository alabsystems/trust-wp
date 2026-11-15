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
#![feature(deref_patterns)]
#![cfg_attr(test, feature(custom_test_frameworks, test, exitcode_exit_method))]
#![cfg_attr(test, reexport_test_harness_main = "trust_wp_test_harness_main")]
#![cfg_attr(test, test_runner(native_test_entry))]
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
extern crate rustc_attr_ir;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
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

#[cfg(test)]
extern crate jobserver_utils;
#[cfg(test)]
extern crate trust_resource_controller;
#[cfg(test)]
mod compiler_test_process;

#[cfg(test)]
extern crate test;

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
mod hir_use;
mod logic;
mod mir_analysis;
mod param_patterns;
mod proof_assert;
mod provenance;
mod result_protocol_state;
mod std_site;
mod trait_credit;

use std::env;

use callbacks::{DefaultCallbacks, TrustWpCallbacks, TrustWpOptions};
use rustc_driver::run_compiler;
#[cfg(not(test))]
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
    // ... and a crate that DID declare one of them (trust-wp-std declares
    // `unsized_fn_params` itself) must not be failed for the duplicate the
    // injection creates: `duplicate_features` is deny-by-default, so
    // `error: the feature 'unsized_fn_params' has already been enabled`
    // would be a compile error the crate's author cannot avoid.
    "--allow=duplicate_features",
    "--cfg",
    "trust_wp",
];

#[derive(Debug, Clone, Default)]
struct ParsedTrustWpRequest {
    options: TrustWpOptions,
    help_requested: bool,
}

#[cfg(test)]
fn native_test_entry(tests: &[&test::TestDescAndFn]) -> ! {
    // SAFETY: FIRST runner operation. The compiler's test_harness.rs::add_main
    // and mk_tests_slice generate only a static test-reference array and an
    // immediate call here; no libtest IO, environment parsing or threads run
    // first. Capture the inherited GNU and SDK custody before libtest can
    // open/reuse descriptors. Reexporting the generated main alone does not
    // run the production main: the generated #[rustc_main] still owns entry.
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("error: inherited WP compiler resource custody unavailable: {error}");
        std::process::exit(75);
    }
    // SAFETY: immediately after the fixed compiler capture above, before
    // libtest IO or callbacks. Its fixed importers retain the original GNU/SDK
    // slots and only duplicate descriptions, so no advertised slot was reused.
    if let Err(error) = unsafe { compiler_test_process::capture_child_custody() } {
        eprintln!("error: inherited compiler test child custody unavailable: {error}");
        std::process::exit(75);
    }
    // This is the compiler's default libtest entry, including its ordinary
    // command-line handling and exact exit code.
    test::test_main_env_args(tests).exit_process()
}

#[cfg(not(test))]
fn main() -> std::process::ExitCode {
    // SAFETY: FIRST native-entry operation, before diagnostics, logging,
    // defaults or callbacks can open/reuse inherited resource descriptors.
    // Capture checked GNU and original SDK custody; this grants no authority.
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("error: inherited WP compiler resource custody unavailable: {error}");
        std::process::exit(75);
    }
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());

    // Set backtrace to minimal by default (verification tools crash often during development)
    if std::env::var_os("RUST_BACKTRACE").is_none() {
        // Item-level env_mutation allow (NOT a blanket): this is a one-shot,
        // process-startup default at the top of `main`, before any threads are
        // spawned and with nothing to restore. It cannot route through the
        // test-only code and there is no save/restore to guard. The
        // single-threaded-startup invariant is what makes the mutation sound.
        // The canonical Trust review gate promotes the Trust toolchain's
        // `env_mutation` lint to deny. This crate links rustc_private and
        // builds only with the Trust toolchain, which knows the lint.
        // SAFETY: single-threaded at this point
        #[allow(env_mutation)]
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

    // Order against `apply_default_solver_stack` does not matter for
    // correctness: ay seeds its flag set from exactly one variable,
    // `AY_SAT_VARIANT`, which this driver never writes, so the set installed
    // here equals the one ay would have built lazily apart from `debug_cert`.
    // What DOES matter is that the install precede the first
    // `misc_cli_flags()` read, because the seam is first-writer-wins; no
    // startup step between here and the callbacks links to ay, and a lost
    // race is reported rather than swallowed.
    apply_ay_cert_diagnostics();

    rustc_driver::install_ice_hook(BUG_REPORT_URL, |_| ());
    rustc_driver::init_rustc_env_logger(&handler);

    // Compiler diagnostics unwind with the compiler's typed fatal marker.
    // Match the compiler entrypoint: map only that marker to ordinary failure;
    // unrelated panics still unwind and keep their crash status.
    rustc_driver::catch_with_exit_code(run_trust_wp_driver)
}

/// Opt-in carrier for ay's certificate-path diagnostics (`--debug-cert`).
///
/// # The gap this closes
///
/// When strict certification refuses an UNSAT, the typed error names the
/// Alethe step and the rule and stops there. The step's CLAUSE is the datum
/// that separates the producers of a refusal — a demoted assumption prints
/// the assumption term, whole-proof poison prints the empty clause, a minted
/// leaf prints its own — and without it a refusal cannot be attributed to
/// one of them. ay prints the clause, but only behind its `--debug-cert`
/// carrier, and this driver parses no ay command line: the flag set is
/// unreachable from here except through ay's process-wide install seam.
///
/// # Why it is off by default
///
/// This is a diagnostic. With the flag off it may not move a verdict, a
/// counter or an exit code, so it is reached only when the operator asks. The whole
/// effect is a `debug_cert` bool that gates `eprintln!` sites in ay's proof
/// checker AND across its executor; every other field of the installed set is
/// exactly what ay would have built for itself. Those sites print and do not
/// steer: the one that also restores state performs the same restore on both
/// arms. Rendering is not free, though, so a budget-sensitive obligation can
/// answer differently with the flag on — it attributes a refusal, it does not
/// measure one.
///
/// The thread-local test override cannot serve here: verification runs on a
/// dedicated verifier stack thread and, by default, inside a forked child.
/// The process-wide install survives both — `fork(2)` copies the address
/// space, so the child inherits the installed set, and its stderr is the
/// parent's.
const AY_CERT_DIAGNOSTICS_ENV: &str = "TRUST_WP_AY_DEBUG_CERT";

/// Whether the operator asked for certificate diagnostics, given the raw
/// environment value.
///
/// Pure half, split out so the default-OFF contract is unit-testable without
/// touching the process environment. An explicit disabling spelling is
/// honoured so that a value set in a wrapper script can be turned off
/// downstream without having to unset the name.
fn ay_cert_diagnostics_requested(raw: Option<&str>) -> bool {
    match raw {
        None => false,
        Some(value) => !matches!(
            value.trim(),
            "" | "0" | "false" | "FALSE" | "off" | "OFF" | "no" | "NO"
        ),
    }
}

/// Install ay's certificate diagnostics when `AY_CERT_DIAGNOSTICS_ENV` asks.
///
/// A refused install is reported rather than swallowed: the seam is
/// first-writer-wins, so a `false` return means something already read or
/// wrote the flag set and the operator's request had NO effect. A diagnostic
/// that silently does nothing is worse than none — it makes an absent
/// `clause=[...]` line read as "no refusal happened".
fn apply_ay_cert_diagnostics() {
    let raw = std::env::var(AY_CERT_DIAGNOSTICS_ENV).ok();
    if !ay_cert_diagnostics_requested(raw.as_deref()) {
        return;
    }
    let installed = ay_core::debug_channel::set_global_misc_cli_flags_with(|flags| {
        flags.debug_cert = true;
    });
    // Silent on success: the driver is re-entered once per crate in a cargo
    // build, so a per-process banner would bury the diagnostic it announces
    // and eat the harness's per-row capture budget. Only the failure is
    // announced, and tracing is not initialized this early in `main`, so it
    // uses the `[TRUST_WP_DEBUG]` stderr idiom the rest of startup uses.
    if !installed {
        eprintln!(
            "[TRUST_WP_DEBUG] {AY_CERT_DIAGNOSTICS_ENV} had no effect: ay's flag set was \
             already initialized by an earlier reader"
        );
    }
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
        #[allow(env_mutation)]
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
    // The bare-name arms match an `--extern trust_wp_std` with no path (the
    // driver's own injection downstream) as well as cargo's `--extern
    // <name>=<path>`. They are scoped to an `--extern` VALUE on purpose:
    // `--crate-name trust_wp_std` also puts the bare string `trust_wp_std`
    // in argv, so an unscoped scan made the driver analyse trust-wp-std
    // ITSELF — which it then refuses outright ("local item `crate::std`
    // shadows a standard or spec-library path root"), leaving no `.rmeta`
    // and failing every crate downstream of it with `extern location for
    // trust_wp_std does not exist`. The spec library is not a crate under
    // verification; it is what the crates under verification are verified
    // against.
    let has_trust_wp = (0..args.len()).any(|i| {
        extern_arg_value(&args, i).is_some_and(|v| {
            let name = v.split('=').next().unwrap_or_default();
            name == "trust_wp" || name == "trust_wp_std"
        })
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
    // E0463/vcgen-depth failures `targo --unverified` switches the pass off
    // for in this workspace's own build. Without it the compat-harness
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
        inject_spec_tc_extern(&mut args);

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
/// Put `trust_wp_std` in the compiled crate's extern prelude.
///
/// Contract macros expand to ABSOLUTE `::trust_wp_std::...` paths — the
/// `__spec_tc` type-check surface, `logic::OrdLogic`, `ghost::Snapshot` — the
/// way Creusot's expansion writes `::creusot_std::...`. An absolute path
/// resolves only against the extern prelude, and cargo puts a crate there only
/// when the manifest names it as a direct dependency. A crate that depends on
/// `trust-wp` alone (or on `creusot-contracts` alone) therefore could not
/// compile a single contract:
///
/// ```text
/// error[E0433]: cannot find `trust_wp_std` in the crate root
/// ```
///
/// which is every one of the `targo-trust-wp` e2e fixtures and
/// `examples/verified_math`. A `pub extern crate trust_wp_std;` re-export in
/// `trust-wp` does NOT fix it: a re-export makes `trust_wp::trust_wp_std` a
/// valid path, it does not enter a downstream crate's extern prelude.
///
/// So the driver adds the name itself, as the PATHLESS `--extern <name>`
/// form: rustc locates the crate with its own resolution — the same one that
/// resolves every other crate — instead of this driver guessing a file name
/// and a metadata hash. That resolution reads the CRATE search path, and
/// cargo passes its `deps` directory as `-L dependency=` (transitive kind
/// only), so the same directories are re-registered as `-L crate=`. Nothing
/// is forced: a pathless `--extern` is resolved lazily, so a crate that
/// mentions no contract is unaffected.
///
/// The one case this cannot settle is a `deps` directory holding SEVERAL
/// builds of trust-wp-std (different features or profiles landing side by
/// side). rustc then reports `E0464: multiple candidates`, naming the files —
/// which is the honest outcome: picking one here could bind the clause to a
/// different trust-wp-std than the `trust_wp` the crate links, and the type
/// errors from that would name neither cause.
///
/// Skipped when the caller already supplied the crate (cargo does when the
/// manifest depends on trust-wp-std directly; `trust-wp <FILE.rs>` injects a
/// resolved path of its own) and when the crate being compiled IS
/// trust-wp-std, whose own contracts resolve against itself.
/// The value of the `--extern` option at `args[i]`, in either spelling
/// (`--extern NAME[=PATH]` as two arguments, or `--extern=NAME[=PATH]`).
fn extern_arg_value(args: &[String], i: usize) -> Option<String> {
    flag_arg_value(args, i, "--extern")
}

fn flag_arg_value(args: &[String], i: usize, flag: &str) -> Option<String> {
    let a = &args[i];
    if a == flag {
        args.get(i + 1).cloned()
    } else {
        a.strip_prefix(&format!("{flag}=")).map(ToString::to_string)
    }
}

fn inject_spec_tc_extern(args: &mut Vec<String>) {
    const CRATE: &str = "trust_wp_std";
    let flag_value = flag_arg_value;
    let already_supplied = (0..args.len()).any(|i| {
        flag_value(args, i, "--extern")
            .is_some_and(|v| v == CRATE || v.starts_with(&format!("{CRATE}=")))
    });
    if already_supplied {
        return;
    }
    let compiling_itself =
        (0..args.len()).any(|i| flag_value(args, i, "--crate-name").as_deref() == Some(CRATE));
    if compiling_itself {
        return;
    }
    // `-L dependency=DIR` is searched for TRANSITIVE crates only; a crate
    // named by `--extern` is looked up in the `crate`/`all` search paths.
    let dep_dirs: Vec<String> = (0..args.len())
        .filter_map(|i| flag_value(args, i, "-L"))
        .filter_map(|v| v.strip_prefix("dependency=").map(ToString::to_string))
        .collect();
    let mut seen: Vec<String> = Vec::new();
    for dir in dep_dirs {
        if seen.contains(&dir) {
            continue;
        }
        seen.push(dir.clone());
        args.push("-L".to_string());
        args.push(format!("crate={dir}"));
    }
    args.push("--extern".to_string());
    args.push(CRATE.to_string());
}

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

DIAGNOSTICS:
    TRUST_WP_AY_DEBUG_CERT=1
        Turn on ay's certificate-path diagnostics. A strict-certification
        refusal then prints the refused proof step's rule AND clause on
        stderr; without it only the opaque reason code is available.
        Diagnostic only, and OFF by default. With it off, verdicts,
        counters and exit codes are unchanged. With it on, clause
        rendering runs inside the solve and its output is large, so a
        budget-sensitive obligation may answer differently: turn it on
        to attribute a refusal, not to measure one.

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
