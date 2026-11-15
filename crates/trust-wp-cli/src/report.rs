// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `--json` report (`trust-wp.cli-report.v1`) and `trust-wp result`.
//!
//! Every report is one JSON document on stdout with the same envelope:
//! `schema`, `tool`, `command`, `exit_code`. Verification reports add the
//! engine's aggregate `summary` (the `TRUST_WP_RESULT:v1` counters) and the
//! per-obligation `diagnostics` (`TRUST_WP_DIAGNOSTIC:v1` records). The schema
//! is additive-only: consumers must ignore keys they do not know.

use std::{
    fs,
    io::{self, BufRead},
    path::Path,
};

use serde_json::{json, Map, Value};
use trust_wp_core::result_protocol::{StructuredVerificationResult, VerificationDiagnosticRecord};

use crate::{
    engine_exit_code, Engine, StderrRelay, UsageError, EXIT_ENCODING_ERROR, EXIT_OK, EXIT_USAGE,
    EXIT_VERIFICATION_FAILURE,
};

/// Everything one engine run produced, for the report.
///
/// Populated by the engine verbs in `main.rs`; the human path does not need it.
#[derive(Debug, Default)]
pub struct RunReport {
    pub exit_code: i32,
    /// `file`, `crate`, or `transcript`.
    pub mode: &'static str,
    pub target: String,
    pub summary: Option<StructuredVerificationResult>,
    pub diagnostics: Vec<VerificationDiagnosticRecord>,
    pub driver: Option<Engine>,
    pub front: Option<Engine>,
    pub child_exit_code: Option<i32>,
    pub notes: Vec<String>,
    pub verify_mode: bool,
    pub dry_run: bool,
    pub dry_run_command: Option<Value>,
    pub error: Option<(ErrorKind, String)>,
}

/// Schema identifier carried by every report.
pub const REPORT_SCHEMA: &str = "trust-wp.cli-report.v1";

/// The `tool` block shared by every report.
pub fn tool() -> Value {
    json!({ "name": "trust-wp", "version": env!("CARGO_PKG_VERSION") })
}

/// The common envelope of every report.
pub fn envelope(command: &str, exit_code: i32) -> Map<String, Value> {
    let mut map = Map::new();
    map.insert("schema".into(), Value::from(REPORT_SCHEMA));
    map.insert("tool".into(), tool());
    map.insert("command".into(), Value::from(command));
    map.insert("exit_code".into(), Value::from(exit_code));
    map
}

/// `trust-wp --json version`.
pub fn version_report() -> Value {
    let mut map = envelope("version", EXIT_OK);
    map.insert(
        "repository".into(),
        Value::from(env!("CARGO_PKG_REPOSITORY")),
    );
    // `version` in the envelope is the package version, which many builds
    // share. `build` names the one commit this binary came from, so a report
    // pasted into an issue identifies a tree. Absent from a tarball build,
    // where there is no commit to name.
    if let Some(build) = option_env!("TWP_BUILD") {
        map.insert("build".into(), Value::from(build));
    }
    Value::Object(map)
}

/// Print one pretty JSON document on stdout.
pub fn print_json(value: &Value) {
    let text = serde_json::to_string_pretty(value).unwrap_or_else(|_| value.to_string());
    println!("{text}");
}

/// A typed error attached to any non-verdict exit.
///
/// `kind` is a small closed vocabulary so a consumer can branch on it without
/// reading `message`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {
    /// The command line was wrong.
    Usage,
    /// A file could not be read or written.
    Io,
    /// A contract expression did not parse.
    ContractParse,
    /// A verify-bundle request or result was not valid.
    InvalidBundle,
    /// An engine binary could not be found.
    EngineMissing,
    /// An engine binary was found but could not be started or did not finish.
    EngineSpawn,
    /// The engine ran but reported no verification summary.
    NoVerdict,
}

impl ErrorKind {
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Usage => "usage",
            Self::Io => "io",
            Self::ContractParse => "contract_parse",
            Self::InvalidBundle => "invalid_bundle",
            Self::EngineMissing => "engine_missing",
            Self::EngineSpawn => "engine_spawn",
            Self::NoVerdict => "no_verdict",
        }
    }
}

/// Build the report's `error` object.
pub fn error_json(kind: ErrorKind, message: impl Into<String>) -> Value {
    json!({ "kind": kind.as_str(), "message": message.into() })
}

/// The document printed for a usage error when `--json` was asked for.
///
/// The guarantee is that `--json` yields exactly one report on stdout on every
/// exit the CLI itself returns, this one included.
pub fn usage_report(err: &UsageError) -> Value {
    let mut map = envelope("usage", EXIT_USAGE);
    map.insert("status".into(), Value::from("error"));
    map.insert(
        "error".into(),
        json!({
            "kind": ErrorKind::Usage.as_str(),
            "message": err.message,
            "help": err.help,
        }),
    );
    Value::Object(map)
}

/// The verdict word for a run.
///
/// Derived from the exit code *and* the engine's counters, because the exit
/// code alone conflates cases a consumer must tell apart: a run that proved
/// nothing, a run that was never asked to prove anything, and a run whose only
/// finding is a soundness gap.
#[must_use]
pub fn verify_status(outcome: &RunReport) -> &'static str {
    if outcome.dry_run {
        return "dry_run";
    }
    let Some(summary) = outcome.summary.as_ref() else {
        // No verdict at all. A non-zero child with no summary is a compile
        // failure, not a proof failure — the engine never got that far.
        return if outcome.child_exit_code.unwrap_or(0) == 0 {
            "no_verdict"
        } else {
            "compile_failed"
        };
    };
    if !outcome.verify_mode {
        // --no-verify / --stop-after-analysis / emit-only: the all-zero line
        // the engine emits is expected and means nothing was asked for.
        return "not_requested";
    }
    match outcome.exit_code {
        // A contract that would not parse, or an obligation that was
        // disproved, is what happened regardless of how many others there were.
        EXIT_USAGE => "parse_error",
        EXIT_VERIFICATION_FAILURE => "failed",
        // Otherwise an all-zero summary is the more specific answer than the
        // exit code: the engine examined nothing. It now FAILS CLOSED (exit 2),
        // so this cannot key off exit 0.
        _ if proved_nothing(summary) => "no_obligations",
        EXIT_OK => "verified",
        EXIT_ENCODING_ERROR if only_soundness_gap(summary) => "soundness_gap",
        _ => "error",
    }
}

/// True when every obligation-outcome counter is zero: the engine looked and
/// found nothing to prove (`--filter` matched nothing, or there are no
/// contracts). `warnings` is deliberately excluded — it counts dropped
/// obligations, which is a finding, not an outcome.
#[must_use]
pub fn proved_nothing(summary: &StructuredVerificationResult) -> bool {
    summary.verified == 0
        && summary.failed == 0
        && summary.errors == 0
        && summary.assumed == 0
        && summary.trusted == 0
        && summary.skipped == 0
        && summary.verified_with_axiom_deps == 0
        && summary.unverified_axioms == 0
        && summary.vacuous == 0
        && summary.evidence_gaps == 0
        && summary.proof_assert_failed == 0
        && summary.proof_assert_errors == 0
        && summary.panics == 0
        && summary.demoted == 0
}

/// True when the run's only reason for exiting 2 is a soundness gap: nothing
/// failed, nothing errored, but something was accepted without proof.
fn only_soundness_gap(summary: &StructuredVerificationResult) -> bool {
    summary.has_soundness_gap()
        && summary.failed == 0
        && summary.proof_assert_failed == 0
        && summary.errors == 0
        && summary.proof_assert_errors == 0
        && summary.panics == 0
        && summary.termination_errors == 0
        && summary.logic_recursion_errors == 0
        && summary.erasure_errors == 0
        && summary.parse_errors == 0
}

/// The `TRUST_WP_RESULT:v1` counters as an object (every field, always).
pub fn summary_json(summary: &StructuredVerificationResult) -> Value {
    json!({
        "base_exit_code": summary.base_exit_code,
        "verified": summary.verified,
        "failed": summary.failed,
        "errors": summary.errors,
        "warnings": summary.warnings,
        "assumed": summary.assumed,
        "trusted": summary.trusted,
        "skipped": summary.skipped,
        "verified_with_axiom_deps": summary.verified_with_axiom_deps,
        "verified_native_only": summary.verified_native_only,
        "unverified_axioms": summary.unverified_axioms,
        "vacuous": summary.vacuous,
        "evidence_gaps": summary.evidence_gaps,
        "proof_assert_failed": summary.proof_assert_failed,
        "proof_assert_errors": summary.proof_assert_errors,
        "panics": summary.panics,
        "demoted": summary.demoted,
        "parse_errors": summary.parse_errors,
        "termination_errors": summary.termination_errors,
        "logic_recursion_errors": summary.logic_recursion_errors,
        "erasure_errors": summary.erasure_errors,
    })
}

/// Keys of a diagnostic record that the typed report fields cover; anything
/// else the engine sends lands verbatim under `extra`.
const KNOWN_DIAGNOSTIC_KEYS: &[&str] = &[
    "def_path",
    "kind",
    "status",
    "reason",
    "solve_time_ms",
    "assertions",
    "timeout_ms",
    "ay_result",
    "accepted_for_consumer",
    "model_validated",
    "unsat_proof_available",
    "verification_level",
    "replay_present",
    "replay_bytes",
    "replay_sha256",
    "native_replay_present",
    "native_replay_bytes",
    "native_replay_sha256",
    "native_replay_schema",
    "native_replay_path",
    "native_replay_write_error",
];

/// Why the engine emitted this record.
///
/// The engine emits a diagnostic for every obligation that is *not* cleanly
/// verified — which includes `status=verified` records whose evidence was not
/// credited. Those are gaps, not successes, so a consumer that iterates the
/// array must branch on this rather than on `status`.
fn classification(record: &VerificationDiagnosticRecord) -> &'static str {
    match record.status.as_str() {
        "failed" => "failed",
        "unknown" => "unknown",
        "assumed" => "assumed",
        // A record only exists for a non-clean obligation, so a verified-shaped
        // one is an uncredited evidence gap.
        "verified" => "evidence_gap",
        _ => "other",
    }
}

/// One `TRUST_WP_DIAGNOSTIC:v1` record as a typed object.
///
/// Sentinel mapping, using the decoders in `trust_wp_core::result_protocol`: a
/// numeric field is an integer, or null when the engine said `none` or sent
/// nothing parsable; a tri-state boolean is true/false, or null when the engine
/// said `unknown`; a string field is null when the engine said `none`.
pub fn diagnostic_json(record: &VerificationDiagnosticRecord) -> Value {
    let text = |key: &str| record.field_opt(key).map_or(Value::Null, Value::from);
    let number = |key: &str| record.field_u64(key).map_or(Value::Null, Value::from);
    let boolean = |key: &str| {
        record
            .field_tristate_bool(key)
            .flatten()
            .map_or(Value::Null, Value::from)
    };
    let extra: Map<String, Value> = record
        .extra(KNOWN_DIAGNOSTIC_KEYS)
        .map(|(key, value)| (key.to_string(), Value::from(value)))
        .collect();
    json!({
        "def_path": record.def_path,
        "kind": record.kind,
        "status": record.status,
        "classification": classification(record),
        "reason": record.reason,
        // Reserved: the engine's diagnostic line carries no source location,
        // violated clause or counterexample today — those exist only in its
        // human output. They are named here so consumers can code against them
        // now and pick them up when the engine starts sending them.
        "location": Value::Null,
        "clause": Value::Null,
        "counterexample": Value::Null,
        "solve_time_ms": number("solve_time_ms"),
        "assertions": number("assertions"),
        "timeout_ms": number("timeout_ms"),
        "ay_result": text("ay_result"),
        "accepted_for_consumer": boolean("accepted_for_consumer"),
        "model_validated": boolean("model_validated"),
        "unsat_proof_available": boolean("unsat_proof_available"),
        "verification_level": text("verification_level"),
        "replay": {
            "present": boolean("replay_present"),
            "bytes": number("replay_bytes"),
            "sha256": text("replay_sha256"),
        },
        "native_replay": {
            "present": boolean("native_replay_present"),
            "bytes": number("native_replay_bytes"),
            "sha256": text("native_replay_sha256"),
            "schema": text("native_replay_schema"),
            "path": text("native_replay_path"),
            "write_error": text("native_replay_write_error"),
        },
        "extra": Value::Object(extra),
    })
}

/// The report for `verify` and `result`.
pub fn verify_report(outcome: &RunReport, command: &str) -> Value {
    let engine = |engine: Option<&Engine>| -> (Value, Value) {
        engine.map_or((Value::Null, Value::Null), |e: &Engine| {
            (
                Value::from(e.program.display().to_string()),
                Value::from(e.origin.as_str()),
            )
        })
    };
    let (driver, driver_origin) = engine(outcome.driver.as_ref());
    let (front, front_origin) = engine(outcome.front.as_ref());

    let mut map = envelope(command, outcome.exit_code);
    map.insert("mode".into(), Value::from(outcome.mode));
    map.insert("target".into(), Value::from(outcome.target.as_str()));
    map.insert("status".into(), Value::from(verify_status(outcome)));
    map.insert(
        "summary".into(),
        outcome.summary.as_ref().map_or(Value::Null, summary_json),
    );
    map.insert(
        "diagnostics".into(),
        Value::Array(outcome.diagnostics.iter().map(diagnostic_json).collect()),
    );
    // Say what the array is, so nobody reads it as the full obligation list.
    map.insert(
        "diagnostics_scope".into(),
        Value::from("non_clean_obligations"),
    );
    map.insert(
        "engine".into(),
        json!({
            "driver": driver,
            "driver_origin": driver_origin,
            "front": front,
            "front_origin": front_origin,
            "child_exit_code": outcome.child_exit_code,
        }),
    );
    map.insert(
        "notes".into(),
        Value::Array(
            outcome
                .notes
                .iter()
                .map(|n| Value::from(n.as_str()))
                .collect(),
        ),
    );
    map.insert(
        "error".into(),
        outcome
            .error
            .as_ref()
            .map_or(Value::Null, |(kind, message)| error_json(*kind, message)),
    );
    if let Some(command) = outcome.dry_run_command.as_ref() {
        map.insert("dry_run".into(), command.clone());
    }
    Value::Object(map)
}

// ---------------------------------------------------------------------------
// `trust-wp result`
// ---------------------------------------------------------------------------

/// Decode a saved transcript (or stdin) into a report.
pub fn decode_transcript(input: Option<&Path>, json: bool) -> i32 {
    let target = input.map_or_else(|| "-".to_string(), |p| p.display().to_string());
    let mut relay = StderrRelay::collecting();
    let fed = match input {
        Some(path) => fs::read_to_string(path).map(|text| {
            for line in text.lines() {
                relay.line(line);
            }
        }),
        None => {
            let stdin = io::stdin();
            let mut result = Ok(());
            for line in stdin.lock().lines() {
                match line {
                    Ok(line) => relay.line(&line),
                    Err(err) => {
                        result = Err(err);
                        break;
                    }
                }
            }
            result
        }
    };
    if let Err(err) = fed {
        eprintln!("error: cannot read `{target}`: {err}");
        if json {
            let mut map = envelope("result", EXIT_USAGE);
            map.insert("target".into(), Value::from(target.as_str()));
            map.insert("status".into(), Value::from("error"));
            map.insert(
                "error".into(),
                error_json(ErrorKind::Io, format!("cannot read `{target}`: {err}")),
            );
            print_json(&Value::Object(map));
        }
        return EXIT_USAGE;
    }

    // A transcript carries no child status; the verdict is the wire's. No
    // result line at all is "nothing was proved", exactly as for a run.
    let exit_code = engine_exit_code(0, relay.wire.as_ref(), true, false, false);
    let outcome = RunReport {
        exit_code,
        mode: "transcript",
        target,
        summary: relay.wire,
        diagnostics: relay.diagnostics,
        // A transcript is the record of a run that was asked for a verdict.
        verify_mode: true,
        ..RunReport::default()
    };

    if json {
        print_json(&verify_report(&outcome, "result"));
    } else {
        print_human_summary(&outcome);
    }
    exit_code
}

fn print_human_summary(outcome: &RunReport) {
    println!(
        "trust-wp result: {} (exit {})",
        verify_status(outcome),
        outcome.exit_code
    );
    match &outcome.summary {
        Some(summary) => {
            let mut parts = vec![
                format!("{} verified", summary.verified),
                format!("{} failed", summary.failed),
                format!("{} errors", summary.errors),
                format!("{} warnings", summary.warnings),
            ];
            let optional: [(&str, u64); 16] = [
                ("assumed", summary.assumed),
                ("trusted", summary.trusted),
                ("skipped", summary.skipped),
                ("verified with axiom deps", summary.verified_with_axiom_deps),
                (
                    "verified, re-checkable only by ay",
                    summary.verified_native_only,
                ),
                ("unverified axioms", summary.unverified_axioms),
                ("vacuous", summary.vacuous),
                ("evidence gaps", summary.evidence_gaps),
                ("proof_assert failed", summary.proof_assert_failed),
                ("proof_assert errors", summary.proof_assert_errors),
                ("panicked", summary.panics),
                ("demoted", summary.demoted),
                ("parse errors", summary.parse_errors),
                ("termination errors", summary.termination_errors),
                ("logic recursion errors", summary.logic_recursion_errors),
                ("erasure errors", summary.erasure_errors),
            ];
            parts.extend(
                optional
                    .iter()
                    .filter(|(_, count)| *count > 0)
                    .map(|(name, count)| format!("{count} {name}")),
            );
            println!("  {}", parts.join(", "));
        }
        None => println!("  no TRUST_WP_RESULT:v1 line in the transcript"),
    }
    println!("  diagnostics: {}", outcome.diagnostics.len());
    for record in &outcome.diagnostics {
        let timing = record
            .field("solve_time_ms")
            .map_or_else(String::new, |ms| format!(" {ms}ms"));
        println!(
            "    {} [{}] {} ({}){timing}",
            record.def_path, record.kind, record.status, record.reason
        );
    }
}

/// `trust-wp doctor --json`.
///
/// The human path in `main.rs` stays the authority on what a healthy install
/// looks like; this reuses the same probes and reports them as data.
pub fn doctor_report() -> i32 {
    use crate::{
        compiler_tool, find_cargo_front, find_contract_rlib, find_engine, repo_root,
        CARGO_FRONT_BIN, CONTRACT_CRATES, DRIVER_BIN, DRIVER_BINS,
    };

    let mut checks: Vec<Value> = Vec::new();
    let mut ready = true;
    let mut row = |name: &str, ok: bool, detail: String, fixes: Vec<String>| {
        checks.push(json!({ "name": name, "ok": ok, "detail": detail, "fixes": fixes }));
    };

    match repo_root() {
        Some(root) => row("checkout", true, root.display().to_string(), Vec::new()),
        None => {
            ready = false;
            row(
                "checkout",
                false,
                "NOT FOUND".to_string(),
                vec!["set $TRUST_WP_HOME to the trust-wp checkout".to_string()],
            );
        }
    }

    match find_engine(&DRIVER_BINS, "TRUST_WP_RUSTC") {
        Ok(engine) => {
            row(
                DRIVER_BIN,
                true,
                format!("{} (via {})", engine.program.display(), engine.origin),
                Vec::new(),
            );
            match std::process::Command::new(&engine.program)
                .env("TRUST_WP_ARGS", "--help")
                .output()
            {
                Ok(output) if output.status.success() => row(
                    "engine runtime",
                    true,
                    "ok (driver loads and responds)".to_string(),
                    Vec::new(),
                ),
                Ok(output) => {
                    ready = false;
                    let detail = String::from_utf8_lossy(&output.stderr);
                    let first = detail
                        .lines()
                        .next()
                        .unwrap_or("no output")
                        .trim()
                        .to_string();
                    row(
                        "engine runtime",
                        false,
                        format!("BROKEN: {first}"),
                        vec![
                            "targo --unverified build --release -p trust-wp-driver --bin trust-wp-rustc"
                                .to_string(),
                        ],
                    );
                }
                Err(err) => {
                    ready = false;
                    row(
                        "engine runtime",
                        false,
                        format!("BROKEN: {err}"),
                        Vec::new(),
                    );
                }
            }
        }
        Err(missing) => {
            ready = false;
            row(
                DRIVER_BIN,
                false,
                "MISSING (single-file and crate mode unavailable)".to_string(),
                missing.actionable_fixes().cloned().collect(),
            );
        }
    }

    match find_cargo_front() {
        Ok(engine) => row(
            CARGO_FRONT_BIN,
            true,
            format!("{} (via {})", engine.program.display(), engine.origin),
            Vec::new(),
        ),
        Err(missing) => {
            ready = false;
            row(
                CARGO_FRONT_BIN,
                false,
                "MISSING (crate mode unavailable)".to_string(),
                missing.actionable_fixes().cloned().collect(),
            );
        }
    }

    for (crate_name, rlib_name, package) in CONTRACT_CRATES {
        match find_contract_rlib(rlib_name) {
            Some((rlib, _)) => row(crate_name, true, rlib.display().to_string(), Vec::new()),
            None => {
                // Only the native contract crate is required; a machine that
                // never built the Creusot compat shim is still ready.
                let required = crate_name == "trust_wp";
                ready &= !required;
                row(
                    crate_name,
                    !required,
                    if required {
                        "NOT BUILT (single-file mode needs it)".to_string()
                    } else {
                        "not built (only needed for creusot_contracts sources)".to_string()
                    },
                    vec![format!("targo --unverified build --release -p {package}")],
                );
            }
        }
    }

    match std::process::Command::new(compiler_tool())
        .args(["--print", "sysroot"])
        .output()
    {
        Ok(output) if output.status.success() => row(
            "active sysroot",
            true,
            String::from_utf8_lossy(&output.stdout).trim().to_string(),
            Vec::new(),
        ),
        Ok(output) => {
            ready = false;
            let detail = String::from_utf8_lossy(&output.stderr);
            row(
                "active sysroot",
                false,
                format!(
                    "UNAVAILABLE: {}",
                    detail.lines().next().unwrap_or("unknown error").trim()
                ),
                vec!["the Trust toolchain must be installed and built".to_string()],
            );
        }
        Err(err) => {
            ready = false;
            row(
                "active sysroot",
                false,
                format!("UNAVAILABLE: {err}"),
                Vec::new(),
            );
        }
    }

    let exit_code = if ready { EXIT_OK } else { EXIT_ENCODING_ERROR };
    let mut map = envelope("doctor", exit_code);
    map.insert("ready".into(), Value::from(ready));
    map.insert(
        "status".into(),
        Value::from(if ready { "ready" } else { "not_ready" }),
    );
    map.insert("checks".into(), Value::Array(checks));
    map.insert("error".into(), Value::Null);
    print_json(&Value::Object(map));
    exit_code
}

#[cfg(test)]
mod tests {
    use super::*;

    fn outcome_with(exit_code: i32, summary: Option<StructuredVerificationResult>) -> RunReport {
        RunReport {
            exit_code,
            mode: "file",
            summary,
            verify_mode: true,
            ..RunReport::default()
        }
    }

    #[test]
    fn status_distinguishes_the_cases_the_exit_code_conflates() {
        let mut verified = StructuredVerificationResult::default();
        verified.verified = 2;
        assert_eq!(
            verify_status(&outcome_with(0, Some(verified.clone()))),
            "verified"
        );

        // Exit 0 with nothing checked is not a proof.
        let empty = StructuredVerificationResult::default();
        assert_eq!(
            verify_status(&outcome_with(0, Some(empty.clone()))),
            "no_obligations"
        );

        // ...and neither is a run that was never asked to verify.
        let not_asked = RunReport {
            verify_mode: false,
            ..outcome_with(0, Some(empty.clone()))
        };
        assert_eq!(verify_status(&not_asked), "not_requested");

        let mut failed = StructuredVerificationResult::default();
        failed.failed = 1;
        failed.normalize_exit_code();
        assert_eq!(verify_status(&outcome_with(1, Some(failed))), "failed");

        // Exit 2 for a gap alone is not the same as exit 2 for an error.
        let mut trusted = StructuredVerificationResult::default();
        trusted.verified = 1;
        trusted.trusted = 1;
        trusted.normalize_exit_code();
        assert_eq!(
            verify_status(&outcome_with(2, Some(trusted))),
            "soundness_gap"
        );

        let mut errored = StructuredVerificationResult::default();
        errored.errors = 1;
        errored.trusted = 1;
        errored.normalize_exit_code();
        assert_eq!(verify_status(&outcome_with(2, Some(errored))), "error");

        let mut parse = StructuredVerificationResult::default();
        parse.parse_errors = 1;
        parse.normalize_exit_code();
        assert_eq!(verify_status(&outcome_with(3, Some(parse))), "parse_error");

        // No summary: a non-zero child never compiled; a zero child ran and
        // said nothing.
        assert_eq!(verify_status(&outcome_with(2, None)), "no_verdict");
        let crashed = RunReport {
            child_exit_code: Some(1),
            ..outcome_with(1, None)
        };
        assert_eq!(verify_status(&crashed), "compile_failed");

        let dry = RunReport {
            dry_run: true,
            ..outcome_with(0, None)
        };
        assert_eq!(verify_status(&dry), "dry_run");
    }

    #[test]
    fn usage_errors_still_produce_a_report() {
        let err = UsageError::new("`--frobnicate` is not a trust-wp option")
            .with_help("run `trust-wp --help`");
        let value = usage_report(&err);
        assert_eq!(value["schema"], REPORT_SCHEMA);
        assert_eq!(value["command"], "usage");
        assert_eq!(value["exit_code"], 3);
        assert_eq!(value["status"], "error");
        assert_eq!(value["error"]["kind"], "usage");
        assert_eq!(value["error"]["help"][0], "run `trust-wp --help`");
    }

    #[test]
    fn summary_json_carries_every_counter() {
        let mut summary = StructuredVerificationResult::default();
        summary.verified = 2;
        summary.failed = 1;
        summary.normalize_exit_code();
        let value = summary_json(&summary);
        let object = value.as_object().unwrap();
        assert_eq!(object.len(), 21);
        assert_eq!(object["verified"], 2);
        assert_eq!(object["failed"], 1);
        assert_eq!(object["base_exit_code"], 1);
        // A caveat counter is reported even when it is zero: a consumer needs
        // to distinguish "no obligation lacked an externally replayable proof"
        // from "this producer does not report that".
        assert_eq!(object["verified_native_only"], 0);
    }

    #[test]
    fn diagnostic_json_types_known_fields_and_keeps_the_rest() {
        let record = VerificationDiagnosticRecord::from_wire_line(
            "TRUST_WP_DIAGNOSTIC:v1 def_path=demo::f kind=function_contract status=failed \
             reason=counterexample solve_time_ms=12 assertions=7 timeout_ms=none ay_result=sat \
             accepted_for_consumer=true model_validated=unknown unsat_proof_available=false \
             verification_level=FullyVerified replay_present=false replay_bytes=0 \
             replay_sha256=none native_replay_present=false native_replay_bytes=0 \
             native_replay_sha256=none native_replay_schema=none native_replay_path=none \
             native_replay_write_error=none brand_new=%7B%7D",
        )
        .unwrap();
        let value = diagnostic_json(&record);
        assert_eq!(value["def_path"], "demo::f");
        assert_eq!(value["solve_time_ms"], 12);
        assert_eq!(value["timeout_ms"], Value::Null);
        assert_eq!(value["accepted_for_consumer"], true);
        assert_eq!(value["model_validated"], Value::Null);
        assert_eq!(value["unsat_proof_available"], false);
        assert_eq!(value["verification_level"], "FullyVerified");
        assert_eq!(value["replay"]["present"], false);
        assert_eq!(value["replay"]["sha256"], Value::Null);
        assert_eq!(value["native_replay"]["schema"], Value::Null);
        assert_eq!(value["extra"]["brand_new"], "{}");
        assert_eq!(value["extra"].as_object().unwrap().len(), 1);
        assert_eq!(value["classification"], "failed");
        // Reserved, always present, always null until the engine sends them.
        assert_eq!(value["location"], Value::Null);
        assert_eq!(value["clause"], Value::Null);
        assert_eq!(value["counterexample"], Value::Null);
    }

    #[test]
    fn a_verified_shaped_diagnostic_is_classified_as_a_gap() {
        // The engine only emits a record for an obligation that is NOT cleanly
        // verified, so `status=verified` here means the evidence was not
        // credited — a consumer must not read it as a success.
        let record = VerificationDiagnosticRecord::from_wire_line(
            "TRUST_WP_DIAGNOSTIC:v1 def_path=demo::g kind=function_contract status=verified \
             reason=none accepted_for_consumer=false",
        )
        .unwrap();
        let value = diagnostic_json(&record);
        assert_eq!(value["status"], "verified");
        assert_eq!(value["classification"], "evidence_gap");
        assert_eq!(value["accepted_for_consumer"], false);
    }

    #[test]
    fn verify_report_has_the_envelope_and_a_verdict() {
        let mut summary = StructuredVerificationResult::default();
        summary.verified = 1;
        let outcome = RunReport {
            exit_code: 0,
            mode: "file",
            target: "/work/demo.rs".to_string(),
            summary: Some(summary),
            verify_mode: true,
            ..RunReport::default()
        };
        let value = verify_report(&outcome, "verify");
        assert_eq!(value["schema"], REPORT_SCHEMA);
        assert_eq!(value["tool"]["name"], "trust-wp");
        assert_eq!(value["command"], "verify");
        assert_eq!(value["mode"], "file");
        assert_eq!(value["status"], "verified");
        assert_eq!(value["summary"]["verified"], 1);
        assert_eq!(value["diagnostics"].as_array().unwrap().len(), 0);
        assert_eq!(value["engine"]["driver"], Value::Null);
        // A verdict-less outcome says so instead of inventing counters.
        let outcome = RunReport {
            exit_code: EXIT_ENCODING_ERROR,
            mode: "crate",
            verify_mode: true,
            ..RunReport::default()
        };
        let value = verify_report(&outcome, "verify");
        assert_eq!(value["status"], "no_verdict");
        assert_eq!(value["summary"], Value::Null);
        assert_eq!(value["diagnostics_scope"], "non_clean_obligations");
        assert_eq!(value["error"], Value::Null);
    }
}
