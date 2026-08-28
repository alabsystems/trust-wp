// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `trust-wp bundle` — verify, validate and replay `trust-wp.verify-bundle.v1`
//! requests in-process.
//!
//! This is trust-wp-core's native pure-replay prover: claims in
//! `trust_wp_pure_expr_v1` or `trust_formula_v1` form are decoded, proved by
//! replaying trust-wp's own rewrite rules, and every verified obligation
//! carries hash-addressed proof evidence that `bundle replay` re-checks
//! independently. No SMT solver is involved; anything the replay rules cannot
//! settle is reported `unsupported`, never guessed.

use std::{
    fs,
    path::{Path, PathBuf},
};

use serde_json::{json, Value};
use trust_wp_core::verify_bundle::{
    replay_verify_bundle_result_evidence, BundleClaim, BundleClaimFormat, BundleDiagnostic,
    BundleDiagnosticSeverity, BundleDigest, BundleObligation, BundleObligationKind,
    BundleObligationStatus, BundleProducer, BundleSourceSpan, BundleTarget,
    NativeTrustWpBundleVerifier, VerifyBundleEngine, VerifyBundleOptions, VerifyBundleRequest,
    VerifyBundleResult,
};

use crate::{
    report::{self, ErrorKind},
    split_inline_value, take_value, write_text, UsageError, EXIT_ENCODING_ERROR, EXIT_OK,
    EXIT_USAGE,
};

/// `bundle verify|validate|replay|example`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BundleCommand {
    Verify {
        request: PathBuf,
        out: Option<PathBuf>,
    },
    Validate {
        request: PathBuf,
    },
    Replay {
        request: PathBuf,
        result: PathBuf,
    },
    Example {
        out: Option<PathBuf>,
    },
}

pub fn parse(args: &[String]) -> Result<BundleCommand, UsageError> {
    const USAGE: &str = "usage: trust-wp bundle verify <REQUEST.json> [-o RESULT.json]\n       \
                         trust-wp bundle validate <REQUEST.json>\n       \
                         trust-wp bundle replay <REQUEST.json> <RESULT.json>\n       \
                         trust-wp bundle example [-o FILE]";
    match args.first().map(String::as_str) {
        Some("verify") => {
            let rest = &args[1..];
            let mut request: Option<PathBuf> = None;
            let mut out: Option<PathBuf> = None;
            let mut i = 0;
            while i < rest.len() {
                let arg = rest[i].clone();
                let (name, inline) = split_inline_value(&arg);
                match name {
                    "-o" | "--out" => {
                        out = Some(PathBuf::from(take_value(name, inline, rest, &mut i)?));
                    }
                    _ if arg.starts_with('-') => {
                        return Err(UsageError::new(format!(
                            "`trust-wp bundle verify` does not accept `{arg}`"
                        ))
                        .with_help(USAGE));
                    }
                    _ => {
                        if request.is_some() {
                            return Err(UsageError::new(
                                "`trust-wp bundle verify` takes one request file",
                            )
                            .with_help(USAGE));
                        }
                        request = Some(PathBuf::from(&arg));
                    }
                }
                i += 1;
            }
            let Some(request) = request else {
                return Err(
                    UsageError::new("`trust-wp bundle verify` needs a request file")
                        .with_help(USAGE)
                        .with_help(
                            "`trust-wp bundle example > request.json` writes one to start from",
                        ),
                );
            };
            Ok(BundleCommand::Verify { request, out })
        }
        Some("validate") => {
            let positionals = positionals_only(&args[1..], "trust-wp bundle validate", USAGE)?;
            match positionals.as_slice() {
                [request] => Ok(BundleCommand::Validate {
                    request: PathBuf::from(request),
                }),
                [] => Err(
                    UsageError::new("`trust-wp bundle validate` needs a request file")
                        .with_help(USAGE),
                ),
                _ => Err(
                    UsageError::new("`trust-wp bundle validate` takes one request file")
                        .with_help(USAGE),
                ),
            }
        }
        Some("replay") => {
            let positionals = positionals_only(&args[1..], "trust-wp bundle replay", USAGE)?;
            match positionals.as_slice() {
                [request, result] => Ok(BundleCommand::Replay {
                    request: PathBuf::from(request),
                    result: PathBuf::from(result),
                }),
                _ => Err(UsageError::new(
                    "`trust-wp bundle replay` needs a request file and a result file",
                )
                .with_help(USAGE)),
            }
        }
        Some("example") => {
            let out = parse_out_only(&args[1..], "trust-wp bundle example")?;
            Ok(BundleCommand::Example { out })
        }
        Some(other) => Err(UsageError::new(format!(
            "unknown `trust-wp bundle` subcommand `{other}`"
        ))
        .with_help(USAGE)),
        None => Err(UsageError::new("`trust-wp bundle` needs a subcommand").with_help(USAGE)),
    }
}

fn parse_out_only(args: &[String], usage: &str) -> Result<Option<PathBuf>, UsageError> {
    let mut out: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].clone();
        let (name, inline) = split_inline_value(&arg);
        match name {
            "-o" | "--out" => {
                let value = take_value(name, inline, args, &mut i)?;
                out = Some(PathBuf::from(value));
            }
            _ => {
                return Err(
                    UsageError::new(format!("`{usage}` does not accept `{arg}`")).with_help(
                        format!("usage: {usage} [-o FILE]  (default: write to stdout)"),
                    ),
                );
            }
        }
        i += 1;
    }
    Ok(out)
}

fn positionals_only(args: &[String], what: &str, usage: &str) -> Result<Vec<String>, UsageError> {
    let mut out = Vec::new();
    for arg in args {
        if arg.starts_with('-') {
            return Err(
                UsageError::new(format!("`{what}` does not accept `{arg}`")).with_help(usage)
            );
        }
        out.push(arg.clone());
    }
    Ok(out)
}

pub fn run(command: &BundleCommand, json: bool) -> i32 {
    match command {
        BundleCommand::Verify { request, out } => verify(request, out.as_deref(), json),
        BundleCommand::Validate { request } => validate(request, json),
        BundleCommand::Replay { request, result } => replay(request, result, json),
        BundleCommand::Example { out } => example(out.as_deref()),
    }
}

/// A request that could not be read or decoded: exit 3 with the reason, and a
/// JSON error report when one was asked for.
fn input_error(
    command: &str,
    path: &Path,
    what: &str,
    err: &dyn std::fmt::Display,
    json: bool,
) -> i32 {
    let message = format!("cannot {what} `{}`: {err}", path.display());
    eprintln!("error: {message}");
    if json {
        let mut map = report::envelope(command, EXIT_USAGE);
        map.insert("status".into(), Value::from("invalid"));
        map.insert("target".into(), Value::from(path.display().to_string()));
        map.insert(
            "error".into(),
            report::error_json(ErrorKind::InvalidBundle, message),
        );
        report::print_json(&Value::Object(map));
    }
    EXIT_USAGE
}

fn load_request(command: &str, path: &Path, json: bool) -> Result<VerifyBundleRequest, i32> {
    let text = fs::read_to_string(path)
        .map_err(|err| input_error(command, path, "read the request", &err, json))?;
    serde_json::from_str::<VerifyBundleRequest>(&text)
        .map_err(|err| input_error(command, path, "decode the request", &err, json))
}

fn load_result(command: &str, path: &Path, json: bool) -> Result<VerifyBundleResult, i32> {
    let text = fs::read_to_string(path)
        .map_err(|err| input_error(command, path, "read the result", &err, json))?;
    serde_json::from_str::<VerifyBundleResult>(&text)
        .map_err(|err| input_error(command, path, "decode the result", &err, json))
}

fn diagnostic_json(diagnostic: &BundleDiagnostic) -> Value {
    json!({
        "severity": diagnostic.severity.as_str(),
        "code": diagnostic.code,
        "message": diagnostic.message,
    })
}

fn print_diagnostics(diagnostics: &[BundleDiagnostic]) {
    for diagnostic in diagnostics {
        eprintln!(
            "  {} {}: {}",
            diagnostic.severity.as_str(),
            diagnostic.code,
            diagnostic.message
        );
    }
}

/// Counts of obligation outcomes, for the one-line summary.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Tally {
    verified: usize,
    failed: usize,
    unknown: usize,
    unsupported: usize,
}

impl Tally {
    fn of(result: &VerifyBundleResult) -> Self {
        let mut tally = Self::default();
        for obligation in &result.obligation_results {
            match obligation.status {
                BundleObligationStatus::Verified { .. } => tally.verified += 1,
                BundleObligationStatus::Failed { .. } => tally.failed += 1,
                BundleObligationStatus::Unknown { .. } => tally.unknown += 1,
                BundleObligationStatus::Unsupported { .. } => tally.unsupported += 1,
                // A status this build does not know is not a success.
                #[allow(unreachable_patterns)]
                _ => tally.unknown += 1,
            }
        }
        tally
    }

    fn json(self) -> Value {
        json!({
            "verified": self.verified,
            "failed": self.failed,
            "unknown": self.unknown,
            "unsupported": self.unsupported,
        })
    }
}

fn verify(request_path: &Path, out: Option<&Path>, json: bool) -> i32 {
    const COMMAND: &str = "bundle verify";
    let request = match load_request(COMMAND, request_path, json) {
        Ok(request) => request,
        Err(code) => return code,
    };
    let bundle_id = request.bundle_id.clone();
    let obligations = request.obligations.len();

    let result = NativeTrustWpBundleVerifier.verify_bundle(request);
    let exit_code = result.exit_code();
    let tally = Tally::of(&result);

    eprintln!(
        "trust-wp: bundle `{bundle_id}`: {} — {} obligation(s): {} verified, {} failed, {} unknown, {} unsupported",
        result.status.as_str(),
        obligations,
        tally.verified,
        tally.failed,
        tally.unknown,
        tally.unsupported
    );
    print_diagnostics(&result.diagnostics);
    for obligation in &result.obligation_results {
        if !obligation.diagnostics.is_empty() {
            eprintln!("  obligation `{}`:", obligation.obligation_id);
            print_diagnostics(&obligation.diagnostics);
        }
    }

    let result_text = match serde_json::to_string_pretty(&result) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("error: cannot encode the result: {err}");
            return EXIT_ENCODING_ERROR;
        }
    };

    if let Some(path) = out {
        if let Err(err) = fs::write(path, &result_text) {
            eprintln!("error: cannot write {}: {err}", path.display());
            return EXIT_ENCODING_ERROR;
        }
        eprintln!("wrote {}", path.display());
    }

    if json {
        // Under `--json`, stdout carries exactly one report — so the result
        // document is embedded, or named by path when `-o` wrote it.
        let mut map = report::envelope(COMMAND, exit_code);
        map.insert("bundle_id".into(), Value::from(bundle_id));
        map.insert("status".into(), Value::from(result.status.as_str()));
        map.insert("obligations".into(), tally.json());
        match out {
            Some(path) => {
                map.insert(
                    "result_path".into(),
                    Value::from(path.display().to_string()),
                );
            }
            None => {
                map.insert(
                    "result".into(),
                    serde_json::to_value(&result).unwrap_or(Value::Null),
                );
            }
        }
        map.insert("error".into(), Value::Null);
        report::print_json(&Value::Object(map));
    } else if out.is_none() {
        // Without `--json` the result document itself is the product.
        println!("{result_text}");
    }
    exit_code
}

/// Order severities so the worst one decides; a severity this build does not
/// know ranks as invalid (fail closed).
fn severity_rank(severity: BundleDiagnosticSeverity) -> u8 {
    match severity {
        BundleDiagnosticSeverity::Warning => 1,
        BundleDiagnosticSeverity::Unsupported => 2,
        BundleDiagnosticSeverity::Invalid => 3,
        #[allow(unreachable_patterns)]
        _ => 3,
    }
}

fn validate(request_path: &Path, json: bool) -> i32 {
    const COMMAND: &str = "bundle validate";
    let request = match load_request(COMMAND, request_path, json) {
        Ok(request) => request,
        Err(code) => return code,
    };
    let diagnostics = request.validation_diagnostics();
    let worst = diagnostics
        .iter()
        .map(|d| severity_rank(d.severity))
        .max()
        .unwrap_or(0);
    let (exit_code, status) = match worst {
        0 | 1 => (EXIT_OK, "valid"),
        2 => (EXIT_ENCODING_ERROR, "unsupported"),
        _ => (EXIT_USAGE, "invalid"),
    };

    eprintln!(
        "trust-wp: bundle `{}`: {status} ({} obligation(s), {} diagnostic(s))",
        request.bundle_id,
        request.obligations.len(),
        diagnostics.len()
    );
    print_diagnostics(&diagnostics);

    if json {
        let mut map = report::envelope(COMMAND, exit_code);
        map.insert("bundle_id".into(), Value::from(request.bundle_id.as_str()));
        map.insert("status".into(), Value::from(status));
        map.insert("obligations".into(), Value::from(request.obligations.len()));
        map.insert(
            "diagnostics".into(),
            Value::Array(diagnostics.iter().map(diagnostic_json).collect()),
        );
        map.insert(
            "error".into(),
            if exit_code == EXIT_OK {
                Value::Null
            } else {
                report::error_json(
                    ErrorKind::InvalidBundle,
                    format!("request is {status}; see diagnostics"),
                )
            },
        );
        report::print_json(&Value::Object(map));
    }
    exit_code
}

fn replay(request_path: &Path, result_path: &Path, json: bool) -> i32 {
    const COMMAND: &str = "bundle replay";
    let request = match load_request(COMMAND, request_path, json) {
        Ok(request) => request,
        Err(code) => return code,
    };
    let result = match load_result(COMMAND, result_path, json) {
        Ok(result) => result,
        Err(code) => return code,
    };

    let replayed = replay_verify_bundle_result_evidence(&request, &result);
    let (exit_code, status) = match &replayed {
        Ok(()) => {
            eprintln!(
                "trust-wp: bundle `{}`: evidence replayed — {} obligation result(s) re-proved",
                result.bundle_id,
                result.obligation_results.len()
            );
            (EXIT_OK, "replayed")
        }
        Err(err) => {
            eprintln!(
                "trust-wp: bundle `{}`: evidence did NOT replay — {}: {}",
                result.bundle_id, err.code, err.message
            );
            (EXIT_ENCODING_ERROR, "not_replayed")
        }
    };

    if json {
        let mut map = report::envelope(COMMAND, exit_code);
        map.insert("bundle_id".into(), Value::from(result.bundle_id.as_str()));
        map.insert("status".into(), Value::from(status));
        map.insert(
            "obligations".into(),
            Value::from(result.obligation_results.len()),
        );
        map.insert(
            "error".into(),
            match &replayed {
                Ok(()) => Value::Null,
                Err(err) => {
                    let mut error =
                        report::error_json(ErrorKind::InvalidBundle, err.message.clone());
                    if let Some(fields) = error.as_object_mut() {
                        fields.insert("code".to_string(), Value::from(err.code.as_str()));
                    }
                    error
                }
            },
        );
        report::print_json(&Value::Object(map));
    }
    exit_code
}

/// The smallest request that verifies: one postcondition whose claim is a
/// linear tautology the native prover actually proves (rather than a constant
/// `true`, which would demonstrate nothing).
pub fn example_request() -> VerifyBundleRequest {
    let mut options = VerifyBundleOptions::default();
    options.require_proof_evidence = true;
    options.timeout_ms = None;

    VerifyBundleRequest::new(
        "example-1",
        BundleProducer::new("trust-wp-cli").with_version(env!("CARGO_PKG_VERSION")),
        BundleTarget::new("demo_crate").with_package_name("demo"),
    )
    .with_obligation(
        BundleObligation::new(
            "post-increment",
            BundleObligationKind::Postcondition,
            "demo::increment",
            BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x + 1 > x")
                .with_digest(BundleDigest::new("sha256", "example-claim-digest")),
        )
        .with_location(BundleSourceSpan::new("src/lib.rs", 10, 5)),
    )
    .with_options(options)
}

fn example(out: Option<&Path>) -> i32 {
    let request = example_request();
    let mut text = match serde_json::to_string_pretty(&request) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("error: cannot encode the example request: {err}");
            return EXIT_ENCODING_ERROR;
        }
    };
    text.push('\n');
    write_text(out, &text, "the example request", |path| {
        format!("trust-wp bundle verify {}", path.display())
    })
}

pub fn help() -> String {
    r"trust-wp bundle — verify-bundle requests, in-process

USAGE:
    trust-wp bundle verify <REQUEST.json> [-o RESULT.json]
    trust-wp bundle validate <REQUEST.json>
    trust-wp bundle replay <REQUEST.json> <RESULT.json>
    trust-wp bundle example [-o FILE]

    A request is a `trust-wp.verify-bundle.v1` JSON document: a producer, a target
    crate, and obligations whose claims are contract expressions
    (`trust_wp_pure_expr_v1`) or Trust formulas (`trust_formula_v1`).

    verify    prove every obligation with trust-wp-core's native pure-replay
              prover and print the result document (JSON) on stdout, or write it
              with -o. Exit 0 verified / 1 failed / 2 unknown or unsupported /
              3 invalid request. No SMT solver is involved: what the replay rules
              cannot settle is `unsupported`, never guessed — an open predicate
              such as `x > 0` is unsupported, while `x + 1 > x` is proved.
              With `--json` stdout carries the report instead, with the result
              embedded under `result` (or named by `result_path` when -o wrote it).
    validate  structural validation only (schema, ids, decodable claims):
              exit 0 valid / 2 unsupported / 3 invalid.
    replay    re-check a result's hash-addressed proof evidence independently of
              the run that produced it: exit 0 replayed / 2 not replayed / 3 bad input.
    example   write the smallest request that verifies.

EXAMPLE:
    trust-wp bundle example -o req.json
    trust-wp bundle verify req.json -o res.json
    trust-wp bundle replay req.json res.json

None of these need rustc, a sysroot or the solver.

`--json` reports: verify {bundle_id, status, obligations{verified, failed, unknown,
unsupported}, result|result_path}; validate {bundle_id, status, obligations,
diagnostics[]}; replay {bundle_id, status, obligations, error}."
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_example_request_is_valid_and_verifies() {
        let request = example_request();
        assert!(request.validation_diagnostics().is_empty());
        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
        assert_eq!(result.exit_code(), EXIT_OK, "{result:?}");
        assert_eq!(Tally::of(&result).verified, 1);
        assert!(replay_verify_bundle_result_evidence(&request, &result).is_ok());
    }

    #[test]
    fn the_example_request_round_trips_through_json() {
        let request = example_request();
        let text = serde_json::to_string(&request).unwrap();
        let again: VerifyBundleRequest = serde_json::from_str(&text).unwrap();
        assert_eq!(again.bundle_id, "example-1");
        assert_eq!(again.obligations.len(), 1);
    }
}
