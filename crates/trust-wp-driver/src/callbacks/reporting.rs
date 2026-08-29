// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification result reporting and summary formatting.
//!
//! Extracted from `verification.rs` as Phase 2 of the callbacks/verification
//! decomposition (#1526). Contains all user-facing output logic: summary
//! formatting, function result reporting, proof_assert result reporting,
//! and diagnostic hints.

use std::{collections::HashSet, fmt::Write as _, fs, path::PathBuf, time::Duration};

use sha2::{Digest, Sha256};
use tracing::debug;
use trust_wp_ay::{
    proof_assert_native_replay_metadata, proof_assert_obligation_slice_claims,
    proof_assert_obligation_slice_derivations, EncodingError, ProofAssertSliceCertificate,
    ProofAssertSliceDerivation, SolveEvidenceSnapshot, SolveStatisticsSnapshot,
    SolveVerificationLevelSnapshot, UnknownReason, VerificationOutcome, VerificationProvenance,
    VerificationResult,
};
use trust_wp_core::{logic::LogicFnDef, result_protocol::encode_wire_value};

use super::{
    super::contracts::FunctionContract, encoding_error_breakdown::EncodingErrorBreakdown,
    helpers::report_counterexample, parsing::ParsedContract,
};

const NATIVE_REPLAY_DIR_ENV: &str = "TRUST_WP_NATIVE_REPLAY_DIR";
const NATIVE_REPLAY_SCHEMA: &str = "ay.native-replay.v1";
const PROOF_ASSERT_REPLAY_TIMEOUT_MAX_MS: u128 = 6_000;

/// Accumulated counters for function contract verification results.
///
/// Consolidates the individual `&mut usize` counter parameters that were
/// previously threaded through `verify_contracts`, `verify_contract_loop_path`,
/// `verify_logic_fn_postconditions`, `check_trait_refinement`, and the
/// reporting functions. Introduced as Phase 3 of the callbacks/verification
/// decomposition (#1526).
#[derive(Debug, Default)]
pub(super) struct VerificationCounters {
    pub verified: usize,
    pub failed: usize,
    pub errors: usize,
    pub skipped: usize,
    pub trusted: usize,
    /// Functions whose contracts were assumed correct by the solver without
    /// SMT proof (e.g., incomplete axioms, solver bailout). Distinct from
    /// `trusted` which counts `#[trusted]`-annotated functions skipped by
    /// design (#1891).
    pub assumed: usize,
    pub warnings: usize,
    /// Functions verified but depending on unproven axioms (#1878).
    /// Not counted in `verified` — these are conditionally verified only.
    pub verified_with_axiom_deps: usize,
    /// Functions verified on proof authority no INDEPENDENT checker can
    /// re-check. Counted in `verified` as well: they ARE proved, and ay
    /// validated every inference — a genuinely unproved step is a `hole` in the
    /// proof IR and is refused outright. What they lack is a rendering the
    /// pinned Alethe calculus can express, so carcara cannot replay them.
    /// Reported separately because "we checked this" and "anyone can check
    /// this" are different claims.
    pub verified_native_only: usize,
    /// Functions where driver-level processing panicked (#1975).
    /// Panics in contract parsing, MIR extraction, or expression analysis are
    /// caught per-function so the rest of the verification run continues.
    pub panics: usize,
    /// Functions whose `Verified` result was demoted to `Unknown` because
    /// encoding approximations (sort fallback, panic recovery, etc.) fired
    /// during their verification (#2106). These are a subset of `errors` —
    /// the `errors` counter is incremented by the normal `Unknown` reporting
    /// path; this counter tracks the demotion reason specifically.
    pub demoted: usize,
    /// Per-variant breakdown of `Err(EncodingError)` contributions to `errors`.
    /// Strict subset telemetry — does not replace the aggregate counter (#2015).
    pub encoding_errors: EncodingErrorBreakdown,
    /// Functions (or loop invariants) where verification returned vacuous —
    /// the base assertions are contradictory, so the postcondition holds
    /// trivially. Not counted as `verified` because no genuine proof was
    /// produced. Tracked for observability and exit-code computation. (#2663)
    pub vacuous: usize,
    /// Verified-shaped function results that could not be counted as clean
    /// because accepted solver proof evidence was missing or rejected.
    pub evidence_gaps: usize,
}

/// Accumulated counters for proof_assert verification results.
#[derive(Debug, Default)]
pub(super) struct ProofAssertCounters {
    pub verified: usize,
    pub failed: usize,
    pub errors: usize,
    /// proof_assert results demoted by unsoundness demotion pipeline (#2106).
    /// Subset of `errors`.
    pub demoted: usize,
    /// Per-variant breakdown of `Err(EncodingError)` contributions to `errors` (#2015).
    pub encoding_errors: EncodingErrorBreakdown,
    /// proof_assert results in contractless functions where the solver returned
    /// an inconclusive result (Incomplete, Quantifiers, etc.). These are NOT
    /// counted as errors because the function has no contracts to provide
    /// verification context. Tracked for observability. (#2700)
    pub inconclusive: usize,
    /// Verified-shaped proof_assert results without accepted solver proof evidence.
    pub evidence_gaps: usize,
}

/// Structured verification outcome returned by `verify_contracts`.
///
/// Replaces the fire-and-forget `()` return — callers can now inspect
/// verification results programmatically instead of parsing stderr (#1365).
#[derive(Debug, Clone, Default)]
pub struct VerificationSummary {
    /// Number of functions whose contracts were proven correct.
    pub verified: usize,
    /// Number of functions whose contracts were disproven (counterexample found).
    pub failed: usize,
    /// Number of functions where verification encountered errors (encoding, solver timeout, etc.).
    pub errors: usize,
    /// Number of functions skipped (e.g., no MIR body available).
    pub skipped: usize,
    /// Number of trusted functions (contracts assumed correct, not checked).
    pub trusted: usize,
    /// Number of functions whose contracts were assumed correct by the solver
    /// without SMT proof — distinct from `trusted` (`#[trusted]`-annotated
    /// functions skipped by design). See #1891.
    pub assumed: usize,
    /// Number of warnings (e.g., unparseable contract clauses dropped during preparation).
    pub warnings: usize,
    /// Functions verified but depending on unproven axioms (#1878).
    pub verified_with_axiom_deps: usize,
    /// Verified, but on authority only ay itself can re-check. See the field of
    /// the same name on the counters struct.
    pub verified_native_only: usize,
    /// Logic function postconditions that could not be verified. These are
    /// unproven axioms even if no downstream caller depends on them yet.
    pub unverified_axioms: usize,
    /// Number of proof_assert statements verified.
    #[cfg_attr(not(test), allow(dead_code))]
    pub proof_assert_verified: usize,
    /// Number of proof_assert statements that failed.
    pub proof_assert_failed: usize,
    /// Number of proof_assert statements with errors.
    pub proof_assert_errors: usize,
    /// Functions where driver-level processing panicked (#1975).
    pub panics: usize,
    /// Functions whose `Verified` result was demoted to `Unknown` because
    /// encoding approximations fired during their verification (#2106).
    /// These are a subset of `errors` — the `errors` counter includes them
    /// via the normal `Unknown` result path.
    pub demoted: usize,
    /// Per-variant breakdown of `Err(EncodingError)` contributions to `errors` (#2015).
    #[cfg_attr(not(test), allow(dead_code))]
    pub encoding_errors: EncodingErrorBreakdown,
    /// Per-variant breakdown for proof_assert encoding errors (#2015).
    #[cfg_attr(not(test), allow(dead_code))]
    pub proof_assert_encoding_errors: EncodingErrorBreakdown,
    /// Functions where verification was vacuous — the base assertions are
    /// contradictory, so the postcondition holds trivially. Not counted in
    /// `verified`. A vacuous-only crate gives exit code 2 (same treatment
    /// as assumed-only). (#2663)
    pub vacuous: usize,
    /// Verified-shaped results that lacked accepted solver proof evidence.
    pub evidence_gaps: usize,
    /// Contractless proof_asserts the solver could not decide (Incomplete,
    /// Quantifiers, ...). An obligation was examined and no verdict reached,
    /// so this is a soundness gap: fail-closed per the CLI contract, rather
    /// than a silent clean pass. (#143)
    pub proof_assert_inconclusive: usize,
}

impl VerificationSummary {
    /// Convert to a wire-format record for cross-process communication (#1690).
    ///
    /// Maps the in-process summary to a `StructuredVerificationResult` suitable
    /// for emission as a machine-readable line on stderr.
    pub fn to_structured_result(
        &self,
    ) -> trust_wp_core::result_protocol::StructuredVerificationResult {
        trust_wp_core::result_protocol::StructuredVerificationResult {
            base_exit_code: self.exit_code(),
            verified: self.verified as u64,
            failed: self.failed as u64,
            errors: self.errors as u64,
            warnings: self.warnings as u64,
            assumed: self.assumed as u64,
            trusted: self.trusted as u64,
            skipped: self.skipped as u64,
            verified_with_axiom_deps: self.verified_with_axiom_deps as u64,
            verified_native_only: self.verified_native_only as u64,
            unverified_axioms: self.unverified_axioms as u64,
            vacuous: self.vacuous as u64,
            evidence_gaps: self.evidence_gaps as u64,
            proof_assert_inconclusive: self.proof_assert_inconclusive as u64,
            proof_assert_verified: self.proof_assert_verified as u64,
            proof_assert_failed: self.proof_assert_failed as u64,
            proof_assert_errors: self.proof_assert_errors as u64,
            panics: self.panics as u64,
            demoted: self.demoted as u64,
            // Fatal counters live in result_protocol_state, not VerificationSummary.
            // They are overlaid by FatalResultCounters::merge_into at emission
            // time (emit_result_protocol_line in callbacks/mod.rs).
            parse_errors: 0,
            termination_errors: 0,
            logic_recursion_errors: 0,
            erasure_errors: 0,
        }
    }

    /// Build from the internal counter structs.
    pub(super) fn from_counters(
        counters: &VerificationCounters,
        pa_counters: &ProofAssertCounters,
    ) -> Self {
        Self {
            verified: counters.verified,
            failed: counters.failed,
            errors: counters.errors,
            skipped: counters.skipped,
            trusted: counters.trusted,
            assumed: counters.assumed,
            warnings: counters.warnings,
            verified_with_axiom_deps: counters.verified_with_axiom_deps,
            verified_native_only: counters.verified_native_only,
            unverified_axioms: 0,
            proof_assert_verified: pa_counters.verified,
            proof_assert_failed: pa_counters.failed,
            proof_assert_errors: pa_counters.errors,
            proof_assert_inconclusive: pa_counters.inconclusive,
            panics: counters.panics,
            demoted: counters.demoted,
            encoding_errors: counters.encoding_errors,
            proof_assert_encoding_errors: pa_counters.encoding_errors,
            vacuous: counters.vacuous,
            evidence_gaps: counters.evidence_gaps + pa_counters.evidence_gaps,
        }
    }

    /// Determine the verification result protocol exit code.
    ///
    /// Priority: failures > errors > soundness gaps > verified.
    /// A verification failure (counterexample found) is a definitive proof that
    /// code is wrong — it must not be masked by solver errors. Exit code 1
    /// (failure) takes precedence over exit code 2 (error) so that CI pipelines
    /// surface actual bugs over solver issues.
    ///
    /// - 0 = all verified (no failures, no errors, no soundness gaps)
    /// - 1 = at least one verification failure
    /// - 2 = at least one encoding/solver error, trusted/skipped result,
    ///        assumed result, axiom-dependent result, vacuous result, or
    ///        evidence gap (#2663)
    pub fn exit_code(&self) -> i32 {
        let has_failed = self.failed > 0 || self.proof_assert_failed > 0;
        let has_errors = self.errors > 0 || self.proof_assert_errors > 0 || self.panics > 0;

        if has_failed {
            1
        } else if has_errors {
            2
        } else if self.has_soundness_gap() {
            // Any trusted, skipped, assumed, axiom-dependent, vacuous, or
            // evidence-gap result means the crate was not a clean proof.
            // Exit 2 even when other functions verified so true-100 gates
            // cannot hide mixed gaps.
            2
        } else {
            0
        }
    }

    /// Determine the process exit code used by the rustc wrapper.
    ///
    /// `proof_assert` failures stay on the structured result wire via
    /// [`Self::exit_code`], where cargo-trust-wp can aggregate them across all
    /// compiler invocations. The wrapper process itself only exits nonzero for
    /// function-level failures/errors, panics, or soundness gaps that require
    /// the current crate to fail immediately. Trusted/skipped dependency crates
    /// remain non-proofs on the structured wire, but do not abort compilation
    /// before the target crate can be checked.
    pub fn rustc_process_exit_code(&self) -> i32 {
        let has_failed = self.failed > 0;
        let has_errors = self.errors > 0 || self.panics > 0;

        if has_failed {
            1
        } else if has_errors {
            2
        } else if self.has_process_blocking_soundness_gap() {
            2
        } else {
            0
        }
    }

    /// Returns `true` when all non-skipped/non-trusted functions were assumed
    /// rather than proven by the solver. This is a soundness concern: the
    /// crate "verified" only because contracts were assumed, not checked (#1891).
    pub fn is_assumed_only(&self) -> bool {
        self.assumed > 0
            && self.verified == 0
            && self.failed == 0
            && self.errors == 0
            && self.panics == 0
            && self.evidence_gaps == 0
    }

    /// Returns `true` when all non-skipped/non-trusted functions depend on
    /// unproven axioms, with no clean verified results. This is a soundness
    /// concern: verification depends on assumptions that have not been proven
    /// (#2120, #1878).
    pub fn is_axiom_deps_only(&self) -> bool {
        self.verified_with_axiom_deps > 0
            && self.verified == 0
            && self.assumed == 0
            && self.failed == 0
            && self.errors == 0
            && self.panics == 0
            && self.evidence_gaps == 0
    }

    /// Returns `true` when any function result depends on a non-proven
    /// disposition that must not be counted as a true proof.
    pub fn has_soundness_gap(&self) -> bool {
        self.trusted > 0
            || self.skipped > 0
            || self.assumed > 0
            || self.verified_with_axiom_deps > 0
            || self.unverified_axioms > 0
            || self.vacuous > 0
            || self.evidence_gaps > 0
            || self.proof_assert_inconclusive > 0
    }

    fn has_process_blocking_soundness_gap(&self) -> bool {
        self.assumed > 0
            || self.verified_with_axiom_deps > 0
            || self.vacuous > 0
            || self.evidence_gaps > 0
    }
}

/// Format the final verification summary line.
///
/// Produces output like: `trust-wp: 3 verified, 1 failed, 0 errors`
/// with optional parts for assumed functions, skipped functions, unverified
/// axioms, and warnings.
pub(super) fn format_verification_summary(
    counters: &VerificationCounters,
    unverified_axiom_count: usize,
) -> String {
    let mut parts = vec![
        format!("{} verified", counters.verified),
        format!("{} failed", counters.failed),
        format!("{} errors", counters.errors),
    ];
    if counters.assumed > 0 {
        parts.push(format!("{} assumed", counters.assumed));
    }
    if counters.trusted > 0 {
        parts.push(format!("{} trusted", counters.trusted));
    }
    if counters.skipped > 0 {
        parts.push(format!("{} skipped", counters.skipped));
    }
    if counters.verified_with_axiom_deps > 0 {
        parts.push(format!(
            "{} verified* (unproven axiom deps)",
            counters.verified_with_axiom_deps
        ));
    }
    if unverified_axiom_count > 0 {
        parts.push(format!("{unverified_axiom_count} unverified axiom(s)"));
    }
    if counters.demoted > 0 {
        parts.push(format!("{} demoted", counters.demoted));
    }
    if counters.vacuous > 0 {
        parts.push(format!("{} vacuous", counters.vacuous));
    }
    if counters.evidence_gaps > 0 {
        parts.push(format!("{} evidence gaps", counters.evidence_gaps));
    }
    if counters.panics > 0 {
        parts.push(format!("{} panicked", counters.panics));
    }
    if counters.warnings > 0 {
        parts.push(format!("{} warnings", counters.warnings));
    }
    if let Some(suffix) = counters.encoding_errors.format_suffix() {
        parts.push(suffix);
    }
    format!("trust-wp: {}", parts.join(", "))
}

/// Format the proof_assert verification summary line (#2015).
///
/// Produces output like: `trust-wp: proof_assert: 3 verified, 0 failed, 2 errors`
/// with an optional encoding-errors suffix when the breakdown is non-empty.
/// Centralizes the proof-assert summary that previously leaked into
/// `verification.rs` as an inline `eprintln!`.
pub(super) fn format_proof_assert_summary(pa_counters: &ProofAssertCounters) -> String {
    let mut parts = vec![
        format!("{} verified", pa_counters.verified),
        format!("{} failed", pa_counters.failed),
        format!("{} errors", pa_counters.errors),
    ];
    if pa_counters.inconclusive > 0 {
        parts.push(format!("{} inconclusive", pa_counters.inconclusive));
    }
    if pa_counters.evidence_gaps > 0 {
        parts.push(format!("{} evidence gaps", pa_counters.evidence_gaps));
    }
    if let Some(suffix) = pa_counters.encoding_errors.format_suffix() {
        parts.push(suffix);
    }
    format!("trust-wp: proof_assert: {}", parts.join(", "))
}

/// Return a hint message when warnings exist and verbose mode is off.
pub(super) fn dropped_obligation_hint(warning_count: usize, verbose: bool) -> Option<&'static str> {
    if warning_count > 0 && !verbose {
        Some("trust-wp: hint: run with -v for additional warning context")
    } else {
        None
    }
}

/// Format a warning message for recursive functions whose MIR body is unavailable.
pub(super) fn recursive_variant_mir_unavailable_warning(def_path: &str) -> String {
    format!(
        "trust-wp: warning: {def_path} is recursive with variants but MIR body unavailable; variant decrease not checked"
    )
}

/// Report and count an error when MIR is unavailable for recursive variant checking.
pub(super) fn handle_recursive_variant_mir_unavailable(
    def_path: &str,
    loc: &str,
    counters: &mut VerificationCounters,
) {
    counters.errors += 1;
    eprintln!("{}", recursive_variant_mir_unavailable_warning(def_path));
    eprintln!("  at {loc}");
    eprintln!("  termination variant check skipped");
}

/// Whether the function carries an explicit, user-authored `#[requires(false)]`.
///
/// Creusot semantics: a function whose precondition is the literal `false` is
/// provably uncallable, so every obligation inside it (the function contract,
/// loop init/post invariants, and any `proof_assert!`) is vacuously discharged
/// and must be CREDITED, not flagged as a soundness gap. This mirrors Creusot's
/// own treatment (e.g. `specification/erasure.rs` uses `#[requires(false)]` as
/// deliberate "don't care about proofs" scaffolding).
///
/// Soundness: the discriminating signal is a LITERAL `false` that appears in the
/// raw, user-written `#[requires(...)]` clause text (`FunctionContract.requires`,
/// a `Vec<String>` populated directly from the source attribute). It is keyed to
/// the PRECONDITION position only:
///   - It does NOT credit `#[ensures(false)]` (a postcondition — accepting that
///     would be a real false-accept, guarded against at the vacuous branch).
///   - It does NOT credit accidental/derived UNSAT bases (synthesized
///     path-conditions never appear in the source `requires` clause vector).
/// We re-parse the raw clause text so that `false`, `(false)`, etc. are matched
/// robustly while anything that is not literally the boolean `false` is rejected.
pub(in crate::callbacks) fn user_authored_requires_false(contract: &FunctionContract) -> bool {
    contract.requires.iter().any(|clause| {
        matches!(
            trust_wp_core::contract_parser::parse_contract(clause),
            Ok(trust_wp_core::formula::PureExpr::Bool(false))
        )
    })
}

/// Per-function context for result reporting (#2657).
///
/// Bundles the function identity and diagnostic fields that are constant
/// across a single verification result dispatch, keeping
/// `report_function_verification_result` under clippy's argument threshold.
pub(super) struct FunctionReportContext<'a> {
    pub(super) def_path: &'a str,
    pub(super) loc: &'a str,
    pub(super) contract: &'a FunctionContract,
    pub(super) parsed: &'a ParsedContract,
    pub(super) source_map: &'a rustc_span::source_map::SourceMap,
}

/// Dispatch a function verification result to counters and report to stderr.
///
/// Returns `true` if the function was verified successfully (used by callers
/// to decide whether to proceed with trait refinement checks).
pub(super) fn report_function_verification_result(
    result: Result<VerificationOutcome, EncodingError>,
    fn_ctx: &FunctionReportContext<'_>,
    logic_fns_opt: Option<&[LogicFnDef]>,
    unverified_axioms: &HashSet<String>,
    counters: &mut VerificationCounters,
) -> bool {
    let def_path = fn_ctx.def_path;
    let loc = fn_ctx.loc;
    let contract = fn_ctx.contract;
    let parsed = fn_ctx.parsed;
    let source_map = fn_ctx.source_map;
    match result {
        Ok(outcome) => {
            emit_verification_diagnostic_if_requested(def_path, "function_contract", &outcome);
            let evidence_gap_reason = verified_evidence_gap_reason(&outcome);
            match outcome.result {
                VerificationResult::Verified(ref certificate) => {
                    if let Some(reason) = evidence_gap_reason {
                        counters.evidence_gaps += 1;
                        counters.warnings += 1;
                        eprintln!("trust-wp: {def_path} evidence gap ({reason})");
                        eprintln!("  at {loc}");
                        return false;
                    }
                    // Report if this verified function depends on unverified axioms (#1490).
                    let deps: Vec<&str> = logic_fns_opt
                        .unwrap_or(&[])
                        .iter()
                        .filter(|lf| unverified_axioms.contains(lf.full_path()))
                        .map(|lf| lf.full_path())
                        .collect();
                    if deps.is_empty() {
                        counters.verified += 1;
                        // A proof ay validated fully but cannot render into the
                        // pinned Alethe calculus is still a proof — it is just
                        // one only ay can re-check. Counted alongside
                        // `verified`, never instead of it.
                        if verified_on_native_only_authority(certificate.as_ref()) {
                            counters.verified_native_only += 1;
                        }
                        eprintln!("trust-wp: {def_path} verified \u{2713}");
                    } else {
                        // Do not count as unconditionally verified (#1878).
                        counters.verified_with_axiom_deps += 1;
                        eprintln!(
                            "trust-wp: {def_path} verified* (depends on {} unverified axiom(s))",
                            deps.len()
                        );
                        for dep in &deps {
                            eprintln!("  unverified axiom: {dep}");
                        }
                    }
                    true
                }
                VerificationResult::Failed(counterexample) => {
                    counters.failed += 1;
                    // Phase 8a: differentiate the FAILED header by obligation
                    // kind. The solver_tail and function-level prechecks tag
                    // `Counterexample.violated_postcondition` for ensures
                    // slices; absence means a non-postcondition obligation
                    // (e.g., loop invariant, type invariant, division-by-zero).
                    let header_kind = if counterexample.violated_postcondition.is_some() {
                        " (postcondition)"
                    } else {
                        ""
                    };
                    eprintln!("trust-wp: {def_path} FAILED \u{2717}{header_kind}");

                    // Show body span if available (Phase 2 source location tracking)
                    if let Some(ref spanned) = parsed.result_expr_spanned {
                        if let Some(body_span) = spanned.span {
                            let body_loc = source_map.span_to_diagnostic_string(body_span);
                            eprintln!("  return expression at {body_loc}");
                        } else {
                            eprintln!("  at {loc}");
                        }
                    } else {
                        eprintln!("  at {loc}");
                    }

                    // Phase 8a: surface the *specific* violated clause when the
                    // solver_tail tagged it. Fall back to listing all ensures
                    // clauses only when no clause was tagged (e.g.,
                    // non-postcondition failures like loop invariants).
                    if let Some(info) = counterexample.violated_postcondition.as_ref() {
                        eprintln!(
                            "  violated ensures #{}: {}",
                            info.clause_idx, info.contract_text,
                        );
                    } else if !contract.ensures.is_empty() {
                        eprintln!("  postcondition(s):");
                        for ens in &contract.ensures {
                            eprintln!("    ensures: {ens}");
                        }
                    }

                    // Display counterexample using rich origin info
                    report_counterexample(&counterexample);
                    false
                }
                VerificationResult::Assumed(reason) => {
                    counters.assumed += 1;
                    eprintln!("trust-wp: {def_path} assumed ({reason})");
                    eprintln!("  at {loc}");
                    false
                }
                VerificationResult::Unknown(ref reason) => {
                    // Vacuous proofs (base assertions contradictory without the
                    // negated postcondition) indicate the preconditions are
                    // inconsistent — the postcondition holds trivially, not because
                    // the implementation is correct. This is NOT a genuine
                    // verification: counting vacuous results as "verified" causes
                    // false-accepts (e.g., #[ensures(false)] on recursive logic
                    // functions passes verification). (#2663)
                    //
                    // Report as a warning but do NOT count as verified. The
                    // function's verification status remains inconclusive.
                    let is_vacuous = matches!(
                        reason,
                        trust_wp_ay::UnknownReason::SolverMessage(msg) if msg.contains("vacuous proof")
                    );
                    if is_vacuous {
                        // An explicit user-authored `#[requires(false)]` makes the
                        // function provably uncallable: its obligations are
                        // vacuously discharged by Creusot semantics and must be
                        // credited, not flagged as a soundness gap. This is keyed
                        // to the PRECONDITION position only, so `#[ensures(false)]`
                        // (a postcondition) is NOT credited here — it still falls
                        // through to the vacuous/soundness-gap path below.
                        if user_authored_requires_false(contract) {
                            counters.verified += 1;
                            eprintln!(
                                "trust-wp: {def_path} verified \u{2713} (vacuous: explicit #[requires(false)])"
                            );
                            eprintln!("  at {loc}");
                            return true;
                        }
                        counters.vacuous += 1;
                        counters.warnings += 1;
                        eprintln!("trust-wp: {def_path} vacuous (contradictory premises)");
                        eprintln!("  at {loc}");
                        return false;
                    }
                    counters.errors += 1;
                    // Track demotions separately: when the demotion pipeline
                    // converts Verified→Unknown due to encoding approximations,
                    // the reason starts with "demoted:" (#2106).
                    let is_demoted = matches!(reason, trust_wp_ay::UnknownReason::Demoted(_));
                    if is_demoted {
                        counters.demoted += 1;
                    }
                    eprintln!("trust-wp: {def_path} unknown ({reason})");
                    eprintln!("  at {loc}");
                    false
                }
                // VerificationResult is #[non_exhaustive]; required for cross-crate match.
                #[allow(unreachable_patterns)]
                _ => {
                    counters.errors += 1;
                    false
                }
            }
        }
        Err(ref e) => {
            counters.errors += 1;
            counters.encoding_errors.record(e);
            eprintln!("trust-wp: {def_path} error: {e}");
            eprintln!("  at {loc}");
            false
        }
    }
}

pub(in crate::callbacks) fn emit_verification_diagnostic_if_requested(
    def_path: &str,
    obligation_kind: &str,
    outcome: &VerificationOutcome,
) {
    if std::env::var(trust_wp_core::result_protocol::RESULT_PROTOCOL_ENV).is_err() {
        return;
    }
    if !should_emit_verification_diagnostic(outcome) {
        return;
    }
    // When the outer hard-timeout kills the ay worker mid-solve, the loop-phase
    // outcome is built via `VerificationOutcome::without_provenance(Unknown(Timeout))`
    // and carries no provenance. Without the synthesized fallback below we would
    // suppress the per-phase diagnostic and reduce the failure mode to "unknown
    // (loop invariant: timeout)" with no breadcrumbs (Fix B in
    // designs/2026-05-19-100doors-vec-sort-leakage.md).
    eprintln!(
        "{}",
        verification_diagnostic_wire_line(
            def_path,
            obligation_kind,
            outcome,
            outcome.provenance.as_ref(),
        )
    );
}

fn should_emit_verification_diagnostic(outcome: &VerificationOutcome) -> bool {
    if matches!(
        outcome.result,
        VerificationResult::Failed(_) | VerificationResult::Unknown(_)
    ) {
        return true;
    }
    if verified_evidence_gap_reason(outcome).is_some() {
        return true;
    }
    outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .is_some_and(|evidence| !evidence.accepted_for_consumer)
}

/// True when an outcome is an `Unknown(Timeout)` lacking solver provenance.
///
/// This happens when the outer hard-timeout (#2457) abandons the ay worker
/// mid-solve and the caller constructs the outcome via
/// `VerificationOutcome::without_provenance(Unknown(Timeout))`. The wire-line
/// builder uses this to override `ay_result=timeout` and other synthesized
/// fields so loop-phase diagnostics remain visible.
fn is_unknown_timeout_without_provenance(outcome: &VerificationOutcome) -> bool {
    outcome.provenance.is_none()
        && matches!(
            outcome.result,
            VerificationResult::Unknown(UnknownReason::Timeout)
        )
}

pub(in crate::callbacks) fn verified_evidence_gap_reason(
    outcome: &VerificationOutcome,
) -> Option<String> {
    if !matches!(outcome.result, VerificationResult::Verified(_)) {
        return None;
    }

    let Some(provenance) = outcome.provenance.as_ref() else {
        return Some("missing solver provenance".to_string());
    };
    let Some(evidence) = provenance.solve_evidence.as_ref() else {
        return Some("missing solver evidence".to_string());
    };
    if !evidence.accepted_for_consumer {
        return Some(
            evidence
                .consumer_rejection
                .clone()
                .unwrap_or_else(|| "solver evidence rejected by consumer".to_string()),
        );
    }
    if !solve_evidence_is_unsat(&evidence.result) {
        return Some(format!(
            "accepted solver evidence was {}, not verified proof evidence",
            evidence.result
        ));
    }
    let Some(statistics) = provenance.solver_statistics.as_ref() else {
        return Some("missing proof-checker statistics".to_string());
    };
    if let Some(failed) = unsat_proof_authority_gap(evidence, statistics) {
        return Some(format!(
            "solver evidence failed mandatory proof-authority checks ({failed})"
        ));
    }
    match &outcome.result {
        VerificationResult::Verified(Some(summary)) if summary.is_fully_verified() => {}
        VerificationResult::Verified(Some(_)) => {
            return Some("proof certificate failed mandatory strict replay".to_string());
        }
        VerificationResult::Verified(None) => {
            return Some("missing proof certificate summary".to_string());
        }
        _ => unreachable!("verified result checked above"),
    }
    None
}

/// Name the FIRST mandatory proof-authority field that the evidence/statistics
/// pair fails, or `None` when the pair carries a complete, strictly checked
/// UNSAT proof.
///
/// The predicate is unchanged from the boolean form it replaces; only the
/// diagnostic is richer. Naming the field matters because the two halves of
/// this pair are captured separately (`solve_evidence` and `solver_statistics`
/// on the same [`VerificationProvenance`]) and a mismatched pair is the exact
/// rot this reports: an authoritative evidence snapshot paired with placeholder
/// statistics reads as "unsat + ProofChecked + no proof steps", which must be
/// refused but is impossible to triage from a bare "checks failed" string.
fn unsat_proof_authority_gap(
    evidence: &SolveEvidenceSnapshot,
    statistics: &SolveStatisticsSnapshot,
) -> Option<&'static str> {
    let extra = |key: &str| {
        statistics
            .extra_ints
            .iter()
            .find_map(|(candidate, value)| (candidate == key).then_some(*value))
    };

    if !evidence.accepted_for_consumer {
        return Some("evidence not accepted for consumer");
    }
    if !solve_evidence_is_unsat(&evidence.result) {
        return Some("evidence result is not unsat");
    }
    if !matches!(
        evidence.verification_level,
        SolveVerificationLevelSnapshot::ProofChecked
            | SolveVerificationLevelSnapshot::FullyVerified
    ) {
        return Some("verification level lacks proof checking");
    }
    if !evidence.verification.unsat_proof_available {
        return Some("no unsat proof artifact");
    }
    if evidence.verification.unsat_proof_checker_failures != 0 {
        return Some("summary reports proof-checker failures");
    }
    if !statistics.proof_complete {
        return Some("statistics.proof_complete is false");
    }
    if extra("proof_checker_failures") != Some(0) {
        return Some("statistics lack proof_checker_failures=0");
    }
    if extra("proof_trust") != Some(0) {
        return Some("statistics lack proof_trust=0");
    }
    if !matches!(
        (
            extra("proof_checker_checked_steps"),
            extra("proof_checker_total_steps")
        ),
        (Some(checked), Some(total)) if total > 0 && checked == total
    ) {
        return Some("statistics lack checked_steps == total_steps > 0");
    }
    if extra("proof_checker_skipped_hole_steps") != Some(0) {
        return Some("statistics lack proof_checker_skipped_hole_steps=0");
    }
    None
}

fn solve_evidence_is_unsat(result: &str) -> bool {
    result.eq_ignore_ascii_case("unsat")
        || result
            .strip_prefix("Unsat")
            .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('('))
}

fn verification_diagnostic_wire_line(
    def_path: &str,
    obligation_kind: &str,
    outcome: &VerificationOutcome,
    provenance: Option<&VerificationProvenance>,
) -> String {
    let evidence = provenance.and_then(|p| p.solve_evidence.as_ref());
    let replay = provenance.and_then(|p| p.replay_artifact.as_deref());
    let replay_sha256 =
        replay.map_or_else(|| "none".to_string(), |text| sha256_hex(text.as_bytes()));
    let native_replay = provenance.and_then(|p| p.native_replay_json.as_deref());
    let native_replay_sha256 =
        native_replay.map_or_else(|| "none".to_string(), |json| sha256_hex(json.as_bytes()));
    let (native_replay_path, native_replay_write_error) = native_replay.map_or_else(
        || ("none".to_string(), "none".to_string()),
        |json| write_native_replay_artifact(def_path, &native_replay_sha256, json),
    );
    let reason = match &outcome.result {
        VerificationResult::Unknown(reason) => reason.to_string(),
        VerificationResult::Assumed(reason) => reason.clone(),
        VerificationResult::Failed(_) => "counterexample".to_string(),
        VerificationResult::Verified(_) => "none".to_string(),
        #[allow(unreachable_patterns)]
        _ => "unknown-result".to_string(),
    };
    let timeout = provenance
        .and_then(|p| p.solver_timeout_ms)
        .map_or_else(|| "none".to_string(), |timeout_ms| timeout_ms.to_string());
    // When the worker was killed by an outer hard-timeout we have no
    // SolveEvidenceSnapshot, but the outcome itself records the timeout. Surface
    // it as `ay_result=timeout` so loop-phase diagnostics stay self-describing
    // even when provenance is missing (Fix B in
    // designs/2026-05-19-100doors-vec-sort-leakage.md).
    let synthetic_timeout = is_unknown_timeout_without_provenance(outcome);
    let ay_result_owned = if synthetic_timeout {
        Some("timeout".to_string())
    } else {
        evidence.map(|evidence| evidence.result.clone())
    };
    let ay_result = ay_result_owned.as_deref().unwrap_or("none");
    let accepted = if synthetic_timeout {
        "false".to_string()
    } else {
        evidence.map_or("unknown".to_string(), |evidence| {
            evidence.accepted_for_consumer.to_string()
        })
    };
    let model_validated = if synthetic_timeout {
        "false".to_string()
    } else {
        evidence.map_or("unknown".to_string(), |evidence| {
            evidence.model_validated.to_string()
        })
    };
    let unsat_proof_available = if synthetic_timeout {
        "false".to_string()
    } else {
        evidence.map_or("unknown".to_string(), |evidence| {
            evidence.verification.unsat_proof_available.to_string()
        })
    };
    let verification_level = evidence.map_or_else(
        || "none".to_string(),
        |evidence| format!("{:?}", evidence.verification_level),
    );
    let solve_time_ms = provenance.map_or(0, |p| p.solve_time.as_millis());
    let assertions = provenance.map_or(0, |p| p.assertion_count);
    format!(
        "{} def_path={} kind={} status={} reason={} solve_time_ms={} assertions={} timeout_ms={} \
         ay_result={} accepted_for_consumer={} model_validated={} unsat_proof_available={} \
         verification_level={} replay_present={} replay_bytes={} replay_sha256={} \
         native_replay_present={} native_replay_bytes={} native_replay_sha256={} \
         native_replay_schema={} native_replay_path={} native_replay_write_error={}",
        trust_wp_core::result_protocol::DIAGNOSTIC_WIRE_PREFIX,
        encode_wire_value(def_path),
        encode_wire_value(obligation_kind),
        verification_status(&outcome.result),
        encode_wire_value(&reason),
        solve_time_ms,
        assertions,
        timeout,
        encode_wire_value(ay_result),
        accepted,
        model_validated,
        unsat_proof_available,
        encode_wire_value(&verification_level),
        replay.is_some(),
        replay.map_or(0, str::len),
        replay_sha256,
        native_replay.is_some(),
        native_replay.map_or(0, str::len),
        native_replay_sha256,
        encode_wire_value(if native_replay.is_some() {
            NATIVE_REPLAY_SCHEMA
        } else {
            "none"
        }),
        encode_wire_value(&native_replay_path),
        encode_wire_value(&native_replay_write_error),
    )
}

fn verification_status(result: &VerificationResult) -> &'static str {
    match result {
        VerificationResult::Verified(_) => "verified",
        VerificationResult::Failed(_) => "failed",
        VerificationResult::Assumed(_) => "assumed",
        VerificationResult::Unknown(_) => "unknown",
        #[allow(unreachable_patterns)]
        _ => "other",
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn write_native_replay_artifact(def_path: &str, sha256: &str, json: &str) -> (String, String) {
    let Some(dir) = std::env::var_os(NATIVE_REPLAY_DIR_ENV).filter(|value| !value.is_empty())
    else {
        return ("none".to_string(), "none".to_string());
    };
    let dir = PathBuf::from(dir);
    if let Err(err) = fs::create_dir_all(&dir) {
        return ("none".to_string(), err.to_string());
    }
    let filename = format!(
        "{}-{}.ay-native-replay.json",
        sanitize_artifact_filename(def_path),
        &sha256[..sha256.len().min(16)]
    );
    let path = dir.join(filename);
    match fs::write(&path, json) {
        Ok(()) => (path.display().to_string(), "none".to_string()),
        Err(err) => ("none".to_string(), err.to_string()),
    }
}

fn sanitize_artifact_filename(def_path: &str) -> String {
    let mut sanitized = String::with_capacity(def_path.len().min(80));
    for ch in def_path.chars() {
        if ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_' | '.') {
            sanitized.push(ch);
        } else if matches!(
            ch,
            ':' | '/' | '\\' | ' ' | '<' | '>' | '(' | ')' | '[' | ']'
        ) {
            sanitized.push('_');
        }
        if sanitized.len() >= 80 {
            break;
        }
    }
    while sanitized.ends_with('_') || sanitized.ends_with('.') {
        sanitized.pop();
    }
    if sanitized.is_empty() {
        "obligation".to_string()
    } else {
        sanitized
    }
}

fn proof_assert_prepared_claim_hash(ordinal: u64, prepared_claim: &str) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.proof-assert-prepared-claim.v1\0");
    hasher.update(ordinal.to_be_bytes());
    hasher.update(prepared_claim.as_bytes());
    hasher.finalize().into()
}

fn proof_assert_normalized_claim_hash(ordinal: u64, normalized_claim: &str) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.proof-assert-slice-claim.v1\0");
    hasher.update(ordinal.to_be_bytes());
    hasher.update(normalized_claim.as_bytes());
    hasher.finalize().into()
}

fn proof_assert_native_problem_hash(native_problem_json: &str) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.proof-assert-native-problem.v1\0");
    hasher.update(native_problem_json.as_bytes());
    hasher.finalize().into()
}

fn proof_assert_certificate_set_hash(certificates: &[ProofAssertSliceCertificate]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.proof-assert-certificate-set.v1\0");
    hasher.update(
        u64::try_from(certificates.len())
            .unwrap_or(u64::MAX)
            .to_be_bytes(),
    );
    for certificate in certificates {
        hasher.update(certificate.ordinal.to_be_bytes());
        hasher.update(certificate.derivation.certificate_hash_tag());
        hasher.update(certificate.prepared_claim_hash);
        hasher.update(certificate.normalized_claim_hash);
        hasher.update(certificate.problem_hash);
    }
    hasher.finalize().into()
}

fn proof_assert_snapshot_has_complete_unsat_proof(
    evidence: &SolveEvidenceSnapshot,
    statistics: &SolveStatisticsSnapshot,
) -> bool {
    let extra = |key: &str| {
        statistics
            .extra_ints
            .iter()
            .find_map(|(candidate, value)| (candidate == key).then_some(*value))
    };
    solve_evidence_is_unsat(&evidence.result)
        && evidence.accepted_for_consumer
        && matches!(
            evidence.verification_level,
            SolveVerificationLevelSnapshot::ProofChecked
                | SolveVerificationLevelSnapshot::FullyVerified
        )
        && evidence.verification.unsat_proof_available
        && evidence.verification.unsat_proof_checker_failures == 0
        && statistics.proof_complete
        && extra("proof_checker_failures") == Some(0)
        && extra("proof_trust") == Some(0)
        && matches!(
            (
                extra("proof_checker_checked_steps"),
                extra("proof_checker_total_steps")
            ),
            (Some(checked), Some(total)) if total > 0 && checked == total
        )
        && extra("proof_checker_skipped_hole_steps") == Some(0)
}

/// Whether this verified obligation's proof is one only ay can re-check.
///
/// True only when the proof was rendered AND the rendering contains a step the
/// pinned Alethe calculus cannot express. An absent rendering answers nothing —
/// it is reported as `false` here so the counter never overstates, which means
/// the counter is a floor: every obligation it counts genuinely lacks an
/// externally replayable proof, but a producer that renders no proof at all
/// contributes zero rather than an honest "unknown". Widening that would need a
/// tri-state on the wire, which the protocol does not have today.
fn verified_on_native_only_authority(
    certificate: Option<&trust_wp_ay::ProofCertificateSummary>,
) -> bool {
    certificate
        .and_then(|summary| summary.alethe_text.as_deref())
        .is_some_and(|text| {
            !trust_wp_core::result_protocol::alethe_proof_is_externally_checkable(text)
        })
}

fn canonical_proof_assert_evidence(mut evidence: SolveEvidenceSnapshot) -> SolveEvidenceSnapshot {
    // Process RSS and elapsed wall time are observations of the checker run,
    // not proof semantics. Every other field remains exact.
    evidence.resource_usage.rss_bytes = 0;
    evidence.resource_usage.wall_time_ms = 0;
    evidence
}

fn canonical_proof_assert_statistics(
    mut statistics: SolveStatisticsSnapshot,
) -> SolveStatisticsSnapshot {
    statistics.extra_ints.retain(|(key, _)| {
        let key = key.to_ascii_lowercase();
        // Volatile observations of the RUN, not of the proof: wall time,
        // memory, and (ay >= 0.10, ay 550e5792b7) the `cert.*`
        // certification-accounting family. ay publishes those counters from a
        // PROCESS-GLOBAL accumulator into every solve's statistics
        // (`executor/proof/check.rs` `publish_certification_accounting`;
        // `executor/cert_accounting.rs` documents them as write-only —
        // "Nothing in ay-dpll reads a counter to decide anything"). A
        // process-cumulative counter can never agree between the certificate's
        // solve and the report-time strict replay, so keeping them made this
        // canonical comparison unsatisfiable and demoted every proof_assert
        // to an evidence gap. Proof-semantic statistics (proof_checker_*,
        // proof_trust, core counters) remain compared exactly.
        !key.contains("time")
            && !key.contains("elapsed")
            && !key.contains("duration")
            && !key.contains("memory")
            && !key.contains("rss")
            && !key.contains("nanos")
            && !key.starts_with("cert.")
    });
    statistics.extra_ints.sort_unstable();
    statistics
}

fn proof_assert_slice_certificate_gap_reason(
    certificate: &ProofAssertSliceCertificate,
    expected_ordinal: u64,
    expected_prepared_claim: &str,
    expected_derivation: ProofAssertSliceDerivation,
) -> Option<String> {
    if certificate.ordinal != expected_ordinal {
        return Some(format!(
            "certificate ordinal mismatch: expected {expected_ordinal}, got {}",
            certificate.ordinal
        ));
    }
    if certificate.derivation != expected_derivation {
        return Some(format!(
            "certificate derivation mismatch at ordinal {expected_ordinal}: expected \
             {expected_derivation:?}, got {:?}",
            certificate.derivation,
        ));
    }
    if certificate.prepared_claim != expected_prepared_claim {
        return Some(format!(
            "certificate source claim mismatch at ordinal {expected_ordinal}"
        ));
    }
    let expected_prepared_hash =
        proof_assert_prepared_claim_hash(expected_ordinal, expected_prepared_claim);
    if certificate.prepared_claim_hash != expected_prepared_hash {
        return Some(format!(
            "certificate source claim hash mismatch at ordinal {expected_ordinal}"
        ));
    }
    let expected_normalized_hash =
        proof_assert_normalized_claim_hash(expected_ordinal, &certificate.normalized_claim);
    if certificate.normalized_claim_hash != expected_normalized_hash {
        return Some(format!(
            "certificate normalized claim hash mismatch at ordinal {expected_ordinal}"
        ));
    }
    if certificate.problem_hash
        != proof_assert_native_problem_hash(&certificate.native_problem_json)
    {
        return Some(format!(
            "certificate native problem hash mismatch at ordinal {expected_ordinal}"
        ));
    }

    let artifact =
        match ay_dpll::api::NativeReplayArtifact::from_json_str(&certificate.native_problem_json) {
            Ok(artifact) => artifact,
            Err(error) => {
                return Some(format!(
                    "certificate native replay parse failed at ordinal {expected_ordinal}: {error}"
                ));
            }
        };
    if artifact.to_pretty_json() != certificate.native_problem_json {
        return Some(format!(
            "certificate native replay is not canonical at ordinal {expected_ordinal}"
        ));
    }
    if artifact.schema != NATIVE_REPLAY_SCHEMA
        || artifact.created_unix_ms != 0
        || artifact.solve.is_some()
        || artifact.checked_replay.is_some()
        || artifact.panic_payload.is_some()
        || !artifact.unsupported_atoms.is_empty()
        || !artifact.replay_gaps.is_empty()
    {
        return Some(format!(
            "certificate native replay envelope is not authority-grade at ordinal \
             {expected_ordinal}: schema={}, created_unix_ms={}, solve={}, checked={}, panic={}, \
             unsupported_atoms={}, replay_gaps={:?}",
            artifact.schema,
            artifact.created_unix_ms,
            artifact.solve.is_some(),
            artifact.checked_replay.is_some(),
            artifact.panic_payload.is_some(),
            artifact.unsupported_atoms.len(),
            artifact.replay_gaps,
        ));
    }
    let expected_metadata = proof_assert_native_replay_metadata(
        expected_ordinal,
        expected_prepared_hash,
        expected_normalized_hash,
    );
    if artifact.metadata != expected_metadata {
        return Some(format!(
            "certificate native replay claim binding mismatch at ordinal {expected_ordinal}"
        ));
    }
    let timeout_ms = match artifact.timeout_ms {
        Some(timeout_ms) if (1..=PROOF_ASSERT_REPLAY_TIMEOUT_MAX_MS).contains(&timeout_ms) => {
            timeout_ms
        }
        _ => {
            return Some(format!(
                "certificate native replay timeout is unbounded or invalid at ordinal \
                 {expected_ordinal}"
            ));
        }
    };
    let timeout = Duration::from_millis(u64::try_from(timeout_ms).unwrap_or(u64::MAX));
    let replay =
        match ay_dpll::api::Solver::replay_native_replay_artifact_with_proofs(&artifact, timeout) {
            Ok(replay) => replay,
            Err(error) => {
                return Some(format!(
                "certificate strict native replay failed at ordinal {expected_ordinal}: {error}"
            ));
            }
        };
    let replay_evidence = SolveEvidenceSnapshot::from_solve_details(&replay);
    let replay_statistics = SolveStatisticsSnapshot::from(&replay.statistics);
    if !proof_assert_snapshot_has_complete_unsat_proof(&replay_evidence, &replay_statistics) {
        return Some(format!(
            "certificate strict native replay lacked complete checked UNSAT authority at \
             ordinal {expected_ordinal}"
        ));
    }
    if canonical_proof_assert_evidence(certificate.solve_evidence.clone())
        != canonical_proof_assert_evidence(replay_evidence)
    {
        return Some(format!(
            "certificate solve evidence disagreed with strict replay at ordinal \
             {expected_ordinal}"
        ));
    }
    if canonical_proof_assert_statistics(certificate.solver_statistics.clone())
        != canonical_proof_assert_statistics(replay_statistics)
    {
        return Some(format!(
            "certificate solver statistics disagreed with strict replay at ordinal \
             {expected_ordinal}"
        ));
    }
    None
}

fn proof_assert_authority_gap_reason(
    outcome: &VerificationOutcome,
    prepared: &super::proof_assert_verify::PreparedAssertion,
) -> Option<String> {
    if !matches!(outcome.result, VerificationResult::Verified(_)) {
        return None;
    }
    let Some(provenance) = outcome.provenance.as_ref() else {
        return Some("missing proof_assert solver provenance".to_string());
    };
    let expected_claims = proof_assert_obligation_slice_claims(&prepared.ensures);
    let expected_derivations =
        proof_assert_obligation_slice_derivations(&prepared.ensures, &prepared.preconditions);
    if expected_derivations.len() != expected_claims.len() {
        return Some("proof_assert derivation/claim count mismatch".to_string());
    }
    let certificates = &provenance.proof_assert_slice_certificates;
    if certificates.len() != expected_claims.len() {
        return Some(format!(
            "proof_assert certificate count mismatch: expected {}, got {}",
            expected_claims.len(),
            certificates.len()
        ));
    }
    if certificates.is_empty() {
        return Some("proof_assert produced no obligation-slice certificates".to_string());
    }
    for (index, ((certificate, expected_claim), expected_derivation)) in certificates
        .iter()
        .zip(expected_claims.iter())
        .zip(expected_derivations.iter())
        .enumerate()
    {
        let ordinal = u64::try_from(index).unwrap_or(u64::MAX);
        if let Some(reason) = proof_assert_slice_certificate_gap_reason(
            certificate,
            ordinal,
            expected_claim,
            *expected_derivation,
        ) {
            return Some(reason);
        }
    }
    if provenance.vc_hash != proof_assert_certificate_set_hash(certificates) {
        return Some("proof_assert certificate-set hash mismatch".to_string());
    }
    let last = certificates
        .last()
        .expect("non-empty proof_assert certificate set checked above");
    if provenance.solve_evidence.as_ref() != Some(&last.solve_evidence)
        || provenance.solver_statistics.as_ref() != Some(&last.solver_statistics)
        || provenance.native_replay_json.as_deref() != Some(last.native_problem_json.as_str())
    {
        return Some("proof_assert aggregate provenance is not the final slice".to_string());
    }
    None
}

/// Dispatch a proof_assert verification result to counters and report to stderr.
pub(super) fn report_proof_assert_result(
    result: Result<VerificationResult, EncodingError>,
    prepared: &super::proof_assert_verify::PreparedAssertion,
    pa_counters: &mut ProofAssertCounters,
) {
    report_proof_assert_outcome_result(
        result.map(VerificationOutcome::without_provenance),
        prepared,
        pa_counters,
    );
}

/// Dispatch a provenance-preserving proof_assert verification outcome.
pub(super) fn report_proof_assert_outcome_result(
    result: Result<VerificationOutcome, EncodingError>,
    prepared: &super::proof_assert_verify::PreparedAssertion,
    pa_counters: &mut ProofAssertCounters,
) {
    match result {
        Ok(outcome) => {
            // A Verified-shaped outcome is not diagnostic authority. Replay and
            // validate every exact slice certificate before emitting any
            // success-adjacent diagnostic or incrementing the verified count.
            if let Some(reason) = proof_assert_authority_gap_reason(&outcome, prepared)
                .or_else(|| verified_evidence_gap_reason(&outcome))
            {
                pa_counters.errors += 1;
                pa_counters.evidence_gaps += 1;
                eprintln!(
                    "trust-wp: proof_assert in {} evidence gap ({reason})",
                    prepared.fn_path
                );
                eprintln!("  at {}", prepared.loc);
                return;
            }
            emit_verification_diagnostic_if_requested(&prepared.fn_path, "proof_assert", &outcome);
            report_proof_assert_verification_result(outcome.result, prepared, pa_counters);
        }
        Err(ref e) => {
            pa_counters.errors += 1;
            pa_counters.encoding_errors.record(e);
            eprintln!("trust-wp: proof_assert in {} error: {e}", prepared.fn_path);
            eprintln!("  at {}", prepared.loc);
        }
    }
}

fn report_proof_assert_verification_result(
    result: VerificationResult,
    prepared: &super::proof_assert_verify::PreparedAssertion,
    pa_counters: &mut ProofAssertCounters,
) {
    match result {
        VerificationResult::Verified(_) => {
            pa_counters.verified += 1;
            eprintln!(
                "trust-wp: proof_assert in {} verified \u{2713}",
                prepared.fn_path
            );
            debug!(loc = %prepared.loc, "proof_assert verified location");
        }
        VerificationResult::Failed(ce) => {
            pa_counters.failed += 1;
            eprintln!(
                "trust-wp: proof_assert in {} FAILED \u{2717}",
                prepared.fn_path
            );
            eprintln!("  at {}", prepared.loc);
            eprintln!("  assertion: {}", prepared.expr_text);
            if prepared.is_contractless {
                eprintln!("  hint: function has no contracts — preconditions may be missing");
            }
            report_counterexample(&ce);
        }
        VerificationResult::Assumed(reason) => {
            // proof_assert should not produce Assumed — counting as error,
            // not verified, since the assertion was not actually proven (#1891).
            pa_counters.errors += 1;
            eprintln!(
                "trust-wp: proof_assert in {} assumed ({reason}) — counted as error",
                prepared.fn_path
            );
            eprintln!("  at {}", prepared.loc);
        }
        VerificationResult::Unknown(ref reason) => {
            // A `proof_assert!` inside a function with an explicit user-authored
            // `#[requires(false)]` is unreachable code: the function is provably
            // uncallable, so the assertion is vacuously discharged by Creusot
            // semantics and must be accepted (not counted as an error). Keyed to
            // the PRECONDITION position only — `#[ensures(false)]` does not set
            // this flag, so a vacuous proof_assert from a false postcondition is
            // still rejected below.
            let is_vacuous = matches!(
                reason,
                UnknownReason::SolverMessage(msg) if msg.contains("vacuous proof")
            );
            if prepared.containing_requires_false && is_vacuous {
                pa_counters.verified += 1;
                eprintln!(
                    "trust-wp: proof_assert in {} verified \u{2713} (vacuous: explicit #[requires(false)])",
                    prepared.fn_path
                );
                eprintln!("  at {}", prepared.loc);
                return;
            }
            // Unknown proof_assert results, including vacuous solver messages,
            // are not genuine proofs and must not inflate the verified count.
            if prepared.is_contractless && is_contractless_proof_assert_inconclusive(reason) {
                pa_counters.inconclusive += 1;
                eprintln!(
                    "trust-wp: proof_assert in {} inconclusive ({reason}) — function has no contracts",
                    prepared.fn_path
                );
                eprintln!("  at {}", prepared.loc);
                eprintln!(
                    "  hint: add #[requires] / #[ensures] contracts to provide verification context"
                );
                return;
            }
            pa_counters.errors += 1;
            // Track demotions from the unsoundness demotion pipeline (#2106).
            if matches!(reason, UnknownReason::Demoted(_)) {
                pa_counters.demoted += 1;
            }
            eprintln!(
                "trust-wp: proof_assert in {} unknown ({reason})",
                prepared.fn_path
            );
            eprintln!("  at {}", prepared.loc);
        }
        // VerificationResult is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {
            pa_counters.errors += 1;
        }
    }
}

fn is_contractless_proof_assert_inconclusive(reason: &UnknownReason) -> bool {
    matches!(
        reason,
        UnknownReason::Incomplete
            | UnknownReason::Quantifiers
            | UnknownReason::QuantifierUnhandled
            | UnknownReason::QuantifierRoundLimit
            | UnknownReason::QuantifierDeferred
            | UnknownReason::QuantifierCegqiIncomplete
            | UnknownReason::QuantifierEmatchingExistsIncomplete
    )
}

#[cfg(test)]
mod diagnostic_tests {
    use std::time::Duration;

    use ay_dpll::api::{Logic, NativeReplayArtifact, Solver, Sort};
    use trust_wp_ay::{
        UnknownReason, VerificationOutcome, VerificationProvenance, VerificationRequest,
    };
    use trust_wp_core::formula::PureExpr;

    use super::*;

    fn proof_assert_prepared(
        ensure: PureExpr,
    ) -> super::super::proof_assert_verify::PreparedAssertion {
        super::super::proof_assert_verify::PreparedAssertion {
            preconditions: Vec::new(),
            ensures: vec![ensure],
            return_expr: None,
            mode_overrides: None,
            closure_capture_infos: Vec::new(),
            has_mutating_call_effect: false,
            is_contractless: false,
            containing_requires_false: false,
            fn_path: "test::proof_assert_firewall".to_string(),
            loc: "test.rs:1:1".to_string(),
            expr_text: "true".to_string(),
        }
    }

    fn proof_assert_test_artifact(
        metadata: ay_dpll::api::NativeReplayMetadata,
        unsat: bool,
    ) -> NativeReplayArtifact {
        let mut solver = Solver::try_new(Logic::QfUf).expect("test solver");
        let p = solver.declare_const("proof_assert_test_p", Sort::Bool);
        solver.assert_term(p);
        if unsat {
            let not_p = solver.not(p);
            solver.assert_term(not_p);
        }
        let mut artifact = solver.export_native_replay_artifact(metadata, None);
        assert_eq!(
            artifact.replay_gaps.as_slice(),
            ["solve details were not captured"]
        );
        artifact.replay_gaps.clear();
        artifact.created_unix_ms = 0;
        artifact.timeout_ms = Some(5_000);
        artifact
    }

    fn proof_assert_test_certificate(
        prepared: &super::super::proof_assert_verify::PreparedAssertion,
    ) -> ProofAssertSliceCertificate {
        let prepared_claim = proof_assert_obligation_slice_claims(&prepared.ensures)
            .into_iter()
            .next()
            .expect("one test claim");
        let normalized_claim = prepared_claim.clone();
        let prepared_claim_hash = proof_assert_prepared_claim_hash(0, &prepared_claim);
        let normalized_claim_hash = proof_assert_normalized_claim_hash(0, &normalized_claim);
        let metadata =
            proof_assert_native_replay_metadata(0, prepared_claim_hash, normalized_claim_hash);
        let artifact = proof_assert_test_artifact(metadata, true);
        let native_problem_json = artifact.to_pretty_json();
        let replay =
            Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
                .expect("strict proof replay for test certificate");
        let solve_evidence = SolveEvidenceSnapshot::from_solve_details(&replay);
        let solver_statistics = SolveStatisticsSnapshot::from(&replay.statistics);
        assert!(proof_assert_snapshot_has_complete_unsat_proof(
            &solve_evidence,
            &solver_statistics
        ));
        ProofAssertSliceCertificate::new(
            0,
            proof_assert_obligation_slice_derivations(&prepared.ensures, &prepared.preconditions)
                .into_iter()
                .next()
                .expect("one test derivation"),
            prepared_claim,
            prepared_claim_hash,
            normalized_claim,
            normalized_claim_hash,
            native_problem_json.clone(),
            proof_assert_native_problem_hash(&native_problem_json),
            solve_evidence,
            solver_statistics,
        )
    }

    fn proof_assert_test_outcome(certificate: ProofAssertSliceCertificate) -> VerificationOutcome {
        let mut provenance = VerificationProvenance::default();
        provenance.vc_hash = proof_assert_certificate_set_hash(std::slice::from_ref(&certificate));
        provenance.solve_evidence = Some(certificate.solve_evidence.clone());
        provenance.solver_statistics = Some(certificate.solver_statistics.clone());
        provenance.native_replay_json = Some(certificate.native_problem_json.clone());
        provenance.proof_assert_slice_certificates = vec![certificate];
        VerificationOutcome::new(VerificationResult::Verified(None), Some(provenance))
    }

    #[test]
    fn proof_assert_firewall_accepts_exact_fresh_checked_slice() {
        let prepared = proof_assert_prepared(PureExpr::Bool(false));
        let certificate = proof_assert_test_certificate(&prepared);
        assert_eq!(
            certificate.derivation,
            ProofAssertSliceDerivation::NativeEncoded
        );
        let outcome = proof_assert_test_outcome(certificate);

        assert_eq!(proof_assert_authority_gap_reason(&outcome, &prepared), None);
    }

    /// Name-level pin of the linked-ay assumption behind the `cert.*`
    /// canonicalization exception (ay 550e5792b7, ay >= 0.10): a strict replay
    /// publishes process-cumulative `cert.*` accounting integers into its
    /// statistics. If this fails, the linked ay stopped publishing them and
    /// the `cert.` arm of `canonical_proof_assert_statistics` is dead — retire
    /// it rather than letting the filter rot unverified.
    #[test]
    fn linked_ay_publishes_process_cumulative_cert_accounting() {
        let artifact =
            proof_assert_test_artifact(ay_dpll::api::NativeReplayMetadata::default(), true);
        let replay =
            Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
                .expect("strict replay for cert accounting pin");
        let statistics = SolveStatisticsSnapshot::from(&replay.statistics);
        assert!(
            statistics
                .extra_ints
                .iter()
                .any(|(key, _)| key.starts_with("cert.")),
            "linked ay no longer publishes cert.* accounting statistics; retire the \
             cert.* exception in canonical_proof_assert_statistics: {:?}",
            statistics.extra_ints
        );
        let canonical = canonical_proof_assert_statistics(statistics);
        assert!(
            canonical.extra_ints.iter().all(|(key, _)| {
                !key.starts_with("cert.") && !key.to_ascii_lowercase().contains("nanos")
            }),
            "canonicalization must strip process-cumulative accounting keys: {:?}",
            canonical.extra_ints
        );
    }

    /// The property the proof_assert firewall's statistics equality relies on:
    /// two strict replays of the IDENTICAL artifact in the same process must
    /// canonicalize to equal statistics. At ay 0.10 the raw snapshots differ
    /// (process-cumulative `cert.*` counters advance between runs), so this
    /// holds only through `canonical_proof_assert_statistics`.
    #[test]
    fn canonical_statistics_agree_across_repeated_strict_replays() {
        let artifact =
            proof_assert_test_artifact(ay_dpll::api::NativeReplayMetadata::default(), true);
        let first =
            Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
                .expect("first strict replay");
        let second =
            Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
                .expect("second strict replay");
        assert_eq!(
            canonical_proof_assert_statistics(SolveStatisticsSnapshot::from(&first.statistics)),
            canonical_proof_assert_statistics(SolveStatisticsSnapshot::from(&second.statistics)),
            "strict replays of one artifact must canonicalize to equal statistics"
        );
    }

    #[test]
    fn proof_assert_firewall_accepts_independently_rechecked_derivations() {
        let truth = proof_assert_prepared(PureExpr::Bool(true));
        let truth_certificate = proof_assert_test_certificate(&truth);
        assert_eq!(
            truth_certificate.derivation,
            ProofAssertSliceDerivation::SyntacticTruth
        );
        assert_eq!(
            proof_assert_authority_gap_reason(
                &proof_assert_test_outcome(truth_certificate),
                &truth,
            ),
            None
        );

        let premise_expr = PureExpr::Var("prepared_premise".to_string(), None);
        let mut premise = proof_assert_prepared(premise_expr.clone());
        premise.preconditions.push(premise_expr);
        let premise_certificate = proof_assert_test_certificate(&premise);
        assert_eq!(
            premise_certificate.derivation,
            ProofAssertSliceDerivation::ExactPreparedPremise
        );
        assert_eq!(
            proof_assert_authority_gap_reason(
                &proof_assert_test_outcome(premise_certificate),
                &premise,
            ),
            None
        );
    }

    #[test]
    fn proof_assert_firewall_rejects_wrong_structural_derivation() {
        let prepared = proof_assert_prepared(PureExpr::Bool(true));
        let mut certificate = proof_assert_test_certificate(&prepared);
        certificate.derivation = ProofAssertSliceDerivation::NativeEncoded;
        let outcome = proof_assert_test_outcome(certificate);

        let reason = proof_assert_authority_gap_reason(&outcome, &prepared)
            .expect("wrong structural derivation must fail closed");
        assert!(reason.contains("derivation mismatch"), "{reason}");
    }

    #[test]
    fn proof_assert_firewall_rejects_forged_complete_snapshot() {
        let prepared = proof_assert_prepared(PureExpr::Bool(true));
        let mut certificate = proof_assert_test_certificate(&prepared);
        let metadata = proof_assert_native_replay_metadata(
            certificate.ordinal,
            certificate.prepared_claim_hash,
            certificate.normalized_claim_hash,
        );
        let sat_artifact = proof_assert_test_artifact(metadata, false);
        certificate.native_problem_json = sat_artifact.to_pretty_json();
        certificate.problem_hash =
            proof_assert_native_problem_hash(&certificate.native_problem_json);
        let outcome = proof_assert_test_outcome(certificate);

        let reason = proof_assert_authority_gap_reason(&outcome, &prepared)
            .expect("forged complete snapshot must fail closed");
        assert!(
            reason.contains("lacked complete checked UNSAT authority"),
            "{reason}"
        );
    }

    #[test]
    fn proof_assert_firewall_rejects_cross_claim_relabel_and_rehash() {
        let original = proof_assert_prepared(PureExpr::Bool(true));
        let relabeled = proof_assert_prepared(PureExpr::Bool(false));
        let mut certificate = proof_assert_test_certificate(&original);
        certificate.prepared_claim = proof_assert_obligation_slice_claims(&relabeled.ensures)
            .into_iter()
            .next()
            .expect("one relabeled claim");
        certificate.prepared_claim_hash =
            proof_assert_prepared_claim_hash(0, &certificate.prepared_claim);
        certificate.normalized_claim = certificate.prepared_claim.clone();
        certificate.normalized_claim_hash =
            proof_assert_normalized_claim_hash(0, &certificate.normalized_claim);
        let outcome = proof_assert_test_outcome(certificate);

        let reason = proof_assert_authority_gap_reason(&outcome, &relabeled)
            .expect("cross-claim relabel must fail closed");
        assert!(
            reason.contains("derivation mismatch") || reason.contains("claim binding mismatch"),
            "{reason}"
        );
    }

    #[test]
    fn diagnostic_wire_line_is_single_line_and_escaped() {
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Timeout,
        ));
        let provenance = VerificationProvenance::with_solve_time(Duration::from_millis(12))
            .with_assertion_count(7)
            .with_solver_timeout(Some(Duration::from_millis(100)))
            .with_replay_artifact(Some("(assert true)\n".to_string()))
            .with_native_replay_json(Some("{\"schema\":\"ay.native-replay.v1\"}".to_string()));

        let line = verification_diagnostic_wire_line(
            "crate::path with space",
            "function_contract",
            &outcome,
            Some(&provenance),
        );

        assert!(line.starts_with(trust_wp_core::result_protocol::DIAGNOSTIC_WIRE_PREFIX));
        assert!(line.contains("def_path=crate::path%20with%20space"));
        assert!(line.contains("kind=function_contract"));
        assert!(line.contains("status=unknown"));
        assert!(line.contains("reason=timeout"));
        assert!(line.contains("solve_time_ms=12"));
        assert!(line.contains("assertions=7"));
        assert!(line.contains("timeout_ms=100"));
        assert!(line.contains("replay_present=true"));
        assert!(line.contains("replay_bytes=14"));
        assert!(line.contains("native_replay_present=true"));
        assert!(line.contains("native_replay_schema=ay.native-replay.v1"));
        assert!(line.contains("native_replay_path=none"));
        assert!(line.contains("native_replay_write_error=none"));
        assert!(!line.contains('\n'));
    }

    #[test]
    fn verified_outcome_with_missing_provenance_is_evidence_gap() {
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Verified(None));

        assert_eq!(
            verified_evidence_gap_reason(&outcome).as_deref(),
            Some("missing solver provenance")
        );
    }

    #[test]
    fn verified_outcome_with_missing_solve_evidence_is_evidence_gap() {
        let outcome = VerificationOutcome::new(
            VerificationResult::Verified(None),
            Some(VerificationProvenance::default()),
        );

        assert_eq!(
            verified_evidence_gap_reason(&outcome).as_deref(),
            Some("missing solver evidence")
        );
    }

    #[test]
    fn verified_outcome_with_accepted_solver_evidence_is_not_evidence_gap() {
        let outcome =
            trust_wp_ay::verify_function_with_modes_outcome(VerificationRequest::new(&[], &[]))
                .expect("empty obligation should encode");

        let VerificationResult::Verified(Some(summary)) = &outcome.result else {
            panic!("checked empty obligation must carry a proof certificate");
        };
        assert!(summary.is_fully_verified());
        assert_eq!(verified_evidence_gap_reason(&outcome), None);

        // Pin the SHAPE of the accepted evidence, not just the verdict. The
        // mandatory boundary reads a pair captured on two different code paths
        // (`solve_evidence` and `solver_statistics` on one
        // `VerificationProvenance`); when the two stopped describing the same
        // solve, every contractless obligation silently became an evidence gap
        // and nothing named which field went missing. Assert each field by
        // name so a rename or a dropped statistic in the solver — or another
        // provenance merge that re-pairs the halves — fails loudly here.
        let provenance = outcome.provenance.as_ref().expect("provenance");
        let evidence = provenance.solve_evidence.as_ref().expect("evidence");
        let statistics = provenance
            .solver_statistics
            .as_ref()
            .expect("statistics paired with the accepted evidence");
        assert_eq!(evidence.result, "unsat");
        assert!(evidence.accepted_for_consumer);
        assert!(evidence.verification.unsat_proof_available);
        assert_eq!(evidence.verification.unsat_proof_checker_failures, 0);
        assert!(matches!(
            evidence.verification_level,
            SolveVerificationLevelSnapshot::ProofChecked
                | SolveVerificationLevelSnapshot::FullyVerified
        ));
        assert!(
            statistics.proof_complete,
            "statistics must belong to the proof the evidence attests to"
        );
        let extra = |key: &str| {
            statistics
                .extra_ints
                .iter()
                .find_map(|(candidate, value)| (candidate == key).then_some(*value))
        };
        assert_eq!(extra("proof_checker_failures"), Some(0));
        assert_eq!(extra("proof_trust"), Some(0));
        assert_eq!(extra("proof_checker_skipped_hole_steps"), Some(0));
        let checked = extra("proof_checker_checked_steps").expect("checked steps");
        let total = extra("proof_checker_total_steps").expect("total steps");
        assert!(total > 0 && checked == total);
        assert_eq!(unsat_proof_authority_gap(evidence, statistics), None);
    }

    /// Fail-closed direction of the same pin: authoritative evidence paired
    /// with statistics that do not describe its proof must still be refused,
    /// and the refusal must name the field. This is exactly the mismatched pair
    /// that `install_preferred_verified_solve_diagnostics` now prevents; if a
    /// future provenance merge reintroduces it, the end-to-end acceptance pin
    /// above fails and this one explains why.
    #[test]
    fn authoritative_evidence_with_placeholder_statistics_is_refused_by_name() {
        let mut outcome =
            trust_wp_ay::verify_function_with_modes_outcome(VerificationRequest::new(&[], &[]))
                .expect("empty obligation should encode");
        outcome
            .provenance
            .as_mut()
            .expect("provenance")
            .solver_statistics = Some(SolveStatisticsSnapshot::default());

        assert_eq!(
            verified_evidence_gap_reason(&outcome).as_deref(),
            Some(
                "solver evidence failed mandatory proof-authority checks \
                 (statistics.proof_complete is false)"
            )
        );
    }

    #[test]
    fn accepted_unsat_without_certificate_is_still_evidence_gap() {
        let mut outcome =
            trust_wp_ay::verify_function_with_modes_outcome(VerificationRequest::new(&[], &[]))
                .expect("empty obligation should encode");
        outcome.result = VerificationResult::Verified(None);

        assert_eq!(
            verified_evidence_gap_reason(&outcome).as_deref(),
            Some("missing proof certificate summary")
        );
    }

    #[test]
    fn verified_outcome_with_structural_provenance_is_evidence_gap() {
        let mut outcome =
            trust_wp_ay::verify_function_with_modes_outcome(VerificationRequest::new(&[], &[]))
                .expect("empty obligation should encode");
        let evidence = outcome
            .provenance
            .as_mut()
            .and_then(|provenance| provenance.solve_evidence.as_mut())
            .expect("empty obligation should carry solve evidence");
        evidence.result = "trust-wp-structural-provenance".to_string();
        evidence.accepted_for_consumer = true;
        evidence.consumer_rejection = None;

        assert_eq!(
            verified_evidence_gap_reason(&outcome).as_deref(),
            Some("accepted solver evidence was trust-wp-structural-provenance, not verified proof evidence")
        );
    }

    #[test]
    fn verified_evidence_gap_rejects_shortcut_unsat_without_proof() {
        let mut outcome =
            trust_wp_ay::verify_function_with_modes_outcome(VerificationRequest::new(&[], &[]))
                .expect("empty obligation should encode");
        let evidence = outcome
            .provenance
            .as_mut()
            .and_then(|provenance| provenance.solve_evidence.as_mut())
            .expect("empty obligation should carry structural solve evidence");
        evidence.result = "unsat".to_string();
        evidence.accepted_for_consumer = false;
        evidence.consumer_rejection = Some(
            "shortcut UNSAT result (shortcut:direct-bool-conflict) did not run ay solve details/proof validation"
                .to_string(),
        );

        assert_eq!(
            verified_evidence_gap_reason(&outcome).as_deref(),
            Some(
                "shortcut UNSAT result (shortcut:direct-bool-conflict) did not run ay solve details/proof validation"
            )
        );
    }

    /// Fix B (designs/2026-05-19-100doors-vec-sort-leakage.md):
    /// `Unknown(Timeout)` outcomes that lack provenance must still gate true so
    /// the loop-phase diagnostic line is emitted when the outer hard-timeout
    /// kills the ay worker before it returns evidence.
    #[test]
    fn unknown_timeout_without_provenance_passes_emission_gate() {
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Timeout,
        ));

        assert!(outcome.provenance.is_none());
        assert!(should_emit_verification_diagnostic(&outcome));
        assert!(is_unknown_timeout_without_provenance(&outcome));
    }

    /// Fix B: the synthesized wire line carries `ay_result=timeout`, marks the
    /// outcome as not accepted by the consumer, and includes the loop-phase
    /// `kind=` token so downstream consumers can attribute the timeout to the
    /// correct phase even with no solver provenance.
    #[test]
    fn unknown_timeout_without_provenance_emits_loop_phase_wire_line() {
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Timeout,
        ));

        let line = verification_diagnostic_wire_line(
            "crate::f",
            "loop_initialization",
            &outcome,
            outcome.provenance.as_ref(),
        );

        assert!(line.starts_with(trust_wp_core::result_protocol::DIAGNOSTIC_WIRE_PREFIX));
        assert!(line.contains("kind=loop_initialization"));
        assert!(line.contains("status=unknown"));
        assert!(line.contains("reason=timeout"));
        assert!(line.contains("ay_result=timeout"));
        assert!(line.contains("accepted_for_consumer=false"));
        assert!(line.contains("model_validated=false"));
        // Provenance-derived numeric fields fall back to zero when the worker
        // was killed mid-solve and no provenance was captured.
        assert!(line.contains("solve_time_ms=0"));
        assert!(line.contains("assertions=0"));
        assert!(line.contains("timeout_ms=none"));
        assert!(line.contains("replay_present=false"));
        assert!(line.contains("native_replay_present=false"));
        assert!(!line.contains('\n'));
    }

    /// The producer and the consumer of `TRUST_WP_DIAGNOSTIC:v1` are one pair:
    /// this driver builds the line with `trust_wp_core`'s encoder, and
    /// `VerificationDiagnosticRecord` decodes it. A def_path full of characters
    /// the wire has to escape (spaces, `<>`, `%`, `=`) must survive the round
    /// trip byte for byte, or a consumer silently reads a different obligation
    /// than the one that was verified.
    #[test]
    fn diagnostic_wire_lines_round_trip_through_the_core_decoder() {
        use trust_wp_core::result_protocol::VerificationDiagnosticRecord;

        let def_path = "crate::f<T = &str> (100% of it)";
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Timeout,
        ));
        let line = verification_diagnostic_wire_line(
            def_path,
            "function_contract",
            &outcome,
            outcome.provenance.as_ref(),
        );

        // Escaping keeps the line splittable: one token per field, no spaces.
        assert!(!line.contains(' ') || line.split(' ').count() > 1);
        let record = VerificationDiagnosticRecord::from_wire_line(&line)
            .expect("the core decoder accepts what this driver emits");
        assert_eq!(record.def_path, def_path);
        assert_eq!(record.kind, "function_contract");
        assert_eq!(record.status, "unknown");
        assert_eq!(record.reason, UnknownReason::Timeout.to_string());

        // The typed accessors agree with the producer's sentinels.
        assert_eq!(record.field_u64("solve_time_ms"), Some(0));
        assert_eq!(record.field("timeout_ms"), Some("none"));
        assert_eq!(record.field_u64("timeout_ms"), None);
        assert_eq!(record.field_opt("native_replay_schema"), None);
        assert_eq!(
            record.field_tristate_bool("accepted_for_consumer"),
            Some(Some(false))
        );

        // A verified-shaped outcome with no evidence reports `unknown`, not a
        // guess, and still round-trips.
        let verified = VerificationOutcome::without_provenance(VerificationResult::Verified(None));
        let line = verification_diagnostic_wire_line(def_path, "proof_assert", &verified, None);
        let record = VerificationDiagnosticRecord::from_wire_line(&line).unwrap();
        assert_eq!(record.status, "verified");
        assert_eq!(record.reason, "none");
        assert_eq!(record.field_tristate_bool("model_validated"), Some(None));
    }
}
