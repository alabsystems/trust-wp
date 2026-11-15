// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification result reporting and summary formatting.
//!
//! All user-facing output logic: summary formatting, function result
//! reporting, proof_assert result reporting, and diagnostic hints.

use std::{collections::HashSet, fmt::Write as _, fs, path::PathBuf, time::Duration};

use sha2::{Digest, Sha256};
use tracing::debug;
use trust_wp_ay::{
    proof_assert_native_replay_metadata, proof_assert_obligation_slice_claims,
    proof_assert_obligation_slice_derivations, refutation_evidence_gap_reason, EncodingError,
    ProofAssertSliceCertificate, ProofAssertSliceDerivation, SolveEvidenceSnapshot,
    SolveStatisticsSnapshot, SolveVerificationLevelSnapshot, UnknownReason, VerificationOutcome,
    VerificationProvenance, VerificationResult,
};
use trust_wp_core::{formula::PureExpr, logic::LogicFnDef, result_protocol::encode_wire_value};

use super::{
    super::{contracts::FunctionContract, mir_analysis::MutBorrowBody},
    encoding_error_breakdown::EncodingErrorBreakdown,
    function_credit::{grant_function_credit, CreditKind, FunctionCredit},
    helpers::report_counterexample,
    parsing::{LoopFields, LoopObligationGroup, MutBorrowFields, ParsedContract},
    verification::neutralized_axiom_reached,
};

const NATIVE_REPLAY_DIR_ENV: &str = "TRUST_WP_NATIVE_REPLAY_DIR";
const NATIVE_REPLAY_SCHEMA: &str = "ay.native-replay.v1";
const PROOF_ASSERT_REPLAY_TIMEOUT_MAX_MS: u128 = 6_000;

/// Accumulated counters for function contract verification results.
///
/// One struct in place of separate `&mut usize` counter parameters threaded
/// through `verify_contracts`, `verify_contract_loop_path`,
/// `verify_logic_fn_postconditions`, `check_trait_refinement`, and the
/// reporting functions.
#[derive(Debug, Default)]
pub(super) struct VerificationCounters {
    /// Logic functions whose own body assertions were all proved. The logic lane
    /// prints each as a `proof_assert in X verified` line, so the proof_assert total
    /// on the wire and in the summary must include it, or the per-function gate
    /// reads a credit line the driver's own count denies.
    pub logic_assertions_verified: usize,
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
    /// `Failed`-shaped results withheld because no VALIDATED counterexample
    /// model backed them (see `withhold_unvalidated_refutation`). A subset of
    /// `errors`: the withheld verdict is reported and counted as `unknown`.
    /// Tracked separately so "trust-wp refuted this" and "trust-wp could not
    /// decide this" stay countable apart.
    pub refutations_withheld: usize,
    /// Lane credits held until their function's own assertions are
    /// adjudicated. Every `verified`/`verified*` credit goes through
    /// `function_credit::grant_function_credit`, never straight to these
    /// counters, so a function is never counted verified beside an unproved
    /// assertion of its own.
    pub(in crate::callbacks) credit_ledger: super::function_credit::CreditLedger,
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
    /// proof_assert `Failed` results withheld for lack of a VALIDATED
    /// counterexample model. See the field of the same name on
    /// `VerificationCounters`.
    pub refutations_withheld: usize,
    /// Functions whose body assertions the in-function pass already
    /// adjudicated.
    ///
    /// A clause-free function that nonetheless reaches the main contract loop
    /// is visited by BOTH assertion passes, and each `proof_assert!` then gets
    /// two identical verdicts for one source obligation. That is a
    /// double-count, not two proofs: the goal inventory sees one assertion and
    /// the driver claims two, so the item reads as a mismatch even though
    /// every assertion was discharged. The standalone pass reads this set and
    /// declines a function the in-function pass has already answered.
    pub assertions_adjudicated: std::collections::HashSet<rustc_hir::def_id::DefId>,
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
            proof_assert_verified: pa_counters.verified + counters.logic_assertions_verified,
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
/// The single spelling of that line; `verification.rs` emits this rather than
/// an inline `eprintln!` of its own.
pub(super) fn format_proof_assert_summary(
    pa_counters: &ProofAssertCounters,
    logic_assertions_verified: usize,
) -> String {
    let mut parts = vec![
        format!(
            "{} verified",
            pa_counters.verified + logic_assertions_verified
        ),
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

/// How many of the user's own `ensures` clauses reach the solver's clause
/// vector, and therefore how many low indices `clause_idx` can still mean a
/// user clause.
///
/// `discharge_ensures_already_required` retains away every `Bool(true)` clause
/// before the vector is handed to the solver, so a literal `#[ensures(true)]`
/// occupies no index and the first synthesized obligation slides down into its
/// place. Counting the raw `parsed.ensures` would then label that obligation
/// `violated ensures #0` on a function whose only written postcondition is
/// `true` — which cannot be violated (D-26).
pub(super) fn surviving_user_clause_count(parsed: &ParsedContract) -> usize {
    parsed
        .ensures
        .iter()
        .filter(|clause| !matches!(clause, trust_wp_core::formula::PureExpr::Bool(true)))
        .count()
}

/// Label a violated function-level clause without claiming it is a user
/// `#[ensures]` when it is not.
///
/// `clause_idx` indexes the FINAL `effective_ensures` vector handed to the
/// solver. That vector starts as the user's parsed `ensures` and is then
/// EXTENDED with obligations synthesized from the body — call-site
/// preconditions (including the fail-closed `requires(false)` an opaque call
/// is owed), machine-integer arithmetic goals, panic-site goals and
/// type-invariant goals. Printing every one of them as `violated ensures #N`
/// would tell users their postcondition failed on a function that has no
/// postcondition: `10 / y` would report `violated ensures #0: (y != 0)` for a
/// function with zero `#[ensures]` clauses (D-26).
///
/// The boundary is one-directional and that is deliberate. Clauses are only
/// ever APPENDED after the user prefix, and the user prefix only ever SHRINKS
/// (`discharge_ensures_already_required` retains away `Bool(true)`), so
/// `clause_idx >= user_clause_count` PROVES the clause is synthesized. The
/// converse does not hold — a synthesized clause can slide below the boundary
/// when a user clause was dropped — so the `ensures #N` label is kept for the
/// low indices rather than replaced by a stronger claim this site cannot make.
pub(super) fn report_violated_clause(
    info: &trust_wp_ay::PostconditionInfo,
    user_clause_count: usize,
) {
    if info.clause_idx >= user_clause_count {
        eprintln!(
            "  violated obligation #{}: {}",
            info.clause_idx, info.contract_text,
        );
        if user_clause_count == 0 {
            eprintln!(
                "  note: this function carries no #[ensures] obligation of its own; the \
                 clause above was raised by its body (a call precondition, an arithmetic \
                 goal or a panic site)"
            );
        }
        return;
    }
    eprintln!(
        "  violated ensures #{}: {}",
        info.clause_idx, info.contract_text,
    );
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
    /// What this function-level check, continuing from a loop, may not claim
    /// (see `LoopCaveats`).
    pub(super) loop_caveats: &'a LoopCaveats,
}

/// What a function-level check that continues from a loop may not claim.
#[derive(Default)]
pub(in crate::callbacks) struct LoopCaveats {
    /// `Some(reason)` when the loop phases were INCOMPLETE (no phase
    /// produced a counterexample, but the invariant was not proven) and
    /// the function-level path runs without the loop's invariant. A
    /// counterexample found there was never checked against the unproven
    /// invariant, so it must be reported as unknown, not FAILED.
    pub(in crate::callbacks) incomplete_loop: Option<String>,
    /// `Some(reason)` when `result` is unbound because no single post-loop
    /// return value describes every path from the loop's exit (D-165). A
    /// proof without the body's value holds whatever it is, so it stands; a
    /// counterexample may contradict it and is reported as unknown.
    pub(in crate::callbacks) result_unbound: Option<String>,
    /// `Some(reason)` when the function-level VC reads a value no premise
    /// states: the loop condition the exit assumptions negate reads an
    /// unstated call result (`LoopBodyExpr::condition_unstated`). The proven
    /// invariant is a sound premise, so a proof stands, but a counterexample
    /// picks that value freely and is reported as unknown.
    pub(in crate::callbacks) unstated_exit_premise: Option<String>,
}

impl LoopCaveats {
    /// Why a function-level counterexample is not checked against what the
    /// loop phases establish: the unproven invariant, else the unbound
    /// `result`.
    pub(in crate::callbacks) fn incomplete_or_unbound(&self) -> Option<&str> {
        self.incomplete_loop
            .as_deref()
            .or(self.result_unbound.as_deref())
    }
}

/// Verdict label for a function-level counterexample.
///
/// A counterexample found while the loop invariant was unproven (all loop
/// phases incomplete, none failed), or while `result` was read without the
/// post-loop return value, was never checked against what the loop
/// establishes: it may describe a state the loop cannot reach. It is therefore
/// unknown, not a refutation. Only a counterexample from a run that carried the
/// loop's proven facts (or had no loop) is reported as FAILED.
pub(super) fn function_counterexample_is_unvalidated(incomplete_loop: Option<&str>) -> bool {
    incomplete_loop.is_some()
}

/// Whether a function-level proof leaves a loop invariant unproved.
///
/// A loop invariant is an obligation of the function, not only a premise
/// for its postcondition: a postcondition the function-level check proves
/// WITHOUT the invariant says nothing about whether the invariant holds, so
/// crediting it would accept a function whose invariant is false
/// (s53_mutcall_prior_loop_init_invariant, whose `ensures(true)` needs no
/// invariant at all).
pub(super) fn function_proof_leaves_loop_invariant_unproven(incomplete_loop: Option<&str>) -> bool {
    incomplete_loop.is_some()
}

/// Every `PureExpr` the parsed contract carries.
///
/// The destructuring is exhaustive on purpose. A clause this walk does not see
/// is a logic-function mention that would go unnoticed, and an unnoticed
/// mention reports a clean `verified` for a contract that names an entry
/// nobody proved. A field added to `ParsedContract` must therefore break this
/// build rather than silently open an unscanned channel.
fn collect_parsed_contract_exprs<'a>(parsed: &'a ParsedContract, out: &mut Vec<&'a PureExpr>) {
    let ParsedContract {
        requires,
        ensures,
        result_expr,
        result_expr_spanned,
        arg_names: _,
        call_assumptions,
        pre_loop_call_assumptions,
        call_obligations,
        pre_loop_call_obligations,
        post_loop_call_obligations,
        returning_path_facts,
        extraction_fail_closed_reason: _,
        panic_unreachability_obligations: _,
        user_written_false_obligations: _,
        // MIR edges; no expression.
        proved_dead_edges: _,
        loop_fields,
        mut_borrow,
        // Enum field indices of a recursive `&mut self` reborrow; no expression.
        reborrow_prophecy: _,
    } = parsed;

    out.extend(requires.iter());
    out.extend(ensures.iter());
    out.extend(result_expr.iter());
    out.extend(result_expr_spanned.iter().map(|spanned| &spanned.expr));
    out.extend(call_assumptions.iter());
    out.extend(pre_loop_call_assumptions.iter());
    out.extend(call_obligations.iter());
    out.extend(pre_loop_call_obligations.iter());
    out.extend(post_loop_call_obligations.iter());
    out.extend(returning_path_facts.iter());

    let LoopFields {
        invariants,
        per_loop_invariants,
        per_loop_variants,
        // Spans and basic blocks; no expression.
        all_loop_spans: _,
        variants,
        loop_analysis: _,
        loop_obligation_groups,
    } = loop_fields;
    out.extend(invariants.iter());
    out.extend(variants.iter());
    out.extend(
        per_loop_invariants
            .iter()
            .chain(per_loop_variants.iter())
            .flat_map(|(_, _, exprs)| exprs.iter()),
    );
    for LoopObligationGroup {
        assumptions,
        obligations,
        condition,
        loop_index: _,
        condition_unstated: _,
        pre_loop_stored_names: _,
        unstated_entry_values: _,
        injected_fail_closed: _,
    } in loop_obligation_groups
    {
        out.extend(assumptions.iter());
        out.extend(obligations.iter());
        out.extend(condition.iter());
    }

    let MutBorrowFields {
        mut_borrow_body,
        mut_ref_param_names: _,
        state_params: _,
        projected_final_pins,
        stale_call_final_params: _,
    } = mut_borrow;
    out.extend(projected_final_pins.iter().map(|pin| &pin.value));
    if let Some(MutBorrowBody {
        final_values,
        indexed_writes,
        // MIR locations, borrow ids and parameter-name sets; no expression.
        resolve_results: _,
        finality: _,
        borrow_id_origins: _,
        delayed_writeback_assumptions,
        mutation_continued_params: _,
        nested_slot_resolutions,
        nested_transfer_params: _,
        lent_path_resolutions,
    }) = mut_borrow_body
    {
        out.extend(final_values.values());
        out.extend(
            indexed_writes
                .iter()
                .flat_map(|write| [&write.index, &write.value]),
        );
        out.extend(delayed_writeback_assumptions.iter());
        out.extend(nested_slot_resolutions.iter());
        out.extend(lent_path_resolutions.iter());
    }
}

/// The unproven entries THIS contract's verdict rests on.
///
/// Scanning the whole crate's logic-function slice made one recorded entry
/// mark every verified contract in the crate, including contracts that never
/// mention it — a caveat attached to a proof that does not carry it says
/// nothing true about that proof. A contract keeps its clean `verified` only
/// when the entry is outside everything its clauses can reach.
///
/// Reachability is decided by `neutralized_axiom_reached` — the same predicate
/// the verdict path uses to WITHHOLD a refutation that rests on a withdrawn
/// axiom. The code that grants the clean verdict and the code that owes the
/// caveat have to answer the same question the same way, or one of them is
/// guessing: that predicate already knows every spelling a call site can carry
/// (unique id, full path, crate-relative path, bare method name) and already
/// walks the live definitions in between. Asking it once per recorded entry
/// treats the OTHER entries as live, which can only widen what this contract
/// is held to reach.
fn contract_unverified_axiom_deps<'a>(
    parsed: &ParsedContract,
    logic_fns: &[LogicFnDef],
    unverified_axioms: &'a HashSet<String>,
) -> Vec<&'a str> {
    if unverified_axioms.is_empty() {
        return Vec::new();
    }
    let mut exprs: Vec<&PureExpr> = Vec::new();
    collect_parsed_contract_exprs(parsed, &mut exprs);
    let mut deps: Vec<&str> = unverified_axioms
        .iter()
        .filter(|path| {
            let entry: HashSet<String> = std::iter::once((*path).clone()).collect();
            neutralized_axiom_reached(logic_fns, &entry, exprs.iter().copied()).is_some()
        })
        .map(String::as_str)
        .collect();
    deps.sort_unstable();
    deps
}

/// Dispatch a function verification result to counters and report to stderr.
///
/// Returns `true` when the result is a credit. The credit itself goes through
/// `function_credit::grant_function_credit`, so while the contract loop is
/// verifying the function it still waits on the function's own assertions
/// and may never be printed or counted.
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
            let outcome =
                withhold_unvalidated_refutation(outcome, &mut counters.refutations_withheld);
            emit_verification_diagnostic_if_requested(def_path, "function_contract", &outcome);
            let evidence_gap_reason = verified_evidence_gap_reason(&outcome);
            match outcome.result {
                VerificationResult::Verified(_)
                    if function_proof_leaves_loop_invariant_unproven(
                        fn_ctx.loop_caveats.incomplete_loop.as_deref(),
                    ) =>
                {
                    counters.errors += 1;
                    let reason = fn_ctx
                        .loop_caveats
                        .incomplete_loop
                        .as_deref()
                        .unwrap_or("loop invariant incomplete");
                    eprintln!("trust-wp: {def_path} unknown (incomplete loop: {reason})");
                    eprintln!("  at {loc}");
                    eprintln!(
                        "  note: the function-level check holds without the loop invariant, \
                         which is itself an obligation and was not proved"
                    );
                    false
                }
                VerificationResult::Verified(ref certificate) => {
                    if let Some(reason) = evidence_gap_reason {
                        counters.evidence_gaps += 1;
                        counters.warnings += 1;
                        eprintln!("trust-wp: {def_path} evidence gap ({reason})");
                        eprintln!("  at {loc}");
                        return false;
                    }
                    // Report the unverified axioms THIS contract can reach
                    // (#1490): the crate's other recorded entries are not this
                    // function's caveat, and the crate summary counts the
                    // functions marked here.
                    let deps = contract_unverified_axiom_deps(
                        parsed,
                        logic_fns_opt.unwrap_or(&[]),
                        unverified_axioms,
                    );
                    let credit = if deps.is_empty() {
                        // A proof ay validated fully but cannot render into the
                        // pinned Alethe calculus is still a proof — it is just
                        // one only ay can re-check. Counted alongside
                        // `verified`, never instead of it.
                        FunctionCredit::new(
                            CreditKind::Verified {
                                native_only: verified_on_native_only_authority(
                                    certificate.as_ref(),
                                ),
                            },
                            format!("trust-wp: {def_path} verified \u{2713}"),
                        )
                    } else {
                        // Do not count as unconditionally verified (#1878).
                        deps.iter().fold(
                            FunctionCredit::new(
                                CreditKind::VerifiedWithAxiomDeps,
                                format!(
                                    "trust-wp: {def_path} verified* (depends on {} unverified axiom(s))",
                                    deps.len()
                                ),
                            ),
                            |credit, dep| credit.with_line(format!("  unverified axiom: {dep}")),
                        )
                    };
                    grant_function_credit(counters, credit);
                    true
                }
                VerificationResult::Failed(_)
                    if fn_ctx.loop_caveats.unstated_exit_premise.is_some() =>
                {
                    counters.errors += 1;
                    let reason = fn_ctx
                        .loop_caveats
                        .unstated_exit_premise
                        .as_deref()
                        .unwrap_or_default();
                    eprintln!(
                        "trust-wp: {def_path} unknown ({}: {reason})",
                        trust_wp_ay::REFUTATION_AUTHORITY_MESSAGE
                    );
                    eprintln!("  at {loc}");
                    false
                }
                VerificationResult::Failed(_)
                    if function_counterexample_is_unvalidated(
                        fn_ctx.loop_caveats.incomplete_or_unbound(),
                    ) =>
                {
                    counters.errors += 1;
                    let reason = fn_ctx
                        .loop_caveats
                        .incomplete_or_unbound()
                        .unwrap_or("loop invariant incomplete");
                    eprintln!("trust-wp: {def_path} unknown (incomplete loop: {reason})");
                    eprintln!("  at {loc}");
                    eprintln!(
                        "  note: the function-level check ran without what the loop \
                         phases establish; its counterexample was not validated against it"
                    );
                    false
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
                        report_violated_clause(info, surviving_user_clause_count(parsed));
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
                            grant_function_credit(
                                counters,
                                FunctionCredit::new(
                                    CreditKind::Verified { native_only: false },
                                    format!(
                                        "trust-wp: {def_path} verified \u{2713} (vacuous: explicit #[requires(false)])"
                                    ),
                                )
                                .with_line(format!("  at {loc}")),
                            );
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
    // (loop invariant: timeout)" with no breadcrumbs.
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

/// Withhold a `Failed` verdict that carries no VALIDATED counterexample.
///
/// **The rule (D-28).** `FAILED \u{2717} (counterexample)` asserts
/// that a state exists which violates the obligation. trust-wp may publish that
/// only when ay actually computed a satisfying assignment for the negated
/// obligation AND validated it (see
/// [`trust_wp_ay::refutation_evidence_gap_reason`] for the exact bar). A
/// verdict that does not clear it -- no provenance, synthesized structural
/// provenance, a shortcut SAT that skipped model validation, an `unsat` or
/// `unknown` snapshot under a `Failed` -- describes an obligation that was NOT
/// refuted, and becomes `unknown` with the withholding reason attached.
///
/// Apply this BEFORE anything reads the verdict, so the wire line, the stderr
/// verdict and the counters cannot disagree. It is idempotent, so applying it
/// again at an inner layer is free.
///
/// Strictly narrowing: it only ever turns a refutation into an inconclusive.
/// `unknown` counts as an error, never as `verified`, so no obligation becomes
/// gate-clean by passing through here, and the crate keeps a non-zero exit.
pub(in crate::callbacks) fn withhold_unvalidated_refutation(
    outcome: VerificationOutcome,
    withheld: &mut usize,
) -> VerificationOutcome {
    if let Some(reason) = refutation_evidence_gap_reason(&outcome) {
        *withheld += 1;
        debug!(reason = %reason, "refutation withheld: no validated counterexample model");
        return outcome.apply_mandatory_refutation_authority();
    }
    // The ay boundary (`apply_mandatory_proof_authority`) usually gets there
    // first, so by the time an outcome reaches the driver the verdict is
    // ALREADY `Unknown` and the gap reason above is `None`. Count it anyway:
    // this counter is what tells "trust-wp could not decide" apart from
    // "trust-wp hit a solver error", and #3771 reads it to decide whether the
    // rest of the crate is still worth attempting. Counting only the downgrades
    // the DRIVER performs would make it report zero on every real run.
    if is_withheld_refutation(&outcome.result) {
        *withheld += 1;
    }
    outcome
}

/// True for a verdict the refutation-authority gate already withheld.
///
/// The gate replaces the verdict with `Unknown(SolverMessage("<prefix>: .."))`,
/// so this is how a later stage recognises "a refutation was withheld here" —
/// at the ay boundary or in the driver, whichever ran first.
pub(in crate::callbacks) fn is_withheld_refutation(result: &VerificationResult) -> bool {
    // One definition, in the crate that owns the gate: the driver must not
    // carry a second spelling of "this refutation was withheld" that can drift
    // from the message `apply_mandatory_refutation_authority` actually writes.
    trust_wp_ay::is_withheld_refutation(result)
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
/// Naming the field, rather than answering a bare boolean, matters because the
/// two halves of this pair are captured separately (`solve_evidence` and
/// `solver_statistics` on the same [`VerificationProvenance`]) and a mismatched
/// pair is the exact rot this reports: an authoritative evidence snapshot
/// paired with placeholder statistics reads as "unsat + ProofChecked + no proof
/// steps", which must be refused but is impossible to triage from a bare
/// "checks failed" string.
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
    // even when provenance is missing.
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
    // Say, in one field, whether this line's verdict is a refutation anybody
    // may rely on. `validated` requires an accepted, model-validated SAT
    // snapshot (`trust_wp_ay::refutation_evidence_gap_reason`); `withheld`
    // marks a refutation this run REFUSED to publish for want of one; `none` is
    // every non-refutation verdict. A consumer must never reconstruct this from
    // `status=failed` alone -- that is the exact mistake this field exists to
    // remove.
    let refutation = match &outcome.result {
        VerificationResult::Failed(_) => {
            if refutation_evidence_gap_reason(outcome).is_some() {
                "withheld"
            } else {
                "validated"
            }
        }
        result if is_withheld_refutation(result) => "withheld",
        _ => "none",
    };
    format!(
        "{} def_path={} kind={} status={} reason={} solve_time_ms={} assertions={} timeout_ms={} \
         ay_result={} accepted_for_consumer={} model_validated={} unsat_proof_available={} \
         verification_level={} replay_present={} replay_bytes={} replay_sha256={} \
         native_replay_present={} native_replay_bytes={} native_replay_sha256={} \
         native_replay_schema={} native_replay_path={} native_replay_write_error={} \
         refutation={} {}",
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
        refutation,
        // Appended last so every existing key keeps its position and meaning:
        // an added instrument, not a redefined one.
        strict_proof_replay_wire_fields(
            provenance.and_then(|provenance| provenance.strict_proof_replay.as_ref()),
            provenance.map_or(0, |provenance| provenance.strict_proof_replay_unbound),
        ),
    )
}

/// Render what the STRICT proof-producing replay measured, for the diagnostic
/// wire line.
///
/// # Read these keys, not `verification_level=` / `unsat_proof_available=`
///
/// Those two keys report whatever solver's snapshot landed in
/// `provenance.solve_evidence`. On the certification-blocked lane that is the
/// long-lived incremental encoder, which is constructed with
/// `set_produce_proofs(false)` and never calls `set_verification_level`, so it
/// answers `Trusted` / `false` for EVERY query — including ones ay proved with a
/// complete derivation. A control replaying a genuine `Unsat` through it is
/// byte-identical to a real refusal. A census that reads those keys as
/// measurements counts "obligations with no proof object" that are really the
/// encoder's configuration.
///
/// The `strict_replay_*` keys below come from a solver that actually had proof
/// production on, so `strict_replay_proof_checked_steps=51`
/// `strict_replay_proof_total_steps=51` next to
/// `strict_replay_authority_accepted=false` reports a replay that checked every
/// step it had and still was not installed as authority.
///
/// `strict_replay=none` means no strict replay ran on this obligation. It does
/// NOT mean no proof exists — absence of measurement, not measurement of
/// absence.
///
/// # Equal step counters do NOT mean "ay built a derivation and refused it"
///
/// `checked == total > 0` with `skipped_hole_steps=0` does not establish a
/// complete derivation: `strict_replay_proof_complete=` is an
/// INDEPENDENT flag, and the proof-authority boundary requires it separately
/// from the step counters. A replay can report `checked=17 total=17` holes 0
/// with `proof_complete=false`, because those counters describe the steps that
/// exist, not whether they reach the empty clause.
///
/// This matters because the two cases need opposite responses. Split them on
/// `strict_replay_unknown_reason=`:
///
/// * `self_check_rejected` / `proof_trusted` — a verdict WAS computed and a
///   soundness gate withheld it. A genuine certification refusal; the
///   derivation is real and the gate is the thing to study.
/// * `quantifier_cegqi_incomplete` and the other `quantifier_*` codes — the
///   solve never established UNSAT at all, so nothing was withheld and no
///   refusal occurred. Nothing here is recoverable by improving certification.
///
/// A census keying on the step counters alone mixes these, and the mixed
/// population reads as a much larger "certification is blocking us" class than
/// exists. Always pair the counters with `strict_replay_proof_complete=` and
/// `strict_replay_unknown_reason=`.
///
/// # `strict_replay_proof_decline=` is almost always `none`, and that is not a
/// finding
///
/// It carries ay's `ProofDeclineMechanism`, whose four mechanisms are reachable
/// only through a parsed SMT-LIB surface AST. This replay uses the native API
/// and never builds one, so the field is structurally `none` here. It does not
/// mean ay declined without recording a reason — ay records one on every
/// withheld solve, and `strict_replay_unknown_reason=` /
/// `strict_replay_unknown_detail=` are where it lands.
///
/// # `strict_replay_unbound=` — read it WITH `strict_replay=`
///
/// A strict replay is bound to the obligation slice that produced it, and a
/// capture reporting a different slice is refused. `strict_replay_unbound=N`
/// counts those refusals for this obligation, so:
///
/// * `strict_replay=none strict_replay_unbound=0` — no strict replay ran here.
/// * `strict_replay=none strict_replay_unbound=1` — one ran on a SIBLING slice
///   of the same function and is deliberately not reported here.
///
/// Without the binding the second row would print as the first row's opposite:
/// the sibling's measurement, `authority_accepted=true` and all, on a blocked
/// obligation's line — a "certified but blocked" class that does not exist.
fn strict_proof_replay_wire_fields(
    observation: Option<&trust_wp_ay::StrictProofReplayObservation>,
    unbound: u32,
) -> String {
    let Some(observation) = observation else {
        return format!("strict_replay=none strict_replay_unbound={unbound}");
    };
    let extra = |key: &str| {
        observation
            .statistics
            .extra_ints
            .iter()
            .find_map(|(candidate, value)| (candidate == key).then_some(*value))
    };
    let int = |key: &str| extra(key).map_or_else(|| "none".to_string(), |value| value.to_string());
    format!(
        "strict_replay=present strict_replay_result={} strict_replay_accepted_for_consumer={} \
         strict_replay_verification_level={:?} strict_replay_unsat_proof_available={} \
         strict_replay_authority_accepted={} strict_replay_proof_decline={} \
         strict_replay_unknown_reason={} strict_replay_unknown_detail={} \
         strict_replay_proof_complete={} strict_replay_proof_checked_steps={} \
         strict_replay_proof_total_steps={} strict_replay_proof_trust={} \
         strict_replay_proof_skipped_hole_steps={} strict_replay_proof_checker_failures={} \
         strict_replay_unbound={}",
        encode_wire_value(&observation.evidence.result),
        observation.evidence.accepted_for_consumer,
        observation.evidence.verification_level,
        observation.evidence.verification.unsat_proof_available,
        observation.authority_accepted,
        encode_wire_value(observation.unsat_proof_decline.as_deref().unwrap_or("none")),
        encode_wire_value(observation.unknown_reason.as_deref().unwrap_or("none")),
        encode_wire_value(observation.unknown_detail.as_deref().unwrap_or("none")),
        observation.statistics.proof_complete,
        int("proof_checker_checked_steps"),
        int("proof_checker_total_steps"),
        int("proof_trust"),
        int("proof_checker_skipped_hole_steps"),
        int("proof_checker_failures"),
        unbound,
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

/// ay's `smt.*_total` counters that accumulate across every executor
/// invocation in the process (`combined_solvers::theory_stats`, published by
/// `collect_theory_stats_incremental`): observations of the process, not of
/// one solve.
const AY_PROCESS_WIDE_TOTALS: [&str; 3] = [
    "smt.no_rounds_total",
    "smt.combiner_checks_total",
    "smt.checks.arrays_total",
];

fn canonical_proof_assert_statistics(
    mut statistics: SolveStatisticsSnapshot,
) -> SolveStatisticsSnapshot {
    statistics.extra_ints.retain(|(key, _)| {
        let key = key.to_ascii_lowercase();
        // Volatile observations of the RUN, not of the proof: wall time,
        // memory, and (ay >= 0.10) the `cert.*` certification-accounting
        // family. ay publishes those counters from a
        // PROCESS-GLOBAL accumulator into every solve's statistics
        // (`executor/proof/check.rs` `publish_certification_accounting`;
        // `executor/cert_accounting.rs` documents them as write-only —
        // "Nothing in ay-dpll reads a counter to decide anything"). A
        // process-cumulative counter can never agree between the certificate's
        // solve and the report-time strict replay, so keeping them would make
        // this canonical comparison unsatisfiable and demote every proof_assert
        // to an evidence gap. Proof-semantic statistics (proof_checker_*,
        // proof_trust, core counters) remain compared exactly.
        //
        // ay 72348e74f added process-wide counters that accumulate across
        // every solver instance in the process: three `smt.*_total` totals
        // and the arrays theory's `arrays_prop_eq_*` family. They disagreed
        // between the certificate's solve and the replay
        // (`smt.combiner_checks_total`: 5 vs 1) and demoted true assertions
        // to an evidence gap. Only those are dropped, by name: a `_total`
        // suffix alone says nothing (ay's `sat.preprocess_tx_*_total` count
        // one solve's preprocessing, and stay compared). A counter in a time
        // unit (`lra_..._compile_us_total`, `_us_max`) is a wall-clock
        // observation whatever its suffix.
        !key.contains("time")
            && !key
                .split(['.', '_'])
                .any(|segment| matches!(segment, "us" | "ms" | "ns"))
            && !key.contains("elapsed")
            && !key.contains("duration")
            && !key.contains("memory")
            && !key.contains("rss")
            && !key.contains("nanos")
            && !key.starts_with("cert.")
            && !AY_PROCESS_WIDE_TOTALS.contains(&key.as_str())
            && !key.starts_with("arrays_prop_eq_")
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
    let certified = canonical_proof_assert_statistics(certificate.solver_statistics.clone());
    let replayed = canonical_proof_assert_statistics(replay_statistics);
    if certified != replayed {
        return Some(format!(
            "certificate solver statistics disagreed with strict replay at ordinal \
             {expected_ordinal}: {}",
            statistics_disagreement(&certified, &replayed)
        ));
    }
    None
}

/// The statistics `certified` and `replayed` disagree on, each as
/// `name: certified vs replayed`, for the evidence-gap reason.
fn statistics_disagreement(
    certified: &SolveStatisticsSnapshot,
    replayed: &SolveStatisticsSnapshot,
) -> String {
    let mut differing = Vec::new();
    macro_rules! compare {
        ($($field:ident),* $(,)?) => {
            $(
                if certified.$field != replayed.$field {
                    differing.push(format!(
                        "{}: {:?} vs {:?}",
                        stringify!($field),
                        certified.$field,
                        replayed.$field
                    ));
                }
            )*
        };
    }
    compare!(
        decisions,
        conflicts,
        propagations,
        restarts,
        theory_conflicts,
        theory_propagations,
        theory_unknown_count,
        partial_clause_count,
        model_validation_skips,
        model_validation_failures,
        proof_clause_count,
        proof_complete,
        ematching_rounds_completed,
        ematching_instances_created,
        term_bytes,
        term_count,
        refinement_count,
        rlimit_count,
        num_vars,
        num_clauses,
        num_assertions,
    );
    let certified_extra: std::collections::BTreeMap<_, _> =
        certified.extra_ints.iter().cloned().collect();
    let replayed_extra: std::collections::BTreeMap<_, _> =
        replayed.extra_ints.iter().cloned().collect();
    let keys: std::collections::BTreeSet<_> = certified_extra
        .keys()
        .chain(replayed_extra.keys())
        .collect();
    for key in keys {
        let (a, b) = (certified_extra.get(key), replayed_extra.get(key));
        if a != b {
            differing.push(format!("{key}: {a:?} vs {b:?}"));
        }
    }
    differing.join(", ")
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
            let outcome =
                withhold_unvalidated_refutation(outcome, &mut pa_counters.refutations_withheld);
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
            let result = demote_loop_head_counterexample(outcome.result, prepared);
            report_proof_assert_verification_result(result, prepared, pa_counters);
        }
        Err(ref e) => {
            pa_counters.errors += 1;
            pa_counters.encoding_errors.record(e);
            eprintln!("trust-wp: proof_assert in {} error: {e}", prepared.fn_path);
            eprintln!("  at {}", prepared.loc);
        }
    }
}

/// A counterexample to an assertion that reads a loop-head value (D-187) is a
/// model of the loop with no invariant beyond its condition, Creusot's
/// implicit `invariant true`: the loop-head symbol ranges over every value of
/// the local's type, including values no iteration can reach (`y` is `x` or
/// `x + 1` at the head of every iteration of `while .. { y = x + 1; }`, but
/// the symbol may be 7). Such a model refutes nothing about the program, so
/// it is reported `unknown`, never `FAILED`. Only a refutation is demoted.
fn demote_loop_head_counterexample(
    result: VerificationResult,
    prepared: &super::proof_assert_verify::PreparedAssertion,
) -> VerificationResult {
    if !matches!(result, VerificationResult::Failed(_)) {
        return result;
    }
    let reads_loop_head = prepared
        .preconditions
        .iter()
        .chain(&prepared.ensures)
        .chain(&prepared.return_expr)
        .any(|expr| {
            expr.free_vars()
                .iter()
                .any(|name| name.starts_with(crate::mir_analysis::extract::LOOP_HEAD_SYMBOL_PREFIX))
        });
    if !reads_loop_head {
        return result;
    }
    VerificationResult::Unknown(UnknownReason::Demoted(
        "loop-head value: the counterexample ranges over a value a loop carries into an \
         arbitrary iteration, which only the loop's invariants constrain (D-187)"
            .to_string(),
    ))
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

    /// ay's process-wide totals (ay 72348e74f) are observations of the
    /// process, not of the proof: two solves of one artifact read them at
    /// different values, so the canonical form drops them, and keeps the
    /// per-solve counter beside them.
    #[test]
    fn canonical_statistics_drop_process_wide_totals() {
        let mut statistics = SolveStatisticsSnapshot::default();
        statistics.extra_ints = vec![
            ("smt.no_rounds_total".to_string(), 5),
            ("smt.combiner_checks_total".to_string(), 5),
            ("smt.checks.arrays_total".to_string(), 3),
            ("arrays_prop_eq_calls".to_string(), 7),
            ("smt.no_rounds".to_string(), 1),
        ];
        let mut later = statistics.clone();
        for (key, value) in &mut later.extra_ints {
            if key != "smt.no_rounds" {
                *value += 1;
            }
        }
        let canonical = canonical_proof_assert_statistics(statistics);
        assert_eq!(
            canonical.extra_ints,
            vec![("smt.no_rounds".to_string(), 1)],
            "only the per-solve counter is compared"
        );
        assert_eq!(canonical, canonical_proof_assert_statistics(later));
    }

    /// A `_total` suffix is no mark of a process-wide counter: ay's
    /// `sat.preprocess_tx_*_total` count one solve's preprocessing, so a
    /// certificate and a replay that disagree on one disagree on the proof,
    /// and the firewall compares them. Dropping every `_total` key once let
    /// such a disagreement through. A counter in a time unit is a wall-clock
    /// observation, `_total` or not.
    #[test]
    fn canonical_statistics_keep_per_solve_totals() {
        let mut statistics = SolveStatisticsSnapshot::default();
        statistics.extra_ints = vec![
            (
                "sat.preprocess_tx_eliminated_variables_total".to_string(),
                4,
            ),
            (
                "sat.preprocess_tx_equivalent_variables_total".to_string(),
                2,
            ),
            (
                "sat.preprocess_tx_planned_substitutions_total".to_string(),
                1,
            ),
            ("sat.two_stage_score_total".to_string(), 9),
            ("smt.combiner_checks_total".to_string(), 5),
            (
                "lra_llvm2_trust_ir_substitute_queue_compile_us_total".to_string(),
                120,
            ),
            (
                "lra_llvm2_trust_ir_substitute_queue_compile_us_max".to_string(),
                80,
            ),
        ];
        let canonical = canonical_proof_assert_statistics(statistics.clone());
        assert_eq!(
            canonical.extra_ints.len(),
            4,
            "only the process-wide total and the wall-clock counters are dropped: {:?}",
            canonical.extra_ints
        );
        let mut disagreeing = statistics;
        disagreeing.extra_ints[0].1 += 1;
        assert_ne!(
            canonical,
            canonical_proof_assert_statistics(disagreeing),
            "a per-solve total that disagrees is a disagreement"
        );
    }

    /// Name-level pin of the linked-ay assumption behind the `cert.*`
    /// canonicalization exception (ay >= 0.10): a strict replay
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

    /// A SAT snapshot ay validated and accepted: an honest refutation.
    fn validated_sat_provenance() -> VerificationProvenance {
        let mut evidence = SolveEvidenceSnapshot::default();
        evidence.result = "sat".to_string();
        evidence.model_validated = true;
        evidence.accepted_for_consumer = true;
        evidence.verification.sat_model_validated = true;
        evidence.verification_level = SolveVerificationLevelSnapshot::FullyVerified;
        VerificationProvenance::with_solve_time(Duration::from_millis(5))
            .with_assertion_count(2)
            .with_solve_evidence(Some(evidence))
    }

    /// The wire line must SAY which kind of refutation it carries. A consumer
    /// that reconstructs it from `status=failed` reads every withheld
    /// refutation as a counterexample that never had a model.
    #[test]
    fn diagnostic_wire_line_marks_a_validated_refutation() {
        let provenance = validated_sat_provenance();
        let outcome = VerificationOutcome::new(
            VerificationResult::Failed(trust_wp_ay::Counterexample::empty()),
            Some(provenance.clone()),
        );

        let line = verification_diagnostic_wire_line(
            "demo::f",
            "function_contract",
            &outcome,
            Some(&provenance),
        );

        assert!(line.contains("status=failed"), "{line}");
        assert!(line.contains("refutation=validated"), "{line}");
    }

    /// And the withheld direction: after the gate the verdict is `unknown` and
    /// the line says the refutation was withheld, not that it never existed.
    #[test]
    fn diagnostic_wire_line_marks_a_withheld_refutation() {
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Failed(
            trust_wp_ay::Counterexample::empty(),
        ))
        .apply_mandatory_refutation_authority();

        let line =
            verification_diagnostic_wire_line("demo::f", "function_contract", &outcome, None);

        assert!(line.contains("status=unknown"), "{line}");
        assert!(line.contains("refutation=withheld"), "{line}");
        assert!(
            !line.contains("reason=counterexample"),
            "a withheld refutation must never claim a counterexample: {line}"
        );
    }

    /// An unvalidated refutation that somehow reaches the emitter unGATED is
    /// still labelled honestly.
    #[test]
    fn diagnostic_wire_line_marks_an_ungated_failed_as_withheld() {
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Failed(
            trust_wp_ay::Counterexample::empty(),
        ));

        let line =
            verification_diagnostic_wire_line("demo::f", "function_contract", &outcome, None);

        assert!(line.contains("refutation=withheld"), "{line}");
    }

    #[test]
    fn diagnostic_wire_line_marks_non_refutations_none() {
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Timeout,
        ));

        let line =
            verification_diagnostic_wire_line("demo::f", "function_contract", &outcome, None);

        assert!(line.contains("refutation=none"), "{line}");
    }

    /// The counter's contract: a withheld refutation is counted once, and an
    /// honest one is not counted at all.
    #[test]
    fn withhold_unvalidated_refutation_counts_only_the_withheld() {
        let mut withheld = 0;
        let gated = withhold_unvalidated_refutation(
            VerificationOutcome::without_provenance(VerificationResult::Failed(
                trust_wp_ay::Counterexample::empty(),
            )),
            &mut withheld,
        );
        assert_eq!(withheld, 1);
        assert!(matches!(gated.result, VerificationResult::Unknown(_)));

        let mut honest = 0;
        let kept = withhold_unvalidated_refutation(
            VerificationOutcome::new(
                VerificationResult::Failed(trust_wp_ay::Counterexample::empty()),
                Some(validated_sat_provenance()),
            ),
            &mut honest,
        );
        assert_eq!(honest, 0);
        assert!(matches!(kept.result, VerificationResult::Failed(_)));
    }

    /// The ay boundary usually withholds FIRST, so what reaches the driver is
    /// already `Unknown`. It must still be counted — otherwise the counter reads
    /// zero on every real run, and #3771 (which reads it) keeps amputating the
    /// siblings of an inconclusive (`bug/final_borrows`: the gate fires, the
    /// verdict is honest, and the crate is still abandoned).
    #[test]
    fn a_refutation_withheld_at_the_ay_boundary_is_still_counted() {
        let already_withheld = VerificationOutcome::without_provenance(VerificationResult::Failed(
            trust_wp_ay::Counterexample::empty(),
        ))
        .apply_mandatory_refutation_authority();
        assert!(is_withheld_refutation(&already_withheld.result));

        let mut withheld = 0;
        let passed_through = withhold_unvalidated_refutation(already_withheld, &mut withheld);
        assert_eq!(withheld, 1);
        assert!(matches!(
            passed_through.result,
            VerificationResult::Unknown(_)
        ));
    }

    /// An ordinary `Unknown` is NOT a withheld refutation and must not be
    /// counted as one — #3771 would then ignore a genuine solver timeout.
    #[test]
    fn an_ordinary_unknown_is_not_a_withheld_refutation() {
        let mut withheld = 0;
        let _ = withhold_unvalidated_refutation(
            VerificationOutcome::without_provenance(VerificationResult::Unknown(
                UnknownReason::Timeout,
            )),
            &mut withheld,
        );
        assert_eq!(withheld, 0);

        assert!(!is_withheld_refutation(&VerificationResult::Unknown(
            UnknownReason::SolverMessage("vacuous proof: base is UNSAT".to_string())
        )));
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
        // `VerificationProvenance`); if the two stop describing the same
        // solve, every contractless obligation silently becomes an evidence gap
        // and nothing names which field went missing. Assert each field by
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
    /// that `install_preferred_verified_solve_diagnostics` prevents; if a
    /// provenance merge reintroduces it, the end-to-end acceptance pin above
    /// fails and this one explains why.
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

    /// The synthesized wire line carries `ay_result=timeout`, marks the
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

#[cfg(test)]
mod incomplete_loop_verdict_tests {
    use super::function_counterexample_is_unvalidated;

    #[test]
    fn counterexample_after_incomplete_loop_is_not_a_failure() {
        assert!(function_counterexample_is_unvalidated(Some(
            "loop invariant timeout"
        )));
    }

    #[test]
    fn counterexample_without_incomplete_loop_stays_a_failure() {
        assert!(!function_counterexample_is_unvalidated(None));
    }

    #[test]
    fn proof_after_incomplete_loop_is_not_a_credit() {
        assert!(super::function_proof_leaves_loop_invariant_unproven(Some(
            "loop invariant refutation withheld"
        )));
        assert!(!super::function_proof_leaves_loop_invariant_unproven(None));
    }
}

#[cfg(test)]
mod axiom_dependency_tests {
    use std::{
        collections::{HashMap, HashSet},
        sync::Arc,
    };

    use trust_wp_core::{
        formula::{BinOp, PureExpr},
        logic::LogicFnDef,
    };

    use super::contract_unverified_axiom_deps;
    use crate::callbacks::parsing::{LoopFields, MutBorrowFields, ParsedContract};

    fn logic_fn(full_path: &str, body: PureExpr) -> LogicFnDef {
        let name = full_path.rsplit("::").next().unwrap_or(full_path);
        LogicFnDef::new(
            name.to_owned(),
            full_path.to_owned(),
            vec!["x".to_owned()],
            body,
        )
    }

    fn call(name: &str) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_owned(),
            args: vec![PureExpr::Var("x".to_owned(), None)],
        }
    }

    /// A contract whose only clause is `ensures`.
    fn contract_ensuring(clause: PureExpr) -> ParsedContract {
        ParsedContract {
            requires: vec![],
            ensures: vec![clause],
            result_expr: None,
            result_expr_spanned: None,
            arg_names: vec!["x".to_owned()],
            call_assumptions: vec![],
            pre_loop_call_assumptions: vec![],
            call_obligations: vec![],
            pre_loop_call_obligations: vec![],
            post_loop_call_obligations: vec![],
            returning_path_facts: vec![],
            extraction_fail_closed_reason: None,
            panic_unreachability_obligations: 0,
            user_written_false_obligations: 0,
            proved_dead_edges: Default::default(),
            loop_fields: LoopFields {
                invariants: vec![],
                per_loop_invariants: vec![],
                per_loop_variants: vec![],
                all_loop_spans: vec![],
                variants: vec![],
                loop_analysis: None,
                loop_obligation_groups: vec![],
            },
            mut_borrow: MutBorrowFields {
                mut_borrow_body: None,
                mut_ref_param_names: HashSet::new(),
                state_params: HashSet::new(),
                projected_final_pins: vec![],
                stale_call_final_params: HashSet::new(),
            },
            reborrow_prophecy: None,
        }
    }

    /// `refused` is recorded; `proved` and `hop` are not. `hop`'s body reaches
    /// `refused`, so a contract naming `hop` reaches it too.
    fn crate_logic_fns() -> Vec<LogicFnDef> {
        vec![
            logic_fn("c::other", PureExpr::Var("x".to_owned(), None)),
            logic_fn("c::refused", call("c::other")),
            logic_fn("c::proved", PureExpr::Var("x".to_owned(), None)),
            logic_fn("c::hop", call("c::refused")),
        ]
    }

    fn recorded() -> HashSet<String> {
        std::iter::once("c::refused".to_owned()).collect()
    }

    #[test]
    fn a_contract_that_names_nothing_keeps_its_clean_verdict() {
        let parsed = contract_ensuring(PureExpr::Bool(true));
        assert!(
            contract_unverified_axiom_deps(&parsed, &crate_logic_fns(), &recorded()).is_empty(),
            "a recorded entry elsewhere in the crate is not this contract's caveat"
        );
    }

    #[test]
    fn a_contract_over_another_law_keeps_its_clean_verdict() {
        let parsed = contract_ensuring(call("c::proved"));
        assert!(
            contract_unverified_axiom_deps(&parsed, &crate_logic_fns(), &recorded()).is_empty(),
            "depending on a proved law is not depending on the refused one"
        );
    }

    #[test]
    fn a_contract_naming_the_recorded_entry_keeps_the_caveat() {
        let parsed = contract_ensuring(call("c::refused"));
        assert_eq!(
            contract_unverified_axiom_deps(&parsed, &crate_logic_fns(), &recorded()),
            vec!["c::refused"],
        );
    }

    #[test]
    fn a_contract_reaching_the_recorded_entry_through_a_body_keeps_the_caveat() {
        let parsed = contract_ensuring(call("c::hop"));
        assert_eq!(
            contract_unverified_axiom_deps(&parsed, &crate_logic_fns(), &recorded()),
            vec!["c::refused"],
            "a withdrawn fact two hops away is just as absent"
        );
    }

    #[test]
    fn every_clause_channel_is_scanned_not_just_ensures() {
        let mut parsed = contract_ensuring(PureExpr::Bool(true));
        parsed.loop_fields.invariants.push(PureExpr::BinOp(
            Arc::new(call("c::refused")),
            BinOp::Eq,
            Arc::new(PureExpr::Var("x".to_owned(), None)),
        ));
        assert_eq!(
            contract_unverified_axiom_deps(&parsed, &crate_logic_fns(), &recorded()),
            vec!["c::refused"],
            "a loop invariant is a clause of this contract like any other"
        );

        let mut parsed = contract_ensuring(PureExpr::Bool(true));
        let mut final_values = HashMap::new();
        final_values.insert("v".to_owned(), call("c::refused"));
        parsed.mut_borrow.mut_borrow_body = Some(crate::mir_analysis::MutBorrowBody {
            final_values,
            indexed_writes: vec![],
            resolve_results: None,
            finality: HashMap::new(),
            borrow_id_origins: HashMap::new(),
            delayed_writeback_assumptions: vec![],
            mutation_continued_params: HashSet::new(),
            nested_slot_resolutions: vec![],
            nested_transfer_params: HashSet::new(),
            lent_path_resolutions: vec![],
        });
        assert_eq!(
            contract_unverified_axiom_deps(&parsed, &crate_logic_fns(), &recorded()),
            vec!["c::refused"],
            "a mut-borrow final value carries the same substituted calls"
        );
    }
}
