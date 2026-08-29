// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ay panic classification and catch boundaries.
//!
//! Extracted from `verify/mod.rs` to keep the root verification module below
//! the file-size policy without changing the `crate::verify` helper surface.
//!
//! # Panic classification refinement (#1977)
//!
//! `ay_core::is_ay_panic_reason` matches `"bug: "` with a non-word boundary
//! check that is too broad for trust-wp's use case — it catches messages like
//! `"known bug: ..."` or `"this is a bug: ..."` that are not ay internal
//! panics. This module applies a trust-wp-side refinement layer: `"bug:"` must
//! appear at the very start of the message (case-insensitive). All other
//! ay_core patterns (sort mismatch, expects Bool, conflict verification,
//! Farkas) are specific enough to delegate directly.

use std::panic::{catch_unwind, resume_unwind};

use tracing::warn;

#[cfg(test)]
use super::LoopVerificationResult;
use super::{UnknownReason, VerificationOutcome, VerificationResult};
use crate::{encoder::unsoundness, error::EncodingError};

/// Returns `true` for ay-dpll internal panics: sort mismatches, model validation,
/// term construction, theory conflict verification, Farkas semantic verification,
/// proof-validation failures, and ay-prefetch debug assertion failures.
/// Returns `false` for all other panics (re-raised as programmer errors).
///
/// Applies a tighter filter than `ay_core::is_ay_panic_reason` for the `"bug:"`
/// pattern: requires it at the start of the message rather than anywhere in it.
/// This prevents non-ay panics containing incidental `"bug:"` substrings from
/// being silently swallowed. (#1977, #997, #1111, #885, #1256, #1258, #1259, #1272)
pub(crate) fn is_ay_panic(reason: &str) -> bool {
    let reason_lower = reason.to_lowercase();

    // trust-wp-side extension: recognize ay proof-validation panics that
    // ay_core::is_ay_panic_reason does not yet classify. These occur when ay
    // finds UNSAT correctly but the proof checker rejects the proof or LRAT
    // hints are malformed. The solver result is still valid — only the proof
    // certificate is broken. (#2664)
    if is_proof_validation_panic(&reason_lower) {
        return true;
    }

    // trust-wp-side extension: recognize ay internal assertion panics from
    // ay-prefetch and ay-dpll that ay_core does not classify. These are
    // invariant violations within the solver, not trust-wp encoding errors.
    // Without this, they escape catch_unwind boundaries via resume_unwind
    // and crash the entire rustc process. (#2687, ay#8414)
    if is_ay_internal_assertion_panic(&reason_lower) {
        return true;
    }

    // If ay_core says it's NOT a ay panic, trust that — the upstream filter
    // rejects things like "debug:", "user_bug:", index-out-of-bounds, etc.
    if !ay_core::is_ay_panic_reason(reason) {
        return false;
    }

    // ay_core accepted this panic. Apply the trust-wp-side refinement: if the
    // ONLY reason ay_core matched is the broad "bug:" pattern, tighten it to
    // require "bug:" at the start of the message. The other ay_core patterns
    // (sort mismatch, expects Bool, conflict verification, Farkas) are
    // specific enough to pass through without refinement.
    if is_matched_only_by_bug_marker(&reason_lower) {
        // Require "bug:" at position 0 (case-insensitive, already lowered).
        return reason_lower.starts_with("bug:");
    }

    true
}

/// Returns `true` for ay proof-validation panics that ay_core does not yet
/// classify. These are internal ay errors where the solver found the correct
/// SAT/UNSAT result but the proof certificate is invalid. (#2664)
fn is_proof_validation_panic(reason_lower: &str) -> bool {
    reason_lower.contains("proof checker rejected")
        || reason_lower.contains("lrat hint contains id 0")
        || reason_lower.contains("incrementaltheorystate::pop() underflow")
}

/// Returns `true` for ay internal assertion panics that ay_core does not yet
/// classify. These originate in ay subcrates (ay-prefetch, ay-dpll) and
/// represent internal invariant violations rather than trust-wp programmer errors.
///
/// Recognized patterns:
/// - ay-prefetch bounds assertions: `val_at:`, `set_val:`, `word_at:`, etc.
///   Fires when the SAT solver's value array is indexed out of bounds, typically
///   from a variable-index mismatch during incremental solving. (#2687, ay#8414)
/// - ay-dpll Tseitin encoding assertion: `"tseitin should always"`. Fires when
///   the Tseitin variable mapping is missing an expected atom during incremental
///   bound refinement or split operations. (#2687)
/// - ay-dpll deprecated datatype API panics: `"invalid argument to
///   datatype_constructor"` / `"invalid argument to datatype_selector"`. Fires
///   when trust-wp calls the panicking `datatype_constructor`/`datatype_selector`
///   API with a mismatched declared return sort (e.g., constructor 'Cons'
///   declared with return sort `Uninterpreted("Adt_Cons_Nil")` instead of the
///   expected datatype). These are ay API mis-use errors surfaced as panics
///   by the deprecated panicking variant; the graceful-degradation path is
///   to catch the panic and report Unknown. (#2687)
/// - ay-dpll datatype declaration collision: `"failed to declare datatype"`
///   plus `"re-declaring it as a datatype"`. Fires when a datatype name was
///   already registered as an opaque sort (AY 0.4 registers unknown field
///   sorts on sight) and the panicking `declare_datatype` wrapper surfaces
///   the rejection. Degrades to a fail-closed Unknown. (#2706)
/// - ay-dpll SeqLIA conflict semantic verification: `"conflict semantic
///   verification failed"`. Variant of the existing `"conflict verification
///   failed"` pattern handled by `ay_core`, but the SeqLIA theory phrases its
///   message with "semantic" between "conflict" and "verification" and
///   therefore is not caught upstream. (#2687)
/// - ay-dpll SAT-model storage assertions: `"term_to_var contains index ... but
///   model has only ... vars"`. These indicate a reverse-mapping/model-size
///   mismatch during model extraction and should be reported as a solver
///   panic rather than escaping the verification boundary.
fn is_ay_internal_assertion_panic(reason_lower: &str) -> bool {
    // ay-dpll Tseitin mapping assertion
    if reason_lower.contains("tseitin should always") {
        return true;
    }
    // ay-dpll deprecated datatype API panics (#2687)
    if reason_lower.contains("invalid argument to datatype_constructor")
        || reason_lower.contains("invalid argument to datatype_selector")
    {
        return true;
    }
    // ay-dpll declare_fun signature-collision panic (#result_own / #transpose).
    // The root cause is sort-mangled away at the emitter, but degrade any
    // residual collision to a recoverable Unknown(SolverPanic) rather than a
    // hard ICE re-raised across the process-isolation boundary
    // (process_isolation.rs). Fail-closed: an Unknown never accepts a proof.
    if reason_lower.contains("invalid argument to declare_fun")
        || reason_lower.contains("invalid argument to declare_const")
        || reason_lower.contains("already in use with a different native signature")
        || reason_lower.contains("symbol name") && reason_lower.contains("is reserved")
    {
        return true;
    }
    // ay-dpll declare_datatype collision panic (#2706 generalized). AY 0.4
    // registers a named-but-unknown field sort as an opaque sort on sight and
    // rejects a later declare-datatype for the same name; the dependency-first
    // declaration order in register_adt_decls removes the known cases, but any
    // residual collision (e.g. mutual recursion) reached through the still-
    // panicking declare_datatype callers must degrade to a recoverable
    // Unknown(SolverPanic) rather than a hard ICE. Fail-closed: an Unknown
    // never accepts a proof.
    if reason_lower.contains("failed to declare datatype")
        && reason_lower.contains("re-declaring it as a datatype")
    {
        return true;
    }
    // ay-dpll SeqLIA conflict semantic verification (#2687)
    if reason_lower.contains("conflict semantic verification failed") {
        return true;
    }
    // ay-dpll SAT-model storage assertion: reverse mapping exceeds model size.
    if reason_lower.contains("term_to_var contains index")
        && reason_lower.contains("model has only")
    {
        return true;
    }
    // ay-prefetch debug assertion panics
    const PREFETCH_FNS: &[&str] = &[
        "val_at:",
        "set_val:",
        "neg_val_at:",
        "assign_val:",
        "decision_val:",
        "word_at:",
        "entry_at:",
        "entry_set:",
    ];
    if reason_lower.contains("out of bounds") {
        for prefix in PREFETCH_FNS {
            if reason_lower.starts_with(prefix) {
                return true;
            }
        }
    }
    false
}

/// Returns `true` when the `"bug:"` marker is the sole pattern that caused
/// `ay_core::is_ay_panic_reason` to return `true`. If any other pattern also
/// matches, this returns `false` (meaning the refinement is unnecessary).
fn is_matched_only_by_bug_marker(reason_lower: &str) -> bool {
    let reason_compact: String = reason_lower
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .collect();

    let has_sort_mismatch =
        reason_lower.contains("sort mismatch") || reason_compact.contains("sortmismatch");
    let has_expects_bool = reason_lower.contains("expects bool, got");
    let has_conflict = reason_lower.contains("conflict verification failed");
    let has_farkas = reason_lower.contains("farkas semantic verification failed");

    // If none of the specific patterns matched, the "bug:" marker must be the
    // sole reason ay_core accepted it.
    !has_sort_mismatch && !has_expects_bool && !has_conflict && !has_farkas
}

/// Generic unwind boundary using the tightened trust-wp-side [`is_ay_panic`]
/// classifier. Drop-in replacement for `ay_core::catch_ay_panics` with the
/// narrower "bug:" filter (#1977). All trust-wp call sites that previously used
/// `ay_core::catch_ay_panics` should use this instead.
pub(crate) fn catch_ay_panics_tightened<T, F, G>(f: F, on_ay_panic: G) -> T
where
    F: FnOnce() -> T + std::panic::UnwindSafe,
    G: FnOnce(String) -> T,
{
    match catch_unwind(f) {
        Ok(value) => value,
        Err(payload) => {
            let reason = ay_core::panic_payload_to_string(&*payload);
            if is_ay_panic(&reason) {
                on_ay_panic(reason)
            } else {
                resume_unwind(payload);
            }
        }
    }
}

/// Wrap a verification closure in a catch-unwind boundary using the tightened
/// trust-wp-side [`is_ay_panic`] classifier to isolate ay internal panics (#997).
/// When ay-dpll triggers assertion failures (sort mismatches, model validation
/// errors, etc.), this converts the panic to an `Unknown` result instead of
/// crashing the entire pipeline. Non-ay panics are re-raised via
/// `resume_unwind` so programmer errors still propagate.
/// (#1111, #885, #1256, #1977)
///
/// Restores unsoundness counters on caught panics so stale increments from
/// partial encoding do not pollute subsequent verifications. (#2623)
pub(crate) fn catch_ay_sort_panics<F>(f: F) -> Result<VerificationResult, EncodingError>
where
    F: FnOnce() -> Result<VerificationResult, EncodingError> + std::panic::UnwindSafe,
{
    let pre_snapshot = unsoundness::snapshot();
    let result = match catch_unwind(f) {
        Ok(value) => value,
        Err(payload) => {
            let reason = ay_core::panic_payload_to_string(&*payload);
            if is_ay_panic(&reason) {
                warn!("trust-wp: ay solver panic during verification: {reason}");
                Ok(VerificationResult::Unknown(UnknownReason::SolverPanic(
                    reason,
                )))
            } else {
                resume_unwind(payload);
            }
        }
    };
    // On a caught ay panic, the result is Ok(Unknown) — not Err. Restore
    // counters when the result contains an Unknown with SolverPanic reason,
    // since the partial encoding's increments are stale.
    if let Ok(VerificationResult::Unknown(UnknownReason::SolverPanic(_))) = &result {
        unsoundness::restore(&pre_snapshot);
    }
    result
}

/// Outcome-preserving variant of [`catch_ay_sort_panics`].
///
/// This keeps the normal pipeline provenance for successful solver paths while
/// still converting ay panics into fail-closed `Unknown` outcomes.
pub(crate) fn catch_ay_sort_panics_outcome<F>(f: F) -> Result<VerificationOutcome, EncodingError>
where
    F: FnOnce() -> Result<VerificationOutcome, EncodingError> + std::panic::UnwindSafe,
{
    let pre_snapshot = unsoundness::snapshot();
    let result = match catch_unwind(f) {
        Ok(value) => value,
        Err(payload) => {
            let reason = ay_core::panic_payload_to_string(&*payload);
            if is_ay_panic(&reason) {
                warn!("trust-wp: ay solver panic during verification: {reason}");
                Ok(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(UnknownReason::SolverPanic(reason)),
                ))
            } else {
                resume_unwind(payload);
            }
        }
    };
    if let Ok(outcome) = &result {
        if matches!(
            outcome.result,
            VerificationResult::Unknown(UnknownReason::SolverPanic(_))
        ) {
            unsoundness::restore(&pre_snapshot);
        }
    }
    result
}

/// Like [`catch_ay_sort_panics`] but for loop verification, which returns
/// `LoopVerificationResult`. On a caught ay panic, all sub-results are
/// set to `Unknown` with the panic reason. (#1111, #1256, #1977)
///
/// Restores unsoundness counters on caught panics. (#2623)
#[cfg(test)] // Production loop verification wraps each phase individually (#1398, closed)
pub(crate) fn catch_ay_sort_panics_loop<F>(f: F) -> Result<LoopVerificationResult, EncodingError>
where
    F: FnOnce() -> Result<LoopVerificationResult, EncodingError> + std::panic::UnwindSafe,
{
    let pre_snapshot = unsoundness::snapshot();
    let result = match catch_unwind(f) {
        Ok(value) => value,
        Err(payload) => {
            let reason = ay_core::panic_payload_to_string(&*payload);
            if is_ay_panic(&reason) {
                warn!("trust-wp: ay solver panic during loop verification: {reason}");
                let unknown = VerificationResult::Unknown(UnknownReason::SolverPanic(reason));
                Ok(LoopVerificationResult {
                    initialization: unknown.clone(),
                    preservation: unknown.clone(),
                    postcondition: unknown,
                    variant_nonneg: None,
                    variant_decrease: None,
                })
            } else {
                resume_unwind(payload);
            }
        }
    };
    // On caught ay panic (Ok result with all Unknown sub-results), restore
    // counters to prevent stale increments from partial loop encoding. (#2623)
    if let Ok(ref r) = result {
        if matches!(
            &r.initialization,
            VerificationResult::Unknown(UnknownReason::SolverPanic(_))
        ) {
            unsoundness::restore(&pre_snapshot);
        }
    }
    result
}
