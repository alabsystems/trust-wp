// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A function's verdict includes its own assertions.
//!
//! A `proof_assert!` is a goal of the function it sits in: Creusot puts it in
//! that function's VC. trust-wp proves the two in separate passes — the lanes
//! that own the contract (function-level VC, loop invariant, termination) run
//! first and the in-function assertion pass after them — so a lane that
//! printed `verified ✓` as soon as its own obligations closed credited a
//! function whose assertion was refuted a few lines later in the same run,
//! and the run summary counted it verified (`s31_int_copy_eq_after_inc.rs`).
//!
//! So a lane does not print its credit while the function is being verified:
//! it GRANTS it into a hold, and the hold is settled once the function's own
//! assertions have their verdicts. The credit stands only when none of them
//! was refuted or left unproved; otherwise the function gets ONE verdict line
//! of the assertion's kind and is counted as that, never as verified. Nothing
//! is printed and withdrawn: a reader and the gate both read the lines, so a
//! function never carries a `verified` line beside an unproved assertion of
//! its own.

use std::collections::HashMap;

use rustc_hir::def_id::DefId;

use super::reporting::{ProofAssertCounters, VerificationCounters};

/// Which positive counter a credit bumps when it stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::callbacks) enum CreditKind {
    /// A clean `verified`; `native_only` additionally counts it among the
    /// proofs only ay itself can re-check (it is still a `verified`).
    Verified { native_only: bool },
    /// `verified*`: the proof leans on logic-function axioms nobody proved.
    VerifiedWithAxiomDeps,
}

/// One lane's positive verdict on a function: the lines it prints and the
/// counter it bumps, kept together so a held credit is emitted exactly as the
/// lane would have printed it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::callbacks) struct FunctionCredit {
    lines: Vec<String>,
    kind: CreditKind,
}

impl FunctionCredit {
    pub(in crate::callbacks) fn new(kind: CreditKind, headline: String) -> Self {
        Self {
            lines: vec![headline],
            kind,
        }
    }

    /// A line printed under the headline (`  at ..`, `  unverified axiom: ..`).
    #[must_use]
    pub(in crate::callbacks) fn with_line(mut self, line: String) -> Self {
        self.lines.push(line);
        self
    }
}

/// What a function's own assertions came to, as far as its credit is concerned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::callbacks) enum OwnAssertions {
    /// Every assertion proved — including a function with none.
    AllProved,
    /// At least one assertion was refuted.
    Refuted,
    /// None refuted, but at least one got no proof (unknown, error, evidence
    /// gap, withheld refutation, inconclusive, skipped on budget, panicked).
    Unproved,
}

/// The assertion counters a function's own assertions are measured against.
///
/// Measured as a delta around the one pass that runs the function's in-body
/// assertions. Every assertion that pass examines ends in exactly one of
/// `verified`, `failed`, `errors` or `inconclusive` (an evidence gap and a
/// withheld refutation are counted in `errors` too), so anything but a
/// `verified` shows up in `failed` or `unproved` here. A `#[trusted]`
/// assertion is skipped by design and moves nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::callbacks) struct AssertionTally {
    failed: usize,
    unproved: usize,
}

impl AssertionTally {
    pub(in crate::callbacks) fn take(pa_counters: &ProofAssertCounters) -> Self {
        Self {
            failed: pa_counters.failed,
            unproved: pa_counters.errors + pa_counters.inconclusive,
        }
    }

    /// The verdicts recorded between `before` and `self`.
    pub(in crate::callbacks) fn since(self, before: Self) -> OwnAssertions {
        if self.failed > before.failed {
            OwnAssertions::Refuted
        } else if self.unproved > before.unproved {
            OwnAssertions::Unproved
        } else {
            OwnAssertions::AllProved
        }
    }
}

/// Run-level credit bookkeeping carried on `VerificationCounters`.
#[derive(Debug, Default)]
pub(in crate::callbacks) struct CreditLedger {
    /// `Some` while one function is being verified: its lanes' credits wait
    /// here for its assertions. `None` everywhere else, where a credit has no
    /// in-body assertion of its function still to come and is emitted at once:
    /// the logic lane answers a logic function's own assertions BEFORE it
    /// grants, and the reporting unit tests have none.
    held: Option<Vec<FunctionCredit>>,
    /// The credits that stood, by function: what a LATER assertion verdict on
    /// the same function would have to withdraw.
    granted: HashMap<DefId, Vec<CreditKind>>,
}

/// Grant a lane's positive verdict: held while the function's own assertions
/// are pending, emitted at once otherwise.
pub(in crate::callbacks) fn grant_function_credit(
    counters: &mut VerificationCounters,
    credit: FunctionCredit,
) {
    if let Some(held) = counters.credit_ledger.held.as_mut() {
        held.push(credit);
        return;
    }
    emit_credit(&credit, counters);
}

fn emit_credit(credit: &FunctionCredit, counters: &mut VerificationCounters) {
    for line in &credit.lines {
        eprintln!("{line}");
    }
    match credit.kind {
        CreditKind::Verified { native_only } => {
            counters.verified += 1;
            if native_only {
                counters.verified_native_only += 1;
            }
        }
        CreditKind::VerifiedWithAxiomDeps => counters.verified_with_axiom_deps += 1,
    }
}

/// Start holding credits for the function about to be verified.
pub(in crate::callbacks) fn hold_function_credits(counters: &mut VerificationCounters) {
    counters.credit_ledger.held = Some(Vec::new());
}

/// Drop credits whose function never reached settlement (its verification
/// panicked): they were never printed or counted, and they never will be.
pub(in crate::callbacks) fn discard_held_credits(counters: &mut VerificationCounters) -> usize {
    counters
        .credit_ledger
        .held
        .take()
        .map_or(0, |held| held.len())
}

/// Settle the held credits of one function against its own assertions.
///
/// Returns the lines printed, in order, so the decision is testable without
/// capturing stderr.
pub(in crate::callbacks) fn settle_function_credits(
    counters: &mut VerificationCounters,
    def_id: DefId,
    def_path: &str,
    loc: &str,
    own: OwnAssertions,
) -> Vec<String> {
    let held = counters.credit_ledger.held.take().unwrap_or_default();
    if held.is_empty() {
        // No lane credited the function: its verdict line (FAILED, unknown,
        // vacuous, ...) is already out and already counted, and an assertion
        // that did not prove cannot make it any less verified.
        return Vec::new();
    }
    match own {
        OwnAssertions::AllProved => {
            let mut printed = Vec::new();
            for credit in &held {
                emit_credit(credit, counters);
                printed.extend(credit.lines.iter().cloned());
            }
            counters
                .credit_ledger
                .granted
                .entry(def_id)
                .or_default()
                .extend(held.iter().map(|credit| credit.kind));
            printed
        }
        OwnAssertions::Refuted => {
            counters.failed += 1;
            print_lines(own_assertion_verdict_lines(def_path, loc, own))
        }
        OwnAssertions::Unproved => {
            counters.errors += 1;
            print_lines(own_assertion_verdict_lines(def_path, loc, own))
        }
    }
}

/// A late assertion verdict on a function whose credit already stood.
///
/// Unreachable while the two assertion passes discover a body's assertions
/// identically: the in-function pass then answers every assertion the
/// standalone pass would, and the standalone pass declines a function the
/// in-function pass answered. Should the standalone pass ever answer for a
/// credited function, the credit is withdrawn rather than left standing on an
/// assertion nobody proved.
pub(in crate::callbacks) fn withdraw_on_late_assertions(
    counters: &mut VerificationCounters,
    def_id: DefId,
    def_path: &str,
    loc: &str,
    own: OwnAssertions,
) -> Vec<String> {
    if own == OwnAssertions::AllProved {
        return Vec::new();
    }
    let Some(kinds) = counters.credit_ledger.granted.remove(&def_id) else {
        return Vec::new();
    };
    for kind in kinds {
        match kind {
            CreditKind::Verified { native_only } => {
                counters.verified = counters.verified.saturating_sub(1);
                if native_only {
                    counters.verified_native_only = counters.verified_native_only.saturating_sub(1);
                }
            }
            CreditKind::VerifiedWithAxiomDeps => {
                counters.verified_with_axiom_deps =
                    counters.verified_with_axiom_deps.saturating_sub(1);
            }
        }
    }
    if own == OwnAssertions::Refuted {
        counters.failed += 1;
    } else {
        counters.errors += 1;
    }
    let mut lines = vec![format!(
        "trust-wp: {def_path} error: verdict withdrawn - its own proof_assert was not proved"
    )];
    lines.extend(
        own_assertion_verdict_lines(def_path, loc, own)
            .into_iter()
            .skip(1),
    );
    print_lines(lines)
}

fn print_lines(lines: Vec<String>) -> Vec<String> {
    for line in &lines {
        eprintln!("{line}");
    }
    lines
}

/// The one verdict line (and its notes) of a function whose lanes proved
/// everything they owned but whose own assertion did not.
fn own_assertion_verdict_lines(def_path: &str, loc: &str, own: OwnAssertions) -> Vec<String> {
    let headline = match own {
        OwnAssertions::Refuted => format!("trust-wp: {def_path} FAILED \u{2717} (proof_assert)"),
        OwnAssertions::Unproved | OwnAssertions::AllProved => {
            format!("trust-wp: {def_path} unknown (proof_assert not proved)")
        }
    };
    vec![
        headline,
        format!("  at {loc}"),
        "  note: a proof_assert! is a goal of the function it sits in; its contract \
         lanes closed, but the assertion reported above did not"
            .to_string(),
    ]
}

#[cfg(test)]
mod tests;
