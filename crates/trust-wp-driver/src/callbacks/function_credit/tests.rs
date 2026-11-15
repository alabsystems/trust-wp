// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use rustc_hir::def_id::{CrateNum, DefId, DefIndex};

use super::*;
use crate::callbacks::reporting::format_verification_summary;

fn def(index: u32) -> DefId {
    DefId {
        krate: CrateNum::from_u32(0),
        index: DefIndex::from_u32(index),
    }
}

fn verified(def_path: &str) -> FunctionCredit {
    FunctionCredit::new(
        CreditKind::Verified { native_only: false },
        format!("trust-wp: {def_path} verified \u{2713}"),
    )
}

/// The adversarial gate's reading of a line as a credit on a function, in any
/// lane's spelling (`run_adversarial.py::_ANY_CREDIT_RE`).
fn reads_as_credit(line: &str) -> bool {
    let Some(rest) = line.strip_prefix("trust-wp: ") else {
        return false;
    };
    let Some((_, verdict)) = rest.split_once(' ') else {
        return false;
    };
    verdict.starts_with("verified*") || verdict.starts_with("verified \u{2713}")
}

fn tally(failed: usize, errors: usize, inconclusive: usize) -> AssertionTally {
    AssertionTally::take(&ProofAssertCounters {
        failed,
        errors,
        inconclusive,
        ..ProofAssertCounters::default()
    })
}

#[test]
fn a_credit_outside_a_hold_is_counted_at_once() {
    let mut counters = VerificationCounters::default();
    grant_function_credit(&mut counters, verified("g"));
    assert_eq!(counters.verified, 1);
}

#[test]
fn a_held_credit_is_not_counted_before_settlement() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    grant_function_credit(&mut counters, verified("f"));
    assert_eq!(
        counters.verified, 0,
        "a held credit must wait for the assertions"
    );
}

#[test]
fn a_credit_stands_when_every_own_assertion_proved() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    grant_function_credit(&mut counters, verified("f"));
    let printed = settle_function_credits(
        &mut counters,
        def(1),
        "f",
        "src/lib.rs:1:1",
        OwnAssertions::AllProved,
    );
    assert_eq!(printed, vec!["trust-wp: f verified \u{2713}".to_string()]);
    assert_eq!(
        (counters.verified, counters.failed, counters.errors),
        (1, 0, 0)
    );
}

#[test]
fn a_refuted_own_assertion_makes_the_function_failed_and_never_verified() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    grant_function_credit(&mut counters, verified("int_copy_eq_wrong"));
    let printed = settle_function_credits(
        &mut counters,
        def(1),
        "int_copy_eq_wrong",
        "src/lib.rs:1:1",
        OwnAssertions::Refuted,
    );
    assert_eq!(
        printed.first().map(String::as_str),
        Some("trust-wp: int_copy_eq_wrong FAILED \u{2717} (proof_assert)")
    );
    assert!(
        !printed.iter().any(|line| reads_as_credit(line)),
        "no credit line may reach the output: {printed:?}"
    );
    assert_eq!(
        (counters.verified, counters.failed, counters.errors),
        (0, 1, 0)
    );
}

#[test]
fn an_unproved_own_assertion_makes_the_function_unknown() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    grant_function_credit(&mut counters, verified("c"));
    let printed = settle_function_credits(
        &mut counters,
        def(1),
        "c",
        "src/lib.rs:1:1",
        OwnAssertions::Unproved,
    );
    assert_eq!(
        printed.first().map(String::as_str),
        Some("trust-wp: c unknown (proof_assert not proved)")
    );
    assert!(!printed.iter().any(|line| reads_as_credit(line)));
    assert_eq!(
        (counters.verified, counters.failed, counters.errors),
        (0, 0, 1)
    );
}

/// A recursive function is credited by the termination lane AND the
/// function-level VC; one refuted assertion withholds both and the function is
/// counted once, as the one line printed for it says.
#[test]
fn every_lane_credit_of_the_function_is_withheld_and_it_counts_once() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    grant_function_credit(
        &mut counters,
        FunctionCredit::new(
            CreditKind::Verified { native_only: false },
            "trust-wp: rec_five verified \u{2713} (termination)".to_string(),
        ),
    );
    grant_function_credit(&mut counters, verified("rec_five"));
    let printed = settle_function_credits(
        &mut counters,
        def(1),
        "rec_five",
        "src/lib.rs:1:1",
        OwnAssertions::Refuted,
    );
    assert!(!printed
        .iter()
        .any(|line| line.contains("verified \u{2713}")));
    assert_eq!((counters.verified, counters.failed), (0, 1));
    assert_eq!(
        format_verification_summary(&counters, 0),
        "trust-wp: 0 verified, 1 failed, 0 errors",
        "the summary must count what the per-function line says"
    );
}

#[test]
fn a_function_no_lane_credited_gets_no_second_verdict() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    // Its lane already printed and counted `unknown (...)`.
    counters.errors += 1;
    let printed = settle_function_credits(
        &mut counters,
        def(1),
        "f",
        "src/lib.rs:1:1",
        OwnAssertions::Refuted,
    );
    assert!(printed.is_empty());
    assert_eq!(
        (counters.verified, counters.failed, counters.errors),
        (0, 0, 1)
    );
}

#[test]
fn a_standing_credit_keeps_its_kind() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    grant_function_credit(
        &mut counters,
        FunctionCredit::new(
            CreditKind::Verified { native_only: true },
            "trust-wp: f verified \u{2713}".to_string(),
        ),
    );
    grant_function_credit(
        &mut counters,
        FunctionCredit::new(
            CreditKind::VerifiedWithAxiomDeps,
            "trust-wp: g verified* (depends on 1 unverified axiom(s))".to_string(),
        )
        .with_line("  unverified axiom: ax".to_string()),
    );
    let printed = settle_function_credits(
        &mut counters,
        def(1),
        "f",
        "src/lib.rs:1:1",
        OwnAssertions::AllProved,
    );
    assert_eq!(
        printed.len(),
        3,
        "every line of every credit is printed: {printed:?}"
    );
    assert_eq!(
        (
            counters.verified,
            counters.verified_native_only,
            counters.verified_with_axiom_deps
        ),
        (1, 1, 1)
    );
}

#[test]
fn a_panicked_function_loses_its_held_credit_and_the_hold_ends() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    grant_function_credit(&mut counters, verified("f"));
    assert_eq!(discard_held_credits(&mut counters), 1);
    assert_eq!(counters.verified, 0);
    // With no hold open, a later credit (a logic function's, say) is not
    // swallowed by the dead function's hold.
    grant_function_credit(&mut counters, verified("g"));
    assert_eq!(counters.verified, 1);
}

#[test]
fn the_tally_reads_a_refutation_before_an_unproved_assertion() {
    let before = tally(0, 0, 0);
    assert_eq!(tally(1, 1, 0).since(before), OwnAssertions::Refuted);
    assert_eq!(tally(0, 1, 0).since(before), OwnAssertions::Unproved);
    assert_eq!(tally(0, 0, 1).since(before), OwnAssertions::Unproved);
    assert_eq!(tally(0, 0, 0).since(before), OwnAssertions::AllProved);
}

#[test]
fn the_tally_is_blind_to_verdicts_recorded_before_the_function() {
    // Earlier functions' failures are not this function's.
    let before = tally(3, 2, 1);
    let after = AssertionTally::take(&ProofAssertCounters {
        verified: 4,
        failed: 3,
        errors: 2,
        inconclusive: 1,
        ..ProofAssertCounters::default()
    });
    assert_eq!(after.since(before), OwnAssertions::AllProved);
}

#[test]
fn an_evidence_gap_and_a_withheld_refutation_are_unproved() {
    // Both are counted in `errors` by the proof_assert reporter.
    let before = AssertionTally::take(&ProofAssertCounters::default());
    let after = AssertionTally::take(&ProofAssertCounters {
        errors: 2,
        evidence_gaps: 1,
        refutations_withheld: 1,
        ..ProofAssertCounters::default()
    });
    assert_eq!(after.since(before), OwnAssertions::Unproved);
}

#[test]
fn a_late_unproved_assertion_withdraws_a_standing_credit_once() {
    let mut counters = VerificationCounters::default();
    hold_function_credits(&mut counters);
    grant_function_credit(&mut counters, verified("f"));
    settle_function_credits(&mut counters, def(1), "f", "l", OwnAssertions::AllProved);
    assert_eq!(counters.verified, 1);

    let printed =
        withdraw_on_late_assertions(&mut counters, def(1), "f", "l", OwnAssertions::Refuted);
    assert_eq!(
        printed.first().map(String::as_str),
        Some("trust-wp: f error: verdict withdrawn - its own proof_assert was not proved")
    );
    assert_eq!((counters.verified, counters.failed), (0, 1));
    let again =
        withdraw_on_late_assertions(&mut counters, def(1), "f", "l", OwnAssertions::Refuted);
    assert!(again.is_empty(), "a credit is withdrawn once");
    assert_eq!((counters.verified, counters.failed), (0, 1));
}

#[test]
fn a_late_verdict_touches_nothing_it_did_not_credit() {
    let mut counters = VerificationCounters::default();
    counters.verified = 2;
    assert!(
        withdraw_on_late_assertions(&mut counters, def(7), "h", "l", OwnAssertions::Unproved)
            .is_empty()
    );
    assert!(
        withdraw_on_late_assertions(&mut counters, def(7), "h", "l", OwnAssertions::AllProved)
            .is_empty()
    );
    assert_eq!((counters.verified, counters.errors), (2, 0));
}
