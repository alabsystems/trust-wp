// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Soundness lock tests for #2663: zero false-accepts, zero demoting passes,
//! vacuity guard completion.
//!
//! These tests enforce the soundness invariants required for 100% Creusot
//! replacement. They are regression guards — any change to the unsoundness
//! tracking, demotion pipeline, or vacuity detection must update these tests
//! explicitly.
//!
//! ## Test categories
//!
//! 1. **Eliminated category regression**: Confirms that `ClosureBodyTrueDefault`
//!    and `BitwiseUfApproximation` remain eliminated (zero production sites).
//! 2. **Demotion pipeline completeness**: Every demoting category, when fired,
//!    correctly demotes `Verified` to `Unknown(Demoted)`.
//! 3. **Non-demotion preservation**: LOW and ELIMINATED categories do not demote.
//! 4. **Vacuity guard integration**: Vacuous UNSAT is caught and rejected.
//! 5. **Soundness budget tracking**: Total demoting sites tracked explicitly.
//! 6. **OpaqueCallTrueAssumption → requires(false)**: The Creusot approach is
//!    confirmed to make proofs impossible (not just demoted).
//! 7. **Category completeness**: Every variant in `UnsoundnessCategory` has a
//!    risk level, production site count, and display string.

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use super::helpers::*;
use crate::{
    encoder::{
        unsoundness::{self, RiskLevel, UnsoundnessCategory},
        AYEncoder, AssertionPhase,
    },
    verify::{
        demote_if_unsound, verify_function_with_modes, UnknownReason, VerificationRequest,
        VerificationResult,
    },
};

// ────────────────────────────────────────────────────────────────────
// 1. Eliminated category regression tests
// ────────────────────────────────────────────────────────────────────

/// ClosureBodyTrueDefault was eliminated in #2541: closure bodies no longer
/// default to `Bool(true)`. This test confirms the classification is stable.
#[test]
#[timeout(30000)]
fn eliminated_closure_body_true_default_stays_eliminated() {
    let cat = UnsoundnessCategory::ClosureBodyTrueDefault;
    assert_eq!(
        cat.risk_level(),
        RiskLevel::Eliminated,
        "ClosureBodyTrueDefault must remain ELIMINATED (#2541)"
    );
    assert_eq!(
        cat.expected_production_sites(),
        0,
        "ELIMINATED category must have 0 production sites"
    );
    assert!(!cat.is_demoting(), "ELIMINATED category must not demote");
}

/// BitwiseUfApproximation was eliminated in #2666: BV mode is always-on.
/// This test confirms the classification is stable.
#[test]
#[timeout(30000)]
fn eliminated_bitwise_uf_approximation_stays_eliminated() {
    let cat = UnsoundnessCategory::BitwiseUfApproximation;
    assert_eq!(
        cat.risk_level(),
        RiskLevel::Eliminated,
        "BitwiseUfApproximation must remain ELIMINATED (#2666)"
    );
    assert_eq!(
        cat.expected_production_sites(),
        0,
        "ELIMINATED category must have 0 production sites"
    );
    assert!(!cat.is_demoting(), "ELIMINATED category must not demote");
}

/// Eliminated categories must never demote — incrementing them during
/// verification should leave Verified unchanged.
#[test]
#[timeout(30000)]
fn eliminated_categories_do_not_demote_verified() {
    let eliminated: Vec<_> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.is_eliminated())
        .collect();

    assert!(
        !eliminated.is_empty(),
        "there should be at least one eliminated category"
    );

    for cat in &eliminated {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        unsoundness::increment(**cat);

        let verified = VerificationResult::Verified(None);
        let result = demote_if_unsound(&before, verified);
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "ELIMINATED category {cat} ({}) should NOT demote Verified: {result:?}",
            cat.risk_level()
        );
        unsoundness::reset();
    }
}

// ────────────────────────────────────────────────────────────────────
// 2. Demotion pipeline completeness: every demoting category demotes
// ────────────────────────────────────────────────────────────────────

/// Every HIGH-risk category must demote Verified to Unknown(Demoted).
#[test]
#[timeout(30000)]
fn every_high_risk_category_demotes_verified() {
    let high_cats: Vec<_> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::High)
        .collect();

    assert_eq!(
        high_cats.len(),
        7,
        "expected 7 HIGH risk categories (5 original + FinalCollapseRefused (Fix A) \
         + OpaqueClosureValueFallback (vacfix: opaque Bool closure value whose \
         ite(b,1,0) promotion fabricates a {{0,1}} bound)), got {}: {high_cats:?}",
        high_cats.len()
    );

    for cat in &high_cats {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        unsoundness::increment(**cat);

        let verified = VerificationResult::Verified(None);
        let result = demote_if_unsound(&before, verified);
        match &result {
            VerificationResult::Unknown(UnknownReason::Demoted(msg)) => {
                let cat_display = format!("{cat}");
                assert!(
                    msg.contains(&cat_display),
                    "demotion message for {cat} should mention the category: {msg}"
                );
            }
            other => panic!(
                "HIGH risk category {cat} should demote Verified to Unknown(Demoted), got: {other:?}"
            ),
        }
        unsoundness::reset();
    }
}

/// Every MEDIUM-risk category must demote Verified to Unknown(Demoted).
#[test]
#[timeout(30000)]
fn every_medium_risk_category_demotes_verified() {
    let medium_cats: Vec<_> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::Medium)
        .collect();

    assert_eq!(
        medium_cats.len(),
        3,
        "expected 3 MEDIUM risk categories, got {}: {medium_cats:?}",
        medium_cats.len()
    );

    for cat in &medium_cats {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        unsoundness::increment(**cat);

        let verified = VerificationResult::Verified(None);
        let result = demote_if_unsound(&before, verified);
        match &result {
            VerificationResult::Unknown(UnknownReason::Demoted(msg)) => {
                let cat_display = format!("{cat}");
                assert!(
                    msg.contains(&cat_display),
                    "demotion message for {cat} should mention the category: {msg}"
                );
            }
            other => panic!(
                "MEDIUM risk category {cat} should demote Verified to Unknown(Demoted), got: {other:?}"
            ),
        }
        unsoundness::reset();
    }
}

// ────────────────────────────────────────────────────────────────────
// 3. Non-demotion preservation: LOW and ELIMINATED don't demote
// ────────────────────────────────────────────────────────────────────

/// Every LOW-risk category must NOT demote Verified.
#[test]
#[timeout(30000)]
fn every_low_risk_category_preserves_verified() {
    let low_cats: Vec<_> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::Low)
        .collect();

    assert_eq!(
        low_cats.len(),
        11,
        "expected 11 LOW risk categories (10 original + PremiseNeutralizedEq), got {}: {low_cats:?}",
        low_cats.len()
    );

    for cat in &low_cats {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        unsoundness::increment(**cat);

        let verified = VerificationResult::Verified(None);
        let result = demote_if_unsound(&before, verified);
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "LOW risk category {cat} should NOT demote Verified: {result:?}"
        );
        unsoundness::reset();
    }
}

// ────────────────────────────────────────────────────────────────────
// 4. Vacuity guard integration tests
// ────────────────────────────────────────────────────────────────────

/// Vacuity guard: contradictory preconditions should not produce a Verified
/// result. The solver may find UNSAT, but the vacuity check should detect
/// that the negated postcondition was irrelevant.
#[test]
#[timeout(30000)]
fn vacuity_guard_catches_contradictory_preconditions() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);

    // Contradictory preconditions: x > 0 AND x < 0
    encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
        let pos = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(pos);
        let neg = encoder.solver_mut().lt(x, zero);
        encoder.assert_term(neg);
    });

    // Any negated postcondition — should be vacuously UNSAT
    let y = encoder.solver_mut().declare_const("y", Sort::Int);
    let five = encoder.solver_mut().int_const(5);
    let (result, vacuity) = encoder.with_negated_goal_label_prefix(
        "__trust_wp_negated_goal_test".to_string(),
        |encoder| {
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
                let goal = encoder.solver_mut().gt(y, five);
                encoder.assert_term(goal);
            });
            (encoder.check_sat(), encoder.is_vacuous_unsat())
        },
    );

    assert_eq!(
        result,
        SolveResult::unsat(),
        "contradictory preconditions should make formula UNSAT"
    );
    assert!(
        matches!(vacuity, Ok(true)),
        "vacuity guard should detect vacuous proof: {vacuity:?}"
    );
}

/// Vacuity guard: genuine proof (non-vacuous) should pass.
#[test]
#[timeout(30000)]
fn vacuity_guard_allows_genuine_proof() {
    let mut encoder = AYEncoder::new_pure();

    let x = encoder.solver_mut().declare_const("x", Sort::Int);
    let zero = encoder.solver_mut().int_const(0);
    let ten = encoder.solver_mut().int_const(10);

    // Consistent preconditions: x > 0 AND x < 10
    encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
        let lower = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(lower);
        let upper = encoder.solver_mut().lt(x, ten);
        encoder.assert_term(upper);
    });

    // Negated postcondition that creates a genuine contradiction: NOT(x > 0)
    let (result, vacuity) = encoder.with_negated_goal_label_prefix(
        "__trust_wp_negated_goal_test_genuine".to_string(),
        |encoder| {
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
                let negated = encoder.solver_mut().le(x, zero);
                encoder.assert_term(negated);
            });
            (encoder.check_sat(), encoder.is_vacuous_unsat())
        },
    );

    assert_eq!(
        result,
        SolveResult::unsat(),
        "precondition implies postcondition — should be UNSAT"
    );
    assert!(
        matches!(vacuity, Ok(false)),
        "genuine proof should NOT be flagged as vacuous: {vacuity:?}"
    );
}

// ────────────────────────────────────────────────────────────────────
// 5. Soundness budget tracking
// ────────────────────────────────────────────────────────────────────

/// The total demoting production site budget is tracked explicitly.
/// Any increase requires review of the new site for soundness impact.
#[test]
#[timeout(30000)]
fn soundness_budget_total_demoting_sites() {
    let total = UnsoundnessCategory::total_demoting_production_sites();
    // Current budget: 15 sites across 9 demoting categories.
    // HIGH (8): SortFallbackToInt(2) + LetAssumeDropped(2) + SpecAxiomDropped(1)
    //           + OpaqueCallTrueAssumption(1) + IntegerCastIdentity(1)
    //           + FinalCollapseRefused(2) — Fix A of the Final-collapse audit,
    //             sort-based arm + constant-carrier arm (tract19). Both sites
    //             are themselves fail-closed (they return EncodingError instead
    //             of the unsound ^x -> x collapse); the counter is demotion
    //             defense-in-depth, so the budget increase does not add a
    //             false-proof origin — it REMOVES uncounted ones. The
    //             constant-carrier arm closed a LIVE false accept: a prophecy
    //             over a constant carrier (`Final(Int(3))`, minted by the
    //             driver's borrow-chain advance) folded away in
    //             encode_wrapper_rewrite's "wrappers are no-ops on literals"
    //             arm, so `#[ensures(result@ == 3)]` verified on a function
    //             returning 99.
    //           + OpaqueClosureValueFallback(1) — vacfix: the encoder
    //             substitutes an opaque Bool constant for a closure VALUE and
    //             KEEPS ENCODING (unlike every other UnsupportedConstructSkip
    //             site, which returns an EncodingError). Its arbitrary Bool
    //             sort is promoted by ite(b,1,0) into a fabricated {0,1}
    //             bound, so the site is a GENUINE false-proof origin; it was
    //             already live and merely mis-booked as LOW/non-demoting.
    // MEDIUM (7): PanicRecoveryFalse(3) + SortFallbackToIntFromLogicFn(2)
    //             + UnconstrainedResultVar(2)
    assert_eq!(
        total, 19,
        "soundness budget changed — review all new/removed sites for soundness impact"
    );
}

/// The soundness budget should never increase without explicit acknowledgment.
/// This test verifies that the demoting production site count is the minimum
/// achievable given current architecture.
#[test]
#[timeout(30000)]
fn soundness_budget_high_risk_sites() {
    let high_total: usize = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::High)
        .map(|c| c.expected_production_sites())
        .sum();
    assert_eq!(
        high_total, 12,
        "HIGH risk production site count changed: {high_total} — \
         7 (#2663 Phase 1a) + FinalCollapseRefused(2) (Fix A, fail-closed \
         refusal sites: sort-based + constant-carrier arms) \
         + SpecAxiomDropped(+2): the two extra sites were \
         always live, only the declared count was stale \
         + OpaqueClosureValueFallback(1) (vacfix, reclassified from LOW) \
         (see soundness_budget_total_demoting_sites)"
    );
}

#[test]
#[timeout(30000)]
fn soundness_budget_medium_risk_sites() {
    let medium_total: usize = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::Medium)
        .map(|c| c.expected_production_sites())
        .sum();
    assert_eq!(
        medium_total, 7,
        "MEDIUM risk production site count changed: {medium_total}"
    );
}

// ────────────────────────────────────────────────────────────────────
// 6. OpaqueCallTrueAssumption: requires(false) makes proof impossible
// ────────────────────────────────────────────────────────────────────

/// When OpaqueCallTrueAssumption fires AND requires(false) is injected,
/// the proof should be impossible (Failed), not just demoted.
/// This validates the Creusot approach implemented in fallback.rs.
#[test]
#[timeout(30000)]
fn opaque_call_with_requires_false_makes_proof_fail() {
    unsoundness::reset();

    // Simulate what fallback.rs does: push Bool(false) as obligation
    // This means the precondition includes `false`, making UNSAT trivial
    // (but vacuously so — the postcondition is irrelevant)
    let requires = vec![
        gt(var("x"), int(0)), // normal precondition
        bool_expr(false),     // requires(false) from opaque call
    ];
    let ensures = vec![gt(var("result"), int(0))];

    let return_expr = add(var("x"), int(1));
    let request = VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr));

    let result = verify_function_with_modes(request).expect("should not error");

    match &result {
        VerificationResult::Unknown(reason) => {
            let reason_str = reason.as_str();
            assert!(
                reason_str.contains("vacuous"),
                "requires(false) should be reported as vacuous: {reason_str}"
            );
        }
        other => panic!("requires(false) should produce Unknown(vacuous), got: {other:?}"),
    }

    unsoundness::reset();
}

/// Regression test for #2663: LetObligation with constant-false obligation
/// must return an encoding error, NOT produce a false "Verified."
///
/// Before the fix, the non-Bool body path in `encode_let_obligation` asserted
/// `false` as a solver fact, making the context trivially UNSAT → "Verified"
/// (unsound). The Bool body path was accidentally correct (`and(false, body)`
/// propagated correctly). Now both paths return `EncodingError::Unsupported`,
/// preventing false proofs regardless of body sort.
///
/// This tests the encoder-level guard. The driver-level `requires(false)`
/// injection (tested above) is the upstream source of these obligations.
#[test]
#[timeout(30000)]
fn let_obligation_false_non_bool_body_no_false_verified() {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;

    // Non-Bool body case: LetObligation { obligation: false, body: x + 1 }
    // Previously: assert(false) → UNSAT → false "Verified"
    // Now: encoding error → no false proof
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Bool(false)),
        body: Arc::new(add(var("x"), int(1))),
    };
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "LetObligation(false, non-Bool body) must error, not produce a term: {result:?}"
    );

    // Bool body case: same result now
    let mut encoder2 = AYEncoder::new();
    let expr2 = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Bool(false)),
        body: Arc::new(PureExpr::Bool(true)),
    };
    let result2 = encoder2.encode_pure(&expr2);
    assert!(
        result2.is_err(),
        "LetObligation(false, Bool body) must also error: {result2:?}"
    );
}

// ────────────────────────────────────────────────────────────────────
// 7. Category completeness and consistency
// ────────────────────────────────────────────────────────────────────

/// Every category in ALL must have:
/// - A valid risk level
/// - A Display implementation that produces snake_case
/// - An expected_production_sites count consistent with its risk level
/// - is_demoting() consistent with risk_level().is_demoting()
#[test]
#[timeout(30000)]
fn all_categories_complete_and_consistent() {
    for cat in UnsoundnessCategory::ALL {
        // Risk level is valid
        let risk = cat.risk_level();
        assert!(
            matches!(
                risk,
                RiskLevel::High | RiskLevel::Medium | RiskLevel::Low | RiskLevel::Eliminated
            ),
            "category {cat} has unexpected risk level"
        );

        // Display produces non-empty snake_case
        let display = format!("{cat}");
        assert!(
            !display.is_empty(),
            "Display for category should be non-empty"
        );
        assert!(
            display.chars().all(|c| c.is_ascii_lowercase() || c == '_'),
            "Display should be snake_case: {display}"
        );

        // is_demoting consistent with risk level
        assert_eq!(
            cat.is_demoting(),
            risk.is_demoting(),
            "is_demoting() disagrees with risk_level().is_demoting() for {cat}"
        );

        // is_eliminated consistent with risk level
        assert_eq!(
            cat.is_eliminated(),
            risk == RiskLevel::Eliminated,
            "is_eliminated() disagrees with risk_level() for {cat}"
        );

        // Eliminated categories have zero sites
        if cat.is_eliminated() {
            assert_eq!(
                cat.expected_production_sites(),
                0,
                "eliminated category {cat} must have 0 production sites"
            );
        }

        // Non-eliminated categories have at least one site
        if !cat.is_eliminated() {
            assert!(
                cat.expected_production_sites() > 0,
                "non-eliminated category {cat} has 0 production sites — \
                 should it be reclassified as Eliminated?"
            );
        }
    }
}

/// The demoting/non-demoting partition is exactly:
/// - 8 demoting (5 HIGH + 3 MEDIUM)
/// - 11 non-demoting (9 LOW + 2 ELIMINATED)
/// - 19 total
#[test]
#[timeout(30000)]
fn demoting_partition_is_locked() {
    let total = UnsoundnessCategory::ALL.len();
    let demoting = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.is_demoting())
        .count();
    let non_demoting = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| !c.is_demoting())
        .count();

    assert_eq!(
        total, 23,
        "total categories changed — added SortFallbackToIntFromCatchAll (#2663), \
         PremiseNeutralizedEq (arc_and_rc sort-plan fix), \
         FinalCollapseRefused (Final-collapse audit Fix A) and \
         OpaqueClosureValueFallback (vacfix)"
    );
    assert_eq!(
        demoting, 10,
        "demoting count changed: {demoting} — 10 = 8 original + \
         FinalCollapseRefused (Fix A) + OpaqueClosureValueFallback (vacfix)"
    );
    assert_eq!(
        non_demoting, 13,
        "non-demoting count changed: {non_demoting} — \
         13 = 11 original + SortFallbackToIntFromCatchAll (#2663) \
         + PremiseNeutralizedEq (Failed-arm only, non-demoting for Verified)"
    );
    assert_eq!(
        demoting + non_demoting,
        total,
        "partition should cover all categories"
    );
}

/// Demoting categories must have explicit names for each one.
/// This pins the exact set and prevents silent additions.
#[test]
#[timeout(30000)]
fn demoting_categories_are_exactly() {
    let demoting_names: Vec<String> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.is_demoting())
        .map(|c| format!("{c}"))
        .collect();

    let expected = vec![
        "let_assume_dropped",
        "spec_axiom_dropped",
        "sort_fallback_to_int",
        "opaque_call_true_assumption",
        "panic_recovery_false",
        "unconstrained_result_var",
        "sort_fallback_to_int_from_logic_fn",
        "integer_cast_identity",
        "final_collapse_refused",
        "opaque_closure_value_fallback",
    ];

    assert_eq!(
        demoting_names.len(),
        expected.len(),
        "demoting category count changed: got {:?}",
        demoting_names
    );

    for name in &expected {
        assert!(
            demoting_names.contains(&name.to_string()),
            "expected demoting category '{name}' not found in: {demoting_names:?}"
        );
    }
}

// ────────────────────────────────────────────────────────────────────
// 8. Demotion message quality
// ────────────────────────────────────────────────────────────────────

/// Demotion messages must include the category name and "demoted" keyword
/// for diagnostic clarity.
#[test]
#[timeout(30000)]
fn demotion_messages_are_diagnostic() {
    for cat in UnsoundnessCategory::ALL.iter().filter(|c| c.is_demoting()) {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        unsoundness::increment(*cat);

        let result = demote_if_unsound(&before, VerificationResult::Verified(None));
        if let VerificationResult::Unknown(UnknownReason::Demoted(msg)) = &result {
            assert!(
                msg.contains("demoted"),
                "demotion message for {cat} missing 'demoted': {msg}"
            );
            assert!(
                msg.contains("encoding approximations"),
                "demotion message for {cat} missing context: {msg}"
            );
            let cat_display = format!("{cat}");
            assert!(
                msg.contains(&cat_display),
                "demotion message for {cat} missing category name: {msg}"
            );
        } else {
            panic!("demoting category {cat} did not produce Unknown(Demoted): {result:?}");
        }

        unsoundness::reset();
    }
}

// ────────────────────────────────────────────────────────────────────
// 9. Multiple demoting categories: worst case
// ────────────────────────────────────────────────────────────────────

/// When multiple demoting categories fire simultaneously, all are reported.
#[test]
#[timeout(30000)]
fn multiple_demoting_categories_all_reported() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);
    unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);

    let result = demote_if_unsound(&before, VerificationResult::Verified(None));
    match &result {
        VerificationResult::Unknown(UnknownReason::Demoted(msg)) => {
            assert!(
                msg.contains("sort_fallback_to_int"),
                "should mention SortFallbackToInt: {msg}"
            );
            assert!(
                msg.contains("opaque_call_true_assumption"),
                "should mention OpaqueCallTrueAssumption: {msg}"
            );
            assert!(
                msg.contains("panic_recovery_false"),
                "should mention PanicRecoveryFalse: {msg}"
            );
        }
        other => panic!("multiple demoting categories should produce Demoted, got: {other:?}"),
    }

    unsoundness::reset();
}

// ────────────────────────────────────────────────────────────────────
// 10. Non-Verified results pass through unchanged
// ────────────────────────────────────────────────────────────────────

/// Failed results are never demoted, even with demoting categories.
#[test]
#[timeout(30000)]
fn failed_result_passes_through_with_demoting_delta() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);

    let failed = VerificationResult::Failed(crate::verify::Counterexample::empty());
    let result = demote_if_unsound(&before, failed);
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Failed should pass through unchanged: {result:?}"
    );
    unsoundness::reset();
}

/// Unknown results are never demoted (already unknown).
#[test]
#[timeout(30000)]
fn unknown_result_passes_through_with_demoting_delta() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);

    let unknown = VerificationResult::Unknown(UnknownReason::Incomplete);
    let result = demote_if_unsound(&before, unknown);
    assert!(
        matches!(
            result,
            VerificationResult::Unknown(UnknownReason::Incomplete)
        ),
        "Unknown(Incomplete) should pass through unchanged: {result:?}"
    );
    unsoundness::reset();
}

// ────────────────────────────────────────────────────────────────────
// 11. Bootstrap false-positive absorption
// ────────────────────────────────────────────────────────────────────

/// Only SortFallbackToIntFromLogicFn has bootstrap false positives.
/// No other category should claim bootstrap behavior.
#[test]
#[timeout(30000)]
fn only_sort_fallback_logic_fn_has_bootstrap_false_positives() {
    let bootstrap_cats: Vec<_> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.has_bootstrap_false_positives())
        .collect();

    assert_eq!(
        bootstrap_cats.len(),
        1,
        "expected exactly 1 category with bootstrap false positives: {bootstrap_cats:?}"
    );
    assert_eq!(
        *bootstrap_cats[0],
        UnsoundnessCategory::SortFallbackToIntFromLogicFn,
        "only SortFallbackToIntFromLogicFn should have bootstrap false positives"
    );
}

// ────────────────────────────────────────────────────────────────────
// 12. E2e: simple function verifies without demotion
// ────────────────────────────────────────────────────────────────────

/// A simple function with no encoding approximations should verify cleanly
/// (Verified, not Unknown(Demoted)).
#[test]
#[timeout(30000)]
fn simple_function_verifies_without_demotion() {
    unsoundness::reset();

    // x > 0 ⟹ x + 1 > 0
    let requires = vec![gt(var("x"), int(0))];
    let ensures = vec![gt(var("result"), int(0))];
    let return_expr = add(var("x"), int(1));

    let request = VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr));

    let result = verify_function_with_modes(request).expect("should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "simple function should verify cleanly without demotion: {result:?}"
    );

    unsoundness::reset();
}

/// A simple function that is genuinely wrong should return Failed.
#[test]
#[timeout(30000)]
fn wrong_function_fails_not_false_verified() {
    unsoundness::reset();

    // x > 0 does NOT imply x + 1 > 10 for all x > 0
    let requires = vec![gt(var("x"), int(0))];
    let ensures = vec![gt(var("result"), int(10))];
    let return_expr = add(var("x"), int(1));

    let request = VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr));

    let result = verify_function_with_modes(request).expect("should not error");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong function should return Failed: {result:?}"
    );

    unsoundness::reset();
}

// ────────────────────────────────────────────────────────────────────
// 13. Demoting category enumeration stability
// ────────────────────────────────────────────────────────────────────

/// Each demoting category has a concrete elimination plan or is being worked on.
/// This test documents the status of each demoting category and locks it.
#[test]
#[timeout(30000)]
fn demoting_category_elimination_status() {
    // HIGH risk: each has either a plan or a tracking issue
    assert_eq!(
        UnsoundnessCategory::LetAssumeDropped.expected_production_sites(),
        2,
        "LetAssumeDropped: 2 sites in pure_encoding/bindings.rs and path_conditions.rs"
    );
    assert_eq!(
        UnsoundnessCategory::SpecAxiomDropped.expected_production_sites(),
        3,
        "SpecAxiomDropped: 3 sites — logic_fn/registration.rs (x2) and verify/function/mod.rs"
    );
    assert_eq!(
        UnsoundnessCategory::SortFallbackToInt.expected_production_sites(),
        2,
        "SortFallbackToInt: 2 genuine sites (operators.rs Eq/Ne) — \
         4 catch-all guards reclassified to SortFallbackToIntFromCatchAll (#2663)"
    );
    assert_eq!(
        UnsoundnessCategory::OpaqueCallTrueAssumption.expected_production_sites(),
        1,
        "OpaqueCallTrueAssumption: 1 site in call_spec/fallback.rs — \
         mitigated by requires(false) injection (#2663)"
    );
    assert_eq!(
        UnsoundnessCategory::IntegerCastIdentity.expected_production_sites(),
        1,
        "IntegerCastIdentity: 1 site in translate/rvalue.rs (#938)"
    );

    // MEDIUM risk
    assert_eq!(
        UnsoundnessCategory::PanicRecoveryFalse.expected_production_sites(),
        3,
        "PanicRecoveryFalse: 3 sites in solver.rs (eq_term, eq_or_iff, safe_ite)"
    );
    assert_eq!(
        UnsoundnessCategory::SortFallbackToIntFromLogicFn.expected_production_sites(),
        2,
        "SortFallbackToIntFromLogicFn: 2 sites (logic_fn_sort.rs, resolution.rs)"
    );
    assert_eq!(
        UnsoundnessCategory::UnconstrainedResultVar.expected_production_sites(),
        2,
        "UnconstrainedResultVar: 2 sites (result_binding.rs, mut_borrow/mod.rs)"
    );
}

// ────────────────────────────────────────────────────────────────────
// 14. PanicRecoveryFalse defense-in-depth regression tests
// ────────────────────────────────────────────────────────────────────

/// Test that when eq_term/eq_or_iff/safe_ite panic and insert bool_const(false),
/// the demotion pipeline catches the false proof.
#[test]
#[timeout(30000)]
fn panic_recovery_false_demotes_verified_when_fired() {
    // PanicRecoveryFalse is MEDIUM risk: inserting false into the formula
    // makes the context trivially UNSAT, which would be a false Verified.
    // The demotion pipeline must catch this.
    unsoundness::reset();
    let before = unsoundness::snapshot();

    // Simulate a panic recovery that inserted false
    unsoundness::increment(UnsoundnessCategory::PanicRecoveryFalse);

    let result = demote_if_unsound(&before, VerificationResult::Verified(None));
    match &result {
        VerificationResult::Unknown(UnknownReason::Demoted(msg)) => {
            assert!(
                msg.contains("panic_recovery_false"),
                "demotion message should cite panic_recovery_false: {msg}"
            );
        }
        other => {
            panic!("PanicRecoveryFalse should demote Verified to Unknown(Demoted), got: {other:?}")
        }
    }
    unsoundness::reset();
}

#[test]
#[timeout(30000)]
fn panic_recovery_false_has_expected_site_count() {
    // PanicRecoveryFalse has 3 production sites:
    // - eq_term in solver.rs
    // - eq_or_iff in solver.rs
    // - safe_ite in solver.rs
    // Adding a new panic recovery site requires updating this count.
    assert_eq!(
        UnsoundnessCategory::PanicRecoveryFalse.expected_production_sites(),
        3,
        "PanicRecoveryFalse: 3 sites in solver.rs (eq_term, eq_or_iff, safe_ite)"
    );
    assert_eq!(
        UnsoundnessCategory::PanicRecoveryFalse.risk_level(),
        RiskLevel::Medium,
        "PanicRecoveryFalse must be MEDIUM risk"
    );
}

// ────────────────────────────────────────────────────────────────────
// 15. Defense-in-depth for opaque calls
// ────────────────────────────────────────────────────────────────────

// The opaque call defense has three layers:
// Layer 1: requires(false) injection (handle_opaque_call in trust-wp-driver)
// Layer 2: LetObligation(false) encoding guard (encoder returns error)
// Layer 3: OpaqueCallTrueAssumption demotion (if layers 1-2 are bypassed)
// This section tests each layer independently.

#[test]
#[timeout(30000)]
fn opaque_call_defense_layer1_requires_false_blocks_verification() {
    unsoundness::reset();

    // Layer 1: requires(false) in the precondition makes the function unprovable.
    // Simulates what handle_opaque_call produces.
    let requires = vec![bool_expr(false)]; // requires(false)
    let ensures = vec![gt(var("result"), int(0))];
    let return_expr = int(42);

    let request = VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr));

    let result = verify_function_with_modes(request).expect("should not error");

    match &result {
        VerificationResult::Unknown(reason) if reason.as_str().contains("vacuous") => {}
        other => panic!("requires(false) should produce Unknown(vacuous), got: {other:?}"),
    }
    unsoundness::reset();
}

#[test]
#[timeout(30000)]
fn opaque_call_defense_layer2_let_obligation_false_errors() {
    // Layer 2: LetObligation(false, body) returns encoding error.
    // This prevents the non-Bool body path from asserting false as a
    // solver fact.
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;

    let mut encoder = AYEncoder::new();

    // Non-Bool body: previously asserted false, now returns error
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Bool(false)),
        body: Arc::new(add(var("x"), int(1))),
    };
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "LetObligation(false, non-Bool) must error: {result:?}"
    );

    // Bool body: also returns error for consistency
    let mut encoder2 = AYEncoder::new();
    let expr2 = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Bool(false)),
        body: Arc::new(bool_expr(true)),
    };
    let result2 = encoder2.encode_pure(&expr2);
    assert!(
        result2.is_err(),
        "LetObligation(false, Bool) must also error: {result2:?}"
    );
}

#[test]
#[timeout(30000)]
fn opaque_call_defense_layer3_demotion_catches_bypass() {
    // Layer 3: If layers 1-2 are somehow bypassed, the demotion pipeline
    // catches the OpaqueCallTrueAssumption counter.
    unsoundness::reset();
    let before = unsoundness::snapshot();

    unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);

    let result = demote_if_unsound(&before, VerificationResult::Verified(None));
    assert!(
        matches!(&result, VerificationResult::Unknown(UnknownReason::Demoted(msg)) if msg.contains("opaque_call_true_assumption")),
        "Layer 3 demotion must catch OpaqueCallTrueAssumption: {result:?}"
    );
    unsoundness::reset();
}

// ────────────────────────────────────────────────────────────────────
// 16. UnconstrainedResultVar regression tests
// ────────────────────────────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn unconstrained_result_var_is_medium_demoting() {
    let cat = UnsoundnessCategory::UnconstrainedResultVar;
    assert_eq!(cat.risk_level(), RiskLevel::Medium);
    assert!(cat.is_demoting());
    assert_eq!(
        cat.expected_production_sites(),
        2,
        "UnconstrainedResultVar: 2 sites (result_binding.rs, mut_borrow/mod.rs)"
    );
}

#[test]
#[timeout(30000)]
fn unconstrained_result_var_demotes_verified() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::UnconstrainedResultVar);

    let result = demote_if_unsound(&before, VerificationResult::Verified(None));
    match &result {
        VerificationResult::Unknown(UnknownReason::Demoted(msg)) => {
            assert!(
                msg.contains("unconstrained_result_var"),
                "demotion message should cite unconstrained_result_var: {msg}"
            );
        }
        other => panic!("UnconstrainedResultVar should demote Verified, got: {other:?}"),
    }
    unsoundness::reset();
}

// ────────────────────────────────────────────────────────────────────
// 17. IntegerCastIdentity regression tests
// ────────────────────────────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn integer_cast_identity_is_high_demoting() {
    let cat = UnsoundnessCategory::IntegerCastIdentity;
    assert_eq!(cat.risk_level(), RiskLevel::High);
    assert!(cat.is_demoting());
    assert_eq!(
        cat.expected_production_sites(),
        1,
        "IntegerCastIdentity: 1 site in translate/rvalue.rs"
    );
}

#[test]
#[timeout(30000)]
fn integer_cast_identity_demotes_verified() {
    unsoundness::reset();
    let before = unsoundness::snapshot();
    unsoundness::increment(UnsoundnessCategory::IntegerCastIdentity);

    let result = demote_if_unsound(&before, VerificationResult::Verified(None));
    assert!(
        matches!(&result, VerificationResult::Unknown(UnknownReason::Demoted(msg)) if msg.contains("integer_cast_identity")),
        "IntegerCastIdentity should demote Verified: {result:?}"
    );
    unsoundness::reset();
}

// ────────────────────────────────────────────────────────────────────
// 18. Comprehensive elimination status documentation
// ────────────────────────────────────────────────────────────────────

// Each demoting category has either:
// - ELIMINATED status (0 production sites)
// - A concrete elimination plan (documented here)
// - Active mitigation (e.g., encoding guard for OpaqueCall)

#[test]
#[timeout(30000)]
fn comprehensive_elimination_status() {
    // HIGH risk categories and their elimination plans:

    // 1. SortFallbackToInt (2 genuine sites) — operators.rs Eq/Ne fallback
    // Plan: #1982 (sort inference improvement), #2231 (coercion reduction)
    // 4 former catch-all sites reclassified to SortFallbackToIntFromCatchAll (#2663).
    let sfi = UnsoundnessCategory::SortFallbackToInt;
    assert_eq!(sfi.expected_production_sites(), 2);
    assert_eq!(sfi.risk_level(), RiskLevel::High);

    // 2. LetAssumeDropped (2 sites) — encoding error recovery
    // Plan: improve encoding coverage to eliminate error fallbacks
    let lad = UnsoundnessCategory::LetAssumeDropped;
    assert_eq!(lad.expected_production_sites(), 2);
    assert_eq!(lad.risk_level(), RiskLevel::High);

    // 3. SpecAxiomDropped (3 sites) — logic fn spec error + corrupted recursive unfolding
    // Plan: strengthen spec axiom encoding to handle all sort combinations
    let sad = UnsoundnessCategory::SpecAxiomDropped;
    assert_eq!(sad.expected_production_sites(), 3);
    assert_eq!(sad.risk_level(), RiskLevel::High);

    // 4. OpaqueCallTrueAssumption (1 site) — MITIGATED
    // Mitigation: requires(false) injection + LetObligation encoding guard
    // The counter still fires but proofs are blocked by the encoding guard.
    let octa = UnsoundnessCategory::OpaqueCallTrueAssumption;
    assert_eq!(octa.expected_production_sites(), 1);
    assert_eq!(octa.risk_level(), RiskLevel::High);

    // 5. IntegerCastIdentity (1 site) — PARTIALLY ADDRESSED
    // Mitigation: BV truncation for known types (#2666)
    // Remaining: fallback path when target type is unknown
    let ici = UnsoundnessCategory::IntegerCastIdentity;
    assert_eq!(ici.expected_production_sites(), 1);
    assert_eq!(ici.risk_level(), RiskLevel::High);

    // 5b. FinalCollapseRefused (2 sites) — MITIGATED BY CONSTRUCTION (Fix A)
    // Both sites live in final_collapse_guard.rs and return an EncodingError
    // (fail-closed) instead of collapsing; the counter is demotion
    // defense-in-depth.
    //   - refuse_final_collapse: the sort-blind ^x -> x collapse on
    //     &mut-embedding carriers.
    //   - refuse_prophecy_over_constant (tract19): ^<literal>. The sort guard
    //     cannot see this — a literal's sort is a pure value — and the
    //     "wrappers are no-ops on literals" arm folded it away, which was a
    //     LIVE false accept (a contract asserting the PRE-state value of a
    //     borrowed local verified on a function that mutates through it).
    let fcr = UnsoundnessCategory::FinalCollapseRefused;
    assert_eq!(fcr.expected_production_sites(), 2);
    assert_eq!(fcr.risk_level(), RiskLevel::High);

    // MEDIUM risk categories:

    // 6. PanicRecoveryFalse (3 sites) — ay panic recovery
    // Plan: migrate to try_* APIs (#2131), eliminate catch_unwind
    let prf = UnsoundnessCategory::PanicRecoveryFalse;
    assert_eq!(prf.expected_production_sites(), 3);
    assert_eq!(prf.risk_level(), RiskLevel::Medium);

    // 7. SortFallbackToIntFromLogicFn (2 sites) — logic fn return sort
    // Plan: complete return-sort threading (#2320)
    let sflfn = UnsoundnessCategory::SortFallbackToIntFromLogicFn;
    assert_eq!(sflfn.expected_production_sites(), 2);
    assert_eq!(sflfn.risk_level(), RiskLevel::Medium);

    // 8. UnconstrainedResultVar (2 sites) — missing return_expr
    // Plan: ensure driver always provides return_expr for result-referencing fns
    let urv = UnsoundnessCategory::UnconstrainedResultVar;
    assert_eq!(urv.expected_production_sites(), 2);
    assert_eq!(urv.risk_level(), RiskLevel::Medium);

    // 5c. OpaqueClosureValueFallback (1 site) — GENUINE, demotion is the net
    // The site (pure_encoding/mod.rs encode_closure_in_logic) is the ONLY
    // former UnsupportedConstructSkip site that keeps encoding with a
    // SYNTHESIZED value instead of returning an EncodingError, and that
    // value's arbitrary Bool sort is promoted by ite(b,1,0) into a fabricated
    // {0,1} bound. Reclassified LOW -> HIGH (vacfix).
    let ocvf = UnsoundnessCategory::OpaqueClosureValueFallback;
    assert_eq!(ocvf.expected_production_sites(), 1);
    assert_eq!(ocvf.risk_level(), RiskLevel::High);

    // Total demoting budget: must not increase without review
    assert_eq!(
        UnsoundnessCategory::total_demoting_production_sites(),
        19,
        "total demoting budget must not increase silently — \
         14 (#2663 Phase 1a) + FinalCollapseRefused(2): the Fix A refusal \
         site is fail-closed by construction (error, never a collapsed term); \
         it closes three previously UNCOUNTED false-proof routes (R1/R2/R3 \
         Final collapses) rather than opening one; + \
         OpaqueClosureValueFallback(1), reclassified from the LOW \
         UnsupportedConstructSkip bucket (the site was always live)"
    );
}

// ────────────────────────────────────────────────────────────────────
// 8. Opaque closure VALUE fallback is demoting (vacfix)
// ────────────────────────────────────────────────────────────────────

/// The last-resort closure-value fallback in `encode_closure_in_logic` mints
/// an opaque `Bool` constant for a closure whose real return sort is unknown,
/// and KEEPS ENCODING. Any arithmetic use of an application of that closure is
/// promoted through `bool_to_int`'s `ite(b, 1, 0)`, which FABRICATES the
/// premise "value in {0,1}" — on `lang/unsized_quant` that makes the flatly
/// false `forall<x> len[x] <= 1` valid.
///
/// This pin fixes the classification: the site must fire a DEMOTING counter,
/// so no obligation encoded on top of a fabricated closure value can ever be
/// reported `Verified`. Before the fix it fired the LOW, non-demoting
/// `UnsupportedConstructSkip`, and `Verified` passed straight through.
#[test]
#[timeout(30000)]
fn opaque_closure_value_fallback_fires_and_demotes() {
    use std::sync::Arc;

    use trust_wp_core::formula::{ExprSort, PureExpr};

    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new();
    // A closure that has no faithful encoding outside Mapping context.
    // `|x: Seq| x.len()` is Int-valued, so the Bool fallback constant is not
    // merely opaque, it is opaquely MIS-SORTED.
    let closure = PureExpr::Closure {
        params: vec![("x".to_string(), Some(ExprSort::Seq))],
        body: Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Seq))),
            method: "len".to_string(),
            args: vec![],
        }),
    };
    encoder
        .encode_pure(&closure)
        .expect("the fallback path encodes rather than erroring — that is the problem it books");

    let delta = unsoundness::delta(&before, &unsoundness::snapshot());
    assert_eq!(
        delta.get(&UnsoundnessCategory::OpaqueClosureValueFallback),
        Some(&1),
        "the opaque closure-value fallback must book OpaqueClosureValueFallback"
    );
    assert_eq!(
        delta.get(&UnsoundnessCategory::UnsupportedConstructSkip),
        None,
        "it must no longer be booked as the LOW, non-demoting UnsupportedConstructSkip"
    );

    assert!(
        UnsoundnessCategory::OpaqueClosureValueFallback.is_demoting(),
        "OpaqueClosureValueFallback must be demoting"
    );
    let demoted = demote_if_unsound(&before, VerificationResult::Verified(None));
    match &demoted {
        VerificationResult::Unknown(reason) => assert!(
            reason.as_str().contains("opaque_closure_value_fallback"),
            "demotion reason should name the category: {reason}"
        ),
        other => panic!("a fabricated closure value must demote Verified, got: {other:?}"),
    }
    unsoundness::reset();
}
