// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_increment_and_snapshot() {
    reset();
    assert!(snapshot().is_empty());

    increment(UnsoundnessCategory::SortFallbackToInt);
    increment(UnsoundnessCategory::SortFallbackToInt);
    increment(UnsoundnessCategory::PanicRecoveryFalse);

    let snap = snapshot();
    assert_eq!(snap.get(&UnsoundnessCategory::SortFallbackToInt), Some(&2));
    assert_eq!(snap.get(&UnsoundnessCategory::PanicRecoveryFalse), Some(&1));
    assert_eq!(snap.get(&UnsoundnessCategory::LetAssumeDropped), None);

    reset();
    assert!(snapshot().is_empty());
}

#[test]
#[timeout(30000)]
fn test_delta_computation() {
    reset();
    increment(UnsoundnessCategory::SortFallbackToInt);
    let before = snapshot();

    increment(UnsoundnessCategory::SortFallbackToInt);
    increment(UnsoundnessCategory::ClosureBodyTrueDefault);
    let after = snapshot();

    let d = delta(&before, &after);
    assert_eq!(d.get(&UnsoundnessCategory::SortFallbackToInt), Some(&1));
    assert_eq!(
        d.get(&UnsoundnessCategory::ClosureBodyTrueDefault),
        Some(&1)
    );
    assert_eq!(d.len(), 2);

    reset();
}

#[test]
#[timeout(30000)]
fn test_delta_empty_when_no_change() {
    reset();
    increment(UnsoundnessCategory::BitwiseUfApproximation);
    let before = snapshot();
    let after = snapshot();
    let d = delta(&before, &after);
    assert!(d.is_empty());
    reset();
}

#[test]
#[timeout(30000)]
fn test_apply_unsoundness_delta_merges_counts() {
    reset();
    increment(UnsoundnessCategory::SortFallbackToInt);

    let mut worker_delta = HashMap::new();
    worker_delta.insert(UnsoundnessCategory::SortFallbackToInt, 2);
    worker_delta.insert(UnsoundnessCategory::PanicRecoveryFalse, 1);

    apply_delta(&worker_delta);

    let merged = snapshot();
    assert_eq!(
        merged.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&3)
    );
    assert_eq!(
        merged.get(&UnsoundnessCategory::PanicRecoveryFalse),
        Some(&1)
    );

    reset();
}

#[test]
#[timeout(30000)]
fn test_has_demoting() {
    let mut d = HashMap::new();
    assert!(!has_demoting(&d));

    d.insert(UnsoundnessCategory::UnsupportedConstructSkip, 3);
    assert!(!has_demoting(&d), "LOW risk should not be demoting");

    d.insert(UnsoundnessCategory::SortFallbackToInt, 1);
    assert!(has_demoting(&d), "HIGH risk should be demoting");
}

#[test]
#[timeout(30000)]
fn test_is_demoting_classification() {
    // HIGH risk — all demoting
    assert!(UnsoundnessCategory::LetAssumeDropped.is_demoting());
    assert!(UnsoundnessCategory::SpecAxiomDropped.is_demoting());
    assert!(UnsoundnessCategory::SortFallbackToInt.is_demoting());
    assert!(
        !UnsoundnessCategory::ClosureBodyTrueDefault.is_demoting(),
        "ClosureBodyTrueDefault is ELIMINATED (#2541) — no production increment sites"
    );
    assert!(
        !UnsoundnessCategory::BitwiseUfApproximation.is_demoting(),
        "BitwiseUfApproximation is ELIMINATED (#2666) — BV mode always-on, no production increment sites"
    );
    assert!(UnsoundnessCategory::OpaqueCallTrueAssumption.is_demoting());
    // MEDIUM risk — also demoting
    assert!(UnsoundnessCategory::PanicRecoveryFalse.is_demoting());
    // LOW risk — NOT demoting
    assert!(!UnsoundnessCategory::UnsupportedConstructSkip.is_demoting());
    assert!(!UnsoundnessCategory::CatchUnwindFallback.is_demoting());
    assert!(!UnsoundnessCategory::SortFallbackToIntFromVar.is_demoting());
    assert!(
        !UnsoundnessCategory::InvariantTrueShortCircuit.is_demoting(),
        "InvariantTrueShortCircuit is provably sound identity transform (#2201)"
    );
    assert!(
        UnsoundnessCategory::SortFallbackToIntFromLogicFn.is_demoting(),
        "LogicFnCall Int fallback remains demoting for truly unknown return sorts (#2320)"
    );
    assert!(
        !UnsoundnessCategory::SortFallbackToIntFromMethodCall.is_demoting(),
        "Known Int-returning methods (len, get, etc.) are correct (#2202)"
    );
    assert!(
        !UnsoundnessCategory::BoolCoercionFromNonBool.is_demoting(),
        "Bool coercion is benign — Int!=0 or fresh Bool are conservative (#2359)"
    );
    assert!(
        !UnsoundnessCategory::PhantomVariableUpgrade.is_demoting(),
        "Phantom variable upgrades weaken proofs but don't produce false ones (#2567)"
    );
    assert!(
        UnsoundnessCategory::IntegerCastIdentity.is_demoting(),
        "Integer cast identity can produce false proofs — narrowing/wrapping is ignored (#938)"
    );
    assert!(
        UnsoundnessCategory::UnconstrainedResultVar.is_demoting(),
        "Unconstrained result var can produce false proofs when result is free (#2663)"
    );
    assert!(
        !UnsoundnessCategory::SortFallbackToIntFromCatchAll.is_demoting(),
        "SortFallbackToIntFromCatchAll is LOW — unreachable catch-all guards (#2663 Phase 1a)"
    );
}

#[test]
#[timeout(30000)]
fn test_all_categories_covered() {
    assert_eq!(
        UnsoundnessCategory::ALL.len(),
        23,
        "ALL should list every variant"
    );
}

#[test]
#[timeout(30000)]
fn test_has_bootstrap_false_positives() {
    // Only SortFallbackToIntFromLogicFn has bootstrap false positives:
    // infer_expr_sort encounters LogicFnCall nodes before declarations
    // exist during sort-hint registration.
    assert!(
        UnsoundnessCategory::SortFallbackToIntFromLogicFn.has_bootstrap_false_positives(),
        "LogicFnCall sort inference during bootstrap triggers false positives"
    );

    // All other categories should NOT have bootstrap false positives.
    let non_bootstrap: Vec<_> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| {
            **c != UnsoundnessCategory::SortFallbackToIntFromLogicFn
                && c.has_bootstrap_false_positives()
        })
        .collect();
    assert!(
        non_bootstrap.is_empty(),
        "unexpected categories with bootstrap false positives: {non_bootstrap:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_secondary_bootstrap_absorption_is_exact_and_category_scoped() {
    reset();
    let before_setup = snapshot();

    // Secondary bootstrap repeats two already-forgiven logic-function sort
    // fallbacks and also records a genuinely demoting category.
    increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    increment(UnsoundnessCategory::SortFallbackToInt);
    let post_bootstrap = snapshot();

    // Both categories can also fire after bootstrap. Those later increments
    // must survive absorption.
    increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    increment(UnsoundnessCategory::SortFallbackToInt);

    absorb_secondary_bootstrap_false_positives(&before_setup, &post_bootstrap);
    let after = snapshot();
    assert_eq!(
        after.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
        Some(&1),
        "only the two secondary-bootstrap logic-fn increments should be removed"
    );
    assert_eq!(
        after.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&2),
        "non-bootstrap categories must never be absorbed"
    );

    reset();
}

#[test]
#[timeout(30000)]
fn test_format_demoting() {
    let mut d = HashMap::new();
    d.insert(UnsoundnessCategory::SortFallbackToInt, 3);
    d.insert(UnsoundnessCategory::UnsupportedConstructSkip, 1);
    d.insert(UnsoundnessCategory::PanicRecoveryFalse, 2);

    let formatted = format_demoting(&d);
    assert!(formatted.contains("sort_fallback_to_int(3)"));
    assert!(formatted.contains("panic_recovery_false(2)"));
    assert!(
        !formatted.contains("unsupported_construct_skip"),
        "LOW risk should not appear in demoting format"
    );
}

#[test]
#[timeout(30000)]
fn test_display_roundtrip() {
    for cat in UnsoundnessCategory::ALL {
        let s = format!("{cat}");
        assert!(!s.is_empty(), "Display should produce non-empty string");
        assert!(
            s.chars().all(|c| c.is_ascii_lowercase() || c == '_'),
            "Display should be snake_case: {s}"
        );
    }
}

// --- RiskLevel and soundness lock tests (#2663) ---

#[test]
#[timeout(30000)]
fn test_risk_level_consistency_with_is_demoting() {
    // Verify that risk_level().is_demoting() agrees with is_demoting() for ALL categories.
    // This catches any divergence if someone updates one but not the other.
    for cat in UnsoundnessCategory::ALL {
        assert_eq!(
            cat.risk_level().is_demoting(),
            cat.is_demoting(),
            "risk_level().is_demoting() disagrees with is_demoting() for {cat}"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_risk_level_exact_classification() {
    use super::RiskLevel;

    // HIGH risk categories
    assert_eq!(
        UnsoundnessCategory::LetAssumeDropped.risk_level(),
        RiskLevel::High
    );
    assert_eq!(
        UnsoundnessCategory::SpecAxiomDropped.risk_level(),
        RiskLevel::High
    );
    assert_eq!(
        UnsoundnessCategory::SortFallbackToInt.risk_level(),
        RiskLevel::High
    );
    assert_eq!(
        UnsoundnessCategory::OpaqueCallTrueAssumption.risk_level(),
        RiskLevel::High
    );
    assert_eq!(
        UnsoundnessCategory::IntegerCastIdentity.risk_level(),
        RiskLevel::High
    );
    assert_eq!(
        UnsoundnessCategory::FinalCollapseRefused.risk_level(),
        RiskLevel::High,
        "FinalCollapseRefused guards the ^x -> x inversion (Fix A) — must stay HIGH demoting"
    );

    // MEDIUM risk categories
    assert_eq!(
        UnsoundnessCategory::PanicRecoveryFalse.risk_level(),
        RiskLevel::Medium
    );
    assert_eq!(
        UnsoundnessCategory::SortFallbackToIntFromLogicFn.risk_level(),
        RiskLevel::Medium
    );
    assert_eq!(
        UnsoundnessCategory::UnconstrainedResultVar.risk_level(),
        RiskLevel::Medium
    );

    // ELIMINATED
    assert_eq!(
        UnsoundnessCategory::ClosureBodyTrueDefault.risk_level(),
        RiskLevel::Eliminated
    );
    assert_eq!(
        UnsoundnessCategory::BitwiseUfApproximation.risk_level(),
        RiskLevel::Eliminated
    );

    // LOW risk categories
    assert_eq!(
        UnsoundnessCategory::UnsupportedConstructSkip.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::CatchUnwindFallback.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::ClosureAxiomSkipped.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::SortFallbackToIntFromVar.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::InvariantTrueShortCircuit.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::SortFallbackToIntFromMethodCall.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::BoolCoercionFromNonBool.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::PhantomVariableUpgrade.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::SortCoercionBridge.risk_level(),
        RiskLevel::Low
    );
    assert_eq!(
        UnsoundnessCategory::SortFallbackToIntFromCatchAll.risk_level(),
        RiskLevel::Low
    );
}

#[test]
#[timeout(30000)]
fn test_risk_level_counts() {
    use super::RiskLevel;

    let high_count = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::High)
        .count();
    let medium_count = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::Medium)
        .count();
    let eliminated_count = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::Eliminated)
        .count();
    let low_count = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.risk_level() == RiskLevel::Low)
        .count();

    assert_eq!(
        high_count, 7,
        "expected 7 HIGH risk categories (5 original + FinalCollapseRefused (Fix A) \
         + OpaqueClosureValueFallback (vacfix))"
    );
    assert_eq!(medium_count, 3, "expected 3 MEDIUM risk categories");
    assert_eq!(eliminated_count, 2, "expected 2 ELIMINATED categories");
    assert_eq!(
        low_count, 11,
        "expected 11 LOW risk categories (10 original + PremiseNeutralizedEq)"
    );
    assert_eq!(
        high_count + medium_count + eliminated_count + low_count,
        23,
        "all categories must be classified"
    );
}

#[test]
#[timeout(30000)]
fn test_is_eliminated() {
    // ClosureBodyTrueDefault (#2541) and BitwiseUfApproximation (#2666) are eliminated.
    assert!(UnsoundnessCategory::ClosureBodyTrueDefault.is_eliminated());
    assert!(UnsoundnessCategory::BitwiseUfApproximation.is_eliminated());

    let eliminated: Vec<_> = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.is_eliminated())
        .collect();
    assert_eq!(
        eliminated.len(),
        2,
        "expected 2 eliminated categories: {eliminated:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_eliminated_category_has_zero_production_sites() {
    for cat in UnsoundnessCategory::ALL {
        if cat.is_eliminated() {
            assert_eq!(
                cat.expected_production_sites(),
                0,
                "eliminated category {cat} must have 0 production sites"
            );
        }
    }
}

#[test]
#[timeout(30000)]
fn test_demoting_production_site_budget() {
    // Total demoting production sites across all demoting categories.
    // This number is the "soundness budget" — the total number of places
    // in production code where false proofs can originate. Track it
    // explicitly so any increase requires deliberate review.
    //
    // Current budget: 16 sites across 8 demoting categories.
    // HIGH (9 sites):
    // - SortFallbackToInt: 2 (down from 6 — 4 catch-alls reclassified to
    //   SortFallbackToIntFromCatchAll per #2663 Phase 1a)
    // - LetAssumeDropped: 2
    // - SpecAxiomDropped: 3 (logic_fn/registration.rs:786,:807 +
    //   verify/function/mod.rs:1282; the previous count of 1 was stale —
    //   the two extra sites already existed, only the lock lagged)
    // - OpaqueCallTrueAssumption: 1
    // - IntegerCastIdentity: 1
    // MEDIUM (7 sites):
    // - PanicRecoveryFalse: 3 (eq_term, eq_or_iff, safe_ite in solver.rs)
    // - SortFallbackToIntFromLogicFn: 2
    // - UnconstrainedResultVar: 2 (reclassified from SortFallbackToInt #2663)
    // ELIMINATED (was demoting, now 0 sites):
    // - BitwiseUfApproximation: 0 (#2666 — BV mode always-on)
    // + FinalCollapseRefused: 2 (final_collapse_guard.rs
    //   refuse_final_collapse + refuse_prophecy_over_constant — Fix A of the
    //   Final-collapse audit, sort-based and constant-carrier arms; both sites
    //   are themselves fail-closed: they return an EncodingError instead of the
    //   unsound ^x -> x collapse, and the counter is demotion defense-in-depth.
    //   The constant-carrier arm (tract19) closed a LIVE false accept, not a
    //   latent one: `^<literal>` folded to the literal in encode_wrapper_rewrite).
    // + OpaqueClosureValueFallback: 1 (pure_encoding/mod.rs
    //   encode_closure_in_logic opaque Bool closure value — vacfix;
    //   reclassified out of the LOW UnsupportedConstructSkip bucket, which
    //   drops from 5 to 4 sites, so the TOTAL production-site count is
    //   unchanged; only the demoting budget moves).
    let total = UnsoundnessCategory::total_demoting_production_sites();
    assert_eq!(
        total, 19,
        "total demoting production sites changed — review all new sites for soundness impact"
    );
}

#[test]
#[timeout(30000)]
fn test_risk_level_display() {
    use super::RiskLevel;

    assert_eq!(format!("{}", RiskLevel::High), "HIGH");
    assert_eq!(format!("{}", RiskLevel::Medium), "MEDIUM");
    assert_eq!(format!("{}", RiskLevel::Low), "LOW");
    assert_eq!(format!("{}", RiskLevel::Eliminated), "ELIMINATED");
}

#[test]
#[timeout(30000)]
fn test_risk_level_is_demoting() {
    use super::RiskLevel;

    assert!(RiskLevel::High.is_demoting());
    assert!(RiskLevel::Medium.is_demoting());
    assert!(!RiskLevel::Low.is_demoting());
    assert!(!RiskLevel::Eliminated.is_demoting());
}

#[test]
#[timeout(30000)]
fn test_risk_level_ordering() {
    use super::RiskLevel;

    // Verify that the derive(Ord) gives a useful ordering
    // (High < Medium < Low < Eliminated by derive order).
    assert!(RiskLevel::High < RiskLevel::Medium);
    assert!(RiskLevel::Medium < RiskLevel::Low);
    assert!(RiskLevel::Low < RiskLevel::Eliminated);
}

#[test]
#[timeout(30000)]
fn test_all_categories_have_nonzero_sites_unless_eliminated() {
    // Every non-eliminated category must have at least one production site.
    // If a category has zero sites AND is not eliminated, something is wrong:
    // either the category should be eliminated, or the count is stale.
    for cat in UnsoundnessCategory::ALL {
        if !cat.is_eliminated() {
            assert!(
                cat.expected_production_sites() > 0,
                "non-eliminated category {cat} ({}) has 0 expected production sites — \
                 should it be reclassified as Eliminated?",
                cat.risk_level()
            );
        }
    }
}

// --- Soundness lock invariant tests (#2663) ---

#[test]
#[timeout(30000)]
fn test_total_production_sites_across_all_categories() {
    // Total production sites across ALL categories (demoting + non-demoting).
    // This is the full observability budget. Track it explicitly so any
    // addition of increment sites is noticed and reviewed.
    //
    // Current total: 18 (demoting) + 60 (non-demoting) = 78
    // (demoting went 17 -> 18 with the tract19 constant-carrier arm of the
    // Fix A Final-collapse guard: `refuse_prophecy_over_constant`)
    // Non-demoting breakdown: UnsupportedConstructSkip(5) + CatchUnwindFallback(1)
    // + ClosureAxiomSkipped(1) + SortFallbackToIntFromVar(8) +
    // InvariantTrueShortCircuit(3) + SortFallbackToIntFromMethodCall(13) +
    // BoolCoercionFromNonBool(1) + PhantomVariableUpgrade(8) +
    // SortCoercionBridge(15) + SortFallbackToIntFromCatchAll(4) +
    // PremiseNeutralizedEq(1) = 60
    let total: usize = UnsoundnessCategory::ALL
        .iter()
        .map(|c| c.expected_production_sites())
        .sum();
    assert_eq!(
        total, 78,
        "total production sites across all categories changed — \
         review new/removed sites: {total}"
    );
}

#[test]
#[timeout(30000)]
fn test_per_category_production_site_values() {
    // Pin exact expected_production_sites values for each category.
    // Any change to the count MUST update both the source and this test.
    // This is the most granular soundness lock: adding a new
    // unsoundness::increment() call in production code requires updating
    // the count here and in expected_production_sites().
    let expected: Vec<(&str, usize)> = vec![
        // HIGH demoting
        ("let_assume_dropped", 2),
        ("spec_axiom_dropped", 3),
        ("sort_fallback_to_int", 2),
        ("opaque_call_true_assumption", 1),
        ("integer_cast_identity", 1),
        ("final_collapse_refused", 2),
        ("opaque_closure_value_fallback", 1),
        // MEDIUM demoting
        ("panic_recovery_false", 3),
        ("sort_fallback_to_int_from_logic_fn", 2),
        ("unconstrained_result_var", 2),
        // ELIMINATED
        ("closure_body_true_default", 0),
        ("bitwise_uf_approximation", 0),
        // LOW
        ("unsupported_construct_skip", 4),
        ("catch_unwind_fallback", 1),
        ("closure_axiom_skipped", 1),
        ("sort_fallback_to_int_from_var", 8),
        ("invariant_true_short_circuit", 3),
        ("sort_fallback_to_int_from_method_call", 13),
        ("bool_coercion_from_non_bool", 1),
        ("phantom_variable_upgrade", 8),
        ("sort_coercion_bridge", 15),
        ("sort_fallback_to_int_from_catch_all", 4),
        ("premise_neutralized_eq", 1),
    ];

    for cat in UnsoundnessCategory::ALL {
        let name = format!("{cat}");
        let actual = cat.expected_production_sites();
        let expected_pair = expected
            .iter()
            .find(|(n, _)| *n == name)
            .unwrap_or_else(|| panic!("category '{name}' not found in expected list"));
        assert_eq!(
            actual, expected_pair.1,
            "expected_production_sites mismatch for {name}: \
             expected {}, got {actual}",
            expected_pair.1
        );
    }

    assert_eq!(
        expected.len(),
        UnsoundnessCategory::ALL.len(),
        "expected list has {} entries but ALL has {} categories — \
         update the expected list when adding/removing categories",
        expected.len(),
        UnsoundnessCategory::ALL.len()
    );
}

#[test]
#[timeout(30000)]
fn test_demoting_budget_equals_sum_of_demoting_sites() {
    // Verify that total_demoting_production_sites() is the sum of
    // expected_production_sites() for all demoting categories.
    let manual_sum: usize = UnsoundnessCategory::ALL
        .iter()
        .filter(|c| c.is_demoting())
        .map(|c| c.expected_production_sites())
        .sum();
    assert_eq!(
        UnsoundnessCategory::total_demoting_production_sites(),
        manual_sum,
        "total_demoting_production_sites disagrees with manual sum"
    );
}

#[test]
#[timeout(30000)]
fn test_eliminated_categories_are_not_demoting() {
    // Eliminated categories must not be demoting. If a category still has
    // production sites that can fire, it should not be classified as
    // Eliminated.
    for cat in UnsoundnessCategory::ALL {
        if cat.is_eliminated() {
            assert!(
                !cat.is_demoting(),
                "eliminated category {cat} is marked as demoting — \
                 eliminated categories cannot produce false proofs"
            );
        }
    }
}

#[test]
#[timeout(30000)]
fn test_restore_category_rolls_back_single_category() {
    reset();
    increment(UnsoundnessCategory::SortFallbackToInt);
    increment(UnsoundnessCategory::PanicRecoveryFalse);
    let snap = snapshot();

    increment(UnsoundnessCategory::SortFallbackToInt);
    increment(UnsoundnessCategory::PanicRecoveryFalse);

    // Only restore SortFallbackToInt
    restore_category(&snap, UnsoundnessCategory::SortFallbackToInt);

    let current = snapshot();
    assert_eq!(
        current.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&1),
        "SortFallbackToInt should be restored to pre-increment value"
    );
    assert_eq!(
        current.get(&UnsoundnessCategory::PanicRecoveryFalse),
        Some(&2),
        "PanicRecoveryFalse should NOT be affected by single-category restore"
    );

    reset();
}

#[test]
#[timeout(30000)]
fn secondary_bootstrap_absorption_removes_only_the_setup_delta() {
    reset();

    // A count predating the secondary setup belongs to the primary solve and
    // must survive.  The two following logic-function fallbacks are the
    // secondary bootstrap repeats; the ordinary sort fallback is deliberately
    // not in the bootstrap-false-positive allowlist.
    increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    let before_setup = snapshot();
    increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    increment(UnsoundnessCategory::SortFallbackToInt);
    let post_bootstrap = snapshot();

    // Simulate later verification-phase increments.  Absorption must retain
    // them even if called after they have appeared in the live counter map.
    increment(UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    increment(UnsoundnessCategory::SortFallbackToInt);
    absorb_secondary_bootstrap_false_positives(&before_setup, &post_bootstrap);

    let current = snapshot();
    assert_eq!(
        current.get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn),
        Some(&2),
        "the primary count and the post-bootstrap count must survive"
    );
    assert_eq!(
        current.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&2),
        "non-allowlisted categories must never be absorbed"
    );

    reset();
}

#[test]
#[timeout(30000)]
fn test_apply_delta_ignores_zero_counts() {
    reset();
    increment(UnsoundnessCategory::SortFallbackToInt);

    let mut delta_map = HashMap::new();
    delta_map.insert(UnsoundnessCategory::SortFallbackToInt, 0);
    delta_map.insert(UnsoundnessCategory::PanicRecoveryFalse, 0);

    apply_delta(&delta_map);

    let current = snapshot();
    assert_eq!(
        current.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&1),
        "zero-count delta should not change existing counter"
    );
    assert_eq!(
        current.get(&UnsoundnessCategory::PanicRecoveryFalse),
        None,
        "zero-count delta should not create new counter entry"
    );

    reset();
}

#[test]
#[timeout(30000)]
fn test_delta_ignores_decreased_counts() {
    // delta() only reports increases. If a category decremented (shouldn't
    // happen in production but tests can via reset/restore), delta returns
    // empty for that category.
    reset();
    increment(UnsoundnessCategory::SortFallbackToInt);
    increment(UnsoundnessCategory::SortFallbackToInt);
    let before = snapshot();

    // Simulate a decrease by restoring to a lower count
    let mut lower = HashMap::new();
    lower.insert(UnsoundnessCategory::SortFallbackToInt, 1_usize);
    restore(&lower);
    let after = snapshot();

    let d = delta(&before, &after);
    assert!(
        d.is_empty(),
        "delta should not report decreased counts: {d:?}"
    );

    reset();
}

#[test]
#[timeout(30000)]
fn test_format_demoting_empty_on_non_demoting_delta() {
    let mut d = HashMap::new();
    d.insert(UnsoundnessCategory::UnsupportedConstructSkip, 5);
    d.insert(UnsoundnessCategory::CatchUnwindFallback, 3);
    d.insert(UnsoundnessCategory::SortFallbackToIntFromVar, 1);

    let formatted = format_demoting(&d);
    assert!(
        formatted.is_empty(),
        "format_demoting should produce empty string for non-demoting delta: '{formatted}'"
    );
}

#[test]
#[timeout(30000)]
fn test_demote_if_unsound_preserves_non_verified_results() {
    use crate::verify::{demote_if_unsound, VerificationResult};

    reset();
    let before = snapshot();

    // Increment a demoting category
    increment(UnsoundnessCategory::SortFallbackToInt);

    // Non-Verified results should pass through unchanged
    let failed = VerificationResult::Failed(crate::verify::Counterexample::empty());
    let result = demote_if_unsound(&before, failed);
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Failed should pass through unchanged: {result:?}"
    );

    let unknown = VerificationResult::Unknown(crate::verify::UnknownReason::Incomplete);
    let result = demote_if_unsound(&before, unknown);
    assert!(
        matches!(
            result,
            VerificationResult::Unknown(crate::verify::UnknownReason::Incomplete)
        ),
        "Unknown should pass through unchanged: {result:?}"
    );

    reset();
}

#[test]
#[timeout(30000)]
fn test_demote_if_unsound_demotes_verified_with_demoting_delta() {
    use crate::verify::{demote_if_unsound, UnknownReason, VerificationResult};

    reset();
    let before = snapshot();

    increment(UnsoundnessCategory::OpaqueCallTrueAssumption);

    let verified = VerificationResult::Verified(None);
    let result = demote_if_unsound(&before, verified);
    match &result {
        VerificationResult::Unknown(UnknownReason::Demoted(msg)) => {
            assert!(
                msg.contains("opaque_call_true_assumption"),
                "demotion message should cite the category: {msg}"
            );
        }
        other => panic!(
            "Verified should be demoted to Unknown(Demoted) when \
             OpaqueCallTrueAssumption fires: {other:?}"
        ),
    }

    reset();
}

#[test]
#[timeout(30000)]
fn test_demote_if_unsound_no_demotion_with_low_risk_only() {
    use crate::verify::{demote_if_unsound, VerificationResult};

    reset();
    let before = snapshot();

    // Increment only LOW risk categories
    increment(UnsoundnessCategory::UnsupportedConstructSkip);
    increment(UnsoundnessCategory::SortFallbackToIntFromVar);
    increment(UnsoundnessCategory::SortCoercionBridge);

    let verified = VerificationResult::Verified(None);
    let result = demote_if_unsound(&before, verified);
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Verified should NOT be demoted when only LOW risk categories fire: {result:?}"
    );

    reset();
}

/// Phase 1 soundness audit (#2663): mitigation_status covers all demoting categories
/// and non-demoting categories return "N/A".
#[test]
#[timeout(30000)]
fn test_mitigation_status_covers_all_demoting_categories() {
    // Every demoting category must have a non-"N/A" mitigation status.
    for cat in UnsoundnessCategory::ALL {
        let status = cat.mitigation_status();
        if cat.is_demoting() {
            assert!(
                !status.starts_with("N/A"),
                "{cat} is demoting but has no mitigation status: {status}"
            );
        } else {
            assert!(
                status.starts_with("N/A"),
                "{cat} is non-demoting but has a mitigation status: {status}"
            );
        }
    }
}

/// Phase 1 soundness audit (#2663): OpaqueCallTrueAssumption is neutralized.
#[test]
#[timeout(30000)]
fn test_opaque_call_mitigation_is_neutralized() {
    let status = UnsoundnessCategory::OpaqueCallTrueAssumption.mitigation_status();
    assert!(
        status.contains("NEUTRALIZED"),
        "OpaqueCallTrueAssumption should be NEUTRALIZED (requires(false) injected): {status}"
    );
}

/// Phase 1 soundness audit (#2663): IntegerCastIdentity is partially addressed.
#[test]
#[timeout(30000)]
fn test_integer_cast_mitigation_is_partially_addressed() {
    let status = UnsoundnessCategory::IntegerCastIdentity.mitigation_status();
    assert!(
        status.contains("PARTIALLY ADDRESSED"),
        "IntegerCastIdentity should be PARTIALLY ADDRESSED (BV truncation): {status}"
    );
}

/// Phase 1a soundness audit (#2663): SortFallbackToInt is now GENUINE (catch-alls reclassified).
#[test]
#[timeout(30000)]
fn test_sort_fallback_mitigation_is_genuine() {
    let status = UnsoundnessCategory::SortFallbackToInt.mitigation_status();
    assert!(
        status.contains("GENUINE"),
        "SortFallbackToInt should be GENUINE after Phase 1a reclassification: {status}"
    );
    assert!(
        status.contains("SortFallbackToIntFromCatchAll"),
        "SortFallbackToInt status should reference the reclassification: {status}"
    );
}

/// Phase 1a soundness audit (#2663): SortFallbackToIntFromCatchAll is LOW (non-demoting).
#[test]
#[timeout(30000)]
fn test_sort_fallback_catch_all_is_non_demoting() {
    assert!(
        !UnsoundnessCategory::SortFallbackToIntFromCatchAll.is_demoting(),
        "SortFallbackToIntFromCatchAll should be LOW (non-demoting) — \
         these are unreachable #[non_exhaustive] catch-all guards"
    );
    assert_eq!(
        UnsoundnessCategory::SortFallbackToIntFromCatchAll.expected_production_sites(),
        4,
        "SortFallbackToIntFromCatchAll should have 4 production sites: \
         sort_inference.rs(3) + sort_mapping.rs(1)"
    );
}
