// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// resolve_nameable_expr tests (#1119: zero direct coverage)
// =============================================================================

mod resolve_nameable_expr_tests {
    use super::*;
    use crate::encoder::sort_context::{resolve_nameable_expr, MutRefVarNames};

    #[test]
    #[timeout(30000)]
    fn test_bare_var() {
        assert_eq!(
            resolve_nameable_expr(&var("v"), None),
            Some("v".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_deref_var() {
        // *v → v_current
        assert_eq!(
            resolve_nameable_expr(&deref(var("v")), None),
            Some("v_current".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_final_var() {
        // ^v → v_final
        assert_eq!(
            resolve_nameable_expr(&final_expr(var("v")), None),
            Some("v_final".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_old_bare_var() {
        // old(v) → old_v
        assert_eq!(
            resolve_nameable_expr(&old(var("v")), None),
            Some("old_v".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_old_deref_var() {
        // old(*v) == *v → v_current (RustHorn: old(*v) keeps same name)
        assert_eq!(
            resolve_nameable_expr(&old(deref(var("v"))), None),
            Some("v_current".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_nested_deref_deref() {
        // *(*v) → v_current_current
        assert_eq!(
            resolve_nameable_expr(&deref(deref(var("v"))), None),
            Some("v_current_current".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_nested_final_deref() {
        // ^(*v) → v_current_final
        assert_eq!(
            resolve_nameable_expr(&final_expr(deref(var("v"))), None),
            Some("v_current_final".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_nested_deref_final() {
        // *(^v) → v_final_current
        assert_eq!(
            resolve_nameable_expr(&deref(final_expr(var("v"))), None),
            Some("v_final_current".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_nested_final_final() {
        // ^(^v) → v_final_final
        assert_eq!(
            resolve_nameable_expr(&final_expr(final_expr(var("v"))), None),
            Some("v_final_final".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_with_prefix() {
        // prefix propagation: old_ prefix on bare var
        assert_eq!(
            resolve_nameable_expr(
                &var("v"),
                Some(crate::encoder::sort_context::DerivedKind::Old)
            ),
            Some("old_v".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_non_nameable_returns_none() {
        // Int literal, BinOp → None
        assert_eq!(resolve_nameable_expr(&int(42), None), None);
        assert_eq!(resolve_nameable_expr(&add(var("x"), int(1)), None), None);
    }

    /// Critical consistency test: MutRefVarNames::new("v") must produce exactly
    /// the same names as calling resolve_nameable_expr with the equivalent
    /// PureExpr trees. This is the key invariant from #1119.
    #[test]
    #[timeout(30000)]
    fn test_names_consistency_with_resolve_nameable() {
        let names = MutRefVarNames::new("v");

        // current: *v → v_current
        assert_eq!(
            resolve_nameable_expr(&deref(var("v")), None)
                .expect("resolve *v should produce v_current"),
            names.current
        );
        // final_val: ^v → v_final
        assert_eq!(
            resolve_nameable_expr(&final_expr(var("v")), None)
                .expect("resolve ^v should produce v_final"),
            names.final_val
        );
        // Cross-compositions still resolve via resolve_nameable_expr
        // but are no longer pre-declared by MutRefVarNames (#2150 Phase 3).
        assert_eq!(
            resolve_nameable_expr(&final_expr(deref(var("v"))), None),
            Some("v_current_final".to_string())
        );
        assert_eq!(
            resolve_nameable_expr(&deref(deref(var("v"))), None),
            Some("v_current_current".to_string())
        );
    }
}

// =============================================================================
// resolve_view_var_name tests (#1119: zero direct coverage)
// =============================================================================

mod resolve_view_var_name_tests {
    use super::*;
    use crate::encoder::sort_context::resolve_view_var_name;

    #[test]
    #[timeout(30000)]
    fn test_view_bare_var() {
        // View(Var("v")) → v_view
        assert_eq!(
            resolve_view_var_name(&view(var("v")), None),
            Some("v_view".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_view_var_with_prefix() {
        // View(Var("v")) with prefix "old_" → old_v_view
        assert_eq!(
            resolve_view_var_name(
                &view(var("v")),
                Some(crate::encoder::sort_context::DerivedKind::Old)
            ),
            Some("old_v_view".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_view_final_var() {
        // View(Final(Var("v"))) → final_v_view
        assert_eq!(
            resolve_view_var_name(&view(final_expr(var("v"))), None),
            Some("final_v_view".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_old_view_var() {
        // Old(View(Var("v"))) → old_v_view
        assert_eq!(
            resolve_view_var_name(&old(view(var("v"))), None),
            Some("old_v_view".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_old_view_final_var() {
        // Old(View(Final(Var("v")))) → final_old_v_view
        assert_eq!(
            resolve_view_var_name(&old(view(final_expr(var("v")))), None),
            Some("final_old_v_view".to_string())
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_bare_var_returns_none() {
        // Var("v") without View wrapper → None
        assert_eq!(resolve_view_var_name(&var("v"), None), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_deref_returns_none() {
        // Deref(Var("v")) → None (not a view expression)
        assert_eq!(resolve_view_var_name(&deref(var("v")), None), None);
    }

    #[test]
    #[timeout(30000)]
    fn test_old_non_view_returns_none() {
        // Old(Var("v")) → None (old wrapping non-view)
        assert_eq!(resolve_view_var_name(&old(var("v")), None), None);
    }
}

// =============================================================================
// register_sort_hints priority tests (#1517)
// =============================================================================

/// Seq hint must not be overwritten by a subsequent Bool hint in the pre-scan.
/// (#1517)
///
/// When a variable appears in both Seq context (e.g., `.len()` receiver) and
/// Bool context (e.g., inside `Not`), `register_sort_hints` records Seq first,
/// then Bool. Before the fix, Bool silently overwrote Seq via HashMap::insert.
#[test]
#[timeout(30000)]
fn sort_hint_seq_not_overwritten_by_bool_via_register() {
    use trust_wp_core::formula::ExprSort;
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Build an expression where "v_view" is both a Seq receiver (.len())
    // and appears in Bool context (Not(Var("v_view")))
    let len_call = method_call(view(var("v")), "len", vec![]);
    let comparison = gt(len_call, int(0));
    let not_v = not(var("v_view"));
    let combined = and(comparison, not_v);

    encoder.register_sort_hints(std::slice::from_ref(&combined));

    assert_eq!(
        encoder.sort_resolver_for_test().get_sort_hint("v_view"),
        Some(&ExprSort::Seq),
        "After register_sort_hints, Seq must survive Bool conflict for v_view"
    );
}

/// Verify the accumulator detects both Seq and Bool hints for the same variable
/// in a conflicting expression. (#1517)
#[test]
#[timeout(30000)]
fn sort_hint_accumulator_detects_seq_bool_conflict() {
    use crate::encoder::sort_context::{collect_all_sort_hints, SortHintAccumulator};

    // v@.len() > 0 && Not(v_view) — v_view is both Seq and Bool
    let len_call = method_call(view(var("v")), "len", vec![]);
    let comparison = gt(len_call, int(0));
    let not_v = not(var("v_view"));
    let combined = and(comparison, not_v);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&combined, &mut acc);

    assert!(
        acc.seqs.contains("v_view"),
        "v_view should be detected as Seq from .len() receiver; seqs={:?}",
        acc.seqs,
    );
    assert!(
        acc.bool_vars.contains("v_view"),
        "v_view should be detected as Bool from Not(v_view); bool_vars={:?}",
        acc.bool_vars,
    );
}

/// Bool-only variable should still get a Bool hint (no false negatives). (#1517)
#[test]
#[timeout(30000)]
fn sort_hint_bool_only_still_recorded() {
    use trust_wp_core::formula::ExprSort;
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Not(b) — b should be tagged as Bool, no Seq conflict
    let expr = not(var("b"));
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    assert_eq!(
        encoder.sort_resolver_for_test().get_sort_hint("b"),
        Some(&ExprSort::Bool),
        "Pure Bool variable must still get Bool hint"
    );
}
