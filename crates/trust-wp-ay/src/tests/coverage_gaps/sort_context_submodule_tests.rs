// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for sort_context submodules after W3's decomposition (#1870 Phase 4).
//!
//! Targets:
//! - `resolve_view_var_name`: Old(View(...)), prefix handling, nested wrappers
//! - `resolve_nameable_expr`: Old(Deref(...)) bypass, Final wrapping
//! - `extract_base_var_name`: Recursive unwrapping through Deref/Final/Old/View
//! - `extract_constructor_name`: LogicFnCall, ITE branches, nullary constructors
//! - `collect_all_sort_hints`: FMap hints, Forall/Exists Seq var hints
//! - `MutRefVarNames`: Naming consistency
//! - Two-hop Seq propagation: final_X_view → X_view → X (#994)

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{BinOp, ExprSort, MatchArm, Pattern};

use super::*;
use crate::encoder::sort_context::{
    collect_all_sort_hints, extract_base_var_name, extract_constructor_name, infer_expr_sort,
    resolve_nameable_expr, resolve_view_var_name, SortHintAccumulator,
};

// ── resolve_view_var_name ─────────────────────────────────────────

/// View(Var("x")) → "x_view"
#[test]
#[timeout(30000)]
fn test_resolve_view_var_name_simple() {
    assert_eq!(
        resolve_view_var_name(&view(var("x")), None),
        Some("x_view".to_string())
    );
}

/// View(Final(Var("self"))) → "final_self_view"
#[test]
#[timeout(30000)]
fn test_resolve_view_var_name_final() {
    assert_eq!(
        resolve_view_var_name(&view(final_expr(var("self"))), None),
        Some("final_self_view".to_string())
    );
}

/// Old(View(Var("x"))) → "old_x_view"
#[test]
#[timeout(30000)]
fn test_resolve_view_var_name_old_view() {
    assert_eq!(
        resolve_view_var_name(&old(view(var("x"))), None),
        Some("old_x_view".to_string())
    );
}

/// Old(View(Final(Var("s")))) → "final_old_s_view"
#[test]
#[timeout(30000)]
fn test_resolve_view_var_name_old_view_final() {
    assert_eq!(
        resolve_view_var_name(&old(view(final_expr(var("s")))), None),
        Some("final_old_s_view".to_string())
    );
}

/// Non-View expression → None
#[test]
#[timeout(30000)]
fn test_resolve_view_var_name_non_view_returns_none() {
    assert_eq!(resolve_view_var_name(&var("x"), None), None);
    assert_eq!(resolve_view_var_name(&int(42), None), None);
    assert_eq!(resolve_view_var_name(&deref(var("x")), None), None);
}

/// Old without inner View → None
#[test]
#[timeout(30000)]
fn test_resolve_view_var_name_old_non_view_returns_none() {
    assert_eq!(resolve_view_var_name(&old(var("x")), None), None);
    assert_eq!(resolve_view_var_name(&old(deref(var("x"))), None), None);
}

// ── resolve_nameable_expr ─────────────────────────────────────────

/// Var("x") with no prefix → "x"
#[test]
#[timeout(30000)]
fn test_resolve_nameable_expr_simple_var() {
    assert_eq!(
        resolve_nameable_expr(&var("x"), None),
        Some("x".to_string())
    );
}

/// Var("x") with prefix "old_" → "old_x"
#[test]
#[timeout(30000)]
fn test_resolve_nameable_expr_with_prefix() {
    assert_eq!(
        resolve_nameable_expr(
            &var("x"),
            Some(crate::encoder::sort_context::DerivedKind::Old)
        ),
        Some("old_x".to_string())
    );
}

/// Deref(Var("x")) → "x_current"
#[test]
#[timeout(30000)]
fn test_resolve_nameable_expr_deref() {
    assert_eq!(
        resolve_nameable_expr(&deref(var("x")), None),
        Some("x_current".to_string())
    );
}

/// Final(Var("x")) → "x_final"
#[test]
#[timeout(30000)]
fn test_resolve_nameable_expr_final() {
    assert_eq!(
        resolve_nameable_expr(&final_expr(var("x")), None),
        Some("x_final".to_string())
    );
}

/// Old(Var("x")) → prefix becomes "old_", so "old_x"
#[test]
#[timeout(30000)]
fn test_resolve_nameable_expr_old() {
    assert_eq!(
        resolve_nameable_expr(&old(var("x")), None),
        Some("old_x".to_string())
    );
}

/// Old(Deref(Var("x"))) → Old delegates to inner (Deref bypass), giving "x_current"
#[test]
#[timeout(30000)]
fn test_resolve_nameable_expr_old_deref_bypass() {
    assert_eq!(
        resolve_nameable_expr(&old(deref(var("x"))), None),
        Some("x_current".to_string()),
        "Old(Deref(...)) should bypass old_ prefix"
    );
}

/// Non-nameable expression → None
#[test]
#[timeout(30000)]
fn test_resolve_nameable_expr_non_var_returns_none() {
    assert_eq!(resolve_nameable_expr(&int(42), None), None);
    assert_eq!(resolve_nameable_expr(&not(var("x")), None), None);
    assert_eq!(resolve_nameable_expr(&add(var("x"), var("y")), None), None);
}

/// `MutRef(Seq)` should still be recognized by the Seq receiver helper. (#2141)
#[test]
#[timeout(30000)]
fn test_is_seq_receiver_accepts_mutref_seq_annotation() {
    let encoder = AYEncoder::new();
    let receiver = view(deref(var_with_sort(
        "xs",
        ExprSort::MutRef(Box::new(ExprSort::Seq)),
    )));
    assert!(
        encoder.is_seq_receiver(&receiver, None),
        "View(Deref(MutRef(Seq))) should still classify as a Seq receiver"
    );
    assert_eq!(
        infer_expr_sort(&deref(var_with_sort(
            "xs",
            ExprSort::MutRef(Box::new(ExprSort::Seq)),
        ))),
        Sort::seq(Sort::Int),
        "Deref(MutRef(Seq)) should still infer as Seq"
    );
}

// ── extract_base_var_name ─────────────────────────────────────────

/// Simple variable
#[test]
#[timeout(30000)]
fn test_extract_base_var_name_simple() {
    assert_eq!(extract_base_var_name(&var("x")), Some("x"));
}

/// Nested wrappers: Deref(Final(Old(View(Var("s"))))) → "s"
#[test]
#[timeout(30000)]
fn test_extract_base_var_name_nested_wrappers() {
    let nested = deref(final_expr(old(view(var("s")))));
    assert_eq!(
        extract_base_var_name(&nested),
        Some("s"),
        "should recurse through all wrapper types"
    );
}

/// Non-var expression → None
#[test]
#[timeout(30000)]
fn test_extract_base_var_name_non_var() {
    assert_eq!(extract_base_var_name(&int(42)), None);
    assert_eq!(extract_base_var_name(&not(var("x"))), None);
}

// ── extract_constructor_name ──────────────────────────────────────

/// LogicFnCall → name
#[test]
#[timeout(30000)]
fn test_extract_constructor_name_logic_fn() {
    assert_eq!(
        extract_constructor_name(&logic_fn_call("Some", vec![int(1)])),
        Some("Some")
    );
}

/// Nullary constructor "None" as Var
#[test]
#[timeout(30000)]
fn test_extract_constructor_name_nullary_none() {
    assert_eq!(extract_constructor_name(&var("None")), Some("None"));
}

/// Regular variable is not a constructor
#[test]
#[timeout(30000)]
fn test_extract_constructor_name_regular_var() {
    assert_eq!(extract_constructor_name(&var("x")), None);
}

/// ITE branches: picks the constructor from either branch
#[test]
#[timeout(30000)]
fn test_extract_constructor_name_ite_picks_branch() {
    let ite_expr = ite(
        var("cond"),
        logic_fn_call("Some", vec![int(1)]),
        logic_fn_call("None", vec![]),
    );
    // Should find Some from the then branch
    assert_eq!(extract_constructor_name(&ite_expr), Some("Some"));
}

/// Nested wrapper around constructor
#[test]
#[timeout(30000)]
fn test_extract_constructor_name_through_wrapper() {
    let wrapped = final_expr(logic_fn_call("Ok", vec![int(1)]));
    assert_eq!(extract_constructor_name(&wrapped), Some("Ok"));
}

// ── collect_all_sort_hints: FMap detection ─────────────────────

/// `x.lookup(key)` should mark x_view as FMap
#[test]
#[timeout(30000)]
fn test_collect_all_sort_hints_fmap_from_lookup() {
    let expr = method_call(view(var("m")), "lookup", vec![int(1)]);
    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);

    assert!(
        acc.fmaps.contains("m_view"),
        "view(m).lookup() should tag m_view as FMap"
    );
}

/// `m.insert(k, v)` should mark bare m as FMap
#[test]
#[timeout(30000)]
fn test_collect_all_sort_hints_fmap_from_insert() {
    let expr = method_call(var("m"), "insert", vec![int(1), int(2)]);
    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);

    assert!(
        acc.fmaps.contains("m"),
        "m.insert() should tag bare m as FMap"
    );
}

// ── collect_all_sort_hints: Forall/Exists Seq ──────────────────

/// `forall<s: Seq> P(s)` should mark s as Seq hint
#[test]
#[timeout(30000)]
fn test_collect_all_sort_hints_forall_seq_var() {
    let expr = PureExpr::Forall {
        var: "s".to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(var("s")),
        triggers: vec![],
    };
    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);

    assert!(
        acc.seqs.contains("s"),
        "forall with Seq var_sort should mark var as Seq"
    );
}

/// `exists<s: Seq> P(s)` should mark s as Seq hint
#[test]
#[timeout(30000)]
fn test_collect_all_sort_hints_exists_seq_var() {
    let expr = PureExpr::Exists {
        var: "s".to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(var("s")),
        triggers: vec![],
    };
    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);

    assert!(
        acc.seqs.contains("s"),
        "exists with Seq var_sort should mark var as Seq"
    );
}

// ── Two-hop Seq propagation (#994) ────────────────────────────────

/// Verify the two-hop chain: final_x_view → x_view → x
///
/// When only `final_x_view` is discovered during prescan (e.g., from
/// `(^self).len()`), the propagation in `register_sort_hints` must
/// back-propagate in two hops to reach the bare base name.
#[test]
#[timeout(30000)]
fn test_two_hop_seq_propagation_994() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only final(self).len() — prescan detects final_self_view as Seq
    let exprs = vec![method_call(final_expr(var("self")), "len", vec![])];
    encoder.register_sort_hints(&exprs);

    // Verify all three levels got the Seq hint
    assert!(
        matches!(
            encoder
                .sort_resolver_for_test()
                .get_sort_hint("final_self_view"),
            Some(ExprSort::Seq)
        ),
        "final_self_view should have Seq hint (direct detection)"
    );
    assert!(
        matches!(
            encoder.sort_resolver_for_test().get_sort_hint("self_view"),
            Some(ExprSort::Seq)
        ),
        "self_view should have Seq hint (first-hop propagation)"
    );
    assert!(
        matches!(
            encoder.sort_resolver_for_test().get_sort_hint("self"),
            Some(ExprSort::Seq)
        ),
        "bare self should have Seq hint (second-hop propagation)"
    );
}

/// Single-hop propagation: x_view → x
#[test]
#[timeout(30000)]
fn test_single_hop_seq_propagation() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // view(v).push_back(x) — directly tags v_view as Seq
    let exprs = vec![method_call(view(var("v")), "push_back", vec![int(1)])];
    encoder.register_sort_hints(&exprs);

    assert!(
        matches!(
            encoder.sort_resolver_for_test().get_sort_hint("v_view"),
            Some(ExprSort::Seq)
        ),
        "v_view should have Seq hint (direct detection)"
    );
    assert!(
        matches!(
            encoder.sort_resolver_for_test().get_sort_hint("v"),
            Some(ExprSort::Seq)
        ),
        "bare v should have Seq hint (single-hop propagation)"
    );
}

// ── MutRefVarNames consistency ────────────────────────────────────

/// Verify MutRefVarNames produces the expected naming pattern.
#[test]
#[timeout(30000)]
fn test_mut_ref_var_names_consistency() {
    use crate::encoder::sort_context::MutRefVarNames;

    let names = MutRefVarNames::new("self_");
    assert_eq!(names.current, "self__current");
    assert_eq!(names.final_val, "self__final");
}

// ── infer_expr_sort edge cases ────────────────────────────────────

/// Int literal → Int
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_int_literal() {
    assert_eq!(infer_expr_sort(&int(42)), Sort::Int);
}

/// Bool literal → Bool
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_bool_literal() {
    assert_eq!(infer_expr_sort(&bool_expr(true)), Sort::Bool);
}

/// Var with Seq sort annotation → Seq uninterpreted sort
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_seq_annotated_var() {
    let expr = var_with_sort("s", ExprSort::Seq);
    assert_eq!(infer_expr_sort(&expr), Sort::seq(Sort::Int));
}

/// Neg(x) → Int
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_neg() {
    assert_eq!(infer_expr_sort(&neg(var("x"))), Sort::Int);
}

/// Not(x) where x is unannotated → Bool. Unannotated variables are not
/// `is_definitely_non_bool`, so Not defaults to logical negation (Bool). (#1096)
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_not() {
    assert_eq!(infer_expr_sort(&not(var("x"))), Sort::Bool);
}

/// Add(x, y) → Int
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_add() {
    assert_eq!(infer_expr_sort(&add(var("x"), var("y"))), Sort::Int);
}

/// x == y → Bool
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_eq() {
    assert_eq!(
        infer_expr_sort(&binop(var("x"), BinOp::Eq, var("y"))),
        Sort::Bool
    );
}

/// x > y → Bool
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_gt() {
    assert_eq!(
        infer_expr_sort(&binop(var("x"), BinOp::Gt, var("y"))),
        Sort::Bool
    );
}

// ── is_fmap_only_method prescan arity bug (#2057 P1-30 finding) ─────

/// 1-arg `insert(elem)` is FSet — prescan should NOT tag receiver as FMap.
///
/// `is_fmap_only_method` now excludes "insert" (arity-dependent: 2-arg → FMap,
/// 1-arg → FSet). The prescan correctly leaves 1-arg insert receivers out of
/// `acc.fmaps`. (#2059)
#[test]
#[timeout(30000)]
fn test_prescan_1arg_insert_should_not_tag_fmap() {
    let expr = method_call(var("s"), "insert", vec![var("elem")]);
    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);
    assert!(
        !acc.fmaps.contains("s"),
        "1-arg insert is FSet, not FMap — receiver should NOT be in acc.fmaps"
    );
}

/// 2-arg `insert(key, value)` is FMap — prescan should tag receiver as FMap.
#[test]
#[timeout(30000)]
fn test_prescan_2arg_insert_correctly_tags_fmap() {
    let expr = method_call(var("m"), "insert", vec![var("k"), var("v")]);
    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);
    assert!(
        acc.fmaps.contains("m"),
        "2-arg insert should tag receiver as FMap"
    );
}

/// FSet `insert` encoding works correctly after arity-aware prescan fix.
///
/// Previously `is_fmap_only_method` incorrectly included 1-arg "insert",
/// tagging the receiver as FMap sort and causing a ay sort mismatch panic.
/// Now the prescan is arity-aware: 1-arg insert → FSet, 2-arg → FMap. (#2059)
#[test]
#[timeout(30000)]
fn test_fset_1arg_insert_encoding_succeeds() {
    let result = std::panic::catch_unwind(|| {
        let mut encoder = crate::encoder::AYEncoder::new();
        let expr = method_call(var("s"), "insert", vec![var("elem")]);
        encoder.encode_pure(&expr)
    });
    assert!(
        result.is_ok() && result.unwrap().is_ok(),
        "FSet 1-arg insert should encode cleanly after arity-aware prescan fix"
    );
}

// ── infer_expr_sort: Ite/Match concrete sort preference ─────────

/// Ite where then-branch is Int (default) and else-branch is Bool (concrete)
/// should infer Bool, not Int. (#1965 Phase 2 audit)
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_ite_prefers_concrete_else_sort() {
    // Ite(cond, Var("x", None), Bool(true))
    // then_sort = Int (unknown/default), else_sort = Bool (concrete)
    let expr = ite(var("cond"), var("x"), bool_expr(true));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Ite should prefer concrete else_sort (Bool) over Int default in then_sort"
    );
}

/// Ite where both branches are concrete should return then_sort (no change).
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_ite_both_concrete_returns_then() {
    // Ite(cond, Bool(false), Bool(true)) — both Bool, returns Bool
    let expr = ite(var("cond"), bool_expr(false), bool_expr(true));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Ite with both Bool branches should return Bool"
    );
}

/// Ite where then is concrete and else is Int — returns then (no override).
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_ite_concrete_then_int_else() {
    // Ite(cond, Bool(true), Var("x", None))
    // then_sort = Bool (concrete), else_sort = Int (default)
    let expr = ite(var("cond"), bool_expr(true), var("x"));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Ite with concrete then_sort should return it even if else is Int"
    );
}

/// Ite where then-branch is Int and else-branch is Seq (annotated var).
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_ite_int_then_seq_else() {
    let expr = ite(var("cond"), var("x"), var_with_sort("s", ExprSort::Seq));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "Ite should prefer concrete Seq in else over Int default in then"
    );
}

// ── infer_expr_sort: Match concrete sort preference ──────────────

/// Match where the first arm body is Int (default) and a later arm body is
/// Bool (concrete) should return Bool. (#1965 Phase 2 audit — Match case)
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_match_prefers_concrete_later_arm() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("a"), // infers as Int (no annotation)
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(true), // infers as Bool
            },
        ],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Match should prefer concrete arm sort (Bool) over Int default in first arm"
    );
}

/// Match where the first arm is concrete (Bool) and a later arm is Int —
/// should return the first arm's sort (no override needed).
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_match_concrete_first_arm_kept() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(false), // infers as Bool
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("a"), // infers as Int
            },
        ],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Match with concrete first arm should return it even if later arms are Int"
    );
}

/// Match where the first arm is Int and a later arm is Seq (annotated).
/// The concrete Seq sort should be preferred over the default Int.
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_match_int_first_seq_later() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("a"), // Int (default)
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("b"), // also Int (default)
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var_with_sort("s", ExprSort::Seq), // Seq (concrete)
            },
        ],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "Match should find concrete Seq in third arm when first two are Int"
    );
}

/// Match where all arms are Int — should return Int (no concrete override).
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_match_all_int_returns_int() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("a"),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: var("b"),
            },
        ],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Match with all Int arms should return Int"
    );
}

/// Match with empty arms falls through to default Int sort.
/// Boundary: exercises the `!arms.is_empty()` guard in sort_inference.rs:191.
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_match_empty_arms_returns_int() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Match with empty arms should fall through to default Int"
    );
}

/// Match with a single concrete arm — no skip(1) iteration needed.
/// Boundary: ensures single-arm match returns first_sort directly.
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_match_single_bool_arm() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("x")),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: bool_expr(true),
        }],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Match with single Bool arm should return Bool"
    );
}
