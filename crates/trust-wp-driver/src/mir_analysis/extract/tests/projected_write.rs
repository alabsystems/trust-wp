// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
// ── Projected-write fact invalidation on whole-local reassignment (#1450) ──

#[test]
fn projected_write_facts_cleared_on_matching_local_name() {
    // Simulate: pair.0 = 5, pair.1 = 10, then pair = (7, 20)
    // After whole-local reassignment, facts referencing "pair" are cleared.
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();

    let lhs_0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };
    let lhs_1 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };

    record_projected_write_fact(&mut facts, lhs_0, PureExpr::Int(5));
    record_projected_write_fact(&mut facts, lhs_1, PureExpr::Int(10));
    assert_eq!(facts.len(), 2);

    // Whole-local reassignment: clear facts referencing "pair"
    let name = "pair";
    facts.retain(|(lhs, _)| !expr_references_var_name(lhs, name));
    assert_eq!(
        facts.len(),
        0,
        "all facts referencing 'pair' should be cleared after whole-local reassignment"
    );
}

#[test]
fn projected_write_facts_for_other_locals_survive() {
    // Simulate: a.0 = 1, b.0 = 2, then a = (7,)
    // Only facts referencing "a" are cleared; "b" facts survive.
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();

    let lhs_a = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("a".to_string(), None)],
    };
    let lhs_b = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("b".to_string(), None)],
    };

    record_projected_write_fact(&mut facts, lhs_a, PureExpr::Int(1));
    record_projected_write_fact(&mut facts, lhs_b.clone(), PureExpr::Int(2));
    assert_eq!(facts.len(), 2);

    // Whole-local reassignment of "a" only
    facts.retain(|(lhs, _)| !expr_references_var_name(lhs, "a"));
    assert_eq!(facts.len(), 1, "only 'a' facts should be cleared");
    assert_eq!(facts[0].0, lhs_b, "'b' fact should survive");
}

#[test]
fn projected_write_facts_clear_descendants_on_prefix_write() {
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    let base = PureExpr::Var("pair".to_string(), None);
    let lhs_prefix = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![base.clone()],
    };
    let lhs_descendant = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![lhs_prefix.clone()],
    };
    let lhs_sibling = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![base],
    };
    record_projected_write_fact(&mut facts, lhs_descendant, PureExpr::Int(10));
    record_projected_write_fact(&mut facts, lhs_sibling.clone(), PureExpr::Int(20));
    assert_eq!(facts.len(), 2);

    invalidate_overlapping_projected_write_facts(&mut facts, &lhs_prefix);

    assert_eq!(facts.len(), 1, "descendant fact should be invalidated");
    assert_eq!(facts[0].0, lhs_sibling, "sibling fact should survive");
}

#[test]
fn projected_write_facts_clear_ancestors_on_deeper_write() {
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    let base = PureExpr::Var("pair".to_string(), None);
    let lhs_prefix = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![base.clone()],
    };
    let lhs_descendant = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![lhs_prefix.clone()],
    };
    let lhs_sibling = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![base],
    };
    record_projected_write_fact(&mut facts, lhs_prefix, PureExpr::Int(7));
    record_projected_write_fact(&mut facts, lhs_sibling.clone(), PureExpr::Int(20));
    assert_eq!(facts.len(), 2);

    invalidate_overlapping_projected_write_facts(&mut facts, &lhs_descendant);

    assert_eq!(facts.len(), 1, "ancestor fact should be invalidated");
    assert_eq!(facts[0].0, lhs_sibling, "sibling fact should survive");
}

// ── Projected-write fact algorithm boundary conditions (#904) ────────

#[test]
fn projected_write_last_write_wins_then_parent_invalidation() {
    // Sequence: pair.0 = 5, pair.0 = 7 (overwrites), pair.1 = 10,
    // then invalidate via parent write "pair".
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    let base = PureExpr::Var("pair".to_string(), None);
    let lhs_0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![base.clone()],
    };
    let lhs_1 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![base.clone()],
    };

    record_projected_write_fact(&mut facts, lhs_0.clone(), PureExpr::Int(5));
    assert_eq!(facts.len(), 1);

    // Overwrite pair.0: last-write-wins
    record_projected_write_fact(&mut facts, lhs_0.clone(), PureExpr::Int(7));
    assert_eq!(
        facts.len(),
        1,
        "duplicate LHS should replace, not accumulate"
    );
    assert_eq!(facts[0].1, PureExpr::Int(7), "should keep last write value");

    record_projected_write_fact(&mut facts, lhs_1.clone(), PureExpr::Int(10));
    assert_eq!(facts.len(), 2);

    // Write to parent "pair" invalidates both children
    invalidate_overlapping_projected_write_facts(&mut facts, &base);
    assert_eq!(
        facts.len(),
        0,
        "writing to base should invalidate all child projected facts"
    );
}

#[test]
fn projected_write_three_level_nesting_invalidation() {
    // Test 3-level deep nesting: x.a.b.c
    // Writing to x.a should invalidate x.a.b.c but not x.d
    let base = PureExpr::Var("x".to_string(), None);
    let x_a = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![base.clone()],
    };
    let x_a_b = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![x_a.clone()],
    };
    let x_a_b_c = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![x_a_b.clone()],
    };
    let x_d = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_3".to_string(),
        args: vec![base],
    };

    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    record_projected_write_fact(&mut facts, x_a_b_c, PureExpr::Int(1));
    record_projected_write_fact(&mut facts, x_d.clone(), PureExpr::Int(2));
    assert_eq!(facts.len(), 2);

    // Write to x.a should invalidate x.a.b.c (descendant) but not x.d (sibling)
    invalidate_overlapping_projected_write_facts(&mut facts, &x_a);
    assert_eq!(
        facts.len(),
        1,
        "only x.a.b.c (descendant of x.a) should be invalidated"
    );
    assert_eq!(facts[0].0, x_d, "x.d (sibling) should survive");
}

#[test]
fn projected_write_invalidation_on_empty_facts() {
    // Invalidation on empty vec should not panic
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    let lhs = PureExpr::Var("x".to_string(), None);
    invalidate_overlapping_projected_write_facts(&mut facts, &lhs);
    assert_eq!(facts.len(), 0);
}

#[test]
fn projected_write_self_path_invalidation() {
    // Writing to the exact same path as an existing fact should invalidate it
    // (because expr_contains_subexpr(a, a) == true for any a)
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    let lhs = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };
    record_projected_write_fact(&mut facts, lhs.clone(), PureExpr::Int(5));
    assert_eq!(facts.len(), 1);

    // Invalidating with the same path should clear it
    invalidate_overlapping_projected_write_facts(&mut facts, &lhs);
    assert_eq!(
        facts.len(),
        0,
        "self-path invalidation should clear the fact"
    );
}

#[test]
fn projected_write_base_variable_invalidates_all_projections() {
    // Writing the base variable `x` should invalidate all projection facts
    // on `x`, because `Var("x")` is a subexpr of `tuple_get_0(Var("x"))`.
    let base = PureExpr::Var("x".to_string(), None);
    let x_0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![base.clone()],
    };
    let x_1 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![base.clone()],
    };
    let y_0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("y".to_string(), None)],
    };

    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    record_projected_write_fact(&mut facts, x_0, PureExpr::Int(1));
    record_projected_write_fact(&mut facts, x_1, PureExpr::Int(2));
    record_projected_write_fact(&mut facts, y_0.clone(), PureExpr::Int(3));
    assert_eq!(facts.len(), 3);

    invalidate_overlapping_projected_write_facts(&mut facts, &base);
    assert_eq!(facts.len(), 1, "all x projections should be invalidated");
    assert_eq!(facts[0].0, y_0, "y.0 should survive");
}

#[test]
fn record_projected_write_replaces_most_recent_only() {
    // Verify that record_projected_write_fact with the same LHS replaces
    // the existing entry and does not duplicate or create ordering issues.
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    let lhs = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let other_lhs = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };

    record_projected_write_fact(&mut facts, other_lhs.clone(), PureExpr::Int(100));
    record_projected_write_fact(&mut facts, lhs.clone(), PureExpr::Int(1));
    record_projected_write_fact(&mut facts, lhs.clone(), PureExpr::Int(2));
    record_projected_write_fact(&mut facts, lhs.clone(), PureExpr::Int(3));

    assert_eq!(
        facts.len(),
        2,
        "should have exactly 2 facts (other + latest lhs)"
    );
    // The replaced entry should be at the end (push after remove)
    assert_eq!(
        facts[0].0, other_lhs,
        "other fact should remain at position 0"
    );
    assert_eq!(facts[1].0, lhs, "replaced fact should be at position 1");
    assert_eq!(
        facts[1].1,
        PureExpr::Int(3),
        "should keep the last written value"
    );
}

/// Projected-write facts should be invalidated when a whole-local
/// reassignment targets a variable whose name appears in a fact LHS,
/// even when facts are from different base variables. This catches
/// potential stale-fact survival across reassignment boundaries. (#1535)
#[test]
fn projected_write_facts_invalidated_on_whole_local_reassignment_prevents_contradiction() {
    // Simulate: x.0 = 5, then x = (7, 20). The fact `tuple_get_0(x) == 5`
    // must be removed by the reassignment, otherwise both `x == (7, 20)` and
    // `tuple_get_0(x) == 5` would coexist — a contradiction.
    let x_field_0 = PureExpr::LogicFnCall {
        name: "tuple_get_0".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    record_projected_write_fact(&mut facts, x_field_0.clone(), PureExpr::Int(5));
    assert_eq!(facts.len(), 1, "should have one fact before reassignment");

    // Whole-local reassignment of `x` should invalidate facts referencing `x`
    facts.retain(|(lhs, _)| !expr_references_var_name(lhs, "x"));
    assert_eq!(
        facts.len(),
        0,
        "fact referencing x must be invalidated after whole-local reassignment of x"
    );
}

// ── Projected-write fact invalidation at function call boundaries (#1535) ──

/// When a `&mut pair.0` is passed to a function, projected-write facts
/// whose LHS overlaps with the referent expression must be invalidated.
/// The referent expression is what `local_exprs` records for the
/// temporary holding the mutable borrow.
#[test]
fn projected_write_facts_invalidated_by_mut_ref_to_exact_projected_path() {
    // Simulate: pair.0 = 5, pair.1 = 10, then modify(&mut pair.0)
    // The local_exprs entry for the &mut temporary is tuple_get_0(pair),
    // which is exactly the LHS of one fact. That fact must be removed,
    // but the sibling (pair.1) fact survives.
    let pair_0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };
    let pair_1 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    record_projected_write_fact(&mut facts, pair_0.clone(), PureExpr::Int(5));
    record_projected_write_fact(&mut facts, pair_1.clone(), PureExpr::Int(10));
    assert_eq!(facts.len(), 2);

    // Referent of `&mut pair.0` is tuple_get_0(pair)
    invalidate_overlapping_projected_write_facts(&mut facts, &pair_0);

    assert_eq!(facts.len(), 1, "exact-match fact must be invalidated");
    assert_eq!(facts[0].0, pair_1, "sibling fact must survive");
}

/// When a `&mut pair` is passed to a function (borrowing the whole
/// local), ALL projected-write facts for that local must be invalidated
/// because the callee can modify any field.
#[test]
fn projected_write_facts_invalidated_by_mut_ref_to_whole_local() {
    let pair_0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };
    let pair_1 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_1".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    record_projected_write_fact(&mut facts, pair_0, PureExpr::Int(5));
    record_projected_write_fact(&mut facts, pair_1, PureExpr::Int(10));
    assert_eq!(facts.len(), 2);

    // Referent of `&mut pair` is Var("pair")
    let referent = PureExpr::Var("pair".to_string(), None);
    invalidate_overlapping_projected_write_facts(&mut facts, &referent);

    assert_eq!(
        facts.len(),
        0,
        "all projected-write facts for the borrowed local must be invalidated"
    );
}

/// Projected-write facts for locals NOT borrowed by `&mut` must survive.
#[test]
fn projected_write_facts_unrelated_local_survives_mut_ref_invalidation() {
    let pair_0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("pair".to_string(), None)],
    };
    let other_0 = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![PureExpr::Var("other".to_string(), None)],
    };
    let mut facts: Vec<(PureExpr, PureExpr)> = Vec::new();
    record_projected_write_fact(&mut facts, pair_0, PureExpr::Int(5));
    record_projected_write_fact(&mut facts, other_0.clone(), PureExpr::Int(99));
    assert_eq!(facts.len(), 2);

    // Only `&mut pair` is passed — "other" facts should survive
    let referent = PureExpr::Var("pair".to_string(), None);
    invalidate_overlapping_projected_write_facts(&mut facts, &referent);

    assert_eq!(facts.len(), 1, "unrelated local's facts must survive");
    assert_eq!(facts[0].0, other_0);
}
