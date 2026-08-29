// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::*;
use crate::tests::helpers::{points_to_int, sep_conj};

#[test]
#[timeout(30000)]
fn footprint_cached_returns_cached_rc_on_hit() {
    let mut encoder = AYEncoder::new();

    let outer = sep_conj(
        sep_conj(points_to_int("cache_a", 1), points_to_int("cache_b", 2)),
        points_to_int("cache_c", 3),
    );
    encoder
        .encode(&outer)
        .expect("nested sep conj should encode and populate cache");

    let Formula::SepConj(inner_box, _) = &outer else {
        panic!("outer formula should be SepConj");
    };
    let inner_formula = inner_box.as_ref();
    let inner_key = FormulaCacheKey::for_formula(inner_formula);
    let inner_cached = encoder
        .sep_cache
        .get_footprint(&inner_key)
        .expect("inner SepConj footprint should be cached");
    let inner_hit = encoder.footprint_cached(inner_formula);
    assert!(
        Rc::ptr_eq(&inner_cached, &inner_hit),
        "cache hit should return the cached Rc for inner SepConj"
    );

    let outer_key = FormulaCacheKey::for_formula(&outer);
    let outer_cached = encoder
        .sep_cache
        .get_footprint(&outer_key)
        .expect("outer SepConj footprint should be cached");
    let outer_hit = encoder.footprint_cached(&outer);
    assert!(
        Rc::ptr_eq(&outer_cached, &outer_hit),
        "cache hit should return the cached Rc for outer SepConj"
    );
}

#[test]
#[timeout(30000)]
fn quantified_incremental_stages_domain_facts_and_constraint_sets() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let left_locs = vec![
        "__sep_left_0".to_string(),
        "__sep_left_1".to_string(),
        "__sep_left_2".to_string(),
    ];
    let right_locs = vec!["__sep_right_0".to_string(), "__sep_right_1".to_string()];

    let (activation_term, _combined_domain, combined_terms) = encoder
        .encode_quantified_disjointness_incremental(&left_locs, &right_locs, None)
        .expect("quantified incremental encoding should succeed");

    assert_eq!(
        combined_terms.len(),
        left_locs.len() + right_locs.len(),
        "combined terms should include both footprints"
    );
    let expected_pending = (left_locs.len() * 2) + (right_locs.len() * 2) + left_locs.len();
    assert_eq!(
        encoder.assertion_pipeline.pending_assertions_len(),
        expected_pending,
        "encoding should stage finite domain membership and exclusion facts"
    );
    assert_eq!(
        encoder
            .assertion_pipeline
            .pending_disjoint_constraints()
            .len(),
        1,
        "encoding should stage one cross-footprint constraint set"
    );

    let (pending_left, pending_right) =
        &encoder.assertion_pipeline.pending_disjoint_constraints()[0];
    assert_eq!(
        pending_left.len(),
        left_locs.len(),
        "pending left terms should match left footprint cardinality"
    );
    assert_eq!(
        pending_right.len(),
        right_locs.len(),
        "pending right terms should match right footprint cardinality"
    );
    let forced_left = pending_left[0];
    let forced_right = pending_right[0];

    encoder.assert_term(activation_term);
    assert!(
        encoder.assertion_pipeline.pending_assertions_is_empty(),
        "assert_term should flush all staged domain facts"
    );
    assert!(
        encoder
            .assertion_pipeline
            .pending_disjoint_constraints()
            .is_empty(),
        "assert_term should activate pending quantified constraints"
    );
    assert_eq!(
        encoder.assertion_pipeline.active_disjoint_constraints_len(),
        1,
        "active quantified constraints should include the staged set"
    );

    let forced_alias = encoder.solver.eq(forced_left, forced_right);
    encoder.assert_term(forced_alias);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "forced cross-footprint alias should violate quantified disjointness, got {sat:?}"
    );
}

fn assert_cached_constraint_shape(
    encoder: &AYEncoder,
    parent_terms: &[Term],
    stale_left_len: usize,
    next_right_len: usize,
    combined_terms_len: usize,
) {
    let expected_pending = next_right_len + parent_terms.len() + combined_terms_len;
    assert_eq!(
        encoder.assertion_pipeline.pending_assertions_len(),
        expected_pending,
        "cached path should stage right-side membership, left exclusion, and combined-domain facts"
    );
    assert_eq!(
        encoder
            .assertion_pipeline
            .pending_disjoint_constraints()
            .len(),
        1,
        "cached path should stage one quantified constraint set"
    );

    let (pending_left, pending_right) =
        &encoder.assertion_pipeline.pending_disjoint_constraints()[0];
    assert_eq!(
        pending_left.len(),
        parent_terms.len(),
        "cached path must reuse parent terms"
    );
    assert_ne!(
        pending_left.len(),
        stale_left_len,
        "cached path should not re-resolve stale_left"
    );
    assert_eq!(
        pending_right.len(),
        next_right_len,
        "right footprint should match new right terms"
    );
    assert_eq!(
        pending_left.as_slice(),
        parent_terms,
        "left terms should be exactly the cached parent terms"
    );
    assert_eq!(
        combined_terms_len,
        parent_terms.len() + next_right_len,
        "combined cache should append new right terms"
    );
}

#[test]
#[timeout(60000)]
fn quantified_incremental_reuses_cached_parent_terms_and_domain() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let base_left = vec!["__sep_base_left".to_string()];
    let base_right = vec!["__sep_base_right".to_string()];
    let (_base_term, parent_domain, parent_terms) = encoder
        .encode_quantified_disjointness_incremental(&base_left, &base_right, None)
        .expect("base incremental encoding should succeed");
    assert_eq!(
        parent_terms.len(),
        2,
        "base call should produce left+right cached terms"
    );

    encoder
        .assertion_pipeline
        .clear_pending_assertions_for_test();
    encoder
        .assertion_pipeline
        .clear_pending_disjoint_constraints_for_test();

    let stale_left = vec!["__sep_not_in_cache".to_string()];
    let next_right = vec![
        "__sep_next_right_0".to_string(),
        "__sep_next_right_1".to_string(),
    ];
    let (membership_term, _combined_domain, combined_terms) = encoder
        .encode_quantified_disjointness_incremental(
            &stale_left,
            &next_right,
            Some((parent_domain, parent_terms.clone())),
        )
        .expect("cached incremental encoding should succeed");

    assert_cached_constraint_shape(
        &encoder,
        &parent_terms,
        stale_left.len(),
        next_right.len(),
        combined_terms.len(),
    );

    let (pending_left, pending_right) =
        &encoder.assertion_pipeline.pending_disjoint_constraints()[0];
    let forced_left = pending_left[0];
    let forced_right = pending_right[0];
    encoder.assert_term(membership_term);
    let forced_alias = encoder.solver.eq(forced_left, forced_right);
    encoder.assert_term(forced_alias);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "cached-path disjointness must be Unsat under forced alias, got {sat:?}"
    );
}

#[test]
#[timeout(30000)]
fn quantified_incremental_overlap_short_circuits_to_false() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let left_locs = vec!["__sep_overlap".to_string()];
    let right_locs = vec!["__sep_overlap".to_string()];

    let (term, _combined_domain, combined_terms) = encoder
        .encode_quantified_disjointness_incremental(&left_locs, &right_locs, None)
        .expect("overlap path should return an immediate contradiction");

    assert!(
        combined_terms.is_empty(),
        "overlap short-circuit should not carry forward any combined terms"
    );
    assert!(
        encoder.assertion_pipeline.pending_assertions_is_empty(),
        "overlap short-circuit should not stage domain facts"
    );
    assert!(
        encoder
            .assertion_pipeline
            .pending_disjoint_constraints()
            .is_empty(),
        "overlap short-circuit should not stage recheck constraints"
    );

    encoder.assert_term(term);
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "overlapping footprints must be immediately UNSAT, got {sat:?}"
    );
}

#[test]
#[timeout(30000)]
fn encode_points_to_stages_permission_constraints() {
    let mut encoder = AYEncoder::new();

    let location = Location("pt_loc".to_string());
    let value = Value::Expr(PureExpr::Int(42));
    let _term = encoder
        .encode_points_to(&location, &value, Permission::FULL)
        .expect("encode_points_to should succeed for Int value");

    assert_eq!(
        encoder.assertion_pipeline.pending_assertions_len(),
        3,
        "encode_points_to should stage 3 permission constraints via pipeline: \
         perm_ok, perm_bounded, perm_non_neg"
    );
}

#[test]
#[timeout(30000)]
fn encode_points_to_unknown_value_no_heap_constraint() {
    let mut encoder = AYEncoder::new();

    let location = Location("pt_unk".to_string());
    let term = encoder
        .encode_points_to(&location, &Value::Unknown, Permission::FULL)
        .expect("encode_points_to should succeed for Unknown value");

    assert_eq!(
        encoder.assertion_pipeline.pending_assertions_len(),
        3,
        "Unknown value should still stage permission constraints"
    );

    encoder.assert_term(term);

    let loc_term = encoder
        .get_or_declare_var("pt_unk", Sort::Int)
        .expect("location var should exist after encode_points_to");
    let heap_at_loc = encoder.solver.select(encoder.mem_state.heap, loc_term);
    let arbitrary_val = encoder.solver.int_const(999);
    let heap_pinned = encoder.solver.eq(heap_at_loc, arbitrary_val);
    encoder.assert_term(heap_pinned);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Unknown value should leave heap unconstrained — pinning heap[loc]=999 must be SAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn encode_points_to_expr_value_constrains_heap() {
    let mut encoder = AYEncoder::new();

    let location = Location("pt_expr".to_string());
    let term = encoder
        .encode_points_to(&location, &Value::Expr(PureExpr::Int(42)), Permission::FULL)
        .expect("encode_points_to should succeed for Expr value");

    encoder.assert_term(term);

    let loc_term = encoder
        .get_or_declare_var("pt_expr", Sort::Int)
        .expect("location var should exist");
    let heap_at_loc = encoder.solver.select(encoder.mem_state.heap, loc_term);
    let wrong_val = encoder.solver.int_const(999);
    let heap_pinned = encoder.solver.eq(heap_at_loc, wrong_val);
    encoder.assert_term(heap_pinned);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Expr(42) should constrain heap — pinning heap[loc]=999 must be UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn encode_points_to_same_location_different_values_unsat() {
    let mut encoder = AYEncoder::new();

    let location = Location("double_loc".to_string());

    let t1 = encoder
        .encode_points_to(&location, &Value::Expr(PureExpr::Int(1)), Permission::FULL)
        .expect("first encode_points_to should succeed");
    let t2 = encoder
        .encode_points_to(&location, &Value::Expr(PureExpr::Int(2)), Permission::FULL)
        .expect("second encode_points_to should succeed");

    let combined = encoder.solver.and(t1, t2);
    encoder.assert_term(combined);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "same location with different values must be UNSAT due to heap conflict, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn encode_points_to_double_full_same_value_sat_under_and() {
    let mut encoder = AYEncoder::new();

    let location = Location("dup_loc".to_string());

    let t1 = encoder
        .encode_points_to(&location, &Value::Expr(PureExpr::Int(42)), Permission::FULL)
        .expect("first encode_points_to should succeed");
    let t2 = encoder
        .encode_points_to(&location, &Value::Expr(PureExpr::Int(42)), Permission::FULL)
        .expect("second encode_points_to should succeed");

    let combined = encoder.solver.and(t1, t2);
    encoder.assert_term(combined);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "double-FULL same-value under And should be SAT (no disjointness), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn encode_points_to_bool_value_sort_coercion() {
    let mut encoder = AYEncoder::new();

    let location = Location("pt_bool".to_string());
    let term = encoder
        .encode_points_to(
            &location,
            &Value::Expr(PureExpr::Bool(true)),
            Permission::FULL,
        )
        .expect("encode_points_to should handle Bool value via sort coercion");

    assert_eq!(
        encoder.assertion_pipeline.pending_assertions_len(),
        3,
        "Bool value should still stage 3 permission constraints"
    );

    encoder.assert_term(term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Bool value via sort coercion should produce a satisfiable encoding, got {result:?}"
    );
}
