// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(30000)]
fn test_activate_pending_constraints_moves_pairs_and_updates_revision() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let left = encoder
        .get_or_declare_var("__ap_left", Sort::Int)
        .expect("left should declare");
    let right = encoder
        .get_or_declare_var("__ap_right", Sort::Int)
        .expect("right should declare");

    encoder
        .assertion_pipeline_mut_for_test()
        .push_pending_disjoint_constraint(vec![left], vec![right]);

    assert_eq!(
        encoder
            .assertion_pipeline_for_test()
            .pending_disjoint_constraints()
            .len(),
        1,
        "the pending pair should be queued before activation"
    );
    assert!(
        encoder
            .assertion_pipeline_for_test()
            .active_disjoint_constraints_is_empty(),
        "activation should be the point where constraints move to the active set"
    );

    encoder
        .assertion_pipeline_mut_for_test()
        .activate_pending_constraints(true, 7);

    let pipeline = encoder.assertion_pipeline_for_test();
    assert!(
        pipeline.pending_disjoint_constraints().is_empty(),
        "activation should drain the pending queue"
    );
    assert_eq!(
        pipeline.active_disjoint_constraints_len(),
        1,
        "activation should materialize one active constraint set"
    );
    assert!(
        pipeline.contains_disjoint_term(left) && pipeline.contains_disjoint_term(right),
        "both sides of the constraint should be indexed for fast quantified-term lookups"
    );
    assert_eq!(
        pipeline.quantified_pairs_revision(),
        6,
        "relevant equalities should force the next check_sat to re-run the overlap pass"
    );

    encoder
        .assertion_pipeline_mut_for_test()
        .activate_pending_constraints(false, 8);
    assert_eq!(
        encoder
            .assertion_pipeline_for_test()
            .quantified_pairs_revision(),
        8,
        "when active constraints already exist, a non-relevant activation should sync to the current revision"
    );
}

#[test]
#[timeout(30000)]
fn test_revision_increment_monotonic() {
    let mut state = AssertionPipelineState::new();

    assert_eq!(state.assertion_revision(), 0);
    assert_eq!(state.quantified_pairs_revision(), 0);

    let r1 = state.increment_revision();
    assert_eq!(r1, 1);
    assert_eq!(state.assertion_revision(), 1);

    let r2 = state.increment_revision();
    assert_eq!(r2, 2);
    assert_eq!(state.assertion_revision(), 2);
}

#[test]
#[timeout(30000)]
fn test_needs_disjoint_recheck_tracks_gap() {
    let mut state = AssertionPipelineState::new();

    assert!(
        !state.needs_disjoint_recheck(),
        "equal revisions should not trigger recheck"
    );

    state.increment_revision();
    assert!(
        state.needs_disjoint_recheck(),
        "assertion_revision > quantified_pairs_revision should trigger recheck"
    );

    state.sync_pairs_revision();
    assert!(
        !state.needs_disjoint_recheck(),
        "after sync, revisions should be equal"
    );
    assert_eq!(
        state.quantified_pairs_revision(),
        state.assertion_revision()
    );
}

#[test]
#[timeout(30000)]
fn test_update_pairs_revision_relevant_vs_irrelevant() {
    let mut state = AssertionPipelineState::new();

    state.update_pairs_revision(true, 10);
    assert_eq!(
        state.quantified_pairs_revision(),
        9,
        "relevant equality should set pairs revision to revision - 1"
    );

    state.update_pairs_revision(false, 10);
    assert_eq!(
        state.quantified_pairs_revision(),
        10,
        "irrelevant equality should sync pairs revision to current"
    );

    state.update_pairs_revision(true, 0);
    assert_eq!(
        state.quantified_pairs_revision(),
        0,
        "saturating_sub should prevent underflow at revision 0"
    );
}

#[test]
#[timeout(30000)]
fn test_pending_assertions_push_drain_cycle() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let t1 = encoder.get_or_declare_var("__pa_a", Sort::Bool).expect("a");
    let t2 = encoder.get_or_declare_var("__pa_b", Sort::Bool).expect("b");

    let state = encoder.assertion_pipeline_mut_for_test();
    assert!(state.pending_assertions_is_empty());
    assert!(!state.has_pending_assertions());

    state.push_pending_assertion(t1);
    state.push_pending_assertion(t2);
    assert_eq!(state.pending_assertions_len(), 2);
    assert!(state.has_pending_assertions());

    let drained = state.drain_pending_assertions();
    assert_eq!(drained.len(), 2);
    assert!(state.pending_assertions_is_empty());
    assert!(!state.has_pending_assertions());

    let empty = state.drain_pending_assertions();
    assert!(empty.is_empty());
}

#[test]
#[timeout(30000)]
fn test_pure_equality_push_clear_cycle() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = encoder.get_or_declare_var("__eq_a", Sort::Int).expect("a");
    let b = encoder.get_or_declare_var("__eq_b", Sort::Int).expect("b");
    let c = encoder.get_or_declare_var("__eq_c", Sort::Int).expect("c");

    let state = encoder.assertion_pipeline_mut_for_test();
    assert!(!state.has_pending_pure_equalities());
    assert_eq!(state.pending_pure_equalities_len(), 0);
    assert!(state.pending_pure_equalities().is_empty());

    state.push_pending_pure_equality((a, b));
    state.push_pending_pure_equality((b, c));
    assert!(state.has_pending_pure_equalities());
    assert_eq!(state.pending_pure_equalities_len(), 2);
    assert_eq!(state.pending_pure_equalities().len(), 2);

    state.clear_pending_pure_equalities();
    assert!(!state.has_pending_pure_equalities());
    assert_eq!(state.pending_pure_equalities_len(), 0);
}

#[test]
#[timeout(30000)]
fn test_neq_pair_insert_dedup() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = encoder.get_or_declare_var("__neq_a", Sort::Int).expect("a");
    let b = encoder.get_or_declare_var("__neq_b", Sort::Int).expect("b");

    let state = encoder.assertion_pipeline_mut_for_test();
    assert!(state.asserted_neq_pairs_is_empty());
    assert!(!state.has_asserted_neq_pair((a, b)));

    assert!(state.insert_asserted_neq_pair((a, b)));
    assert!(state.has_asserted_neq_pair((a, b)));
    assert_eq!(state.asserted_neq_pairs_len(), 1);

    assert!(
        !state.insert_asserted_neq_pair((a, b)),
        "duplicate pair should not be re-inserted"
    );
    assert_eq!(
        state.asserted_neq_pairs_len(),
        1,
        "duplicate should not increase count"
    );

    assert!(
        !state.has_asserted_neq_pair((b, a)),
        "(b, a) is distinct from (a, b) in the HashSet"
    );
    assert!(state.insert_asserted_neq_pair((b, a)));
    assert_eq!(state.asserted_neq_pairs_len(), 2);
}

#[test]
#[timeout(30000)]
fn test_disjoint_terms_index_isolation() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let x = encoder.get_or_declare_var("__dt_x", Sort::Int).expect("x");
    let y = encoder.get_or_declare_var("__dt_y", Sort::Int).expect("y");
    let z = encoder.get_or_declare_var("__dt_z", Sort::Int).expect("z");

    let state = encoder.assertion_pipeline_mut_for_test();
    assert!(state.disjoint_terms_is_empty());

    state.insert_disjoint_term_for_test(x);
    state.insert_disjoint_term_for_test(y);
    assert_eq!(state.disjoint_terms_len(), 2);
    assert!(state.contains_disjoint_term(x));
    assert!(state.contains_disjoint_term(y));
    assert!(!state.contains_disjoint_term(z), "z was not inserted");
}

#[test]
#[timeout(30000)]
fn test_active_disjoint_constraints_query() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let a = encoder.get_or_declare_var("__adc_a", Sort::Int).expect("a");
    let b = encoder.get_or_declare_var("__adc_b", Sort::Int).expect("b");

    let state = encoder.assertion_pipeline_mut_for_test();
    assert!(!state.has_active_disjoint_constraints());
    assert!(state.active_disjoint_constraints().is_empty());

    state.push_active_disjoint_constraint_for_test(vec![a], vec![b]);
    assert!(state.has_active_disjoint_constraints());
    assert_eq!(state.active_disjoint_constraints().len(), 1);
    assert_eq!(state.active_disjoint_constraints()[0].0, vec![a]);
    assert_eq!(state.active_disjoint_constraints()[0].1, vec![b]);
}

#[test]
#[timeout(30000)]
fn test_pending_disjoint_constraints_eagerly_registers_terms() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let p = encoder.get_or_declare_var("__pdc_p", Sort::Int).expect("p");
    let q = encoder.get_or_declare_var("__pdc_q", Sort::Int).expect("q");

    let state = encoder.assertion_pipeline_mut_for_test();
    assert!(!state.has_pending_disjoint_constraints());

    state.push_pending_disjoint_constraint(vec![p], vec![q]);
    assert!(state.has_pending_disjoint_constraints());
    assert_eq!(state.pending_disjoint_constraints().len(), 1);

    assert!(
        state.contains_disjoint_term(p),
        "push_pending_disjoint_constraint should eagerly register left terms"
    );
    assert!(
        state.contains_disjoint_term(q),
        "push_pending_disjoint_constraint should eagerly register right terms"
    );

    state.clear_pending_disjoint_constraints_for_test();
    assert!(!state.has_pending_disjoint_constraints());
    assert!(
        state.contains_disjoint_term(p),
        "clearing pending should not remove terms from the index"
    );
}
