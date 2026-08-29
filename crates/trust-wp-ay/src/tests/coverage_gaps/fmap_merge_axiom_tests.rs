// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use crate::AYEncoder;

/// Canonical FMap sort for tests — matches `fmap_sort()` in sort_inference.rs.
fn fmap_sort() -> Sort {
    Sort::Uninterpreted("FMap".to_string())
}

/// Helper: declare all FMap UFs and assert axioms.
fn setup_fmap_merge_encoder() -> AYEncoder {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();
    // UF declarations use FMap sort for map-typed parameters (#2059)
    encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    encoder.get_or_declare_spec_fn("fmap_contains", &[fmap.clone(), Sort::Int], Sort::Bool);
    encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap.clone(), Sort::Int], Sort::Int);
    encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);
    encoder.get_or_declare_spec_fn("fmap_merge", &[fmap.clone(), fmap.clone()], fmap);
    encoder.assert_fmap_axioms();
    encoder
}

/// Merge-contains-forward: if m1 contains k, then merge(m1, m2) contains k.
#[test]
#[timeout(30000)]
fn fmap_merge_contains_left() {
    let mut encoder = setup_fmap_merge_encoder();
    let fmap = fmap_sort();

    let fmap_contains = encoder
        .decls()
        .get_spec_func("fmap_contains")
        .unwrap()
        .clone();
    let fmap_merge = encoder.decls().get_spec_func("fmap_merge").unwrap().clone();

    let m1 = encoder.solver.fresh_var("m1", fmap.clone());
    let m2 = encoder.solver.fresh_var("m2", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);

    // Assume m1 contains k
    let c_m1_k = encoder.solver.apply(&fmap_contains, &[m1, k]);
    encoder.solver.assert_term(c_m1_k);

    // Negate: merge(m1, m2) does NOT contain k
    let merged = encoder.solver.apply(&fmap_merge, &[m1, m2]);
    let c_merge_k = encoder.solver.apply(&fmap_contains, &[merged, k]);
    let not_c = encoder.solver.not(c_merge_k);
    encoder.solver.assert_term(not_c);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "m1 contains k but merge(m1,m2) doesn't should be UNSAT, got: {result:?}"
    );
}

/// Merge-contains-forward-right: if m2 contains k, then merge(m1, m2) contains k.
#[test]
#[timeout(30000)]
fn fmap_merge_contains_right() {
    let mut encoder = setup_fmap_merge_encoder();
    let fmap = fmap_sort();

    let fmap_contains = encoder
        .decls()
        .get_spec_func("fmap_contains")
        .unwrap()
        .clone();
    let fmap_merge = encoder.decls().get_spec_func("fmap_merge").unwrap().clone();

    let m1 = encoder.solver.fresh_var("m1", fmap.clone());
    let m2 = encoder.solver.fresh_var("m2", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);

    // Assume m2 contains k
    let c_m2_k = encoder.solver.apply(&fmap_contains, &[m2, k]);
    encoder.solver.assert_term(c_m2_k);

    // Negate: merge(m1, m2) does NOT contain k
    let merged = encoder.solver.apply(&fmap_merge, &[m1, m2]);
    let c_merge_k = encoder.solver.apply(&fmap_contains, &[merged, k]);
    let not_c = encoder.solver.not(c_merge_k);
    encoder.solver.assert_term(not_c);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "m2 contains k but merge(m1,m2) doesn't should be UNSAT, got: {result:?}"
    );
}

/// Merge-contains-backward: if merge(m1,m2) contains k, then m1 or m2 contains k.
#[test]
#[timeout(30000)]
fn fmap_merge_contains_backward() {
    let mut encoder = setup_fmap_merge_encoder();
    let fmap = fmap_sort();

    let fmap_contains = encoder
        .decls()
        .get_spec_func("fmap_contains")
        .unwrap()
        .clone();
    let fmap_merge = encoder.decls().get_spec_func("fmap_merge").unwrap().clone();

    let m1 = encoder.solver.fresh_var("m1", fmap.clone());
    let m2 = encoder.solver.fresh_var("m2", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);

    // Assume merge(m1,m2) contains k
    let merged = encoder.solver.apply(&fmap_merge, &[m1, m2]);
    let c_merge_k = encoder.solver.apply(&fmap_contains, &[merged, k]);
    encoder.solver.assert_term(c_merge_k);

    // Assume neither m1 nor m2 contains k
    let c_m1_k = encoder.solver.apply(&fmap_contains, &[m1, k]);
    let c_m2_k = encoder.solver.apply(&fmap_contains, &[m2, k]);
    let not_m1 = encoder.solver.not(c_m1_k);
    let not_m2 = encoder.solver.not(c_m2_k);
    encoder.solver.assert_term(not_m1);
    encoder.solver.assert_term(not_m2);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "merge contains k but neither m1 nor m2 does should be UNSAT, got: {result:?}"
    );
}

/// Merge-lookup-left-bias: if m1 contains k, then lookup(merge(m1,m2), k) == lookup(m1, k).
#[test]
#[timeout(30000)]
fn fmap_merge_lookup_left_bias() {
    let mut encoder = setup_fmap_merge_encoder();
    let fmap = fmap_sort();

    let fmap_contains = encoder
        .decls()
        .get_spec_func("fmap_contains")
        .unwrap()
        .clone();
    let fmap_lookup = encoder
        .decls()
        .get_spec_func("fmap_lookup")
        .unwrap()
        .clone();
    let fmap_merge = encoder.decls().get_spec_func("fmap_merge").unwrap().clone();

    let m1 = encoder.solver.fresh_var("m1", fmap.clone());
    let m2 = encoder.solver.fresh_var("m2", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);

    // Assume m1 contains k
    let c_m1_k = encoder.solver.apply(&fmap_contains, &[m1, k]);
    encoder.solver.assert_term(c_m1_k);

    // merge(m1, m2)
    let merged = encoder.solver.apply(&fmap_merge, &[m1, m2]);
    let l_merge_k = encoder.solver.apply(&fmap_lookup, &[merged, k]);
    let l_m1_k = encoder.solver.apply(&fmap_lookup, &[m1, k]);

    // Negate: lookup(merge(m1,m2), k) != lookup(m1, k)
    let eq = encoder.solver.eq(l_merge_k, l_m1_k);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "left-bias merge lookup mismatch should be UNSAT, got: {result:?}"
    );
}

/// Merge-lookup-right-only: if m1 does NOT contain k but m2 does,
/// then lookup(merge(m1,m2), k) == lookup(m2, k).
#[test]
#[timeout(30000)]
fn fmap_merge_lookup_right_only() {
    let mut encoder = setup_fmap_merge_encoder();
    let fmap = fmap_sort();

    let fmap_contains = encoder
        .decls()
        .get_spec_func("fmap_contains")
        .unwrap()
        .clone();
    let fmap_lookup = encoder
        .decls()
        .get_spec_func("fmap_lookup")
        .unwrap()
        .clone();
    let fmap_merge = encoder.decls().get_spec_func("fmap_merge").unwrap().clone();

    let m1 = encoder.solver.fresh_var("m1", fmap.clone());
    let m2 = encoder.solver.fresh_var("m2", fmap);
    let k = encoder.solver.fresh_var("k", Sort::Int);

    // Assume m1 does NOT contain k
    let c_m1_k = encoder.solver.apply(&fmap_contains, &[m1, k]);
    let not_c_m1 = encoder.solver.not(c_m1_k);
    encoder.solver.assert_term(not_c_m1);

    // Assume m2 contains k
    let c_m2_k = encoder.solver.apply(&fmap_contains, &[m2, k]);
    encoder.solver.assert_term(c_m2_k);

    // merge(m1, m2)
    let merged = encoder.solver.apply(&fmap_merge, &[m1, m2]);
    let l_merge_k = encoder.solver.apply(&fmap_lookup, &[merged, k]);
    let l_m2_k = encoder.solver.apply(&fmap_lookup, &[m2, k]);

    // Negate: lookup(merge(m1,m2), k) != lookup(m2, k)
    let eq = encoder.solver.eq(l_merge_k, l_m2_k);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "right-only merge lookup mismatch should be UNSAT, got: {result:?}"
    );
}
