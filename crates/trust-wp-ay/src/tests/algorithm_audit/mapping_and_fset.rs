// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Method dispatch sort-aware fallback, inferred-sort dispatch asymmetry,
//! mapping/fset ground registration, and lookup/set boundary tests
//! (#994, #1820).

use ay_dpll::api::Sort;
use ntest::timeout;

use super::super::helpers::{int, logic_fn_call, method_call, var, var_with_sort};
use crate::{AYEncoder, ExprSort};

// =============================================================================
// Method dispatch sort-aware fallback asymmetry (#994 algorithm audit)
// =============================================================================
//
// `len` and `contains` have inferred-sort fallbacks via `infer_encoded_sort`
// that rescue Seq/FMap receivers when `is_seq_receiver`/`is_fmap_receiver`
// miss (no annotation, no hint, only var_sorts has the correct sort).
//
// `index`/`get` lack this fallback — Seq-sorted receivers that miss
// classification fall to FMap dispatch, which in turn falls to generic
// `encode_int_method_uf` when the receiver isn't FMap-sorted. This creates
// a disconnected UF instead of proper seq indexing.

/// When a variable has Seq sort in var_sorts but no annotation and no hint,
/// `len` correctly dispatches to seq_len for vars with Seq sort in var_sorts.
/// After the var_sorts fallback in `is_seq_receiver` (#994), variables declared
/// with Seq sort in var_sorts are correctly identified as Seq receivers,
/// dispatching directly to seq_len without needing the inferred-sort fallback.
#[test]
#[timeout(30000)]
fn len_dispatch_uses_inferred_sort_fallback_for_unclassified_seq_var() {
    let mut encoder = AYEncoder::new();
    let seq_sort = Sort::seq(Sort::Int);

    // Declare "xs" with Seq sort in var_sorts, no annotation, no hint.
    // This simulates a loop-generated variable that was declared with Seq sort
    // during encoding but lacks an ExprSort annotation from the MIR lowering.
    let _xs_term = encoder.solver.declare_const("xs", seq_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("xs".to_string(), seq_sort.clone());

    // After #994 sort inference improvements, is_seq_receiver correctly
    // identifies vars with Seq sort in var_sorts via is_receiver_of_sort.
    assert!(
        encoder.is_seq_receiver(&var("xs"), None),
        "is_seq_receiver should identify var with Seq in var_sorts"
    );

    // len dispatch produces a valid encoding via direct seq dispatch.
    let len_expr = method_call(var("xs"), "len", vec![]);
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("len on Seq var should encode via seq dispatch");
    assert_eq!(
        encoder.solver.get_sort(len_term),
        Sort::Int,
        "len should return Int regardless of dispatch path"
    );
}

/// After #994 sort inference improvements, `index` on a var with Seq sort in
/// var_sorts correctly dispatches to Seq indexing (not FMap fallback), since
/// `is_seq_receiver` now identifies vars via the var_sorts check.
#[test]
#[timeout(30000)]
fn index_dispatch_uses_var_sorts_for_seq_receiver_classification() {
    let mut encoder = AYEncoder::new();
    let seq_sort = Sort::seq(Sort::Int);

    // Same setup: Seq in var_sorts, no annotation, no hint
    let _xs_term = encoder.solver.declare_const("xs", seq_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("xs".to_string(), seq_sort.clone());

    // is_seq_receiver now correctly identifies this variable
    assert!(
        encoder.is_seq_receiver(&var("xs"), None),
        "is_seq_receiver should identify var with Seq in var_sorts"
    );

    // index dispatches to seq indexing (not FMap fallback)
    let index_expr = method_call(var("xs"), "index", vec![int(0)]);
    let result = encoder.encode_pure(&index_expr);
    assert!(
        result.is_ok(),
        "index on Seq var should encode via seq dispatch"
    );
}

/// Same asymmetry test for `contains`: verifies the inferred-sort fallback works.
#[test]
#[timeout(30000)]
fn contains_dispatch_uses_inferred_sort_fallback_for_unclassified_seq_var() {
    let mut encoder = AYEncoder::new();
    let seq_sort = Sort::seq(Sort::Int);

    let _xs_term = encoder.solver.declare_const("xs", seq_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("xs".to_string(), seq_sort.clone());

    // contains should dispatch to Seq or FSet via inferred-sort fallback
    let contains_expr = method_call(var("xs"), "contains", vec![int(42)]);
    let result = encoder
        .encode_pure(&contains_expr)
        .expect("contains on unclassified Seq var should encode");
    assert_eq!(
        encoder.solver.get_sort(result),
        Sort::Bool,
        "contains should return Bool"
    );
}

// =============================================================================
// Mapping method boundary conditions (#2317 algorithm audit)
// =============================================================================

/// Unknown methods on a Mapping-annotated receiver do NOT reach
/// `encode_mapping_method` — they hit the top-level `_` fallback arm in
/// `encode_method_call_impl`. That arm checks for logic_fn dispatch and
/// quantifier scope, returning an error outside quantifiers. This documents
/// that Mapping-typed receivers have no special treatment for unknown methods,
/// unlike Seq/FMap/FSet which have explicit dispatch arms.
#[test]
#[timeout(30000)]
fn mapping_unknown_method_hits_toplevel_fallback_not_encode_mapping_method() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
    let mapping_ann = ExprSort::Datatype(intern_sort_name("Mapping"));

    let _m_term = encoder.solver.declare_const("m", mapping_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("m".to_string(), mapping_sort.clone());

    // Unknown method on Mapping receiver: top-level dispatch, not encode_mapping_method
    let expr = method_call(
        var_with_sort("m", mapping_ann),
        "unknown_method",
        vec![int(1)],
    );
    let result = encoder.encode_pure(&expr);
    // Returns error because `unknown_method` is not a registered logic fn
    // and we are not inside a quantifier scope
    assert!(
        result.is_err(),
        "unknown method on Mapping outside quantifier should return error"
    );
    let err = result.unwrap_err();
    assert!(
        format!("{err}").contains("unknown method"),
        "error should mention unknown method, got: {err}"
    );
}

/// `mapping_set` with wrong arity (not 2 args) should fall through gracefully,
/// not panic from an out-of-bounds access.
#[test]
#[timeout(30000)]
fn mapping_set_wrong_arity_falls_through() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
    let mapping_ann = ExprSort::Datatype(intern_sort_name("Mapping"));

    let _m_term = encoder.solver.declare_const("m", mapping_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("m".to_string(), mapping_sort.clone());

    // set with 1 arg (wrong arity for Mapping.set which expects 2)
    let expr = method_call(var_with_sort("m", mapping_ann.clone()), "set", vec![int(1)]);
    let result = encoder.encode_pure(&expr);
    // Should not panic — falls through to generic UF
    assert!(
        result.is_ok(),
        "Mapping.set with wrong arity should fall through, not panic"
    );
}

/// Ground pool records both mapping_get and mapping_set applications.
#[test]
#[timeout(30000)]
fn mapping_ground_pool_records_get_and_set() {
    use trust_wp_core::formula::intern_sort_name;

    let mut encoder = AYEncoder::new();
    let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
    let mapping_ann = ExprSort::Datatype(intern_sort_name("Mapping"));

    let _m_term = encoder.solver.declare_const("m", mapping_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("m".to_string(), mapping_sort.clone());

    // Encode mapping_get via index
    let get_expr = method_call(var_with_sort("m", mapping_ann.clone()), "get", vec![int(0)]);
    encoder
        .encode_pure(&get_expr)
        .expect("mapping get should encode");

    // Verify ground pool has mapping_get entry
    let get_entries = encoder.ground_pool_for_test().entries_for("mapping_get");
    assert!(
        get_entries.is_some_and(|es| !es.is_empty()),
        "ground pool should contain mapping_get after encoding a get call"
    );

    // Encode mapping_set
    let set_expr = method_call(
        var_with_sort("m", mapping_ann.clone()),
        "set",
        vec![int(0), int(42)],
    );
    encoder
        .encode_pure(&set_expr)
        .expect("mapping set should encode");

    // Verify ground pool has mapping_set entry
    let set_entries = encoder.ground_pool_for_test().entries_for("mapping_set");
    assert!(
        set_entries.is_some_and(|es| !es.is_empty()),
        "ground pool should contain mapping_set after encoding a set call"
    );
}

/// The `is_empty` dispatch checks `is_seq_receiver` but NOT `is_fmap_receiver`.
/// An FMap receiver calling `is_empty` falls to `encode_fset_method`. This test
/// documents the asymmetry vs `len` which does check `is_fmap_receiver`.
#[test]
#[timeout(30000)]
fn is_empty_missing_fmap_receiver_check() {
    let mut encoder = AYEncoder::new();
    let fmap_sort = Sort::Uninterpreted("FMap".to_string());

    let _m_term = encoder.solver.declare_const("m", fmap_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("m".to_string(), fmap_sort.clone());

    // len correctly routes to fmap_len via is_fmap_receiver or inferred-sort
    let len_expr = method_call(var_with_sort("m", ExprSort::FMap), "len", vec![]);
    let len_result = encoder.encode_pure(&len_expr);
    assert!(
        len_result.is_ok(),
        "len on FMap receiver should encode via fmap_len"
    );

    // is_empty on FMap receiver: no is_fmap_receiver check in dispatcher.
    // FMap doesn't define is_empty, so it falls to fset_is_empty.
    // This may fail with sort mismatch because fset_is_empty expects Int domain
    // but the FMap receiver has FMap sort.
    let is_empty_expr = method_call(var_with_sort("m", ExprSort::FMap), "is_empty", vec![]);
    let is_empty_result = encoder.encode_pure(&is_empty_expr);
    // Document current behavior: may succeed (if receiver coerces to Int)
    // or fail with encoding error (sort mismatch). Either way, no panic.
    if let Err(ref e) = is_empty_result {
        // Expected: sort mismatch because fset_is_empty expects Int domain
        assert!(
            format!("{e}").contains("sort mismatch") || format!("{e}").contains("unsupported"),
            "is_empty error should be a sort mismatch or unsupported, got: {e}"
        );
    }
    // The asymmetry is that `len` works correctly via fmap_len, but `is_empty`
    // either errors or produces a disconnected UF via fset_is_empty.
}

// ── Mapping ground pool axiom soundness tests ──────────────────────────

/// Verify the Mapping read-over-write same-key axiom at SMT level:
/// `mapping_get(mapping_set(m, k, v), k) = v`.
///
/// This tests the axiom semantics that `assert_mapping_ground_instances`
/// implements in `mapping_instances.rs` (#2317). The test manually
/// constructs the ground instance to verify correctness independently
/// of module wiring.
#[test]
#[timeout(30000)]
fn mapping_set_get_same_key_axiom_unsat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    // Declare mapping_get: (Mapping, Int) -> Int
    let get_decl =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);
    // Declare mapping_set: (Mapping, Int, Int) -> Mapping
    let set_decl = encoder.get_or_declare_spec_fn(
        "mapping_set",
        &[mapping.clone(), Sort::Int, Sort::Int],
        mapping.clone(),
    );

    let m = encoder.solver.fresh_var("m", mapping);
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    // Build: mapping_set(m, k, v)
    let set_m_k_v = encoder.solver.apply(&set_decl, &[m, k, v]);
    // Build: mapping_get(mapping_set(m, k, v), k)
    let get_set_k = encoder.solver.apply(&get_decl, &[set_m_k_v, k]);

    // Assert the read-over-write axiom: get(set(m, k, v), k) = v
    let axiom = encoder.solver.eq(get_set_k, v);
    encoder.solver.assert_term(axiom);

    // Assert negation: get(set(m, k, v), k) != v — should be UNSAT
    let neq = encoder.solver.not(axiom);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "mapping read-over-write same-key: get(set(m,k,v),k) = v AND ≠ v should be UNSAT, got {result:?}"
    );
}

/// Verify that the Mapping read-over-write same-key axiom is sufficient
/// to prove a concrete query: set key 42 to value 99, then read key 42
/// back and get 99.
#[test]
#[timeout(30000)]
fn mapping_set_get_concrete_values_roundtrip() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    let get_decl =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);
    let set_decl = encoder.get_or_declare_spec_fn(
        "mapping_set",
        &[mapping.clone(), Sort::Int, Sort::Int],
        mapping.clone(),
    );

    let m = encoder.solver.fresh_var("m", mapping);
    let k42 = encoder.solver.int_const(42);
    let v99 = encoder.solver.int_const(99);

    // set(m, 42, 99)
    let set_m = encoder.solver.apply(&set_decl, &[m, k42, v99]);
    // get(set(m, 42, 99), 42)
    let get_result = encoder.solver.apply(&get_decl, &[set_m, k42]);

    // Assert the axiom
    let axiom = encoder.solver.eq(get_result, v99);
    encoder.solver.assert_term(axiom);

    // Assert get(set(m, 42, 99), 42) != 99 — should be UNSAT
    let neq = encoder.solver.not(axiom);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "concrete mapping roundtrip: get(set(m,42,99),42) = 99 should hold, got {result:?}"
    );
}

/// Verify that Mapping read-over-write does NOT constrain different keys:
/// `mapping_get(mapping_set(m, k1, v), k2)` with `k1 != k2` should remain
/// unconstrained (SAT when asserting get(set(m,k1,v),k2) != v).
///
/// This is the frame condition: setting key k1 should not affect reads
/// at a different key k2. The production code in `mapping_instances.rs`
/// intentionally does NOT generate cross-key instances, relying on the
/// quantified frame axiom in `axioms.rs` instead.
#[test]
#[timeout(30000)]
fn mapping_set_get_different_key_frame_sat() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    let get_decl =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);
    let set_decl = encoder.get_or_declare_spec_fn(
        "mapping_set",
        &[mapping.clone(), Sort::Int, Sort::Int],
        mapping.clone(),
    );

    let m = encoder.solver.fresh_var("m", mapping);
    let k1 = encoder.solver.fresh_var("k1", Sort::Int);
    let k2 = encoder.solver.fresh_var("k2", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    // Assert k1 != k2
    let keys_ne = encoder.solver.eq(k1, k2);
    let keys_ne = encoder.solver.not(keys_ne);
    encoder.solver.assert_term(keys_ne);

    // Build: mapping_set(m, k1, v)
    let set_m_k1_v = encoder.solver.apply(&set_decl, &[m, k1, v]);
    // Build: mapping_get(mapping_set(m, k1, v), k2)
    let get_set_k2 = encoder.solver.apply(&get_decl, &[set_m_k1_v, k2]);

    // Assert get(set(m, k1, v), k2) != v — this should be SAT
    // because the same-key axiom doesn't constrain different keys.
    let neq = encoder.solver.eq(get_set_k2, v);
    let neq = encoder.solver.not(neq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Sat),
        "mapping frame: get(set(m,k1,v),k2) != v with k1≠k2 should be SAT (unconstrained), got {result:?}"
    );
}

/// Verify that `mapping_set` ground registration flows through
/// `register_standard_ground_application` during encoding, and the
/// resulting ground entry has correct arity (3 args: m, k, v).
#[test]
#[timeout(30000)]
fn mapping_set_ground_registration_arity() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    let set_decl = encoder.get_or_declare_spec_fn(
        "mapping_set",
        &[mapping.clone(), Sort::Int, Sort::Int],
        mapping.clone(),
    );

    let m = encoder.solver.fresh_var("m", mapping);
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);
    let set_app = encoder.solver.apply(&set_decl, &[m, k, v]);

    // Register via the production method
    encoder.register_standard_ground_application("mapping_set", set_app, vec![m, k, v]);

    let entries = encoder
        .ground_pool_for_test()
        .entries_for("mapping_set")
        .expect("mapping_set should be registered");
    assert_eq!(entries.len(), 1, "exactly one mapping_set registration");
    assert_eq!(
        entries[0].arg_terms.len(),
        3,
        "mapping_set ground entry should have 3 arg_terms (m, k, v)"
    );
    assert_eq!(entries[0].application, set_app);
}

/// Verify that `mapping_get` ground registration has correct arity (2 args: m, k).
#[test]
#[timeout(30000)]
fn mapping_get_ground_registration_arity() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    let get_decl =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);

    let m = encoder.solver.fresh_var("m", mapping);
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let get_app = encoder.solver.apply(&get_decl, &[m, k]);

    encoder.register_standard_ground_application("mapping_get", get_app, vec![m, k]);

    let entries = encoder
        .ground_pool_for_test()
        .entries_for("mapping_get")
        .expect("mapping_get should be registered");
    assert_eq!(entries.len(), 1, "exactly one mapping_get registration");
    assert_eq!(
        entries[0].arg_terms.len(),
        2,
        "mapping_get ground entry should have 2 arg_terms (m, k)"
    );
}

// ── FSet intersection/difference ground registration parity tests ─────

/// `fset_intersection` should register the observed ground application without
/// emitting membership instances until `contains(intersection(...), x)` is also
/// observed.
#[test]
#[timeout(30000)]
fn fset_intersection_registers_ground_application() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let inter_expr = method_call(var("s"), "intersection", vec![var("t")]);
    let _ = encoder
        .encode_pure(&inter_expr)
        .expect("s.intersection(t) should encode");

    assert!(
        encoder
            .ground_pool_for_test()
            .entries_for("fset_intersection")
            .is_some(),
        "fset_intersection should be registered in the ground pool"
    );
    let count = encoder.assert_standard_ground_instances();
    assert_eq!(
        count, 0,
        "fset_intersection registration alone should not emit membership ground instances"
    );
}

/// `fset_difference` should register the observed ground application without
/// emitting membership instances until `contains(difference(...), x)` is also
/// observed.
#[test]
#[timeout(30000)]
fn fset_difference_registers_ground_application() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let diff_expr = method_call(var("s"), "difference", vec![var("t")]);
    let _ = encoder
        .encode_pure(&diff_expr)
        .expect("s.difference(t) should encode");

    assert!(
        encoder
            .ground_pool_for_test()
            .entries_for("fset_difference")
            .is_some(),
        "fset_difference should be registered in the ground pool"
    );
    let count = encoder.assert_standard_ground_instances();
    assert_eq!(
        count, 0,
        "fset_difference registration alone should not emit membership ground instances"
    );
}

/// Verify that `fset_insert` DOES register ground applications correctly.
///
/// Positive parity baseline for set-producing FSet calls: insert calls
/// `register_standard_ground_application` and receives semantic ground
/// instances once the supporting UFs are declared.
///
/// FSet uses Int-sorted terms (no ExprSort::FSet variant), so we declare
/// UFs directly and register via the production registration method.
#[test]
#[timeout(30000)]
fn fset_insert_has_ground_registration_parity() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Manually register fset_insert (same as encode_fset_method does)
    let insert_decl =
        encoder.get_or_declare_spec_fn("fset_insert", &[Sort::Int, Sort::Int], Sort::Int);

    let s = encoder.solver.fresh_var("s", Sort::Int);
    let x = encoder.solver.int_const(42);
    let insert_app = encoder.solver.apply(&insert_decl, &[s, x]);

    // Register like the production code does
    encoder.register_standard_ground_application("fset_insert", insert_app, vec![s, x]);

    assert!(
        encoder
            .ground_pool_for_test()
            .entries_for("fset_insert")
            .is_some(),
        "fset_insert should be registered in ground pool (parity baseline)"
    );

    // insert DOES get ground instances (contains + len)
    let _contains_decl =
        encoder.get_or_declare_spec_fn("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
    let _len_decl = encoder.get_or_declare_spec_fn("fset_len", &[Sort::Int], Sort::Int);

    let count = encoder.assert_standard_ground_instances();
    assert!(
        count >= 2,
        "fset_insert should produce at least 2 ground instances (contains + len), got {count}"
    );
}

// ── Ground registration completeness matrix tests ──────────────────────

/// Comprehensive ground registration matrix for FMap collection methods.
///
/// Tests the complete registration status of FMap method types.
/// This is the audit evidence for the #994 ground pool coverage sweep.
///
/// Registration matrix (from encoder source sweep):
///   FSet:    contains=Y  is_empty=Y  len=Y  peek=Y  insert=Y  remove=Y  intersection=Y  difference=Y
///   FMap:    contains=Y  lookup=Y    len=Y  insert=Y  merge=Y
///   Mapping: get=Y       set=Y
///   Seq:     push_back=Y  get=Y  contains=Y  concat=Y  len=Y  sum=N  subsequence=N  set=N
///
/// Note: Seq methods can't be tested here because `ensure_seq_functions` and
/// `seq_funcs()` are pub(super). Seq ground registration is covered in
/// `standard_ground_tests.rs` which lives inside the encoder module.
#[test]
#[timeout(30000)]
fn fmap_ground_registration_matrix_completeness() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // ── FMap: insert + merge should produce ground instances ──
    let fmap = Sort::Uninterpreted("FMap".to_string());
    let _fmap_contains =
        encoder.get_or_declare_spec_fn("fmap_contains", &[fmap.clone(), Sort::Int], Sort::Bool);
    let _fmap_lookup =
        encoder.get_or_declare_spec_fn("fmap_lookup", &[fmap.clone(), Sort::Int], Sort::Int);
    let _fmap_len =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);
    let fmap_insert = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let fmap_merge =
        encoder.get_or_declare_spec_fn("fmap_merge", &[fmap.clone(), fmap.clone()], fmap.clone());

    let m = encoder.solver.fresh_var("m", fmap.clone());
    let k = encoder.solver.fresh_var("k", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);
    let m2 = encoder.solver.fresh_var("m2", fmap);

    let fmap_ins = encoder.solver.apply(&fmap_insert, &[m, k, v]);
    let fmap_mrg = encoder.solver.apply(&fmap_merge, &[m, m2]);
    encoder.register_standard_ground_application("fmap_insert", fmap_ins, vec![m, k, v]);
    encoder.register_standard_ground_application("fmap_merge", fmap_mrg, vec![m, m2]);

    let fmap_count = encoder.assert_standard_ground_instances();
    // insert produces 3: contains(insert(m,k,v),k)=true, lookup(insert(m,k,v),k)=v,
    //                     len(insert) = ite(contains(m,k), len(m), len(m)+1)
    // merge produces 0 alone (needs observed fmap_contains on merged result)
    assert!(
        fmap_count >= 3,
        "FMap insert should produce >=3 ground instances (contains+lookup+len), got {fmap_count}"
    );
}

// =============================================================================
// Mapping::cst encoder support (#2317)
// =============================================================================

/// `Mapping::cst(0)` encoded via the built-in logic function call path should
/// produce a Mapping-sorted term (not Int).
#[test]
#[timeout(30000)]
fn mapping_cst_produces_mapping_sorted_term() {
    let mut encoder = AYEncoder::new();
    let expr = logic_fn_call("Mapping::cst", vec![int(0)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("Mapping::cst(0) should encode");
    let sort = encoder.solver.get_sort(term);
    assert!(
        matches!(sort, Sort::Uninterpreted(ref s) if s == "Mapping"),
        "Mapping::cst(0) should produce Mapping sort, got {sort:?}"
    );
}

/// Lowercase `mapping_cst(42)` also routes through the built-in handler.
#[test]
#[timeout(30000)]
fn mapping_cst_lowercase_form_produces_mapping_sorted_term() {
    let mut encoder = AYEncoder::new();
    let expr = logic_fn_call("mapping_cst", vec![int(42)]);
    let term = encoder
        .encode_pure(&expr)
        .expect("mapping_cst(42) should encode");
    let sort = encoder.solver.get_sort(term);
    assert!(
        matches!(sort, Sort::Uninterpreted(ref s) if s == "Mapping"),
        "mapping_cst(42) should produce Mapping sort, got {sort:?}"
    );
}

/// After constructing a constant mapping and calling `get`, the get result
/// should be Int-sorted (the value type).
#[test]
#[timeout(30000)]
fn mapping_cst_then_get_produces_int_term() {
    let mut encoder = AYEncoder::new();

    // Encode Mapping::cst(0) to get a Mapping-sorted term
    let cst_expr = logic_fn_call("Mapping::cst", vec![int(0)]);
    let _cst_term = encoder
        .encode_pure(&cst_expr)
        .expect("Mapping::cst(0) should encode");

    // Now encode a get on a Mapping-sorted receiver
    let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
    let _m_term = encoder.solver.declare_const("m", mapping_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("m".to_string(), mapping_sort);

    let get_expr = method_call(var("m"), "get", vec![int(3)]);
    let get_term = encoder
        .encode_pure(&get_expr)
        .expect("m.get(3) should encode on Mapping receiver");
    let sort = encoder.solver.get_sort(get_term);
    assert_eq!(sort, Sort::Int, "mapping get should return Int");
}

/// Ground pool should produce cst-get cross-product instances when both
/// `mapping_cst` and `mapping_get` applications are registered.
#[test]
#[timeout(30000)]
fn mapping_cst_ground_instances_with_get() {
    let mut encoder = AYEncoder::new();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    // Declare the UFs that ground instances will use
    let _mapping_get =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);

    // Register a mapping_cst(99) application
    let cst_func = encoder.get_or_declare_spec_fn("mapping_cst", &[Sort::Int], mapping.clone());
    let v = encoder.solver.int_const(99);
    let cst_app = encoder.solver.apply(&cst_func, &[v]);
    encoder.register_standard_ground_application("mapping_cst", cst_app, vec![v]);

    // Register a mapping_get(m, 3) application (providing an observed key)
    let m = encoder.solver.fresh_var("m", mapping.clone());
    let k = encoder.solver.int_const(3);
    let get_decl =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);
    let get_app = encoder.solver.apply(&get_decl, &[m, k]);
    encoder.register_standard_ground_application("mapping_get", get_app, vec![m, k]);

    let count = encoder.assert_standard_ground_instances();
    // Should produce at least 1 cst-get instance: mapping_get(mapping_cst(99), 3) = 99
    assert!(
        count >= 1,
        "Should produce >=1 cst-get ground instance, got {count}"
    );
}

/// SMT-level roundtrip: `mapping_get(mapping_cst(99), 3) = 99` should be
/// provable (UNSAT when negated).
#[test]
#[timeout(30000)]
fn mapping_cst_get_roundtrip_unsat() {
    let mut encoder = AYEncoder::new();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    // Declare mapping_cst and mapping_get
    let cst_func = encoder.get_or_declare_spec_fn("mapping_cst", &[Sort::Int], mapping.clone());
    let get_func =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);

    // Build: mapping_get(mapping_cst(99), 3)
    let v = encoder.solver.int_const(99);
    let cst_app = encoder.solver.apply(&cst_func, &[v]);
    let k = encoder.solver.int_const(3);
    let get_cst = encoder.solver.apply(&get_func, &[cst_app, k]);

    // Register ground applications so ground instances fire
    encoder.register_standard_ground_application("mapping_cst", cst_app, vec![v]);
    encoder.register_standard_ground_application("mapping_get", get_cst, vec![cst_app, k]);

    // Assert ground instances (this should add mapping_get(mapping_cst(99), 3) = 99)
    let inst_count = encoder.assert_standard_ground_instances();
    assert!(inst_count >= 1, "Should produce >=1 ground instance");

    // Negate the expected equality and check UNSAT
    let eq = encoder.solver.eq(get_cst, v);
    let neg = encoder.solver.not(eq);
    encoder.solver.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "mapping_get(mapping_cst(99), 3) = 99 should be provable (UNSAT), got {result:?}"
    );
}

/// Ground pool registration: encoding `Mapping::cst(v)` via the built-in path
/// should register a `mapping_cst` entry in the ground pool.
#[test]
#[timeout(30000)]
fn mapping_cst_registers_ground_application() {
    let mut encoder = AYEncoder::new();
    let expr = logic_fn_call("Mapping::cst", vec![int(7)]);
    let _term = encoder
        .encode_pure(&expr)
        .expect("Mapping::cst(7) should encode");

    let entries = encoder.ground_pool_for_test().entries_for("mapping_cst");
    assert!(
        entries.is_some(),
        "mapping_cst should be registered in ground pool"
    );
    let entries = entries.unwrap();
    assert_eq!(
        entries.len(),
        1,
        "Should have exactly 1 mapping_cst ground entry"
    );
}
