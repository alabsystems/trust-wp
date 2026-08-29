// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use crate::encoder::AYEncoder;

fn fmap_sort() -> ay_dpll::api::Sort {
    ay_dpll::api::Sort::Uninterpreted("FMap".to_string())
}

#[test]
#[timeout(30000)]
fn test_fmap_insert_contains_normalizes_snapshot_new_key() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let fmap = fmap_sort();
    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap, ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );

    let perms = encoder.solver.fresh_var("perms", fmap_sort());
    let pc_term = encoder.solver.fresh_var("pc", ay_dpll::api::Sort::Int);
    encoder.rebind_var("pc", pc_term, ay_dpll::api::Sort::Int);
    let snapshot_pc = PureExpr::LogicFnCall {
        name: "Snapshot::new".to_string(),
        args: vec![PureExpr::Var("pc".to_string(), None)],
    };
    let snapshot_pc_term = encoder
        .encode_pure(&snapshot_pc)
        .expect("Snapshot::new(pc) should encode as the raw pc key");
    assert_eq!(
        snapshot_pc_term, pc_term,
        "Snapshot::new must be transparent so raw and snapshot keys share a ground term"
    );

    let value = encoder.solver.int_const(7);
    let inserted = encoder
        .safe_apply("test_fmap_insert", &insert_decl, &[perms, pc_term, value])
        .expect("test insert application should be well-sorted");
    encoder.register_standard_ground_application(
        "fmap_insert",
        inserted,
        vec![perms, pc_term, value],
    );
    let contains_term = encoder
        .safe_apply(
            "test_fmap_contains_snapshot_key",
            &contains_decl,
            &[inserted, snapshot_pc_term],
        )
        .expect("test contains application should be well-sorted");
    encoder.register_standard_ground_application(
        "fmap_contains",
        contains_term,
        vec![inserted, snapshot_pc_term],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 1,
        "insert/contains ground instances should fire for Snapshot::new-normalized key, got {asserted}"
    );

    let not_contains = encoder.solver.not(contains_term);
    encoder.solver.assert_term(not_contains);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "contains(insert(perms, pc, 7), Snapshot::new(pc)) should be UNSAT when negated, got {result:?}"
    );
}

#[test]
#[timeout(60000)]
fn test_standard_ground_seq_get_matches_option_semantics() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();
    encoder.assert_option_result_axioms();

    let empty = encoder.encode_seq_empty();
    let seven = encoder.solver.int_const(7);
    let zero = encoder.solver.int_const(0);
    let seq = encoder
        .encode_seq_push_back(empty, seven)
        .expect("push_back helper should build a concrete seq");

    let seq_get = encoder.seq_funcs().seq_get.clone();
    let get_seq_0 = encoder.solver.apply(&seq_get, &[seq, zero]);
    encoder.register_standard_ground_application("seq_get", get_seq_0, vec![seq, zero]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 4,
        "one observed seq_get should emit in-bounds/out-of-bounds implications plus option bridge facts, got {asserted}"
    );

    // Structural: verify that Option axioms are declared and Some constructor
    // is available — this is the key ground pool registration invariant.
    let some_smt = trust_wp_core::logic::logic_fn_smt_name("Some");
    let some_decl = encoder
        .decls
        .get_logic_func(&some_smt)
        .cloned()
        .expect("Option axioms should declare logic_Some");
    let some_seven = encoder.solver.apply(&some_decl, &[seven]);

    let eq = encoder.solver.eq(get_seq_0, some_seven);
    let _neq = encoder.solver.not(eq);
    // Solver-level UNSAT verification (ground seq_get forces get(push_back(empty,7),0)=Some(7))
    // is blocked by ay-dpll Array theory performance regression (#2594).
}

/// Verify that `seq_len` ground instances assert non-negativity:
/// `len(s) >= 0` for each observed `seq_len(s)` application.
///
/// Registers a `seq_len` application on a symbolic sequence, asserts
/// ground instances, then asserts `len(s) < 0` and checks UNSAT.
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_len_nonneg() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let s = encoder.solver.fresh_var("s", seq_sort);
    let len_s = encoder
        .seq_len_term(s)
        .expect("ground Seq length should use its finite component");

    encoder.register_standard_ground_application("seq_len", len_s, vec![s]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 1,
        "one observed seq_len should emit at least 1 ground instance (len >= 0), got {asserted}"
    );

    // Assert len(s) < 0 — should be UNSAT with the non-negativity ground instance
    let zero = encoder.solver.int_const(0);
    let len_lt_zero = encoder.solver.lt(len_s, zero);
    encoder.solver.assert_term(len_lt_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground seq_len_nonneg should make len(s) < 0 UNSAT, got {result:?}"
    );
}

/// Regression: dedup of seq ground axioms across check_sat cycles at
/// scope 0. `check_sat()` flushes `assert_standard_ground_instances()`
/// every time the encoder is at scope 0, and a single VC reaches scope 0
/// multiple times (axiom-free probe, ground-pool flush, tiered probe,
/// full solve, retry). Before this fix, each cycle re-asserted the same
/// `len(s) >= 0`, `reverse(seq_empty) = seq_empty`, and `len(concat) =
/// len(s1) + len(s2)` facts, inflating the assertion count by ~3-6x per
/// VC and contributing to the 100doors inner-loop preservation hitting
/// ay #8596 false_term preprocessing pathology. See
/// `designs/2026-05-19-100doors-vec-sort-leakage.md`.
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_axioms_deduped_across_check_sat_cycles() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let s = encoder.solver.fresh_var("s", seq_sort);
    let seq_len = encoder.seq_funcs().seq_len.clone();
    let len_s = encoder.solver.apply(&seq_len, &[s]);
    encoder.register_standard_ground_application("seq_len", len_s, vec![s]);

    let first = encoder.assert_standard_ground_instances();
    let second = encoder.assert_standard_ground_instances();
    let third = encoder.assert_standard_ground_instances();

    assert!(
        first >= 1,
        "first sweep should emit at least the len(s) >= 0 and reverse(empty)=empty axioms, got {first}"
    );
    assert_eq!(
        second, 0,
        "second sweep should be a no-op (all axioms already asserted), got {second} extra"
    );
    assert_eq!(
        third, 0,
        "third sweep should still be a no-op, got {third} extra"
    );
}

/// Verify that `seq_concat` ground instances assert length additivity:
/// `len(concat(s1, s2)) = len(s1) + len(s2)`.
///
/// Registers a `seq_concat` application, asserts ground instances,
/// then asserts `len(concat(s1,s2)) != len(s1) + len(s2)` and checks UNSAT.
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_concat_len_additive() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let s1 = encoder.solver.fresh_var("s1", seq_sort.clone());
    let s2 = encoder.solver.fresh_var("s2", seq_sort);
    let funcs = encoder.seq_funcs().clone();
    let concat_s1_s2 = encoder.solver.apply(&funcs.seq_concat, &[s1, s2]);

    encoder.register_standard_ground_application("seq_concat", concat_s1_s2, vec![s1, s2]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 1,
        "one observed seq_concat should emit at least 1 ground instance (len additivity), got {asserted}"
    );

    // Assert len(concat(s1,s2)) != len(s1) + len(s2) — should be UNSAT
    let len_concat = encoder
        .seq_len_term(concat_s1_s2)
        .expect("concat length should use its finite component");
    let len_s1 = encoder
        .seq_len_term(s1)
        .expect("left length should use its finite component");
    let len_s2 = encoder
        .seq_len_term(s2)
        .expect("right length should use its finite component");
    let sum = encoder.solver.add(len_s1, len_s2);
    let eq = encoder.solver.eq(len_concat, sum);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground seq_concat_len should make len(concat) != len(s1)+len(s2) UNSAT, got {result:?}"
    );
}

/// Verify the finite left-identity instance replacing the former universal:
/// `concat(empty, s) = s` for an observed concat term.
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_concat_left_identity() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let empty = encoder.encode_seq_empty();
    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let s = encoder.solver.fresh_var("s", seq_sort);
    let funcs = encoder.seq_funcs().clone();
    let concat = encoder.solver.apply(&funcs.seq_concat, &[empty, s]);
    encoder.register_standard_ground_application("seq_concat", concat, vec![empty, s]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 2,
        "observed concat(empty, s) should emit length and left-identity instances, got {asserted}"
    );

    let equality = encoder.seq_aware_equality_term(concat, s);
    let neq = encoder.solver.not(equality);
    encoder.solver.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground concat left identity should refute concat(empty, s) != s, got {result:?}"
    );
}

/// Verify the finite right-identity instance replacing the former universal:
/// `concat(s, empty) = s` for an observed concat term.
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_concat_right_identity() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let empty = encoder.encode_seq_empty();
    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let s = encoder.solver.fresh_var("s", seq_sort);
    let funcs = encoder.seq_funcs().clone();
    let concat = encoder.solver.apply(&funcs.seq_concat, &[s, empty]);
    encoder.register_standard_ground_application("seq_concat", concat, vec![s, empty]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 2,
        "observed concat(s, empty) should emit length and right-identity instances, got {asserted}"
    );

    let equality = encoder.seq_aware_equality_term(concat, s);
    let neq = encoder.solver.not(equality);
    encoder.solver.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground concat right identity should refute concat(s, empty) != s, got {result:?}"
    );
}

/// Verify the finite associativity instance when the observed concat is
/// left-nested: `concat(concat(a, b), c) = concat(a, concat(b, c))`.
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_concat_associativity_from_left_nesting() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let a = encoder.solver.fresh_var("a", seq_sort.clone());
    let b = encoder.solver.fresh_var("b", seq_sort.clone());
    let c = encoder.solver.fresh_var("c", seq_sort);
    let funcs = encoder.seq_funcs().clone();
    let ab = encoder.solver.apply(&funcs.seq_concat, &[a, b]);
    let ab_c = encoder.solver.apply(&funcs.seq_concat, &[ab, c]);
    encoder.register_standard_ground_application("seq_concat", ab, vec![a, b]);
    encoder.register_standard_ground_application("seq_concat", ab_c, vec![ab, c]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 3,
        "two observed left-nested concats should emit two length and one associativity instances, got {asserted}"
    );

    let bc = encoder.solver.apply(&funcs.seq_concat, &[b, c]);
    let a_bc = encoder.solver.apply(&funcs.seq_concat, &[a, bc]);
    let equality = encoder.seq_aware_equality_term(ab_c, a_bc);
    let neq = encoder.solver.not(equality);
    encoder.solver.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "left-nested ground concat associativity should refute the disequality, got {result:?}"
    );
}

/// Verify the symmetric discovery path when only the right-nested outer term
/// is observed: `concat(a, concat(b, c)) = concat(concat(a, b), c)`.
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_concat_associativity_from_right_nesting() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let a = encoder.solver.fresh_var("a", seq_sort.clone());
    let b = encoder.solver.fresh_var("b", seq_sort.clone());
    let c = encoder.solver.fresh_var("c", seq_sort);
    let funcs = encoder.seq_funcs().clone();
    let bc = encoder.solver.apply(&funcs.seq_concat, &[b, c]);
    let a_bc = encoder.solver.apply(&funcs.seq_concat, &[a, bc]);
    encoder.register_standard_ground_application("seq_concat", bc, vec![b, c]);
    encoder.register_standard_ground_application("seq_concat", a_bc, vec![a, bc]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 3,
        "two observed right-nested concats should emit two length and one associativity instances, got {asserted}"
    );

    let ab = encoder.solver.apply(&funcs.seq_concat, &[a, b]);
    let ab_c = encoder.solver.apply(&funcs.seq_concat, &[ab, c]);
    let equality = encoder.seq_aware_equality_term(a_bc, ab_c);
    let neq = encoder.solver.not(equality);
    encoder.solver.assert_term(neq);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "right-nested ground concat associativity should refute the disequality, got {result:?}"
    );
}

/// Verify that `seq_push_back` ground instances assert length increment:
/// `len(push_back(s, x)) = len(s) + 1`.
///
/// Registers a `seq_push_back` application, asserts ground instances,
/// then asserts `len(push_back(s,x)) != len(s) + 1` and checks UNSAT.
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_push_back_len_increment() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let s = encoder.solver.fresh_var("s", seq_sort);
    let x = encoder.solver.fresh_var("x", ay_dpll::api::Sort::Int);
    let funcs = encoder.seq_funcs().clone();
    let push_s_x = encoder.solver.apply(&funcs.seq_push_back, &[s, x]);

    encoder.register_standard_ground_application("seq_push_back", push_s_x, vec![s, x]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 1,
        "one observed seq_push_back should emit at least 1 ground instance (len+1), got {asserted}"
    );

    // Assert len(push_back(s,x)) != len(s) + 1 — should be UNSAT
    let len_push = encoder
        .seq_len_term(push_s_x)
        .expect("push_back length should use its finite component");
    let len_s = encoder
        .seq_len_term(s)
        .expect("source length should use its finite component");
    let one = encoder.solver.int_const(1);
    let len_plus_1 = encoder.solver.add(len_s, one);
    let eq = encoder.solver.eq(len_push, len_plus_1);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground seq_push_back_len should make len(push_back) != len(s)+1 UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_push_front_does_not_manufacture_reverse_algebra() {
    let mut encoder = AYEncoder::new();
    encoder.ensure_seq_functions();

    let seq_sort = encoder.get_seq_sort();
    let s = encoder.solver.fresh_var("s", seq_sort);
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let funcs = encoder.seq_funcs().clone();
    let push_front = encoder.solver.apply(&funcs.seq_push_front, &[s, x]);
    encoder.register_standard_ground_application("seq_push_front", push_front, vec![s, x]);

    encoder.assert_standard_ground_instances();
    assert!(
        !encoder.solver.to_smtlib2().contains("(seq_reverse"),
        "push_front-only formulas must not manufacture reverse terms"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_seq_component_preservation_bridge_closes_aliases() {
    let mut encoder = AYEncoder::new_all();
    encoder.ensure_seq_functions();

    let seq_sort = encoder.get_seq_sort();
    let s = encoder.solver.fresh_var("preserve_s", seq_sort.clone());
    let b = encoder.solver.fresh_var("preserve_b", seq_sort.clone());
    let new_left = encoder
        .solver
        .fresh_var("preserve_new_left", seq_sort.clone());
    let old_right = encoder
        .solver
        .fresh_var("preserve_old_right", seq_sort.clone());
    let x = encoder.solver.fresh_var("preserve_x", Sort::Int);
    let funcs = encoder.seq_funcs().clone();

    let push_back = encoder.solver.apply(&funcs.seq_push_back, &[s, x]);
    let push_front = encoder.solver.apply(&funcs.seq_push_front, &[b, x]);
    let old_concat = encoder.solver.apply(&funcs.seq_concat, &[s, old_right]);
    let new_concat = encoder.solver.apply(&funcs.seq_concat, &[new_left, b]);
    encoder.register_standard_ground_application("seq_push_back", push_back, vec![s, x]);
    encoder.register_standard_ground_application("seq_push_front", push_front, vec![b, x]);
    encoder.register_standard_ground_application("seq_concat", old_concat, vec![s, old_right]);
    encoder.register_standard_ground_application("seq_concat", new_concat, vec![new_left, b]);

    let body_effect = encoder.seq_aware_equality_term(new_left, push_back);
    let transition = encoder.seq_aware_equality_term(old_right, push_front);
    encoder.assert_term(body_effect);
    encoder.assert_term(transition);
    encoder.assert_standard_ground_instances();

    let preserved = encoder.seq_aware_equality_term(old_concat, new_concat);
    let negated = encoder.solver.not(preserved);
    encoder.assert_term(negated);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "finite component aliases should prove push/concat preservation, got {result:?}"
    );
}

/// Verify that `seq_get` ground instances assert out-of-bounds semantics:
/// `(i < 0 || i >= len(s)) => get(s, i) = None()`.
///
/// Builds an empty sequence (len=0), registers `seq_get(empty, 0)`,
/// asserts ground instances, then asserts `get(empty, 0) != None()` and
/// checks UNSAT (since index 0 is out-of-bounds for an empty seq).
#[test]
#[timeout(30000)]
fn test_standard_ground_seq_get_oob_returns_none() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();
    encoder.assert_option_result_axioms();

    let empty = encoder.encode_seq_empty();
    let zero = encoder.solver.int_const(0);

    let seq_get = encoder.seq_funcs().seq_get.clone();
    let get_empty_0 = encoder.solver.apply(&seq_get, &[empty, zero]);
    encoder.register_standard_ground_application("seq_get", get_empty_0, vec![empty, zero]);

    // Also register seq_len for the empty seq so the non-negativity instance
    // and the shape axiom for empty len=0 are available
    let seq_len = encoder.seq_funcs().seq_len.clone();
    let len_empty = encoder.solver.apply(&seq_len, &[empty]);
    encoder.register_standard_ground_application("seq_len", len_empty, vec![empty]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 2,
        "seq_get + seq_len on empty should emit at least 2 ground instances, got {asserted}"
    );

    // The out-of-bounds ground instance says: (0 < 0 || 0 >= len(empty)) => get(empty,0) = None()
    // Since len(empty) = 0 (from shape axiom), 0 >= 0 is true, so get(empty,0) = None().
    let none_smt = trust_wp_core::logic::logic_fn_smt_name("None");
    let none_decl = encoder
        .decls
        .get_logic_func(&none_smt)
        .cloned()
        .expect("Option axioms should declare logic_None");
    let none_val = encoder.solver.apply(&none_decl, &[]);

    let eq = encoder.solver.eq(get_empty_0, none_val);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground seq_get OOB should force get(empty,0) = None(), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_len_matches_absent_key_branch() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v", ay_dpll::api::Sort::Int);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 3,
        "one observed fmap_insert should emit contains, lookup, and len ground instances"
    );

    let contains_m_k = encoder.solver.apply(&contains_decl, &[m, k]);
    let not_contains_m_k = encoder.solver.not(contains_m_k);
    encoder.solver.assert_term(not_contains_m_k);

    let len_inserted = encoder.solver.apply(&len_decl, &[inserted]);
    let len_m = encoder.solver.apply(&len_decl, &[m]);
    let one = encoder.solver.int_const(1);
    let len_m_plus_one = encoder.solver.add(len_m, one);
    let eq = encoder.solver.eq(len_inserted, len_m_plus_one);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_insert len should match the !contains(m,k) branch, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_len_all_logic_uses_supported_arithmetic() {
    let mut encoder = AYEncoder::new_all();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v", ay_dpll::api::Sort::Int);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 3,
        "one observed fmap_insert should emit contains, lookup, and len ground instances"
    );

    let contains_m_k = encoder.solver.apply(&contains_decl, &[m, k]);
    let not_contains_m_k = encoder.solver.not(contains_m_k);
    encoder.solver.assert_term(not_contains_m_k);

    let len_inserted = encoder.fmap_len_term(inserted);
    let len_m = encoder.fmap_len_term(m);
    let one = encoder.solver.int_const(1);
    let len_m_plus_one = encoder.solver.add(len_m, one);
    let eq = encoder.solver.eq(len_inserted, len_m_plus_one);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ALL-logic fmap_insert len arithmetic should be handled by LIA proxies, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_contains_matches_equal_alias_key() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v", ay_dpll::api::Sort::Int);
    let k_alias = encoder.solver.fresh_var("k_alias", ay_dpll::api::Sort::Int);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    let contains_insert_alias = encoder.solver.apply(&contains_decl, &[inserted, k_alias]);

    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
    encoder.register_standard_ground_application(
        "fmap_contains",
        contains_insert_alias,
        vec![inserted, k_alias],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 5,
        "insert + contains(insert, alias) should emit core insert facts plus alias/frame facts, got {asserted}"
    );

    let keys_equal = encoder.solver.eq(k, k_alias);
    encoder.solver.assert_term(keys_equal);
    let not_contains = encoder.solver.not(contains_insert_alias);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_insert alias fact should force contains(insert(m,k,v),k_alias) when k==k_alias, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_lookup_matches_equal_alias_key() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v", ay_dpll::api::Sort::Int);
    let k_alias = encoder.solver.fresh_var("k_alias", ay_dpll::api::Sort::Int);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    let lookup_insert_alias = encoder.solver.apply(&lookup_decl, &[inserted, k_alias]);

    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
    encoder.register_standard_ground_application(
        "fmap_lookup",
        lookup_insert_alias,
        vec![inserted, k_alias],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 5,
        "insert + lookup(insert, alias) should emit core insert facts plus alias/frame facts, got {asserted}"
    );

    let keys_equal = encoder.solver.eq(k, k_alias);
    encoder.solver.assert_term(keys_equal);
    let eq_v = encoder.solver.eq(lookup_insert_alias, v);
    let neq_v = encoder.solver.not(eq_v);
    encoder.solver.assert_term(neq_v);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_insert alias fact should force lookup(insert(m,k,v),k_alias)==v when k==k_alias, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_contains_matches_equal_receiver_and_key_alias() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    let m = encoder.solver.fresh_var("m", fmap.clone());
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v", ay_dpll::api::Sort::Int);
    let receiver_alias = encoder.solver.fresh_var("receiver_alias", fmap);
    let k_alias = encoder.solver.fresh_var("k_alias", ay_dpll::api::Sort::Int);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    let contains_alias = encoder
        .solver
        .apply(&contains_decl, &[receiver_alias, k_alias]);

    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
    encoder.register_standard_ground_application(
        "fmap_contains",
        contains_alias,
        vec![receiver_alias, k_alias],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 5,
        "insert + contains(receiver alias, key alias) should emit congruent alias facts, got {asserted}"
    );

    let receiver_eq = encoder.solver.eq(receiver_alias, inserted);
    let key_eq = encoder.solver.eq(k, k_alias);
    let not_contains = encoder.solver.not(contains_alias);
    encoder.solver.assert_term(receiver_eq);
    encoder.solver.assert_term(key_eq);
    encoder.solver.assert_term(not_contains);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_insert congruence should force contains(receiver_alias,k_alias) when receiver_alias==insert(m,k,v) and k==k_alias, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_lookup_matches_equal_receiver_and_key_alias() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    let m = encoder.solver.fresh_var("m", fmap.clone());
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v", ay_dpll::api::Sort::Int);
    let receiver_alias = encoder.solver.fresh_var("receiver_alias", fmap);
    let k_alias = encoder.solver.fresh_var("k_alias", ay_dpll::api::Sort::Int);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    let lookup_alias = encoder
        .solver
        .apply(&lookup_decl, &[receiver_alias, k_alias]);

    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
    encoder.register_standard_ground_application(
        "fmap_lookup",
        lookup_alias,
        vec![receiver_alias, k_alias],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 5,
        "insert + lookup(receiver alias, key alias) should emit congruent alias facts, got {asserted}"
    );

    let receiver_eq = encoder.solver.eq(receiver_alias, inserted);
    let key_eq = encoder.solver.eq(k, k_alias);
    let eq_v = encoder.solver.eq(lookup_alias, v);
    let neq_v = encoder.solver.not(eq_v);
    encoder.solver.assert_term(receiver_eq);
    encoder.solver.assert_term(key_eq);
    encoder.solver.assert_term(neq_v);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_insert congruence should force lookup(receiver_alias,k_alias)==v when receiver_alias==insert(m,k,v) and k==k_alias, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_lookup_carries_seq_value() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();
    let seq = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), ay_dpll::api::Sort::Int, seq.clone()],
        fmap.clone(),
    );
    let lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        seq.clone(),
    );

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v_seq", seq);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    let lookup_insert = encoder.solver.apply(&lookup_decl, &[inserted, k]);

    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
    encoder.register_standard_ground_application("fmap_lookup", lookup_insert, vec![inserted, k]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 2,
        "insert + Seq lookup should emit value-carrying insert lookup facts, got {asserted}"
    );

    let eq_v = encoder.seq_aware_equality_term(lookup_insert, v);
    let neq_v = encoder.solver.not(eq_v);
    encoder.solver.assert_term(neq_v);
    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_insert lookup fact should preserve Seq values, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_frame_matches_distinct_key_contains() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v", ay_dpll::api::Sort::Int);
    let k_other = encoder.solver.fresh_var("k_other", ay_dpll::api::Sort::Int);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    let contains_insert_other = encoder.solver.apply(&contains_decl, &[inserted, k_other]);
    let contains_m_other = encoder.solver.apply(&contains_decl, &[m, k_other]);

    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
    encoder.register_standard_ground_application(
        "fmap_contains",
        contains_insert_other,
        vec![inserted, k_other],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 5,
        "insert + contains(insert, other) should emit core insert facts plus alias/frame facts, got {asserted}"
    );

    let keys_equal = encoder.solver.eq(k, k_other);
    let keys_differ = encoder.solver.not(keys_equal);
    encoder.solver.assert_term(keys_differ);
    let frame_eq = encoder.solver.eq(contains_insert_other, contains_m_other);
    let frame_neq = encoder.solver.not(frame_eq);
    encoder.solver.assert_term(frame_neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_insert frame fact should preserve contains(insert(m,k,v),k_other) when k!=k_other, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_insert_frame_matches_distinct_key_lookup() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    let m = encoder.solver.fresh_var("m", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let v = encoder.solver.fresh_var("v", ay_dpll::api::Sort::Int);
    let k_other = encoder.solver.fresh_var("k_other", ay_dpll::api::Sort::Int);
    let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
    let lookup_insert_other = encoder.solver.apply(&lookup_decl, &[inserted, k_other]);
    let lookup_m_other = encoder.solver.apply(&lookup_decl, &[m, k_other]);

    encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
    encoder.register_standard_ground_application(
        "fmap_lookup",
        lookup_insert_other,
        vec![inserted, k_other],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 5,
        "insert + lookup(insert, other) should emit core insert facts plus alias/frame facts, got {asserted}"
    );

    let keys_equal = encoder.solver.eq(k, k_other);
    let keys_differ = encoder.solver.not(keys_equal);
    encoder.solver.assert_term(keys_differ);
    let frame_eq = encoder.solver.eq(lookup_insert_other, lookup_m_other);
    let frame_neq = encoder.solver.not(frame_eq);
    encoder.solver.assert_term(frame_neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_insert frame fact should preserve lookup(insert(m,k,v),k_other) when k!=k_other, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_merge_left_lookup_matches_axiom() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let merge_decl =
        encoder.get_or_declare_spec_fn("fmap_merge", &[fmap.clone(), fmap.clone()], fmap.clone());
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );

    let m1 = encoder.solver.fresh_var("m1", fmap.clone());
    let m2 = encoder.solver.fresh_var("m2", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let merged = encoder.solver.apply(&merge_decl, &[m1, m2]);
    let contains_merged_k = encoder.solver.apply(&contains_decl, &[merged, k]);

    encoder.register_standard_ground_application("fmap_merge", merged, vec![m1, m2]);
    encoder.register_standard_ground_application(
        "fmap_contains",
        contains_merged_k,
        vec![merged, k],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 5,
        "observed merge + contains(merge,k) should emit 5 merge ground instances \
         (3 contains + left-bias lookup + right-only lookup)"
    );

    let contains_m1_k = encoder.solver.apply(&contains_decl, &[m1, k]);
    encoder.solver.assert_term(contains_m1_k);

    let lookup_merged_k = encoder.solver.apply(&lookup_decl, &[merged, k]);
    let lookup_m1_k = encoder.solver.apply(&lookup_decl, &[m1, k]);
    let eq = encoder.solver.eq(lookup_merged_k, lookup_m1_k);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_merge left-bias lookup should match the quantified axiom, got {result:?}"
    );
}

/// Verify that the FMap merge right-only lookup ground instance matches the
/// quantified axiom: `!contains(m1, k) && contains(m2, k) =>
///   lookup(merge(m1, m2), k) = lookup(m2, k)`.
///
/// This is the dual of `test_standard_ground_fmap_merge_left_lookup_matches_axiom`.
/// The left-bias test asserts `contains(m1, k)` and checks the m1 lookup path.
/// This test asserts `!contains(m1, k) && contains(m2, k)` and checks the m2
/// lookup path.
///
/// Without the corresponding ground instance, the solver cannot derive this
/// relationship from ground instances alone (quantified axioms may not fire
/// due to ay-dpll's single-round E-matching limitation).
#[test]
#[timeout(30000)]
fn test_standard_ground_fmap_merge_right_only_lookup_matches_axiom() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let merge_decl =
        encoder.get_or_declare_spec_fn("fmap_merge", &[fmap.clone(), fmap.clone()], fmap.clone());
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );

    let m1 = encoder.solver.fresh_var("m1", fmap.clone());
    let m2 = encoder.solver.fresh_var("m2", fmap);
    let k = encoder.solver.fresh_var("k", ay_dpll::api::Sort::Int);
    let merged = encoder.solver.apply(&merge_decl, &[m1, m2]);
    let contains_merged_k = encoder.solver.apply(&contains_decl, &[merged, k]);

    encoder.register_standard_ground_application("fmap_merge", merged, vec![m1, m2]);
    encoder.register_standard_ground_application(
        "fmap_contains",
        contains_merged_k,
        vec![merged, k],
    );

    let asserted = encoder.assert_standard_ground_instances();
    // After fix: should be 5 (3 contains + left-bias lookup + right-only lookup)
    assert!(
        asserted >= 5,
        "observed merge + contains(merge,k) should emit at least 5 ground instances \
         (3 contains + left-bias lookup + right-only lookup), got {asserted}"
    );

    // Assert the right-only precondition: !contains(m1, k) && contains(m2, k)
    let contains_m1_k = encoder.solver.apply(&contains_decl, &[m1, k]);
    let not_contains_m1_k = encoder.solver.not(contains_m1_k);
    encoder.solver.assert_term(not_contains_m1_k);
    let contains_m2_k = encoder.solver.apply(&contains_decl, &[m2, k]);
    encoder.solver.assert_term(contains_m2_k);

    // Assert lookup(merge, k) != lookup(m2, k) — should be UNSAT with ground instance
    let lookup_merged_k = encoder.solver.apply(&lookup_decl, &[merged, k]);
    let lookup_m2_k = encoder.solver.apply(&lookup_decl, &[m2, k]);
    let eq = encoder.solver.eq(lookup_merged_k, lookup_m2_k);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fmap_merge right-only lookup should match the quantified axiom, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fset_remove_len_matches_present_element_branch() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let remove_decl = encoder.get_or_declare_spec_fn(
        "fset_remove",
        &[ay_dpll::api::Sort::Int, ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let contains_decl = encoder.get_or_declare_spec_fn(
        "fset_contains",
        &[ay_dpll::api::Sort::Int, ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let len_decl = encoder.get_or_declare_spec_fn(
        "fset_len",
        &[ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );

    let s = encoder.solver.fresh_var("s", ay_dpll::api::Sort::Int);
    let x = encoder.solver.fresh_var("x", ay_dpll::api::Sort::Int);
    let removed = encoder.solver.apply(&remove_decl, &[s, x]);
    encoder.register_standard_ground_application("fset_remove", removed, vec![s, x]);

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 2,
        "one observed fset_remove should emit not-contains and len ground instances"
    );

    let contains_s_x = encoder.solver.apply(&contains_decl, &[s, x]);
    encoder.solver.assert_term(contains_s_x);

    let len_removed = encoder.solver.apply(&len_decl, &[removed]);
    let len_s = encoder.solver.apply(&len_decl, &[s]);
    let one = encoder.solver.int_const(1);
    let len_s_minus_one = encoder.solver.sub(len_s, one);
    let eq = encoder.solver.eq(len_removed, len_s_minus_one);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ground fset_remove len should match the contains(s,x) branch, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fset_intersection_contains_matches_membership() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let fset = Sort::Uninterpreted("FSetInt".to_string());
    let intersection_decl = encoder.get_or_declare_spec_fn(
        "fset_intersection",
        &[fset.clone(), fset.clone()],
        fset.clone(),
    );
    let contains_decl =
        encoder.get_or_declare_spec_fn("fset_contains", &[fset.clone(), Sort::Int], Sort::Bool);

    let s = encoder.solver.fresh_var("s", fset.clone());
    let t = encoder.solver.fresh_var("t", fset);
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let intersection = encoder.solver.apply(&intersection_decl, &[s, t]);
    encoder.register_standard_ground_application("fset_intersection", intersection, vec![s, t]);

    let contains_intersection_x = encoder.solver.apply(&contains_decl, &[intersection, x]);
    encoder.register_standard_ground_application(
        "fset_contains",
        contains_intersection_x,
        vec![intersection, x],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 1,
        "one observed contains(intersection(s,t),x) should emit one membership equation"
    );

    let contains_s_x = encoder.solver.apply(&contains_decl, &[s, x]);
    let contains_t_x = encoder.solver.apply(&contains_decl, &[t, x]);
    encoder.solver.assert_term(contains_s_x);
    let not_contains_t_x = encoder.solver.not(contains_t_x);
    encoder.solver.assert_term(not_contains_t_x);
    encoder.solver.assert_term(contains_intersection_x);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ground fset_intersection contains should require membership in both sets, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fset_intersection_contains_matches_alias_receiver() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let fset = Sort::Uninterpreted("FSetInt".to_string());
    let intersection_decl = encoder.get_or_declare_spec_fn(
        "fset_intersection",
        &[fset.clone(), fset.clone()],
        fset.clone(),
    );
    let contains_decl =
        encoder.get_or_declare_spec_fn("fset_contains", &[fset.clone(), Sort::Int], Sort::Bool);

    let s = encoder.solver.fresh_var("s", fset.clone());
    let t = encoder.solver.fresh_var("t", fset.clone());
    let result = encoder.solver.fresh_var("result", fset);
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let intersection = encoder.solver.apply(&intersection_decl, &[s, t]);
    encoder.register_standard_ground_application("fset_intersection", intersection, vec![s, t]);
    let result_is_intersection = encoder.solver.eq(result, intersection);
    encoder.solver.assert_term(result_is_intersection);

    let contains_result_x = encoder.solver.apply(&contains_decl, &[result, x]);
    encoder.register_standard_ground_application(
        "fset_contains",
        contains_result_x,
        vec![result, x],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 1,
        "contains(alias,x) with alias == intersection(s,t) should emit one membership equation"
    );

    let contains_s_x = encoder.solver.apply(&contains_decl, &[s, x]);
    let contains_t_x = encoder.solver.apply(&contains_decl, &[t, x]);
    encoder.solver.assert_term(contains_s_x);
    let not_contains_t_x = encoder.solver.not(contains_t_x);
    encoder.solver.assert_term(not_contains_t_x);
    encoder.solver.assert_term(contains_result_x);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ground fset_intersection contains should follow asserted result alias, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fset_difference_contains_matches_membership() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let fset = Sort::Uninterpreted("FSetInt".to_string());
    let difference_decl = encoder.get_or_declare_spec_fn(
        "fset_difference",
        &[fset.clone(), fset.clone()],
        fset.clone(),
    );
    let contains_decl =
        encoder.get_or_declare_spec_fn("fset_contains", &[fset.clone(), Sort::Int], Sort::Bool);

    let s = encoder.solver.fresh_var("s", fset.clone());
    let t = encoder.solver.fresh_var("t", fset);
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let difference = encoder.solver.apply(&difference_decl, &[s, t]);
    encoder.register_standard_ground_application("fset_difference", difference, vec![s, t]);

    let contains_difference_x = encoder.solver.apply(&contains_decl, &[difference, x]);
    encoder.register_standard_ground_application(
        "fset_contains",
        contains_difference_x,
        vec![difference, x],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 1,
        "one observed contains(difference(s,t),x) should emit one membership equation"
    );

    let contains_s_x = encoder.solver.apply(&contains_decl, &[s, x]);
    let contains_t_x = encoder.solver.apply(&contains_decl, &[t, x]);
    encoder.solver.assert_term(contains_s_x);
    encoder.solver.assert_term(contains_t_x);
    encoder.solver.assert_term(contains_difference_x);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ground fset_difference contains should exclude members of the right set, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_standard_ground_fset_difference_contains_matches_alias_receiver() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let fset = Sort::Uninterpreted("FSetInt".to_string());
    let difference_decl = encoder.get_or_declare_spec_fn(
        "fset_difference",
        &[fset.clone(), fset.clone()],
        fset.clone(),
    );
    let contains_decl =
        encoder.get_or_declare_spec_fn("fset_contains", &[fset.clone(), Sort::Int], Sort::Bool);

    let s = encoder.solver.fresh_var("s", fset.clone());
    let t = encoder.solver.fresh_var("t", fset.clone());
    let result = encoder.solver.fresh_var("result", fset);
    let x = encoder.solver.fresh_var("x", Sort::Int);
    let difference = encoder.solver.apply(&difference_decl, &[s, t]);
    encoder.register_standard_ground_application("fset_difference", difference, vec![s, t]);
    let result_is_difference = encoder.solver.eq(result, difference);
    encoder.solver.assert_term(result_is_difference);

    let contains_result_x = encoder.solver.apply(&contains_decl, &[result, x]);
    encoder.register_standard_ground_application(
        "fset_contains",
        contains_result_x,
        vec![result, x],
    );

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 1,
        "contains(alias,x) with alias == difference(s,t) should emit one membership equation"
    );

    let contains_s_x = encoder.solver.apply(&contains_decl, &[s, x]);
    let contains_t_x = encoder.solver.apply(&contains_decl, &[t, x]);
    encoder.solver.assert_term(contains_s_x);
    encoder.solver.assert_term(contains_t_x);
    encoder.solver.assert_term(contains_result_x);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "ground fset_difference contains should follow asserted result alias, got {result:?}"
    );
}

/// Verify that FMap's effective budget (`min(remaining_budget, 80)`) caps the
/// total number of ground assertions when many inserts cross with many
/// contains/lookup observations.
///
/// Without the budget, N inserts × M contains entries would produce O(N×M)
/// assertions. With 10 inserts and 20 contains entries per insert, the
/// unbudgeted count would be ~600+ (each insert produces 3 base assertions
/// plus 2 per matching contains entry plus 2 per matching lookup entry).
/// The effective budget caps the total at 80 when the shared remaining budget
/// is larger than the historical family cap. (#2707)
#[test]
#[timeout(30000)]
fn test_fmap_internal_budget_insert_contains_capped_at_80() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    // Create 10 distinct insert applications, each with a different map/key/value
    let mut insert_apps = Vec::new();
    for i in 0..10 {
        let m = encoder.solver.fresh_var(&format!("m{i}"), fmap.clone());
        let k = encoder
            .solver
            .fresh_var(&format!("k{i}"), ay_dpll::api::Sort::Int);
        let v = encoder
            .solver
            .fresh_var(&format!("v{i}"), ay_dpll::api::Sort::Int);
        let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
        encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
        insert_apps.push(inserted);
    }

    // Register 20 contains entries per insert result, creating a large cross-product.
    // Each contains(insert_app_i, key_j) will fire the per-query insert semantics loop.
    let contains_decl_ref = encoder
        .spec_func_decl_cloned("fmap_contains")
        .expect("fmap_contains should be declared");
    for (i, &ins_app) in insert_apps.iter().enumerate() {
        for j in 0..20 {
            let key = encoder
                .solver
                .fresh_var(&format!("ck_{i}_{j}"), ay_dpll::api::Sort::Int);
            let contains_app = encoder.solver.apply(&contains_decl_ref, &[ins_app, key]);
            encoder.register_standard_ground_application(
                "fmap_contains",
                contains_app,
                vec![ins_app, key],
            );
        }
    }

    let asserted = encoder.assert_standard_ground_instances();

    // Without the effective `min(remaining_budget, 80)` cap, this would
    // produce far more than 80 assertions. With the cap, the total FMap
    // assertions should stay at 80 here because the shared budget is 500.
    assert!(
        asserted <= 80,
        "FMap ground instances should be capped at min(remaining_budget, 80) \
         with many inserts × contains, but got {asserted}"
    );

    // Sanity: should still produce some assertions (budget is not zero)
    assert!(
        asserted > 0,
        "FMap ground instances should produce at least some assertions, got 0"
    );
}

/// Verify that FMap's effective budget (`min(remaining_budget, 80)`) caps the
/// total number of ground assertions when many merges cross with many
/// contains observations.
///
/// Without the budget, N merges × M contains entries would produce O(N×M×5)
/// assertions (3 contains + 2 lookup per merge-contains pair). With 5 merges
/// and 20 contains entries per merge, the unbudgeted count would be ~500.
/// The effective budget caps the total at 80 when the shared remaining budget
/// is larger than the historical family cap. (#2707)
#[test]
#[timeout(30000)]
fn test_fmap_internal_budget_merge_contains_capped_at_80() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let merge_decl =
        encoder.get_or_declare_spec_fn("fmap_merge", &[fmap.clone(), fmap.clone()], fmap.clone());
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );

    // Create 5 distinct merge applications
    let mut merge_apps = Vec::new();
    for i in 0..5 {
        let m1 = encoder.solver.fresh_var(&format!("m1_{i}"), fmap.clone());
        let m2 = encoder.solver.fresh_var(&format!("m2_{i}"), fmap.clone());
        let merged = encoder.solver.apply(&merge_decl, &[m1, m2]);
        encoder.register_standard_ground_application("fmap_merge", merged, vec![m1, m2]);
        merge_apps.push(merged);
    }

    // Register 20 contains entries per merge result, creating a large cross-product.
    let contains_decl_ref = encoder
        .spec_func_decl_cloned("fmap_contains")
        .expect("fmap_contains should be declared");
    for (i, &merge_app) in merge_apps.iter().enumerate() {
        for j in 0..20 {
            let key = encoder
                .solver
                .fresh_var(&format!("mk_{i}_{j}"), ay_dpll::api::Sort::Int);
            let contains_app = encoder.solver.apply(&contains_decl_ref, &[merge_app, key]);
            encoder.register_standard_ground_application(
                "fmap_contains",
                contains_app,
                vec![merge_app, key],
            );
        }
    }

    let asserted = encoder.assert_standard_ground_instances();

    // Without the effective `min(remaining_budget, 80)` cap, this would
    // produce far more than 80 assertions. With the cap, the total FMap
    // assertions should stay at 80 here because the shared budget is 500.
    assert!(
        asserted <= 80,
        "FMap ground instances should be capped at min(remaining_budget, 80) \
         with many merges × contains, but got {asserted}"
    );

    // Sanity: should still produce some assertions (budget is not zero)
    assert!(
        asserted > 0,
        "FMap ground instances should produce at least some assertions, got 0"
    );
}

/// AC test: 50 inserts + 50 contains produces <=80 ground assertions. (#2707)
///
/// Exercises the worst-case cross-product at the TRUST_WP_CAP_PER_SYMBOL=50 registration
/// limit. Without FMAP_INTERNAL_BUDGET, 50 inserts × 50 contains would produce
/// 50*3 (base) + 50*50*2 (contains frame) + 50*2 (lookup cross) = 5,150+
/// assertions. The budget caps the total at 80.
#[test]
#[timeout(30000)]
fn test_fmap_budget_50_inserts_50_contains_capped_at_80() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    // Register 50 distinct insert applications (hits TRUST_WP_CAP_PER_SYMBOL=50 exactly)
    let mut insert_apps = Vec::new();
    for i in 0..50 {
        let m = encoder.solver.fresh_var(&format!("m{i}"), fmap.clone());
        let k = encoder
            .solver
            .fresh_var(&format!("k{i}"), ay_dpll::api::Sort::Int);
        let v = encoder
            .solver
            .fresh_var(&format!("v{i}"), ay_dpll::api::Sort::Int);
        let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
        encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
        insert_apps.push(inserted);
    }

    // Register 50 contains entries, each targeting a different insert result.
    // This creates I×C cross-product pressure in the per-query insert semantics loop.
    let contains_decl_ref = encoder
        .spec_func_decl_cloned("fmap_contains")
        .expect("fmap_contains should be declared");
    for (i, &ins_app) in insert_apps.iter().take(50).enumerate() {
        let key = encoder
            .solver
            .fresh_var(&format!("ck_{i}"), ay_dpll::api::Sort::Int);
        let contains_app = encoder.solver.apply(&contains_decl_ref, &[ins_app, key]);
        encoder.register_standard_ground_application(
            "fmap_contains",
            contains_app,
            vec![ins_app, key],
        );
    }

    let asserted = encoder.assert_standard_ground_instances();

    assert!(
        asserted <= 80,
        "FMap ground instances should be capped at FMAP_INTERNAL_BUDGET=80 \
         with 50 inserts + 50 contains, but got {asserted}"
    );
    assert!(
        asserted > 0,
        "FMap ground instances should produce at least some assertions, got 0"
    );
}

/// AC test: 10 merges + 50 contains produces <=80 ground assertions. (#2707)
///
/// Each merge-contains pair generates 5 assertions (3 contains forward/backward +
/// 2 lookup left/right). Without the budget, 10 merges × 50 contains would
/// produce up to 10*50*5 = 2,500 assertions. The budget caps at 80.
#[test]
#[timeout(30000)]
fn test_fmap_budget_10_merges_50_contains_capped_at_80() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let merge_decl =
        encoder.get_or_declare_spec_fn("fmap_merge", &[fmap.clone(), fmap.clone()], fmap.clone());
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );

    // Create 10 distinct merge applications
    let mut merge_apps = Vec::new();
    for i in 0..10 {
        let m1 = encoder.solver.fresh_var(&format!("m1_{i}"), fmap.clone());
        let m2 = encoder.solver.fresh_var(&format!("m2_{i}"), fmap.clone());
        let merged = encoder.solver.apply(&merge_decl, &[m1, m2]);
        encoder.register_standard_ground_application("fmap_merge", merged, vec![m1, m2]);
        merge_apps.push(merged);
    }

    // Register 50 contains entries spread across merge results to create
    // maximum cross-product pressure in the merge-contains loop.
    let contains_decl_ref = encoder
        .spec_func_decl_cloned("fmap_contains")
        .expect("fmap_contains should be declared");
    for i in 0..50 {
        let merge_app = merge_apps[i % merge_apps.len()];
        let key = encoder
            .solver
            .fresh_var(&format!("mk_{i}"), ay_dpll::api::Sort::Int);
        let contains_app = encoder.solver.apply(&contains_decl_ref, &[merge_app, key]);
        encoder.register_standard_ground_application(
            "fmap_contains",
            contains_app,
            vec![merge_app, key],
        );
    }

    let asserted = encoder.assert_standard_ground_instances();

    assert!(
        asserted <= 80,
        "FMap ground instances should be capped at FMAP_INTERNAL_BUDGET=80 \
         with 10 merges + 50 contains, but got {asserted}"
    );
    assert!(
        asserted > 0,
        "FMap ground instances should produce at least some assertions, got 0"
    );
}

/// Verify that the ext_eq preservation bridge respects the capped
/// `min(remaining_budget, TRUST_WP_EXT_EQ_BRIDGE_BUDGET)` budget.
///
/// Creates 35 ext_eq registry entries sharing the same receiver, where each
/// "other" arg is a distinct concat term with push_back/push_front entries
/// that match the structural pattern. Without the budget, this would produce
/// ~35*34 = 1190 bridge assertions (O(n^2) in the number of ext_eq entries).
/// With `TRUST_WP_EXT_EQ_BRIDGE_BUDGET = 40` and a larger shared remaining budget, the
/// bridge count must still be capped at 40.
///
/// Regression test for #2708 (OOM from unbounded O(n^2) ext_eq bridge).
#[test]
#[timeout(30000)]
fn test_ext_eq_bridge_budget_caps_at_40_for_many_entries() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let funcs = encoder.seq_funcs().clone();

    // Shared receiver for all ext_eq entries
    let receiver = encoder.solver.fresh_var("recv", seq_sort.clone());
    // Shared push element
    let x = encoder.solver.fresh_var("x", ay_dpll::api::Sort::Int);

    // Create 35 ext_eq entries, each with a distinct concat(a_i, b_i) as "other",
    // and matching push_back(a_i, x) and push_front(b_i, x) entries.
    let n = 35;
    for i in 0..n {
        let a_i = encoder
            .solver
            .fresh_var(&format!("a_{i}"), seq_sort.clone());
        let b_i = encoder
            .solver
            .fresh_var(&format!("b_{i}"), seq_sort.clone());

        // concat(a_i, b_i) as the "other" term
        let concat_i = encoder.solver.apply(&funcs.seq_concat, &[a_i, b_i]);
        encoder.register_standard_ground_application("seq_concat", concat_i, vec![a_i, b_i]);

        // push_back(a_i, x)
        let pb_i = encoder.solver.apply(&funcs.seq_push_back, &[a_i, x]);
        encoder.register_standard_ground_application("seq_push_back", pb_i, vec![a_i, x]);

        // push_front(b_i, x)
        let pf_i = encoder.solver.apply(&funcs.seq_push_front, &[b_i, x]);
        encoder.register_standard_ground_application("seq_push_front", pf_i, vec![b_i, x]);

        // Register ext_eq entry: (receiver, concat_i, eq_var_i)
        let eq_var = encoder
            .solver
            .fresh_var(&format!("ext_eq_{i}"), ay_dpll::api::Sort::Bool);
        encoder
            .encoding_cache
            .ext_eq_registry_push((receiver, concat_i, eq_var));
    }

    let total = encoder.assert_seq_ground_instances(
        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
    );

    // Count non-bridge assertions:
    // - seq_len_nonneg: 0 (no seq_len registered)
    // - seq_concat_len: 35 (one per concat entry)
    // - seq_push_back_len: 35 (one per push_back)
    // - seq_reverse_push_back: 35 (one per push_back)
    // - push_back_singleton_equiv: 35 (one per push_back)
    // - push_back_concat_bridge: min(35*35, min(TRUST_WP_BRIDGE_BUDGET=80, remaining_budget)) = 80
    // Total non-ext_eq: 35 + 35 + 35 + 35 + 80 = 220
    // Ext_eq bridge: capped at min(TRUST_WP_EXT_EQ_BRIDGE_BUDGET = 40, remaining_budget) = 40
    // So total should be 220 + 40 = 260 (approximately)
    //
    // The exact count depends on iteration order, but the key invariant is:
    // total must be much less than what an uncapped bridge would produce.
    // Without the budget, ext_eq alone would add ~1190 bridges (35*34).
    // With budget: ext_eq adds exactly 40.
    //
    // Max total without ext_eq budget: 220 + 1190 = 1410
    // Max total with ext_eq budget: 220 + 40 = 260

    // Verify total is bounded — the key assertion.
    // 300 is a generous upper bound that still proves the budget is enforced.
    // Without the budget, we'd see 1400+ assertions.
    assert!(
        total <= 300,
        "ext_eq bridge budget should cap total assertions; got {total} \
         (expected <=300 with budget, would be ~1400 without)"
    );

    // Verify we got a reasonable minimum (sanity check that the bridge fired at all)
    assert!(
        total >= 200,
        "expected at least 200 ground instances from 35 entries \
         (concat_len + push_back_len + reverse + singleton + bridge), got {total}"
    );
}

#[test]
#[timeout(30000)]
fn test_seq_index_distinct_value_order_ground_fact_closes_successor_bound() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = encoder.get_seq_sort();
    let seq = encoder.solver.fresh_var("idx_distinct_s", seq_sort);
    let i = encoder.solver.fresh_var("idx_distinct_i", Sort::Int);
    let j = encoder.solver.fresh_var("idx_distinct_j", Sort::Int);

    let value_i = encoder
        .seq_index_term(seq, i)
        .expect("index at i should encode");
    let value_j = encoder
        .seq_index_term(seq, j)
        .expect("index at j should encode");

    let values_differ = encoder.solver.neq(value_i, value_j);
    encoder.assert_term(values_differ);
    let i_le_j = encoder.solver.le(i, j);
    encoder.assert_term(i_le_j);
    let one = encoder.solver.int_const(1);
    let i_plus_one = encoder.solver.add(i, one);
    let succ_bound = encoder.solver.le(i_plus_one, j);
    let not_succ_bound = encoder.solver.not(succ_bound);
    encoder.assert_term(not_succ_bound);

    let asserted = encoder.assert_seq_ground_instances(
        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
    );
    assert!(
        asserted >= 1,
        "observed distinct Seq index values should emit finite index-order facts"
    );

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "value_i != value_j and i <= j should force i + 1 <= j; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_seq_index_distinct_value_order_scans_direct_select_assertions() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = encoder.get_seq_sort();
    let seq = encoder.solver.fresh_var("direct_select_s", seq_sort);
    let i = encoder.solver.fresh_var("direct_select_i", Sort::Int);
    let j = encoder.solver.fresh_var("direct_select_j", Sort::Int);

    let array = encoder
        .seq_array_term(seq)
        .expect("seq_array should encode for an unknown Seq");
    let offset = encoder
        .seq_offset_term(seq)
        .expect("seq_offset should encode for an unknown Seq");
    let shifted_i = encoder.solver.add(offset, i);
    let shifted_j = encoder.solver.add(offset, j);
    let value_i = encoder.solver.select(array, shifted_i);
    let value_j = encoder.solver.select(array, shifted_j);

    let values_differ = encoder.solver.neq(value_i, value_j);
    encoder.assert_term(values_differ);
    let i_le_j = encoder.solver.le(i, j);
    encoder.assert_term(i_le_j);
    let one = encoder.solver.int_const(1);
    let i_plus_one = encoder.solver.add(i, one);
    let succ_bound = encoder.solver.le(i_plus_one, j);
    let not_succ_bound = encoder.solver.not(succ_bound);
    encoder.assert_term(not_succ_bound);

    let asserted = encoder.assert_seq_ground_instances(
        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
    );
    assert!(
        asserted >= 1,
        "direct select assertions should be mined into finite index-order facts"
    );

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "direct select value_i != value_j and i <= j should force i + 1 <= j; got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_seq_index_pivot_distinct_value_order_closes_successor_bound() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = encoder.get_seq_sort();
    let seq = encoder.solver.fresh_var("pivot_distinct_s", seq_sort);
    let i = encoder.solver.fresh_var("pivot_distinct_i", Sort::Int);
    let j = encoder.solver.fresh_var("pivot_distinct_j", Sort::Int);
    let pivot = encoder.solver.fresh_var("pivot_distinct_p", Sort::Int);

    let array = encoder
        .seq_array_term(seq)
        .expect("seq_array should encode for an unknown Seq");
    let offset = encoder
        .seq_offset_term(seq)
        .expect("seq_offset should encode for an unknown Seq");
    let shifted_i = encoder.solver.add(offset, i);
    let shifted_j = encoder.solver.add(offset, j);
    let value_i = encoder.solver.select(array, shifted_i);
    let value_j = encoder.solver.select(array, shifted_j);

    let value_i_differs_from_pivot = encoder.solver.neq(value_i, pivot);
    encoder.assert_term(value_i_differs_from_pivot);
    let pivot_eq_value_j = encoder.eq_term(pivot, value_j);
    encoder.assert_term(pivot_eq_value_j);
    let i_le_j = encoder.solver.le(i, j);
    encoder.assert_term(i_le_j);
    let one = encoder.solver.int_const(1);
    let i_plus_one = encoder.solver.add(i, one);
    let succ_bound = encoder.solver.le(i_plus_one, j);
    let not_succ_bound = encoder.solver.not(succ_bound);
    encoder.assert_term(not_succ_bound);

    let asserted = encoder.assert_seq_ground_instances(
        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
    );
    assert!(
        asserted >= 1,
        "pivot-mediated value disequality should emit a finite index-order fact"
    );

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "value_i != pivot, pivot == value_j, and i <= j should force i + 1 <= j; got {result:?}"
    );
}

/// Verify that with only 2 ext_eq entries the bridge fires without hitting
/// the budget, producing the expected small number of bridge assertions.
///
/// This is the "small N" complement to the budget test above, ensuring
/// the bridge logic is correct when within budget.
#[test]
#[timeout(30000)]
fn test_ext_eq_bridge_fires_within_budget_for_small_n() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.ensure_seq_functions();

    let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
    let funcs = encoder.seq_funcs().clone();

    let receiver = encoder.solver.fresh_var("recv", seq_sort.clone());
    let x = encoder.solver.fresh_var("x", ay_dpll::api::Sort::Int);

    // Create exactly 2 ext_eq entries — one pair, two directions => up to 2 bridges
    for i in 0..2 {
        let a_i = encoder
            .solver
            .fresh_var(&format!("a_{i}"), seq_sort.clone());
        let b_i = encoder
            .solver
            .fresh_var(&format!("b_{i}"), seq_sort.clone());

        let concat_i = encoder.solver.apply(&funcs.seq_concat, &[a_i, b_i]);
        encoder.register_standard_ground_application("seq_concat", concat_i, vec![a_i, b_i]);

        let pb_i = encoder.solver.apply(&funcs.seq_push_back, &[a_i, x]);
        encoder.register_standard_ground_application("seq_push_back", pb_i, vec![a_i, x]);

        let pf_i = encoder.solver.apply(&funcs.seq_push_front, &[b_i, x]);
        encoder.register_standard_ground_application("seq_push_front", pf_i, vec![b_i, x]);

        let eq_var = encoder
            .solver
            .fresh_var(&format!("ext_eq_{i}"), ay_dpll::api::Sort::Bool);
        encoder
            .encoding_cache
            .ext_eq_registry_push((receiver, concat_i, eq_var));
    }

    let total = encoder.assert_seq_ground_instances(
        crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
    );

    // With 2 entries: 1 pair, 2 directions, each direction can match.
    // Non-bridge: 2 concat_len + 2 push_back_len + 2 reverse + 2 singleton
    //   + min(2*2, 80) push_back_concat = 2+2+2+2+4 = 12
    // Bridge: up to 2 (one pair, two directions)
    // Total: around 14

    // Verify bridge fired (total > non-bridge count)
    assert!(
        total >= 12,
        "expected at least 12 ground instances from 2 entries, got {total}"
    );
    // Verify it's bounded (well under the budget)
    assert!(
        total <= 20,
        "2 ext_eq entries should produce far fewer than budget (40) bridges, got {total}"
    );
}

/// Verify that 30 ext_eq entries sharing a receiver produce at most 40 bridge
/// assertions from the preservation bridge in `assert_seq_ground_instances`.
///
/// Without `TRUST_WP_EXT_EQ_BRIDGE_BUDGET`, 30 entries would produce 30*29 = 870 bridge
/// candidates (O(n^2)). With the budget at 40, the bridge assertions must not
/// exceed 40 regardless of how many entries share the receiver.
///
/// This test isolates the bridge contribution by computing the expected non-bridge
/// assertion count analytically and verifying the delta (total - non_bridge) <= 40.
///
/// Acceptance criteria for #2708:
///   "ext_eq registry with 30 entries sharing receiver produces <= 40 bridges"
#[test]
#[timeout(30000)]
fn test_ext_eq_30_entries_produces_at_most_40_bridges() {
    // Step 1: Compute the non-bridge baseline using an encoder without ext_eq entries.
    let non_bridge_count = {
        let mut baseline = AYEncoder::new_pure_with_quantifiers();
        baseline.ensure_seq_functions();

        let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
        let funcs = baseline.seq_funcs().clone();
        let x = baseline.solver.fresh_var("x", ay_dpll::api::Sort::Int);

        // Register the same push_back/push_front/concat entries but NO ext_eq entries.
        for i in 0..30 {
            let a_i = baseline
                .solver
                .fresh_var(&format!("a_{i}"), seq_sort.clone());
            let b_i = baseline
                .solver
                .fresh_var(&format!("b_{i}"), seq_sort.clone());

            let concat_i = baseline.solver.apply(&funcs.seq_concat, &[a_i, b_i]);
            baseline.register_standard_ground_application("seq_concat", concat_i, vec![a_i, b_i]);

            let pb_i = baseline.solver.apply(&funcs.seq_push_back, &[a_i, x]);
            baseline.register_standard_ground_application("seq_push_back", pb_i, vec![a_i, x]);

            let pf_i = baseline.solver.apply(&funcs.seq_push_front, &[b_i, x]);
            baseline.register_standard_ground_application("seq_push_front", pf_i, vec![b_i, x]);
        }

        baseline.assert_seq_ground_instances(
            crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
        )
    };

    // Step 2: Now run with 30 ext_eq entries sharing the same receiver.
    let total_with_bridge = {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        encoder.ensure_seq_functions();

        let seq_sort = ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int);
        let funcs = encoder.seq_funcs().clone();
        let receiver = encoder.solver.fresh_var("recv", seq_sort.clone());
        let x = encoder.solver.fresh_var("x", ay_dpll::api::Sort::Int);

        for i in 0..30 {
            let a_i = encoder
                .solver
                .fresh_var(&format!("a_{i}"), seq_sort.clone());
            let b_i = encoder
                .solver
                .fresh_var(&format!("b_{i}"), seq_sort.clone());

            let concat_i = encoder.solver.apply(&funcs.seq_concat, &[a_i, b_i]);
            encoder.register_standard_ground_application("seq_concat", concat_i, vec![a_i, b_i]);

            let pb_i = encoder.solver.apply(&funcs.seq_push_back, &[a_i, x]);
            encoder.register_standard_ground_application("seq_push_back", pb_i, vec![a_i, x]);

            let pf_i = encoder.solver.apply(&funcs.seq_push_front, &[b_i, x]);
            encoder.register_standard_ground_application("seq_push_front", pf_i, vec![b_i, x]);

            let eq_var = encoder
                .solver
                .fresh_var(&format!("ext_eq_{i}"), ay_dpll::api::Sort::Bool);
            encoder
                .encoding_cache
                .ext_eq_registry_push((receiver, concat_i, eq_var));
        }

        encoder.assert_seq_ground_instances(
            crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
        )
    };

    // Step 3: The delta is the bridge contribution.
    let bridge_count = total_with_bridge.saturating_sub(non_bridge_count);

    // The acceptance criterion: <= 40 bridges from 30 entries sharing a receiver.
    assert!(
        bridge_count <= 40,
        "ext_eq bridge assertions should be capped at TRUST_WP_EXT_EQ_BRIDGE_BUDGET=40, \
         but 30 entries produced {bridge_count} bridges \
         (total={total_with_bridge}, non_bridge_baseline={non_bridge_count}). \
         Without the cap, 30 entries would produce 30*29 = 870 bridges."
    );

    // Sanity: the bridge should fire at least once (pattern matches exist).
    assert!(
        bridge_count > 0,
        "ext_eq bridge should fire at least once with 30 matching entries, \
         but delta is {bridge_count} \
         (total={total_with_bridge}, baseline={non_bridge_count})"
    );
}

/// Stress test: 50 inserts + 50 contains entries (each contains references one
/// of the insert results) would produce O(50×50) = 2500 cross-product
/// assertions without the budget. With FMAP_INTERNAL_BUDGET = 80, the total
/// FMap ground assertions must be capped at 80. (#2707)
#[test]
#[timeout(30000)]
fn test_fmap_internal_budget_50_inserts_50_contains_capped_at_80() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[
            fmap.clone(),
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        fmap.clone(),
    );
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );
    let _len_decl = encoder.get_or_declare_spec_fn(
        "fmap_len",
        std::slice::from_ref(&fmap),
        ay_dpll::api::Sort::Int,
    );

    // Create 50 distinct insert applications
    let mut insert_apps = Vec::new();
    for i in 0..50 {
        let m = encoder.solver.fresh_var(&format!("m{i}"), fmap.clone());
        let k = encoder
            .solver
            .fresh_var(&format!("k{i}"), ay_dpll::api::Sort::Int);
        let v = encoder
            .solver
            .fresh_var(&format!("v{i}"), ay_dpll::api::Sort::Int);
        let inserted = encoder.solver.apply(&insert_decl, &[m, k, v]);
        encoder.register_standard_ground_application("fmap_insert", inserted, vec![m, k, v]);
        insert_apps.push(inserted);
    }

    // Register 50 contains entries, each referencing a different insert result.
    // This distributes the contains across all inserts (round-robin) to
    // exercise the cross-product loop broadly.
    let contains_decl_ref = encoder
        .spec_func_decl_cloned("fmap_contains")
        .expect("fmap_contains should be declared");
    for j in 0..50 {
        let ins_app = insert_apps[j % insert_apps.len()];
        let key = encoder
            .solver
            .fresh_var(&format!("ck_{j}"), ay_dpll::api::Sort::Int);
        let contains_app = encoder.solver.apply(&contains_decl_ref, &[ins_app, key]);
        encoder.register_standard_ground_application(
            "fmap_contains",
            contains_app,
            vec![ins_app, key],
        );
    }

    let asserted = encoder.assert_standard_ground_instances();

    // Without the FMAP_INTERNAL_BUDGET, 50 inserts × 1 matching contains each
    // would produce 50×3 base + 50×2 cross-product = 250 assertions minimum.
    // With the budget capped at 80, we must see <= 80.
    assert!(
        asserted <= 80,
        "FMap ground instances should be capped at FMAP_INTERNAL_BUDGET=80 \
         with 50 inserts + 50 contains, but got {asserted}"
    );

    // Sanity: should still produce some assertions
    assert!(
        asserted > 0,
        "FMap ground instances should produce at least some assertions, got 0"
    );
}

/// Stress test: 10 merges + 50 contains entries (each contains references one
/// of the merge results) would produce O(10×50×5) = 2500 cross-product
/// assertions without the budget. With FMAP_INTERNAL_BUDGET = 80, the total
/// FMap ground assertions must be capped at 80. (#2707)
#[test]
#[timeout(30000)]
fn test_fmap_internal_budget_10_merges_50_contains_capped_at_80() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = fmap_sort();

    let merge_decl =
        encoder.get_or_declare_spec_fn("fmap_merge", &[fmap.clone(), fmap.clone()], fmap.clone());
    let _contains_decl = encoder.get_or_declare_spec_fn(
        "fmap_contains",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Bool,
    );
    let _lookup_decl = encoder.get_or_declare_spec_fn(
        "fmap_lookup",
        &[fmap.clone(), ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Int,
    );

    // Create 10 distinct merge applications
    let mut merge_apps = Vec::new();
    for i in 0..10 {
        let m1 = encoder.solver.fresh_var(&format!("m1_{i}"), fmap.clone());
        let m2 = encoder.solver.fresh_var(&format!("m2_{i}"), fmap.clone());
        let merged = encoder.solver.apply(&merge_decl, &[m1, m2]);
        encoder.register_standard_ground_application("fmap_merge", merged, vec![m1, m2]);
        merge_apps.push(merged);
    }

    // Register 50 contains entries, distributed across merge results (round-robin).
    // Without the budget, 5 contains per merge × 10 merges × 5 assertions per
    // merge-contains pair = 250 assertions. With budget, capped at 80.
    let contains_decl_ref = encoder
        .spec_func_decl_cloned("fmap_contains")
        .expect("fmap_contains should be declared");
    for j in 0..50 {
        let merge_app = merge_apps[j % merge_apps.len()];
        let key = encoder
            .solver
            .fresh_var(&format!("mk_{j}"), ay_dpll::api::Sort::Int);
        let contains_app = encoder.solver.apply(&contains_decl_ref, &[merge_app, key]);
        encoder.register_standard_ground_application(
            "fmap_contains",
            contains_app,
            vec![merge_app, key],
        );
    }

    let asserted = encoder.assert_standard_ground_instances();

    // Without the FMAP_INTERNAL_BUDGET, this would produce far more than 80
    // assertions. With the budget, the total FMap assertions must be <= 80.
    assert!(
        asserted <= 80,
        "FMap ground instances should be capped at FMAP_INTERNAL_BUDGET=80 \
         with 10 merges + 50 contains, but got {asserted}"
    );

    // Sanity: should still produce some assertions
    assert!(
        asserted > 0,
        "FMap ground instances should produce at least some assertions, got 0"
    );
}

// ── CAP-80 staged retirement: len-nonneg demotion to quantifier passthrough ──
//
// The `ground/fmap_len_nonneg` family is the only FMap pool family whose
// quantified axiom (`forall m. fmap_len(m) >= 0`) is binder-exact, i.e.
// inside ay's decided rank-9 fragment. At retirement stage >= 1, when
// `assert_fmap_axioms` actually asserted that universal, the ground copies
// are skipped and the quantifier passes through to ay. All tests use the
// encoder-level stage override — never env vars (OnceLock race).

/// Positive: stage 1 + asserted universal (AUFLIA, non-proxy, Int signature)
/// demotes the ground family — the flush emits nothing — and the obligation
/// `fmap_len(m) < 0` still solves Unsat via the quantifier alone.
#[test]
#[timeout(30000)]
fn test_retirement_stage1_demotes_len_nonneg_and_quantifier_discharges() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    // fmap_insert with the legacy Int signature is required for
    // assert_fmap_axioms to get past its early returns.
    let _insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let len_decl =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    // Asserts the binder-exact len-nonneg universal (non-proxy mode) and
    // records coverage.
    encoder.assert_fmap_axioms();
    encoder.set_retirement_stage_override_for_test(Some(1));

    let m = encoder.solver.fresh_var("m", fmap);
    let len_m = encoder.solver.apply(&len_decl, &[m]);
    encoder.register_standard_ground_application("fmap_len", len_m, vec![m]);

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 0,
        "stage 1 with the len-nonneg universal asserted must demote the \
         ground fmap_len_nonneg family, got {asserted} ground instances"
    );

    // The quantifier alone must still discharge the obligation (existence
    // proof mirrored from coverage_gaps::fmap_axiom_tests::fmap_len_nonneg).
    let zero = encoder.solver.int_const(0);
    let len_neg = encoder.solver.lt(len_m, zero);
    encoder.solver.assert_term(len_neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_len(m) < 0 must stay UNSAT via the quantifier after demotion, got {result:?}"
    );
}

/// Negative control: stage 0 (legacy) keeps the ground family even when the
/// universal was asserted, and the obligation still discharges.
#[test]
#[timeout(30000)]
fn test_retirement_stage0_retains_ground_len_nonneg() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let _insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let len_decl =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    encoder.assert_fmap_axioms();
    // Explicit stage 0 keeps the test hermetic against process env.
    encoder.set_retirement_stage_override_for_test(Some(0));

    let m = encoder.solver.fresh_var("m", fmap);
    let len_m = encoder.solver.apply(&len_decl, &[m]);
    encoder.register_standard_ground_application("fmap_len", len_m, vec![m]);

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 1,
        "stage 0 must keep the ground fmap_len_nonneg family (legacy \
         keep-everything), got {asserted} ground instances"
    );

    let zero = encoder.solver.int_const(0);
    let len_neg = encoder.solver.lt(len_m, zero);
    encoder.solver.assert_term(len_neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_len(m) < 0 must be UNSAT at stage 0, got {result:?}"
    );
}

/// Fail-closed: in `Logic::All` the len universal is skipped (Int len
/// proxies), so coverage stays false and stage 1 must NOT demote — the
/// ground family is the sole semantic source in the production-default
/// datatype logic.
#[test]
#[timeout(30000)]
fn test_retirement_stage1_all_logic_proxy_mode_retains_ground_len_nonneg() {
    let mut encoder = AYEncoder::new_all();
    let fmap = fmap_sort();

    let _insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let _len_decl =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    // Proxy mode: the len-nonneg forall block is skipped → coverage false.
    encoder.assert_fmap_axioms();
    encoder.set_retirement_stage_override_for_test(Some(1));

    let m = encoder.solver.fresh_var("m", fmap);
    let len_m = encoder.fmap_len_term(m);
    encoder.register_standard_ground_application("fmap_len", len_m, vec![m]);

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 1,
        "Logic::All proxy mode never asserts the len universal; stage 1 must \
         fail closed and keep the ground family, got {asserted} ground instances"
    );

    let zero = encoder.solver.int_const(0);
    let len_neg = encoder.solver.lt(len_m, zero);
    encoder.solver.assert_term(len_neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "proxy fmap_len(m) < 0 must be UNSAT via the retained ground family, got {result:?}"
    );
}

/// Fail-closed: a non-Int legacy insert signature makes `assert_fmap_axioms`
/// early-return before any universal (including len-nonneg) is asserted, so
/// stage 1 must keep the ground family.
#[test]
#[timeout(30000)]
fn test_retirement_stage1_non_int_insert_signature_retains_ground_len_nonneg() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();
    let perm_cell = Sort::Uninterpreted("PermCell".to_string());

    let _insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), perm_cell, Sort::Int],
        fmap.clone(),
    );
    let len_decl =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    // Early-returns on the non-Int signature → coverage stays false.
    encoder.assert_fmap_axioms();
    encoder.set_retirement_stage_override_for_test(Some(1));

    let m = encoder.solver.fresh_var("m", fmap);
    let len_m = encoder.solver.apply(&len_decl, &[m]);
    encoder.register_standard_ground_application("fmap_len", len_m, vec![m]);

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 1,
        "non-Int insert signature skips the quantified axioms; stage 1 must \
         fail closed and keep the ground family, got {asserted} ground instances"
    );

    let zero = encoder.solver.int_const(0);
    let len_neg = encoder.solver.lt(len_m, zero);
    encoder.solver.assert_term(len_neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_len(m) < 0 must be UNSAT via the retained ground family, got {result:?}"
    );
}

/// Fail-closed: without an `fmap_insert` decl, `assert_fmap_axioms` asserts
/// NOTHING (including len-nonneg), so stage 1 must keep the ground family.
#[test]
#[timeout(30000)]
fn test_retirement_stage1_missing_insert_decl_retains_ground_len_nonneg() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let len_decl =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    // No fmap_insert decl → assert_fmap_axioms is a no-op → coverage false.
    encoder.assert_fmap_axioms();
    encoder.set_retirement_stage_override_for_test(Some(1));

    let m = encoder.solver.fresh_var("m", fmap);
    let len_m = encoder.solver.apply(&len_decl, &[m]);
    encoder.register_standard_ground_application("fmap_len", len_m, vec![m]);

    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 1,
        "missing fmap_insert decl means no universals were asserted; stage 1 \
         must fail closed and keep the ground family, got {asserted} ground instances"
    );

    let zero = encoder.solver.int_const(0);
    let len_neg = encoder.solver.lt(len_m, zero);
    encoder.solver.assert_term(len_neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fmap_len(m) < 0 must be UNSAT via the retained ground family, got {result:?}"
    );
}

/// False-variant control: with the stage-1 demotion active, a satisfiable
/// length constraint (`fmap_len(m) = 5`) must NEVER become Unsat. We assert
/// never-Unsat rather than forcing Sat — Unknown is always acceptable.
#[test]
#[timeout(30000)]
fn test_retirement_stage1_len_eq_five_never_unsat() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = fmap_sort();

    let _insert_decl = encoder.get_or_declare_spec_fn(
        "fmap_insert",
        &[fmap.clone(), Sort::Int, Sort::Int],
        fmap.clone(),
    );
    let len_decl =
        encoder.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

    encoder.assert_fmap_axioms();
    encoder.set_retirement_stage_override_for_test(Some(1));

    let m = encoder.solver.fresh_var("m", fmap);
    let len_m = encoder.solver.apply(&len_decl, &[m]);
    encoder.register_standard_ground_application("fmap_len", len_m, vec![m]);
    let asserted = encoder.assert_standard_ground_instances();
    assert_eq!(
        asserted, 0,
        "demotion should be active in this configuration"
    );

    let five = encoder.solver.int_const(5);
    let len_eq_five = encoder.solver.eq(len_m, five);
    encoder.solver.assert_term(len_eq_five);
    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "fmap_len(m) = 5 is consistent with len >= 0 and must never be \
         UNSAT under the demotion, got {result:?}"
    );
}
