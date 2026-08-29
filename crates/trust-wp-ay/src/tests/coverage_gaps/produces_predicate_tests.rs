// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// `produces(iter, visited, o)` must encode as a Bool-sorted UF.
/// Two independent produces calls can have different truth values.
#[test]
#[timeout(30000)]
fn test_produces_encodes_as_bool_uf() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

    let call1 = method_call(var("i1"), "produces", vec![var("v1"), var("o1")]);
    let call2 = method_call(var("i2"), "produces", vec![var("v2"), var("o2")]);
    let t1 = encoder
        .encode_pure(&call1)
        .expect("first produces call should encode");
    let t2 = encoder
        .encode_pure(&call2)
        .expect("second produces call should encode");

    // Assert produces(i1,v1,o1) = false AND produces(i2,v2,o2) = true
    let neg_t1 = encoder.solver_mut().not(t1);
    encoder.assert_term(neg_t1);
    encoder.assert_term(t2);

    // ay's soundness guard (ay#2865) may return Unknown for formulas
    // with unhandled quantifiers from seq axioms.
    let produces_result = encoder.check_sat();
    assert!(
        !matches!(produces_result, SolveResult::Unsat(_)),
        "Two independent produces calls should not be Unsat, got {produces_result:?}"
    );
}

/// `produces` must reject wrong argument count (too few).
#[test]
#[timeout(30000)]
fn test_produces_wrong_arity_too_few_errors() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let bad_call = method_call(var("iter"), "produces", vec![var("visited")]);
    let result = encoder.encode_pure(&bad_call);
    let err = result.expect_err("produces with 1 argument should return EncodingError");
    let msg = err.to_string();
    assert!(
        msg.contains("produces") || msg.contains("arity") || msg.contains("argument"),
        "error message should mention produces or arity, got: {msg}"
    );
}

/// `produces` must reject wrong argument count (too many).
#[test]
#[timeout(30000)]
fn test_produces_wrong_arity_too_many_errors() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let bad_call = method_call(
        var("iter"),
        "produces",
        vec![var("v"), var("o"), var("extra")],
    );
    let result = encoder.encode_pure(&bad_call);
    let err = result.expect_err("produces with 3 arguments should return EncodingError");
    let msg = err.to_string();
    assert!(
        msg.contains("produces") || msg.contains("arity") || msg.contains("argument"),
        "error message should mention produces or arity, got: {msg}"
    );
}

/// Calling produces twice with same args should reuse the same UF declaration.
#[test]
#[timeout(30000)]
fn test_produces_idempotent_func_decl() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let call = method_call(var("iter"), "produces", vec![var("visited"), var("o")]);
    let t1 = encoder
        .encode_pure(&call)
        .expect("first encode should succeed");
    let t2 = encoder
        .encode_pure(&call)
        .expect("second encode should succeed (reuse)");

    let eq = encoder.solver_mut().eq(t1, t2);
    let neg_eq = encoder.solver_mut().not(eq);
    encoder.assert_term(neg_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Two encodes of same produces call must produce equal terms"
    );
}

/// Bare variable as visited param should get Seq sort hint — no panic.
/// Verify the result is Bool-sorted by checking contradiction is UNSAT.
#[test]
#[timeout(30000)]
fn test_produces_visited_gets_seq_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let call = method_call(var("iter"), "produces", vec![var("seq_var"), var("next")]);
    let term = encoder
        .encode_pure(&call)
        .expect("produces should handle bare variable visited param via Seq sort hint");

    // Verify the result is Bool-sorted: p AND NOT p is UNSAT
    let contradiction = {
        let solver = encoder.solver_mut();
        let neg = solver.not(term);
        solver.and(term, neg)
    };
    encoder.assert_term(contradiction);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "produces result must be Bool-sorted (contradiction should be UNSAT)"
    );
}

/// Reflexivity axiom: `produces(iter, seq_empty, iter)` must be true.
///
/// The produces predicate asserts `forall iter. produces(iter, empty, iter)`.
/// If we negate this for a specific `a` — `NOT produces(a, seq_empty, a)` —
/// it should be UNSAT because the universal axiom covers all `a`.
#[test]
#[timeout(30000)]
fn test_produces_reflexivity_axiom_semantic() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // First, trigger produces axiom registration by encoding any produces call.
    let trigger = method_call(
        var("dummy_iter"),
        "produces",
        vec![var("dummy_v"), var("dummy_o")],
    );
    encoder
        .encode_pure(&trigger)
        .expect("trigger call should encode");

    // Now encode produces(a, seq_empty, a) using the LogicFnCall for seq_empty.
    let seq_empty_expr = logic_fn_call("seq_empty", vec![]);
    let refl_call = method_call(var("a"), "produces", vec![seq_empty_expr, var("a")]);
    let refl_term = encoder
        .encode_pure(&refl_call)
        .expect("produces(a, seq_empty, a) should encode");

    // Negate: NOT produces(a, seq_empty, a) — should be UNSAT by reflexivity axiom
    let neg = encoder.solver_mut().not(refl_term);
    encoder.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "produces reflexivity axiom: produces(a, seq_empty, a) must hold for all a"
    );
}

#[test]
#[timeout(30000)]
fn test_logical_fmap_iter_produces_implies_length_partition() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let iter_sort = ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(
        "logic::fmap::Iter",
    ));
    let produces = method_call(
        var_with_sort("it", iter_sort.clone()),
        "produces",
        vec![
            var_with_sort("visited", ExprSort::Seq),
            var_with_sort("next", iter_sort.clone()),
        ],
    );
    encoder.register_sort_hints(std::slice::from_ref(&produces));
    encoder.register_formula_sort_hints(std::slice::from_ref(&produces));
    let produces_term = encoder
        .encode_pure(&produces)
        .expect("logical FMapIter produces should encode");
    encoder.assert_term(produces_term);

    let len_partition = eq(
        method_call(view(var_with_sort("it", iter_sort.clone())), "len", vec![]),
        add(
            method_call(var_with_sort("visited", ExprSort::Seq), "len", vec![]),
            method_call(view(var_with_sort("next", iter_sort)), "len", vec![]),
        ),
    );
    encoder.register_sort_hints(std::slice::from_ref(&len_partition));
    encoder.register_formula_sort_hints(std::slice::from_ref(&len_partition));
    let len_partition_term = encoder
        .encode_pure(&len_partition)
        .expect("length partition should encode");
    let neg = encoder.solver_mut().not(len_partition_term);
    encoder.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "logical FMapIter produces should imply len(self@) == len(visited) + len(next@)"
    );
}

#[test]
#[timeout(30000)]
fn test_repeated_logical_fmap_iter_produces_keeps_length_partition() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let iter_sort = ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(
        "logic::fmap::Iter",
    ));
    let produces = method_call(
        var_with_sort("it", iter_sort.clone()),
        "produces",
        vec![
            var_with_sort("visited", ExprSort::Seq),
            var_with_sort("next", iter_sort.clone()),
        ],
    );
    encoder.register_sort_hints(std::slice::from_ref(&produces));
    encoder.register_formula_sort_hints(std::slice::from_ref(&produces));
    let first = encoder
        .encode_pure(&produces)
        .expect("first logical FMapIter produces should encode");
    let second = encoder
        .encode_pure(&produces)
        .expect("repeated logical FMapIter produces should encode");

    assert_eq!(
        encoder.solver().format_term(first),
        encoder.solver().format_term(second),
        "deduplicating the asserted implication must not drop the returned length consequence"
    );

    encoder.assert_term(second);
    let len_partition = eq(
        method_call(view(var_with_sort("it", iter_sort.clone())), "len", vec![]),
        add(
            method_call(var_with_sort("visited", ExprSort::Seq), "len", vec![]),
            method_call(view(var_with_sort("next", iter_sort)), "len", vec![]),
        ),
    );
    encoder.register_sort_hints(std::slice::from_ref(&len_partition));
    encoder.register_formula_sort_hints(std::slice::from_ref(&len_partition));
    let len_partition_term = encoder
        .encode_pure(&len_partition)
        .expect("length partition should encode after repeated produces");
    let neg = encoder.solver_mut().not(len_partition_term);
    encoder.assert_term(neg);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "a repeated logical FMapIter produces call must retain its length partition"
    );
}

#[test]
#[timeout(30000)]
fn test_non_fmap_datatype_produces_does_not_imply_fmap_partition() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));
    let vec_sort = ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("std::vec::Vec"));
    let produces = method_call(
        var_with_sort("v", vec_sort.clone()),
        "produces",
        vec![
            var_with_sort("visited", ExprSort::Seq),
            var_with_sort("next", vec_sort.clone()),
        ],
    );
    encoder.register_sort_hints(std::slice::from_ref(&produces));
    encoder.register_formula_sort_hints(std::slice::from_ref(&produces));
    let produces_term = encoder
        .encode_pure(&produces)
        .expect("non-FMap datatype produces should encode");
    encoder.assert_term(produces_term);

    let len_partition = eq(
        method_call(
            logic_fn_call(
                "__trust_wp_fmap_iter_view",
                vec![var_with_sort("v", vec_sort.clone())],
            ),
            "len",
            vec![],
        ),
        add(
            method_call(var_with_sort("visited", ExprSort::Seq), "len", vec![]),
            method_call(
                logic_fn_call(
                    "__trust_wp_fmap_iter_view",
                    vec![var_with_sort("next", vec_sort)],
                ),
                "len",
                vec![],
            ),
        ),
    );
    encoder.register_sort_hints(std::slice::from_ref(&len_partition));
    encoder.register_formula_sort_hints(std::slice::from_ref(&len_partition));
    let len_partition_term = encoder
        .encode_pure(&len_partition)
        .expect("fmap partition probe should encode");
    let neg = encoder.solver_mut().not(len_partition_term);
    encoder.assert_term(neg);

    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "non-FMap datatype receivers must not inherit the logical FMapIter produces decomposition: {result:?}"
    );
}
