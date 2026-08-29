// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// spec_unwrap is shared between Option and Result.
/// Disjointness axioms must prevent conflation: is_some(x) must NOT
/// imply is_ok(x) even when they share the same spec_unwrap UF.
///
/// This tests a concrete scenario: x = Some(5), so is_some(x) and
/// spec_unwrap(x) = 5. If we also assert is_ok(x) (attempting to treat
/// x as both Some and Ok), the disjointness axioms must make it UNSAT.
#[test]
#[timeout(30000)]
fn test_spec_unwrap_shared_uf_no_conflation() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode is_some(x) and is_ok(x) on the same x
    let is_some_x = method_call(var("x"), "is_some", vec![]);
    let is_ok_x = method_call(var("x"), "is_ok", vec![]);
    let unwrap_x = method_call(var("x"), "unwrap", vec![]);

    let is_some_term = encoder
        .encode_pure(&is_some_x)
        .expect("is_some(x) should encode");
    let is_ok_term = encoder
        .encode_pure(&is_ok_x)
        .expect("is_ok(x) should encode");
    let unwrap_term = encoder
        .encode_pure(&unwrap_x)
        .expect("unwrap(x) should encode");

    encoder.assert_option_result_axioms();

    // x is Some with a specific unwrap value
    encoder.assert_term(is_some_term);
    let five = encoder.encode_pure(&int(5)).unwrap();
    let unwrap_eq_5 = encoder.solver_mut().eq(unwrap_term, five);
    encoder.assert_term(unwrap_eq_5);

    // Now try to also assert is_ok(x) — disjointness must make this UNSAT
    encoder.assert_term(is_ok_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(x) && is_ok(x) must be UNSAT even when sharing spec_unwrap UF"
    );
}

/// Negated unwrap axiom: spec_unwrap(Some(42)) must equal 42.
#[test]
#[timeout(30000)]
fn test_spec_unwrap_some_semantic() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let some_42 = logic_fn_call("Some", vec![int(42)]);
    let unwrap_some = method_call(some_42, "unwrap", vec![]);

    let unwrap_term = encoder
        .encode_pure(&unwrap_some)
        .expect("Some(42).unwrap() should encode");
    let forty_two = encoder.encode_pure(&int(42)).unwrap();

    encoder.assert_option_result_axioms();

    let eq_term = encoder.solver_mut().eq(unwrap_term, forty_two);
    let neq = encoder.solver_mut().not(eq_term);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "spec_unwrap(Some(42)) != 42 must be UNSAT (unwrap accessor axiom)"
    );
}

/// Option round-trip: unwrap(Some(v)) must equal v for symbolic v.
#[test]
#[timeout(30000)]
fn test_option_unwrap_round_trip_symbolic() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let some_v = logic_fn_call("Some", vec![var("v")]);
    let unwrap_sv = method_call(some_v.clone(), "unwrap", vec![]);

    // Encode Some(v) to register the symbol
    let _sv = encoder.encode_pure(&some_v).expect("Some(v) should encode");
    let unwrap_term = encoder
        .encode_pure(&unwrap_sv)
        .expect("unwrap(Some(v)) should encode");

    encoder.assert_option_result_axioms();

    let v_term = encoder.encode_pure(&var("v")).unwrap();
    let eq_term = encoder.solver_mut().eq(unwrap_term, v_term);
    let neq = encoder.solver_mut().not(eq_term);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap(Some(v)) must equal v (option accessor round-trip)"
    );
}

/// Result Err round-trip: unwrap_err(Err(e)) must equal e.
#[test]
#[timeout(30000)]
fn test_result_err_unwrap_round_trip_symbolic() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let err_v = logic_fn_call("Err", vec![var("e")]);
    let unwrap_err_ev = method_call(err_v.clone(), "unwrap_err", vec![]);

    let _ev = encoder.encode_pure(&err_v).expect("Err(e) should encode");
    let unwrap_err_term = encoder
        .encode_pure(&unwrap_err_ev)
        .expect("unwrap_err(Err(e)) should encode");

    encoder.assert_option_result_axioms();

    let e_term = encoder.encode_pure(&var("e")).unwrap();
    let eq_term = encoder.solver_mut().eq(unwrap_err_term, e_term);
    let neq = encoder.solver_mut().not(eq_term);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unwrap_err(Err(e)) must equal e (result error accessor round-trip)"
    );
}

/// Closure fn_mut_law res_state boundary: arity 4 postcondition.
/// Tests the res_state_idx = post_arity - 1 calculation in
/// assert_fn_mut_law_and_hist_inv (axioms.rs:388) at a non-trivial arity.
#[test]
#[timeout(30000)]
fn test_fn_mut_law_res_state_idx_boundary_arity_4() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // 4-param postcondition: (f, x, y, r)
    let post_expr = method_call(
        var("f"),
        "postcondition",
        vec![var("x"), var("y"), var("r")],
    );
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("y"), var("s"), var("r")],
    );
    let once_expr = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("y"), var("r")],
    );

    encoder.encode_pure(&post_expr).expect("post");
    encoder.encode_pure(&mut_expr).expect("mut");
    encoder.encode_pure(&once_expr).expect("once");

    encoder.assert_fn_closure_laws();

    // Assert postcondition_mut(f, x, y, s, r) with s != f
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    encoder.assert_term(mut_term);

    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let s_term = encoder.encode_pure(&var("s")).unwrap();
    let f_eq_s = encoder.solver_mut().eq(f_term, s_term);
    let f_neq_s = encoder.solver_mut().not(f_eq_s);
    encoder.assert_term(f_neq_s);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "postcondition_mut with s != f must be UNSAT by fn_mut_law (arity-4 boundary); got {result:?}"
    );
}

/// fn_once_law at minimum arity (2): (self, result) only.
/// Tests boundary where sort_tags has exactly 2 elements.
#[test]
#[timeout(30000)]
fn test_fn_once_law_arity_2_boundary() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // 2-param postcondition: (f, r)
    let post_expr = method_call(var("f"), "postcondition", vec![var("r")]);
    let once_expr = method_call(var("f"), "postcondition_once", vec![var("r")]);

    encoder.encode_pure(&post_expr).expect("post");
    encoder.encode_pure(&once_expr).expect("once");

    encoder.assert_fn_closure_laws();

    // postcondition AND NOT postcondition_once should be UNSAT
    let post_term = encoder.encode_pure(&post_expr).unwrap();
    let once_term = encoder.encode_pure(&once_expr).unwrap();
    let neg_once = encoder.solver_mut().not(once_term);
    let both = encoder.solver_mut().and(post_term, neg_once);
    encoder.assert_term(both);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "postcondition AND NOT postcondition_once must be UNSAT at arity 2; got {result:?}"
    );
}

/// Closure spec symbol format: encode_closure_spec_method must register
/// SMT function symbols with the exact format `closure_{method}_{arity}_{sort_sig}`.
///
/// This tests the `closure_spec_symbol` helper (axioms.rs:54) via its
/// observable effect on `decls.logic_funcs`. Without this test, a bug that
/// corrupts the sort signature suffix (e.g., missing delimiter) would not
/// be caught — existing tests only use `starts_with` prefix checks.
#[test]
#[timeout(30000)]
fn test_closure_spec_symbol_exact_format() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // 3-param postcondition: (f, x, r) — all Int-sorted
    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder
        .encode_pure(&post_expr)
        .expect("postcondition should encode");

    assert!(
        encoder
            .decls()
            .has_logic_func("closure_postcondition_3_i_i_i"),
        "encode_closure_spec_method must register closure_postcondition_3_i_i_i; \
         found keys: {:?}",
        encoder
            .decls()
            .logic_func_names()
            .filter(|k| k.starts_with("closure_"))
            .collect::<Vec<_>>()
    );

    // 4-param postcondition_mut with Bool arg: (f, x_bool, s, r)
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![bool_expr(true), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    assert!(
        encoder
            .decls()
            .has_logic_func("closure_postcondition_mut_4_i_b_i_i"),
        "Bool-arg closure spec must produce sort tag 'b' in symbol; \
         found keys: {:?}",
        encoder
            .decls()
            .logic_func_names()
            .filter(|k| k.starts_with("closure_postcondition_mut_"))
            .collect::<Vec<_>>()
    );
}

/// fn_closure_laws when postcondition exists but postcondition_once does NOT.
///
/// Tests the early return in `assert_fn_once_law` (axioms.rs:457-459)
/// where `once_decl` is `None`. The fn_mut law should still fire correctly
/// even though the fn_once law has nothing to connect.
#[test]
#[timeout(30000)]
fn test_fn_closure_laws_no_postcondition_once_no_crash() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("s"), var("r")],
    );

    encoder.encode_pure(&post_expr).expect("post");
    encoder.encode_pure(&mut_expr).expect("mut");

    // Should not crash despite missing postcondition_once
    encoder.assert_fn_closure_laws();

    // The fn_mut law should still work (postcondition ↔ postcondition_mut)
    let mut_term = encoder.encode_pure(&mut_expr).unwrap();
    let post_term = encoder.encode_pure(&post_expr).unwrap();

    let f_term = encoder.encode_pure(&var("f")).unwrap();
    let s_term = encoder.encode_pure(&var("s")).unwrap();
    let f_eq_s = encoder.solver_mut().eq(f_term, s_term);
    encoder.assert_term(f_eq_s);
    encoder.assert_term(mut_term);
    let neg_post = encoder.solver_mut().not(post_term);
    encoder.assert_term(neg_post);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "fn_mut_law must still connect postcondition and postcondition_mut \
         even when postcondition_once is absent; got {result:?}"
    );
}

/// fn_closure_laws when postcondition exists but postcondition_mut does NOT.
///
/// Tests the early return in `assert_fn_mut_law_and_hist_inv` (axioms.rs:373-375)
/// where `mut_decl` is `None`. The postcondition should remain unconstrained.
#[test]
#[timeout(30000)]
fn test_fn_closure_laws_postcondition_without_mut_unconstrained() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let post_expr = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder.encode_pure(&post_expr).expect("post");

    // Should not crash
    encoder.assert_fn_closure_laws();

    let post_term = encoder.encode_pure(&post_expr).unwrap();
    encoder.assert_term(post_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "postcondition without postcondition_mut should remain unconstrained; got {result:?}"
    );

    // Dual check: negated postcondition should also be satisfiable.
    let mut encoder_dual = AYEncoder::new_with_quantifiers();
    let post_expr_dual = method_call(var("f"), "postcondition", vec![var("x"), var("r")]);
    encoder_dual
        .encode_pure(&post_expr_dual)
        .expect("postcondition should encode for dual check");
    encoder_dual.assert_fn_closure_laws();
    let post_term_dual = encoder_dual.encode_pure(&post_expr_dual).unwrap();
    let neg_post_dual = encoder_dual.solver_mut().not(post_term_dual);
    encoder_dual.assert_term(neg_post_dual);
    let dual_result = encoder_dual.check_sat();
    assert!(
        matches!(dual_result, SolveResult::Sat),
        "negated postcondition without postcondition_mut should remain unconstrained; got {dual_result:?}"
    );
}

/// Produces axiom sort guard: `assert_produces_axioms` must silently skip
/// axiom generation when `param_sorts.len() != 3` (axioms.rs:868-870).
///
/// Declares a produces-like function with arity 2 (should be 3) and
/// verifies that `assert_produces_axioms` returns without asserting any
/// axioms and without crashing.
#[test]
#[timeout(30000)]
fn test_produces_axioms_wrong_arity_skips_silently() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let wrong_decl =
        encoder
            .solver_mut()
            .declare_fun("produces_wrong", &[Sort::Int, Sort::Int], Sort::Bool);

    // Should not crash — arity guard returns early
    encoder.assert_produces_axioms(&wrong_decl);

    // Verify no axioms were asserted: context should remain trivially SAT
    let x = encoder.solver_mut().fresh_var("x", Sort::Int);
    let y = encoder.solver_mut().fresh_var("y", Sort::Int);
    let app = encoder.solver_mut().apply(&wrong_decl, &[x, y]);
    encoder.assert_term(app);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Wrong-arity produces func should not trigger any axioms; got {result:?}"
    );

    // Dual check: the negated application should also remain satisfiable.
    let mut encoder_dual = AYEncoder::new_with_quantifiers();
    let wrong_decl_dual = encoder_dual.solver_mut().declare_fun(
        "produces_wrong_dual",
        &[Sort::Int, Sort::Int],
        Sort::Bool,
    );
    encoder_dual.assert_produces_axioms(&wrong_decl_dual);
    let x_dual = encoder_dual.solver_mut().fresh_var("x", Sort::Int);
    let y_dual = encoder_dual.solver_mut().fresh_var("y", Sort::Int);
    let app_dual = encoder_dual
        .solver_mut()
        .apply(&wrong_decl_dual, &[x_dual, y_dual]);
    let neg_app_dual = encoder_dual.solver_mut().not(app_dual);
    encoder_dual.assert_term(neg_app_dual);
    let dual_result = encoder_dual.check_sat();
    assert!(
        matches!(dual_result, SolveResult::Sat),
        "negated wrong-arity produces app should also remain unconstrained; got {dual_result:?}"
    );
}

/// Produces axiom sort guard: `state_sort != succ_sort` (axioms.rs:874-878).
///
/// When the first and third parameter sorts differ, `assert_produces_axioms`
/// must skip silently because IteratorSpec laws require homogeneous state.
#[test]
#[timeout(30000)]
fn test_produces_axioms_heterogeneous_state_skips_silently() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Get the Seq sort before borrowing encoder mutably. The skip path under
    // test only depends on the declaration domain sorts, so avoid registering
    // unrelated produces/seq axioms that can make this SAT-side query Unknown.
    let seq_sort = encoder.seq_state_mut_for_test().get_or_init_sort();

    // Declare produces with mismatched state sorts: (Int, Seq, Bool)
    let hetero_decl = encoder.solver_mut().declare_fun(
        "produces_hetero",
        &[Sort::Int, seq_sort.clone(), Sort::Bool],
        Sort::Bool,
    );

    // Should silently skip due to state_sort (Int) != succ_sort (Bool).
    let assertions_before = encoder.solver().assertions().len();
    let ground_axioms_before = encoder.ground_pool_axiom_count();
    encoder.assert_produces_axioms(&hetero_decl);
    assert_eq!(
        encoder.solver().assertions().len(),
        assertions_before,
        "heterogeneous produces declaration must not install IteratorSpec axioms"
    );
    assert_eq!(
        encoder.ground_pool_axiom_count(),
        ground_axioms_before,
        "heterogeneous produces declarations must not register ground axioms"
    );

    // The function should remain unconstrained
    let dummy_seq = encoder.solver_mut().fresh_var("dummy_seq", seq_sort);
    let zero = encoder.solver_mut().int_const(0);
    let t = encoder.solver_mut().bool_const(true);
    let app = encoder
        .solver_mut()
        .apply(&hetero_decl, &[zero, dummy_seq, t]);
    let neg = encoder.solver_mut().not(app);
    encoder.assert_term(neg);

    encoder.set_timeout(Some(std::time::Duration::from_secs(2)));
    let result = encoder.check_sat();
    assert!(
        !result.is_unsat(),
        "an unconstrained heterogeneous produces application must not become contradictory; AY may conservatively return Unknown when the Seq carrier model is incomplete, got {result:?}"
    );
}
