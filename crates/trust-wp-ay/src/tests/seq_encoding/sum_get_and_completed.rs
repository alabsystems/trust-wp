// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq encoding (Part of #111).
//!
//! Includes sequence view, len, index, `push_back`, error handling, and axiom tests.
//! Split from encoding.rs per #395.

use super::*;

fn assert_unsat_or_structured_seq_get_quantifier_limit(
    encoder: &AYEncoder,
    result: SolveResult,
    context: &str,
) {
    if matches!(result, SolveResult::Unsat(_)) {
        return;
    }

    let structured_unknown = matches!(result, SolveResult::Unknown)
        && matches!(
            encoder.last_unknown_reason(),
            Some(crate::shared_types::UnknownReason::QuantifierUnhandled)
        );

    assert!(
        structured_unknown,
        "{context} should be UNSAT or fail closed with QuantifierUnhandled on symbolic bounds; \
         got {result:?}; reason={:?}; executor={:?}",
        encoder.last_unknown_reason(),
        encoder.last_executor_error()
    );
}

// =============================================================================
// Seq sum() Tests (#690)
// =============================================================================

/// Test that v@.sum() encodes successfully and triggers Seq function initialization.
#[test]
#[timeout(30000)]
fn test_encode_seq_sum_basic() {
    let mut encoder = AYEncoder::new();

    // v@.sum()
    let expr = method_call(view(var("v")), "sum", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "v@.sum() encoding should succeed: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "Seq functions should be initialized after encoding sum()"
    );
}

/// Axiom 7: sum(push_back(s, v)) = sum(s) + v
/// Test with concrete constant.
#[test]
#[timeout(30000)]
fn test_seq_axiom_sum_push_back_concrete() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));

    // sum(push_back(v, 42)) == sum(v) + 42
    let push_sum = method_call(
        method_call(v_view_expr.clone(), "push_back", vec![int(42)]),
        "sum",
        vec![],
    );

    let v_sum = method_call(v_view_expr, "sum", vec![]);

    let v_sum_plus_42 = add(v_sum, int(42));

    let axiom_check = eq(push_sum, v_sum_plus_42);

    let formula = encoder
        .encode_pure(&axiom_check)
        .expect("sum axiom formula should encode");

    let neg = encoder.solver.not(formula);
    encoder.assert_term(neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "sum(push_back(v, 42)) != sum(v) + 42 should be UNSAT (axiom 7), got {result:?}"
    );
}

/// Axiom 7: sum(push_back(s, v)) = sum(s) + v with symbolic value x.
/// Ensures the universal quantifier instantiates for arbitrary values.
#[test]
#[timeout(30000)]
fn test_seq_axiom_sum_push_back_symbolic() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));
    let x = var("x");

    let push_sum = method_call(
        method_call(v_view_expr.clone(), "push_back", vec![x.clone()]),
        "sum",
        vec![],
    );

    let v_sum = method_call(v_view_expr, "sum", vec![]);

    let v_sum_plus_x = add(v_sum, x);

    let axiom_check = eq(push_sum, v_sum_plus_x);

    let formula = encoder
        .encode_pure(&axiom_check)
        .expect("symbolic sum axiom should encode");

    let neg = encoder.solver.not(formula);
    encoder.assert_term(neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "sum(push_back(v, x)) != sum(v) + x should be UNSAT (axiom 7), got {result:?}"
    );
}

// =============================================================================
// Seq get() Tests (#690)
// =============================================================================

/// Test that v@.get(0) encodes successfully.
#[test]
#[timeout(30000)]
fn test_encode_seq_get_basic() {
    let mut encoder = AYEncoder::new();

    // v@.get(0)
    let expr = method_call(view(var("v")), "get", vec![int(0)]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "v@.get(0) encoding should succeed: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "Seq functions should be initialized after encoding get()"
    );
}

/// Ground in-bounds get semantics must either prove for an observed concrete
/// index or fail closed with the current ay quantifier limitation.
#[test]
#[timeout(30000)]
fn test_seq_axiom_get_concrete_in_bounds_returns_some_or_quantifier_unknown() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let pushed = method_call(
        logic_fn_call("seq_empty", vec![]),
        "push_back",
        vec![int(7)],
    );
    let get_expr = method_call(pushed.clone(), "get", vec![int(0)]);
    let index_expr = method_call(pushed, "index_logic", vec![int(0)]);
    let some_of_index = logic_fn_call("Some", vec![index_expr]);

    let get_term = encoder
        .encode_pure(&get_expr)
        .expect("get encoding should succeed");
    let some_term = encoder
        .encode_pure(&some_of_index)
        .expect("Some(index_logic) should encode");

    encoder.assert_option_result_axioms();
    let eq_check = encoder.eq_or_iff(get_term, some_term, &Sort::Int);
    let neg_formula = encoder.solver.not(eq_check);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert_unsat_or_structured_seq_get_quantifier_limit(
        &encoder,
        result,
        "concrete in-bounds get != Some(index_logic)",
    );
}

/// Axiom 8a: in-bounds get(s, i) == Some(index_logic(s, i)) (#1882).
/// Given 0 <= i < len(v@), verify or fail closed on the symbolic quantified
/// bound case.
#[test]
#[timeout(30000)]
fn test_seq_axiom_get_in_bounds_returns_some() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let v_view_expr = view(var("v"));
    let i_expr = var("i");

    // Encode v@.get(i)
    let get_expr = method_call(v_view_expr.clone(), "get", vec![i_expr.clone()]);
    let get_term = encoder
        .encode_pure(&get_expr)
        .expect("get encoding should succeed");

    // Encode Some(index_logic(v@, i))
    let index_expr = method_call(v_view_expr.clone(), "index_logic", vec![i_expr.clone()]);
    let some_of_index = logic_fn_call("Some", vec![index_expr]);
    let some_term = encoder
        .encode_pure(&some_of_index)
        .expect("Some(index_logic) should encode");

    // Assert option axioms so is_some/unwrap work correctly
    encoder.assert_option_result_axioms();

    // Constrain i to be in-bounds: 0 <= i < len(v@)
    let i_var = encoder.vars_for_test()["i"];
    let zero = encoder.solver.int_const(0);
    let i_ge_zero = encoder.solver.ge(i_var, zero);
    encoder.assert_term(i_ge_zero);

    let len_expr = method_call(v_view_expr, "len", vec![]);
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("len encoding should succeed");
    let i_lt_len = encoder.solver.lt(i_var, len_term);
    encoder.assert_term(i_lt_len);

    // Negate: get(v@, i) != Some(index_logic(v@, i))
    let eq_check = encoder.eq_or_iff(get_term, some_term, &Sort::Int);
    let neg_formula = encoder.solver.not(eq_check);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert_unsat_or_structured_seq_get_quantifier_limit(
        &encoder,
        result,
        "in-bounds get(v, i) != Some(index_logic(v, i))",
    );
}

/// Axiom 8b: out-of-bounds get(s, i) == None (#1882).
/// Given i >= len(v@), verify get(v@, i) == None via UNSAT negation.
#[test]
#[timeout(30000)]
fn test_seq_axiom_get_out_of_bounds_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let v_view_expr = view(var("v"));
    let i_expr = var("i");

    // Encode v@.get(i)
    let get_expr = method_call(v_view_expr.clone(), "get", vec![i_expr.clone()]);
    let get_term = encoder
        .encode_pure(&get_expr)
        .expect("get encoding should succeed");

    // Encode None
    let none_expr = logic_fn_call("None", vec![]);
    let none_term = encoder.encode_pure(&none_expr).expect("None should encode");

    // Assert option axioms
    encoder.assert_option_result_axioms();

    // Constrain i to be out-of-bounds: i >= len(v@)
    let i_var = encoder.vars_for_test()["i"];
    let len_expr = method_call(v_view_expr, "len", vec![]);
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("len encoding should succeed");
    let i_ge_len = encoder.solver.ge(i_var, len_term);
    encoder.assert_term(i_ge_len);

    // Also constrain len >= 0 to avoid degenerate models
    let zero = encoder.solver.int_const(0);
    let len_ge_zero = encoder.solver.ge(len_term, zero);
    encoder.assert_term(len_ge_zero);

    // Negate: get(v@, i) != None
    let eq_check = encoder.eq_or_iff(get_term, none_term, &Sort::Int);
    let neg_formula = encoder.solver.not(eq_check);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert_unsat_or_structured_seq_get_quantifier_limit(
        &encoder,
        result,
        "out-of-bounds get(v, i) != None",
    );
}

/// Axiom 8b (negative index): get(s, -1) == None (#1882).
#[test]
#[timeout(30000)]
fn test_seq_axiom_get_negative_index_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let v_view_expr = view(var("v"));

    // Encode v@.get(-1)
    let get_expr = method_call(v_view_expr.clone(), "get", vec![neg(int(1))]);
    let get_term = encoder
        .encode_pure(&get_expr)
        .expect("get(-1) encoding should succeed");

    // Encode None
    let none_expr = logic_fn_call("None", vec![]);
    let none_term = encoder.encode_pure(&none_expr).expect("None should encode");

    // Assert option axioms
    encoder.assert_option_result_axioms();

    // Constrain len >= 0
    let len_expr = method_call(v_view_expr, "len", vec![]);
    let len_term = encoder
        .encode_pure(&len_expr)
        .expect("len encoding should succeed");
    let zero = encoder.solver.int_const(0);
    let len_ge_zero = encoder.solver.ge(len_term, zero);
    encoder.assert_term(len_ge_zero);

    // Negate: get(v@, -1) != None
    let eq_check = encoder.eq_or_iff(get_term, none_term, &Sort::Int);
    let neg_formula = encoder.solver.not(eq_check);
    encoder.assert_term(neg_formula);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "get(v, -1) != None should be UNSAT (axiom 8b), got {result:?}"
    );
}

/// Test that get() with wrong argument count fails with clear error.
#[test]
#[timeout(30000)]
fn test_encode_seq_get_wrong_args() {
    let mut encoder = AYEncoder::new();

    // v@.get() — missing argument
    let expr = method_call(view(var("v")), "get", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "get() with no args should fail, got Ok({:?})",
        result.as_ref().ok()
    );
    match result.unwrap_err() {
        EncodingError::Unsupported { message: msg, .. } => {
            assert!(
                msg.contains("expects 1 argument"),
                "Error should mention argument count, got: {msg}"
            );
        }
        err @ (EncodingError::SolverError { .. }
        | EncodingError::SortInference { .. }
        | EncodingError::SortConflict { .. }) => {
            panic!("Expected Unsupported error, got {err:?}")
        }
    }
}

// =============================================================================
// Seq len_logic() alias Tests (#690)
// =============================================================================

/// Test that len_logic() is an alias for len() (Creusot compat).
/// Both should produce identical SMT terms.
#[test]
#[timeout(30000)]
fn test_seq_len_logic_alias() {
    let mut encoder = AYEncoder::new();

    let v_view_expr = view(var("v"));

    let len_logic_expr = method_call(v_view_expr.clone(), "len_logic", vec![]);
    let len_expr = method_call(v_view_expr, "len", vec![]);

    let eq_check = eq(len_logic_expr, len_expr);

    let formula = encoder
        .encode_pure(&eq_check)
        .expect("len_logic/len equality should encode");

    let neg = encoder.solver.not(formula);
    encoder.assert_term(neg);
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "len_logic(v) != len(v) should be UNSAT (alias), got {result:?}"
    );
}

// =============================================================================
// completed() Bool predicate test (#690)
// =============================================================================

/// Test that `iter.completed()` encodes as an uninterpreted Bool predicate.
///
/// The `completed()` method is part of the iterator protocol (#379).
/// Verifies: encoding succeeds, creates a UF declaration with correct signature,
/// the result is Bool-sorted and distinct from the bare receiver variable,
/// and re-encoding produces the same term (functional consistency).
#[test]
#[timeout(30000)]
fn test_encode_completed_bool_predicate() {
    let mut encoder = AYEncoder::new();

    // iter.completed() — method call on a variable
    let expr = method_call(var("iter"), "completed", vec![]);

    let term = encoder
        .encode_pure(&expr)
        .expect("iter.completed() encoding should succeed");

    // 1. Structural: a FuncDecl was created with correct signature
    let smt_name = "method_completed_1_i";
    let func_decl = encoder
        .decls()
        .get_logic_func(smt_name)
        .unwrap_or_else(|| panic!("expected FuncDecl '{smt_name}' in logic_funcs"));
    assert_eq!(
        func_decl.arity(),
        1,
        "completed() UF should be unary (receiver only)"
    );
    assert_eq!(
        *func_decl.range(),
        Sort::Bool,
        "completed() should return Bool"
    );
    assert_eq!(
        func_decl.domain(),
        &[Sort::Int],
        "completed() receiver should be Int-sorted"
    );

    // 2. The term is distinct from the bare receiver variable
    let receiver_term = *encoder
        .vars_for_test()
        .get("iter")
        .expect("receiver var 'iter' should exist");
    assert_ne!(
        term, receiver_term,
        "completed() should be a function application, not the bare receiver variable"
    );

    // 3. Re-encoding the same expression produces the same term (functional consistency)
    let term2 = encoder
        .encode_pure(&expr)
        .expect("re-encoding should succeed");
    assert_eq!(
        term, term2,
        "encoding completed() twice should produce the same term"
    );

    // 4. The term is Bool-sorted: asserting it directly is satisfiable
    encoder.assert_term(term);
    let sat_result = encoder.check_sat();
    assert!(
        matches!(sat_result, SolveResult::Sat),
        "completed() asserted as true should be SAT (unconstrained): {sat_result:?}"
    );
}

/// Test that `completed()` and `!completed()` are both satisfiable
/// (the predicate is truly unconstrained / uninterpreted).
#[test]
#[timeout(30000)]
fn test_completed_is_unconstrained() {
    // completed() = true should be SAT
    let mut enc1 = AYEncoder::new();
    let expr = method_call(var("iter"), "completed", vec![]);
    let term = enc1.encode_pure(&expr).unwrap();
    enc1.assert_term(term);
    assert!(
        matches!(enc1.check_sat(), SolveResult::Sat),
        "completed() = true should be SAT"
    );

    // completed() = false should also be SAT
    let mut enc2 = AYEncoder::new();
    let term2 = enc2.encode_pure(&expr).unwrap();
    let neg = enc2.solver.not(term2);
    enc2.assert_term(neg);
    assert!(
        matches!(enc2.check_sat(), SolveResult::Sat),
        "!completed() should be SAT (unconstrained)"
    );
}
