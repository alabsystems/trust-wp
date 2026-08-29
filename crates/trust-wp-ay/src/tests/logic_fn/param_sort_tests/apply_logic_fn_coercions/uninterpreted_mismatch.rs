// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// apply_logic_fn coerces Uninterpreted-vs-Uninterpreted mismatches.
///
/// Previously, the coercion only fired for Datatype and Int↔Uninterpreted
/// cases. This left mismatches like List-vs-Seq or FMap-vs-Seq unhandled,
/// causing ay panics. The widened coercion handles all sort mismatches.
/// (#2155)
#[test]
#[timeout(30000)]
fn test_apply_logic_fn_coerces_uninterpreted_vs_uninterpreted() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a function f: Seq -> Int
    let seq_sort = Sort::seq(Sort::Int);
    let func_decl =
        encoder
            .solver
            .declare_fun("logic_f", std::slice::from_ref(&seq_sort), Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("logic_f".to_string(), func_decl);

    // Create a term with a different Uninterpreted sort ("List")
    let list_sort = Sort::Uninterpreted("List".to_string());
    let list_term = encoder.solver.declare_const("x_list", list_sort.clone());
    assert_eq!(encoder.solver.get_sort(list_term), list_sort);

    // apply_logic_fn should coerce List → Seq via fresh const, not panic
    let result = encoder.apply_logic_fn("f", &[list_term], None, None);
    assert!(
        result.is_ok(),
        "apply_logic_fn should coerce Uninterpreted(List) → Seq without panic: {result:?}"
    );
}

/// apply_logic_fn coerces Bool-vs-Uninterpreted mismatches.
///
/// Bool arguments passed to functions expecting Uninterpreted sorts
/// (e.g., Seq) previously fell through the coercion gate. (#2155)
#[test]
#[timeout(30000)]
fn test_apply_logic_fn_coerces_bool_vs_uninterpreted() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a function g: Seq -> Bool
    let seq_sort = Sort::seq(Sort::Int);
    let func_decl = encoder
        .solver
        .declare_fun("logic_g", &[seq_sort], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("logic_g".to_string(), func_decl);

    // Create a Bool term
    let bool_term = encoder.solver.bool_const(true);

    // apply_logic_fn should coerce Bool → Seq, not panic
    let result = encoder.apply_logic_fn("g", &[bool_term], None, None);
    assert!(
        result.is_ok(),
        "apply_logic_fn should coerce Bool → Seq without panic: {result:?}"
    );
}
