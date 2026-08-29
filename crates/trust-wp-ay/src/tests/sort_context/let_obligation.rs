// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// MutRefVarNames tests (#P1-325: zero direct coverage)
// =============================================================================

mod mut_ref_var_names_tests {
    use ntest::timeout;

    use crate::encoder::sort_context::MutRefVarNames;

    #[test]
    #[timeout(30000)]
    fn test_all_names_from_base() {
        let names = MutRefVarNames::new("v");
        assert_eq!(names.current, "v_current");
        assert_eq!(names.final_val, "v_final");
    }

    #[test]
    #[timeout(30000)]
    fn test_names_are_unique() {
        let names = MutRefVarNames::new("x");
        let all = [&names.current, &names.final_val];
        let unique: std::collections::HashSet<_> = all.iter().collect();
        assert_eq!(
            unique.len(),
            2,
            "Both MutRefVarNames should be distinct for any base"
        );
    }
}

// =============================================================================
// collect_bool_hints: LetAssume / LetObligation coverage (#P1-325)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_collect_bool_hints_through_let_assume_assumption() {
    // LetAssume { assumption: !x, body: y } => x is Bool (inside assumption)
    let expr = let_assume(not(var("x")), var("y"));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside LetAssume assumption should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_hints_through_let_assume_body() {
    // LetAssume { assumption: var("a"), body: !x } => x is Bool (inside body)
    let expr = let_assume(var("a"), not(var("x")));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside LetAssume body should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_hints_through_let_obligation_obligation() {
    // LetObligation { obligation: x && y, body: z } => x, y are Bool
    let expr = let_obligation(and(var("x"), var("y")), var("z"));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside LetObligation obligation should be found"
    );
    assert!(
        names.contains("y"),
        "Bool var inside LetObligation obligation should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_bool_hints_through_let_obligation_body() {
    // LetObligation { obligation: var("a"), body: x ==> y } => x, y are Bool
    let expr = let_obligation(var("a"), implies(var("x"), var("y")));
    let mut names = HashSet::new();
    collect_bool_var_names(&expr, &mut names);
    assert!(
        names.contains("x"),
        "Bool var inside LetObligation body should be found"
    );
    assert!(
        names.contains("y"),
        "Bool var inside LetObligation body should be found"
    );
}

// =============================================================================
// infer_expr_sort: LetAssume / LetObligation sort inference (#P1-325)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_let_assume_with_bool_body() {
    // LetAssume { assumption: var("a"), body: x > 0 } => sort is Bool (from body)
    let expr = let_assume(var("a"), gt(var("x"), int(0)));
    assert_eq!(infer_expr_sort(&expr), Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_let_assume_with_int_body() {
    // LetAssume { assumption: var("a"), body: x + 1 } => sort is Int (from body)
    let expr = let_assume(var("a"), add(var("x"), int(1)));
    assert_eq!(infer_expr_sort(&expr), Sort::Int);
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_let_obligation_with_bool_body() {
    // LetObligation { obligation: var("a"), body: x > 0 } => sort is Bool
    let expr = let_obligation(var("a"), gt(var("x"), int(0)));
    assert_eq!(infer_expr_sort(&expr), Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_infer_expr_sort_let_obligation_with_int_body() {
    // LetObligation { obligation: var("a"), body: x + 1 } => sort is Int
    let expr = let_obligation(var("a"), add(var("x"), int(1)));
    assert_eq!(infer_expr_sort(&expr), Sort::Int);
}

// =============================================================================
// collect_seq_view_names: LetAssume / LetObligation coverage (#P1-325)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_let_assume() {
    // LetAssume { assumption: v@.len() > 0, body: true }
    let len_call = method_call(view(var("v")), "len", vec![]);
    let expr = let_assume(gt(len_call, int(0)), bool_expr(true));
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "Seq method in LetAssume assumption should be found"
    );
}

#[test]
#[timeout(30000)]
fn test_collect_seq_view_names_through_let_obligation() {
    // LetObligation { obligation: var("a"), body: v@.len() }
    let len_call = method_call(view(var("v")), "len", vec![]);
    let expr = let_obligation(var("a"), len_call);
    let mut names = HashSet::new();
    collect_seq_view_names(&expr, &mut names);
    assert!(
        names.contains("v_view"),
        "Seq method in LetObligation body should be found"
    );
}
