// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- assert_by_value_alias_constraints (#970) ---

/// When an encoder has `f` and `f_current`, the alias constraint
/// `f_current = f` should be asserted. Verifying: if we assert `f = 5`
/// and then the alias constraint, querying `f_current != 5` should be UNSAT.
#[test]
#[timeout(30000)]
fn alias_constraint_equates_current_with_base() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let f = encoder
        .get_or_declare_var("f", Sort::Int)
        .expect("f should declare");
    let f_current = encoder
        .get_or_declare_var("f_current", Sort::Int)
        .expect("f_current should declare");
    // Assert f = 5
    let five = encoder.solver_mut().int_const(5);
    let eq = encoder.solver_mut().eq(f, five);
    encoder.assert_term(eq);
    // Assert alias constraints
    assert_by_value_alias_constraints(&mut encoder).expect("alias constraints should succeed");
    // Now f_current should also equal 5 — assert f_current != 5 and check UNSAT
    let five2 = encoder.solver_mut().int_const(5);
    let eq2 = encoder.solver_mut().eq(f_current, five2);
    let neq = encoder.solver_mut().not(eq2);
    encoder.assert_term(neq);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "f_current should equal f after alias constraint"
    );
}

/// When no `_current` variables exist, alias constraints should be a no-op.
#[test]
#[timeout(30000)]
fn alias_constraint_noop_without_current_vars() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let _f = encoder
        .get_or_declare_var("f", Sort::Int)
        .expect("f should declare");
    assert_by_value_alias_constraints(&mut encoder)
        .expect("alias constraints should succeed (noop)");
    assert_ne!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "empty alias constraints should not make context UNSAT"
    );
}

/// `f_final_current` should be equated with `f_final` (not with `f_final`'s
/// prophecy chain). This tests the nested current-suffix pattern.
#[test]
#[timeout(30000)]
fn alias_constraint_equates_final_current_with_final() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let f_final = encoder
        .get_or_declare_var("f_final", Sort::Int)
        .expect("f_final should declare");
    let f_final_current = encoder
        .get_or_declare_var("f_final_current", Sort::Int)
        .expect("f_final_current should declare");
    // Assert f_final = 10
    let ten = encoder.solver_mut().int_const(10);
    let eq = encoder.solver_mut().eq(f_final, ten);
    encoder.assert_term(eq);
    assert_by_value_alias_constraints(&mut encoder).expect("alias constraints should succeed");
    // f_final_current should now equal 10
    let ten2 = encoder.solver_mut().int_const(10);
    let eq2 = encoder.solver_mut().eq(f_final_current, ten2);
    let neq = encoder.solver_mut().not(eq2);
    encoder.assert_term(neq);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "f_final_current should equal f_final after alias constraint"
    );
}

/// `f_current_current` IS aliased to `f_current` for Box<T> deref erasure (#1302).
///
/// Contracts referencing Box parameters produce extra Deref layers that the
/// encoder maps to `_current_current`. The body treats Box deref as a no-op,
/// producing only `_current`. Chaining `x_current_current = x_current`
/// connects these. This test verifies the chain works transitively:
/// f_current_current = f_current = 7, so f_current_current != 99 is UNSAT.
#[test]
#[timeout(30000)]
fn alias_constraint_chains_current_current_suffix() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let f_current = encoder
        .get_or_declare_var("f_current", Sort::Int)
        .expect("f_current should declare");
    let f_current_current = encoder
        .get_or_declare_var("f_current_current", Sort::Int)
        .expect("f_current_current should declare");
    let _f = encoder
        .get_or_declare_var("f", Sort::Int)
        .expect("f should declare");
    // Assert f_current = 7
    let seven = encoder.solver_mut().int_const(7);
    let eq = encoder.solver_mut().eq(f_current, seven);
    encoder.assert_term(eq);
    // Assert alias constraints — should equate f_current = f AND
    // f_current_current = f_current (for Box deref erasure).
    assert_by_value_alias_constraints(&mut encoder).expect("alias constraints should succeed");
    // f_current_current should now equal 7 (via f_current_current = f_current = 7)
    let ninety_nine = encoder.solver_mut().int_const(99);
    let eq2 = encoder.solver_mut().eq(f_current_current, ninety_nine);
    encoder.assert_term(eq2);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "f_current_current should be constrained to 7 (aliased to f_current)"
    );
}

/// When `f_current_current` exists and `f` exists but `f_current` does NOT,
/// the intermediate chain should be created: f_current_current = f_current = f.
/// This is the Box deref erasure pattern where the contract's double deref
/// produces `f_current_current` and the body only creates `f`. (#1302)
#[test]
#[timeout(30000)]
fn alias_constraint_creates_intermediate_chain() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // Only declare f_current_current and f — f_current is missing.
    let f_current_current = encoder
        .get_or_declare_var("f_current_current", Sort::Int)
        .expect("f_current_current should declare");
    let f = encoder
        .get_or_declare_var("f", Sort::Int)
        .expect("f should declare");
    // Assert f = 42
    let forty_two = encoder.solver_mut().int_const(42);
    let eq = encoder.solver_mut().eq(f, forty_two);
    encoder.assert_term(eq);
    // Assert alias constraints — should create f_current and chain:
    // f_current_current = f_current = f
    assert_by_value_alias_constraints(&mut encoder).expect("alias constraints should succeed");
    // f_current_current should now equal 42 (via the chain)
    let ninety_nine = encoder.solver_mut().int_const(99);
    let eq2 = encoder.solver_mut().eq(f_current_current, ninety_nine);
    encoder.assert_term(eq2);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "f_current_current should be constrained to 42 via intermediate chain"
    );
}

/// `_current` aliases for whole-borrow carriers must be skipped in the
/// by-value alias pass. `x_current` is the referent of `*x`, not an alias for
/// the whole `&mut` carrier `x`. Regresses compat `bug/1562`.
#[test]
#[timeout(30000)]
fn alias_constraint_skips_mutref_carriers() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let whole_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    encoder
        .get_or_declare_var("x", whole_sort)
        .expect("x should declare as a whole mutref carrier");
    encoder
        .get_or_declare_var("x_current", Sort::Int)
        .expect("x_current should declare as the referent sort");

    let result = assert_by_value_alias_constraints(&mut encoder);
    assert!(
        result.is_ok(),
        "by-value alias constraints must skip mutref carriers instead of forcing x_current = x: {result:?}"
    );
}
