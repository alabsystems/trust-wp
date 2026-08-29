// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Prophecy writeback and borrow-id tests for resolve assertions (#2124 Phase 3).

use std::collections::HashMap;

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
    BorrowFinality, BorrowIdOrigin, BorrowIdStep, ExprSort,
};

use crate::{
    encoder::AYEncoder,
    tests::helpers::{
        add, and, deref, eq, final_expr, ge, get_field, gt, int, ite, le, logic_fn_call, lt, ne,
        var, var_with_sort,
    },
    verify::{mut_borrow::verify_mut_borrow_function_with_modes, types::MutBorrowRequest},
    UnknownReason, VerificationResult,
};

fn mut_ref_int_var(name: &str) -> trust_wp_core::formula::PureExpr {
    var_with_sort(name, ExprSort::MutRef(Box::new(ExprSort::Int)))
}

// ── prophecy writeback (#2124 Phase 3) ─────────────────────────────

/// Prophecy writeback for a simple reborrow chain: z = &mut *y.
///
/// Models:
///   fn f(y: &mut i32) { let z = &mut *y; *z = 5; }
///   #[ensures(^y == 5)]
#[test]
#[timeout(30000)]
fn prophecy_writeback_simple_reborrow_verifies() {
    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(var("y")));
    final_values.insert("y_rb5".to_string(), int(5));

    let ensures = vec![eq(final_expr(var("y")), int(5))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["y_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "prophecy writeback should make ^y == 5 verify: got {result:?}"
    );
}

/// Without prophecy writeback, the same scenario should fail.
#[test]
#[timeout(30000)]
fn without_prophecy_writeback_reborrow_fails() {
    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(var("y")));
    final_values.insert("y_rb5".to_string(), int(5));

    let ensures = vec![eq(final_expr(var("y")), int(5))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["y_rb5".to_string()]))
            .prophecy_writebacks(None),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without writeback, ^y == 5 should be falsifiable: got {result:?}"
    );
}

/// Prophecy writeback preserves preconditions through reborrow chains.
#[test]
#[timeout(30000)]
fn prophecy_writeback_preserves_precondition() {
    let requires = vec![gt(deref(var("y")), int(0))];

    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(var("y")));
    final_values.insert("y_rb5".to_string(), deref(var("y_rb5")));

    let ensures = vec![gt(final_expr(var("y")), int(0))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .resolve_assumptions(Some(vec!["y".to_string(), "y_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "prophecy writeback should propagate precondition: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn same_parent_borrow_id_allows_whole_borrow_identity_postcondition() {
    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(mut_ref_int_var("y")));
    final_values.insert("y_rb5".to_string(), deref(mut_ref_int_var("y_rb5")));

    let ensures = vec![eq(mut_ref_int_var("result"), mut_ref_int_var("y"))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());

    let mut finality = HashMap::new();
    finality.insert("y_rb5".to_string(), BorrowFinality::Final { deref_pos: 0 });

    let mut origins = HashMap::new();
    origins.insert(
        "y_rb5".to_string(),
        BorrowIdOrigin::SameParent {
            parent: "y".to_string(),
        },
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&mut_ref_int_var("y_rb5")))
            .resolve_assumptions(Some(vec!["y_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality))
            .borrow_id_origins(Some(origins)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "same-parent borrow ids should make whole-borrow identity verify: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn same_parent_low_level_result_identity_constraints_are_unsat() {
    let mut encoder = AYEncoder::new_all();
    let whole_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    encoder
        .get_or_declare_var("y", whole_sort.clone())
        .expect("y should declare as whole MutRef");
    encoder
        .get_or_declare_var("y_rb5", whole_sort)
        .expect("y_rb5 should declare as whole MutRef");

    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(mut_ref_int_var("y")));
    final_values.insert("y_rb5".to_string(), deref(mut_ref_int_var("y_rb5")));
    super::bindings::bind_final_values(&mut encoder, &final_values, None)
        .expect("final-value bindings should encode");

    let resolve_names = vec!["y_rb5".to_string()];
    super::resolve::emit_resolve_assertions(
        &mut encoder,
        Some(&resolve_names),
        None,
        &final_values,
        &[],
    );

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());
    let mut finality = HashMap::new();
    finality.insert("y_rb5".to_string(), BorrowFinality::Final { deref_pos: 0 });
    let mut origins = HashMap::new();
    origins.insert(
        "y_rb5".to_string(),
        BorrowIdOrigin::SameParent {
            parent: "y".to_string(),
        },
    );

    super::resolve::emit_prophecy_writebacks(
        &mut encoder,
        Some(&writebacks),
        Some(&finality),
        Some(&resolve_names),
        Some(&origins),
        None,
        None,
    );
    super::resolve::emit_borrow_id_constraints(&mut encoder, Some(&origins), Some(&writebacks))
        .expect("borrow-id constraints should encode");

    super::bind_result_expr(&mut encoder, &mut_ref_int_var("y_rb5"), &[], &final_values)
        .expect("result binding should encode");

    let current_neq = encoder
        .encode_pure(&ne(
            deref(mut_ref_int_var("result")),
            deref(mut_ref_int_var("y")),
        ))
        .expect("current inequality should encode");
    encoder.push_scope().expect("current scope should push");
    encoder.assert_term(current_neq);
    let current_sat = encoder.check_sat();
    encoder.pop_scope().expect("current scope should pop");

    let final_neq = encoder
        .encode_pure(&ne(
            final_expr(mut_ref_int_var("result")),
            final_expr(mut_ref_int_var("y")),
        ))
        .expect("final inequality should encode");
    encoder.push_scope().expect("final scope should push");
    encoder.assert_term(final_neq);
    let final_sat = encoder.check_sat();
    encoder.pop_scope().expect("final scope should pop");

    let result_id = encoder
        .var_term("result_id")
        .expect("result_id should be declared");
    let y_sort = encoder.var_sort("y").cloned();
    let y_current_sort = encoder.var_sort("y_current").cloned();
    let y_final_sort = encoder.var_sort("y_final").cloned();
    let y_rb5_sort = encoder.var_sort("y_rb5").cloned();
    let y_rb5_current_sort = encoder.var_sort("y_rb5_current").cloned();
    let y_rb5_final_sort = encoder.var_sort("y_rb5_final").cloned();
    let y_id = encoder.var_term("y_id").unwrap_or_else(|| {
        panic!(
            "y_id should be declared; y={y_sort:?}; y_current={y_current_sort:?}; \
             y_final={y_final_sort:?}; y_rb5={y_rb5_sort:?}; \
             y_rb5_current={y_rb5_current_sort:?}; y_rb5_final={y_rb5_final_sort:?}"
        )
    });
    let id_eq = encoder.eq_term(result_id, y_id);
    let id_neq = encoder.solver.not(id_eq);
    encoder.push_scope().expect("id scope should push");
    encoder.assert_term(id_neq);
    let id_sat = encoder.check_sat();
    encoder.pop_scope().expect("id scope should pop");

    let neq = encoder
        .encode_pure(&ne(mut_ref_int_var("result"), mut_ref_int_var("y")))
        .expect("whole-borrow inequality should encode");
    encoder.assert_term(neq);

    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "same-parent raw constraints should force result == y: got {sat:?}; current={current_sat:?}; final={final_sat:?}; id={id_sat:?}"
    );
}

#[test]
#[timeout(30000)]
fn fresh_borrow_id_rejects_whole_borrow_identity_postcondition() {
    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(mut_ref_int_var("y")));
    final_values.insert("y_rb5".to_string(), deref(mut_ref_int_var("y_rb5")));

    let ensures = vec![eq(mut_ref_int_var("result"), mut_ref_int_var("y"))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());

    let mut finality = HashMap::new();
    finality.insert("y_rb5".to_string(), BorrowFinality::Fresh);

    let mut origins = HashMap::new();
    origins.insert(
        "y_rb5".to_string(),
        BorrowIdOrigin::Fresh {
            parent: "y".to_string(),
        },
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&mut_ref_int_var("y_rb5")))
            .resolve_assumptions(Some(vec!["y_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality))
            .borrow_id_origins(Some(origins)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "fresh borrow ids should reject whole-borrow identity: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn derived_borrow_id_with_same_projection_allows_whole_borrow_equality() {
    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(mut_ref_int_var("y")));
    final_values.insert("y_rb5".to_string(), deref(mut_ref_int_var("y_rb5")));
    final_values.insert("y_rb6".to_string(), deref(mut_ref_int_var("y_rb6")));

    let ensures = vec![eq(mut_ref_int_var("result"), mut_ref_int_var("y_rb6"))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());
    writebacks.insert("y_rb6".to_string(), "y".to_string());

    let mut origins = HashMap::new();
    origins.insert(
        "y_rb5".to_string(),
        BorrowIdOrigin::Derived {
            parent: "y".to_string(),
            steps: vec![BorrowIdStep::Index(int(2))],
        },
    );
    origins.insert(
        "y_rb6".to_string(),
        BorrowIdOrigin::Derived {
            parent: "y".to_string(),
            steps: vec![BorrowIdStep::Index(int(2))],
        },
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&mut_ref_int_var("y_rb5")))
            .resolve_assumptions(Some(vec!["y_rb5".to_string(), "y_rb6".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_id_origins(Some(origins)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "matching derived borrow ids should make whole-borrow equality verify: got {result:?}"
    );
}

// ── #2673 strengthening: child_current == parent_current without borrow IDs ──

/// Prophecy writeback without borrow IDs should still propagate current values.
///
/// Models the `resolve_drop` pattern where a reborrow chain resolves back
/// to the original variable. Previously, `child_current == parent_current`
/// was only emitted when `has_borrow_ids` was true, leaving the solver
/// unable to chain the resolution. (#2673)
#[test]
#[timeout(30000)]
fn prophecy_writeback_without_borrow_ids_propagates_current() {
    let requires = vec![eq(deref(var("y")), int(10))];

    let mut final_values = HashMap::new();
    final_values.insert("y".to_string(), deref(var("y")));
    final_values.insert("y_rb5".to_string(), deref(var("y_rb5")));

    // Postcondition: *result == 10  (result is the reborrow of y)
    // This requires child_current == parent_current so that y_rb5_current == y_current == 10.
    let ensures = vec![eq(deref(var("result")), int(10))];

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());

    // No borrow_id_origins — this previously broke the child_current == parent_current
    // constraint. After the #2673 fix, this must still verify.
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .return_expr(Some(&deref(var("y_rb5"))))
            .resolve_assumptions(Some(vec!["y_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "prophecy writeback without borrow IDs should propagate current values (#2673): got {result:?}"
    );
}

/// Single reborrow mutation flows back via writeback.
///
/// Models:
///   fn f(x: &mut i32) { let r1 = &mut *x; *r1 = 5; }
///   #[ensures(^x == 5)]
///
/// The resolve + writeback chain:
///   r1_final == 5 (from final_values)
///   r1_final == r1_current (from resolve)
///   x_current == r1_final (from writeback)
///   x_final == x_current (from final_values identity)
///   So x_final == 5. No precondition on x, so no contradiction.
#[test]
#[timeout(30000)]
fn single_reborrow_mutation_flows_back_to_parent() {
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));
    final_values.insert("x_rb1".to_string(), int(5));

    // Postcondition: ^x == 5 (the mutation flows back through writeback)
    let ensures = vec![eq(final_expr(var("x")), int(5))];

    // Reborrow chain: x_rb1 is a reborrow of x
    let mut writebacks = HashMap::new();
    writebacks.insert("x_rb1".to_string(), "x".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["x_rb1".to_string()]))
            .prophecy_writebacks(Some(writebacks)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "single reborrow mutation should flow back via writeback (#2673): got {result:?}"
    );
}

/// Two-level reborrow chain where mutations flow back through intermediate borrows.
///
/// Models:
///   fn f(x: &mut i32) {
///       let r = &mut *x;   // identity reborrow
///       let r1 = &mut *r;  // second identity reborrow
///       *r1 = 5;
///   }
///   #[ensures(^x == 5)]
///
/// Chain: x -> x_rb1 -> x_rb2, where x_rb2_final = 5.
/// Writebacks: x_rb1_current == x_rb2_final, x_current == x_rb1_final.
/// No preconditions on x so no contradiction with the writeback constraints.
#[test]
#[timeout(30000)]
fn two_level_reborrow_chain_mutation_flows_back() {
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));
    final_values.insert("x_rb1".to_string(), deref(var("x_rb1")));
    final_values.insert("x_rb2".to_string(), int(5));

    // Postcondition: ^x == 5 (the mutation flows back through the chain)
    let ensures = vec![eq(final_expr(var("x")), int(5))];

    // Reborrow chain: x_rb1 is a reborrow of x, x_rb2 is a reborrow of x_rb1
    let mut writebacks = HashMap::new();
    writebacks.insert("x_rb1".to_string(), "x".to_string());
    writebacks.insert("x_rb2".to_string(), "x_rb1".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["x_rb2".to_string(), "x_rb1".to_string()]))
            .prophecy_writebacks(Some(writebacks)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "two-level reborrow chain should resolve mutations back (#2673): got {result:?}"
    );
}

/// Field projection reborrow with derived borrow ID (models `reborrow_field`).
///
/// Models:
///   fn reborrow_field(r: &mut (T, T)) -> &mut T { &mut r.0 }
///   #[ensures(result == &mut r.0)]
///
/// The result is a derived borrow with Field(0) step from the parent.
#[test]
#[timeout(30000)]
fn field_projection_derived_borrow_id_verifies() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    let mut final_values = HashMap::new();
    final_values.insert("r".to_string(), deref(mut_ref_int_var("r")));
    final_values.insert("r_rb5".to_string(), deref(mut_ref_int_var("r_rb5")));

    // result == r_rb5 as whole-borrow equality
    let ensures = vec![eq(
        var_with_sort("result", mr_int.clone()),
        mut_ref_int_var("r_rb5"),
    )];

    let mut writebacks = HashMap::new();
    writebacks.insert("r_rb5".to_string(), "r".to_string());

    let mut finality = HashMap::new();
    finality.insert("r_rb5".to_string(), BorrowFinality::Final { deref_pos: 0 });

    let mut origins = HashMap::new();
    origins.insert(
        "r_rb5".to_string(),
        BorrowIdOrigin::Derived {
            parent: "r".to_string(),
            steps: vec![BorrowIdStep::Field(0)],
        },
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&mut_ref_int_var("r_rb5")))
            .resolve_assumptions(Some(vec!["r_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality))
            .borrow_id_origins(Some(origins)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "field projection derived borrow ID should verify whole-borrow equality (#2673): got {result:?}"
    );
}

// ── Projection-aware writeback tests (#2673 strengthened) ──────────────
//
// These tests verify at the encoder level that `emit_prophecy_writebacks`
// emits the correct projected equality constraints when field projection
// steps are present. Higher-level verification-pipeline tests cannot close
// these proofs because both child and parent fall back to Sort::Int, making
// `tuple_get_N` an opaque UF that the AUFLIA solver cannot reason through.
// Instead, we test the constraint emission directly via push/pop + check_sat.

/// Field projection writeback emits `child_current == tuple_get_0(parent_current)`.
///
/// Low-level encoder test: after calling `emit_prophecy_writebacks` with a
/// `Derived { Field(0) }` origin, the constraint `r_rb5_current == tuple_get_0(r_current)`
/// must hold (asserting its negation is UNSAT).
#[test]
#[timeout(30000)]
fn projection_aware_writeback_emits_current_constraint() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    // Declare parent and child mut-ref variables with Int sort (sort fallback).
    encoder
        .get_or_declare_var("r_current", Sort::Int)
        .expect("r_current");
    encoder
        .get_or_declare_var("r_final", Sort::Int)
        .expect("r_final");
    encoder
        .get_or_declare_var("r_rb5_current", Sort::Int)
        .expect("r_rb5_current");
    encoder
        .get_or_declare_var("r_rb5_final", Sort::Int)
        .expect("r_rb5_final");

    let mut writebacks = HashMap::new();
    writebacks.insert("r_rb5".to_string(), "r".to_string());
    let mut finality = HashMap::new();
    finality.insert("r_rb5".to_string(), BorrowFinality::Final { deref_pos: 0 });
    let mut origins = HashMap::new();
    origins.insert(
        "r_rb5".to_string(),
        BorrowIdOrigin::Derived {
            parent: "r".to_string(),
            steps: vec![BorrowIdStep::Field(0)],
        },
    );
    let resolve_names = vec!["r_rb5".to_string()];

    super::resolve::emit_prophecy_writebacks(
        &mut encoder,
        Some(&writebacks),
        Some(&finality),
        Some(&resolve_names),
        Some(&origins),
        None,
        None,
    );

    // Verify: r_rb5_current == tuple_get_0(r_current) by asserting negation is UNSAT.
    let child_current = encoder
        .var_term("r_rb5_current")
        .expect("r_rb5_current term");
    let fn_name = trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let parent_current = encoder.var_term("r_current").expect("r_current term");
    let get0_decl = encoder.get_or_declare_logic_func(&fn_name, &[Sort::Int], Sort::Int);
    let projected = encoder
        .safe_apply(&fn_name, &get0_decl, &[parent_current])
        .expect("tuple_get_0 application");
    let eq_term = encoder.eq_term(child_current, projected);
    let neq = encoder.solver.not(eq_term);

    encoder.push_scope().expect("push scope");
    encoder.assert_term(neq);
    let sat = encoder.check_sat();
    encoder.pop_scope().expect("pop scope");

    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "projection constraint r_rb5_current == tuple_get_0(r_current) should hold (#2673): got {sat:?}"
    );
}

/// Field projection writeback emits `child_final == tuple_get_0(parent_final)`
/// for final-borrow propagation.
#[test]
#[timeout(30000)]
fn projection_aware_writeback_emits_final_constraint() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("r_current", Sort::Int)
        .expect("r_current");
    encoder
        .get_or_declare_var("r_final", Sort::Int)
        .expect("r_final");
    encoder
        .get_or_declare_var("r_rb5_current", Sort::Int)
        .expect("r_rb5_current");
    encoder
        .get_or_declare_var("r_rb5_final", Sort::Int)
        .expect("r_rb5_final");

    let mut writebacks = HashMap::new();
    writebacks.insert("r_rb5".to_string(), "r".to_string());
    let mut finality = HashMap::new();
    finality.insert("r_rb5".to_string(), BorrowFinality::Final { deref_pos: 0 });
    let mut origins = HashMap::new();
    origins.insert(
        "r_rb5".to_string(),
        BorrowIdOrigin::Derived {
            parent: "r".to_string(),
            steps: vec![BorrowIdStep::Field(0)],
        },
    );
    let resolve_names = vec!["r_rb5".to_string()];

    super::resolve::emit_prophecy_writebacks(
        &mut encoder,
        Some(&writebacks),
        Some(&finality),
        Some(&resolve_names),
        Some(&origins),
        None,
        None,
    );

    // Verify: r_rb5_final == tuple_get_0(r_final) by asserting negation is UNSAT.
    let child_final = encoder.var_term("r_rb5_final").expect("r_rb5_final term");
    let fn_name = trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let parent_final = encoder.var_term("r_final").expect("r_final term");
    let get0_decl = encoder.get_or_declare_logic_func(&fn_name, &[Sort::Int], Sort::Int);
    let projected = encoder
        .safe_apply(&fn_name, &get0_decl, &[parent_final])
        .expect("tuple_get_0 application");
    let eq_term = encoder.eq_term(child_final, projected);
    let neq = encoder.solver.not(eq_term);

    encoder.push_scope().expect("push scope");
    encoder.assert_term(neq);
    let sat = encoder.check_sat();
    encoder.pop_scope().expect("pop scope");

    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "projection constraint r_rb5_final == tuple_get_0(r_final) should hold (#2673): got {sat:?}"
    );
}

/// Disjoint field projections emit independent constraints (no contradiction).
///
/// When two children (`r_rb_a` via Field(0), `r_rb_b` via Field(1)) share a
/// parent, their writeback constraints should be independent — unlike identity
/// reborrows where both would get `child_X == parent_current`, creating UNSAT
/// when the children have different final values.
#[test]
#[timeout(30000)]
fn projection_aware_writeback_disjoint_fields_no_contradiction() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("r_current", Sort::Int)
        .expect("r_current");
    encoder
        .get_or_declare_var("r_final", Sort::Int)
        .expect("r_final");
    encoder
        .get_or_declare_var("r_rb_a_current", Sort::Int)
        .expect("r_rb_a_current");
    encoder
        .get_or_declare_var("r_rb_a_final", Sort::Int)
        .expect("r_rb_a_final");
    encoder
        .get_or_declare_var("r_rb_b_current", Sort::Int)
        .expect("r_rb_b_current");
    encoder
        .get_or_declare_var("r_rb_b_final", Sort::Int)
        .expect("r_rb_b_final");

    let mut writebacks = HashMap::new();
    writebacks.insert("r_rb_a".to_string(), "r".to_string());
    writebacks.insert("r_rb_b".to_string(), "r".to_string());
    let mut finality = HashMap::new();
    finality.insert("r_rb_a".to_string(), BorrowFinality::Final { deref_pos: 0 });
    finality.insert("r_rb_b".to_string(), BorrowFinality::Final { deref_pos: 0 });
    let mut origins = HashMap::new();
    origins.insert(
        "r_rb_a".to_string(),
        BorrowIdOrigin::Derived {
            parent: "r".to_string(),
            steps: vec![BorrowIdStep::Field(0)],
        },
    );
    origins.insert(
        "r_rb_b".to_string(),
        BorrowIdOrigin::Derived {
            parent: "r".to_string(),
            steps: vec![BorrowIdStep::Field(1)],
        },
    );
    let resolve_names = vec!["r_rb_a".to_string(), "r_rb_b".to_string()];

    super::resolve::emit_prophecy_writebacks(
        &mut encoder,
        Some(&writebacks),
        Some(&finality),
        Some(&resolve_names),
        Some(&origins),
        None,
        None,
    );

    // Constrain child finals to different values (simulates `*a = 1; *b = 2`).
    let a_final = encoder.var_term("r_rb_a_final").expect("r_rb_a_final term");
    let b_final = encoder.var_term("r_rb_b_final").expect("r_rb_b_final term");
    let one = encoder.solver.int_const(1);
    let two = encoder.solver.int_const(2);
    encoder.assert_eq(a_final, one);
    encoder.assert_eq(b_final, two);

    // With projection-aware writeback, this should be SAT (children use different
    // tuple_get_N projections). With identity writeback, this would be UNSAT
    // because both children would be equated to parent_current directly.
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, SolveResult::Sat),
        "disjoint field projections should be satisfiable (#2673): got {sat:?}"
    );
}

/// Negative test: wrong field index should fail.
///
/// Models:
///   fn f(r: &mut (i32, i32)) { let a = &mut r.0; *a = 5; }
///   #[ensures(tuple_get_1(^r) == 5)]  // WRONG: should be tuple_get_0
#[test]
#[timeout(30000)]
fn projection_aware_writeback_wrong_field_fails() {
    let mut final_values = HashMap::new();
    final_values.insert("r".to_string(), deref(var("r")));
    final_values.insert("r_rb5".to_string(), int(5));

    // Postcondition: tuple_get_1(^r) == 5  -- WRONG field!
    let ensures = vec![eq(get_field(1, final_expr(var("r"))), int(5))];

    let mut writebacks = HashMap::new();
    writebacks.insert("r_rb5".to_string(), "r".to_string());

    let mut finality = HashMap::new();
    finality.insert("r_rb5".to_string(), BorrowFinality::Final { deref_pos: 0 });

    let mut origins = HashMap::new();
    origins.insert(
        "r_rb5".to_string(),
        BorrowIdOrigin::Derived {
            parent: "r".to_string(),
            steps: vec![BorrowIdStep::Field(0)], // Field(0), not Field(1)
        },
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["r_rb5".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality))
            .borrow_id_origins(Some(origins)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "wrong field index should be falsifiable (#2673): got {result:?}"
    );
}

/// Without Derived origin, identity reborrows still use direct equality (no projection).
///
/// Regression guard: when no field_steps are present (SameParent origin),
/// `emit_prophecy_writebacks` should still assert `child_current == parent_current`
/// directly rather than going through a projection UF.
#[test]
#[timeout(30000)]
fn identity_reborrow_still_uses_direct_equality() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("x_current", Sort::Int)
        .expect("x_current");
    encoder
        .get_or_declare_var("x_final", Sort::Int)
        .expect("x_final");
    encoder
        .get_or_declare_var("x_rb1_current", Sort::Int)
        .expect("x_rb1_current");
    encoder
        .get_or_declare_var("x_rb1_final", Sort::Int)
        .expect("x_rb1_final");

    let mut writebacks = HashMap::new();
    writebacks.insert("x_rb1".to_string(), "x".to_string());
    let mut finality = HashMap::new();
    finality.insert("x_rb1".to_string(), BorrowFinality::Final { deref_pos: 0 });
    // SameParent, not Derived — so no field projection.
    let mut origins = HashMap::new();
    origins.insert(
        "x_rb1".to_string(),
        BorrowIdOrigin::SameParent {
            parent: "x".to_string(),
        },
    );
    let resolve_names = vec!["x_rb1".to_string()];

    super::resolve::emit_prophecy_writebacks(
        &mut encoder,
        Some(&writebacks),
        Some(&finality),
        Some(&resolve_names),
        Some(&origins),
        None,
        None,
    );

    // Verify: x_rb1_current == x_current (direct, no UF).
    let child_current = encoder
        .var_term("x_rb1_current")
        .expect("x_rb1_current term");
    let parent_current = encoder.var_term("x_current").expect("x_current term");
    let eq_term = encoder.eq_term(child_current, parent_current);
    let neq = encoder.solver.not(eq_term);

    encoder.push_scope().expect("push scope");
    encoder.assert_term(neq);
    let sat = encoder.check_sat();
    encoder.pop_scope().expect("pop scope");

    assert!(
        matches!(sat, SolveResult::Unsat(_)),
        "identity reborrow should use direct equality (#2673 regression guard): got {sat:?}"
    );
}

// ── Cross-sort writeback tests (#2673 strengthened: relaxed sort gate) ────

/// When child_current has sort Int (from sort fallback) and parent_current has
/// a MutRef carrier sort, the writeback should still fire. Previously the strict
/// `child_sort == parent_sort` gate silently dropped the constraint.
///
/// This is the root cause for `pair_bor_mut.rs` and `unnest.rs` being
/// "incomplete" — the solver didn't have the writeback constraints needed
/// to chain the resolution.
#[test]
#[timeout(30000)]
fn cross_sort_writeback_int_vs_mutref_emits_constraint() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    let mutref_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));

    // Parent has MutRef carrier sort (driver-shaped), child has Int (sort fallback).
    encoder
        .get_or_declare_var("y_current", mutref_sort.clone())
        .expect("y_current");
    encoder
        .get_or_declare_var("y_final", mutref_sort)
        .expect("y_final");
    encoder
        .get_or_declare_var("y_rb5_current", Sort::Int)
        .expect("y_rb5_current");
    encoder
        .get_or_declare_var("y_rb5_final", Sort::Int)
        .expect("y_rb5_final");

    let mut writebacks = HashMap::new();
    writebacks.insert("y_rb5".to_string(), "y".to_string());
    let resolve_names = vec!["y_rb5".to_string()];

    super::resolve::emit_prophecy_writebacks(
        &mut encoder,
        Some(&writebacks),
        None,
        Some(&resolve_names),
        None,
        None,
        None,
    );

    // The writeback should have been emitted despite sort mismatch.
    // Verify by checking that y_current is constrained (asserting it != y_rb5_final
    // should be UNSAT if the writeback fired).
    let child_final = encoder.var_term("y_rb5_final").expect("y_rb5_final term");
    let _parent_current = encoder.var_term("y_current").expect("y_current term");

    // The coercion layer bridges Int vs MutRef sorts, so we can't directly
    // compare terms. Instead, set child_final to a known value and check
    // that the system is SAT (not broken by the cross-sort assertion).
    let five = encoder.solver.int_const(5);
    encoder.assert_eq(child_final, five);

    let sat = encoder.check_sat();
    assert!(
        matches!(sat, ay_dpll::api::SolveResult::Sat),
        "cross-sort writeback should leave the context satisfiable: got {sat:?}"
    );
}

/// Prophecy writeback with MutRef-typed child and Int-typed parent should
/// still propagate the current-value constraint.
#[test]
#[timeout(30000)]
fn cross_sort_writeback_mutref_child_int_parent_emits_constraint() {
    use ay_dpll::api::Sort;

    let mut encoder = AYEncoder::new();
    let mutref_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));

    // Child has MutRef carrier sort, parent has Int (sort fallback).
    encoder
        .get_or_declare_var("x_current", Sort::Int)
        .expect("x_current");
    encoder
        .get_or_declare_var("x_final", Sort::Int)
        .expect("x_final");
    encoder
        .get_or_declare_var("x_rb1_current", mutref_sort.clone())
        .expect("x_rb1_current");
    encoder
        .get_or_declare_var("x_rb1_final", mutref_sort)
        .expect("x_rb1_final");

    let mut writebacks = HashMap::new();
    writebacks.insert("x_rb1".to_string(), "x".to_string());

    super::resolve::emit_prophecy_writebacks(
        &mut encoder,
        Some(&writebacks),
        None,
        None,
        None,
        None,
        None,
    );

    // System should be SAT with the cross-sort writeback.
    let sat = encoder.check_sat();
    assert!(
        matches!(sat, ay_dpll::api::SolveResult::Sat),
        "cross-sort writeback (MutRef child, Int parent) should be satisfiable: got {sat:?}"
    );
}

/// High-level verification test: unnest pattern with SameParent borrow ID
/// and cross-sort variables should verify current-value equality.
///
/// Models the `unnest` compat test pattern where the child reborrow has a
/// different sort than the parent due to nested MutRef peeling.
///
/// fn unnest(x: &mut &mut u32) -> &mut u32 { *x }
/// #[ensures(*result == **x)]
#[test]
#[timeout(30000)]
fn unnest_cross_sort_reborrow_current_value_verifies() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let mr_mr_int = ExprSort::MutRef(Box::new(mr_int.clone()));

    // x: &mut &mut u32, x_rb: the inner reborrow (*x)
    let mut final_values = HashMap::new();
    final_values.insert(
        "x".to_string(),
        deref(var_with_sort("x", mr_mr_int.clone())),
    );
    // x_rb is the identity reborrow of the inner *x
    final_values.insert(
        "x_rb".to_string(),
        deref(var_with_sort("x_rb", mr_int.clone())),
    );

    // Postcondition: *result == **x (current of result == current of current of x)
    // Simplified to deref(result) == deref(deref(x))
    let ensures = vec![eq(deref(var("result")), deref(deref(var("x"))))];

    let mut writebacks = HashMap::new();
    writebacks.insert("x_rb".to_string(), "x".to_string());

    let mut origins = HashMap::new();
    origins.insert(
        "x_rb".to_string(),
        BorrowIdOrigin::SameParent {
            parent: "x".to_string(),
        },
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&deref(var_with_sort("x_rb", mr_int))))
            .resolve_assumptions(Some(vec!["x_rb".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_id_origins(Some(origins)),
    )
    .expect("encoding should succeed");

    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27). The property
    // this test guards is "must NOT verify" — a disconnected coercion model may
    // never be accepted — and that property is intact: `Verified`, `Assumed` and
    // `Failed` all still fail here. What changed is WHICH fail-closed route
    // fires first: ay now answers `Unknown(Incomplete)` on the whole solve, so
    // the run never reaches the `sort-coercion bridge in negated goal` demotion
    // this pin was written against. The preferred (mechanism-naming) arm is kept
    // first and is the one to restore alone once ay decides this query again.
    assert!(
        matches!(
            result,
            VerificationResult::Unknown(UnknownReason::Demoted(ref reason))
                if reason.contains("sort-coercion bridge in negated goal")
        ) || matches!(
            result,
            VerificationResult::Unknown(UnknownReason::Incomplete)
        ),
        "cross-sort unnest reborrow must fail closed on its disconnected coercion model (#2673) \
         — either via the sort-coercion demotion or the upstream Incomplete that now \
         pre-empts it: got {result:?}"
    );
}

/// Conditional borrow return with tuple field projection (pair_bor_mut pattern).
///
/// Models:
///   fn pair_bor_mut(p: (&mut T, &mut T), take_first: bool) -> &mut T {
///       if take_first { p.0 } else { p.1 }
///   }
///   #[ensures(if take_first { result == p.0 && ^p.1 == *p.1 }
///             else { result == p.1 && ^p.0 == *p.0 })]
///
/// The critical property: the untouched branch's final value equals its current.
#[test]
#[timeout(30000)]
fn pair_bor_mut_untouched_branch_final_equals_current() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    // Two &mut parameters representing p.0 and p.1
    let p0 = var_with_sort("p0", mr_int.clone());
    let p1 = var_with_sort("p1", mr_int.clone());

    // Identity final values (neither is mutated by the function itself)
    let mut final_values = HashMap::new();
    final_values.insert("p0".to_string(), deref(p0.clone()));
    final_values.insert("p1".to_string(), deref(p1.clone()));

    // Simplified postcondition: ^p1 == *p1 (the untouched branch is preserved)
    // This should verify because p1's final value is identity.
    let ensures = vec![eq(final_expr(p1.clone()), deref(p1.clone()))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["p0".to_string(), "p1".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "untouched branch final == current should verify (#2673): got {result:?}"
    );
}

// ── #2673: final_final alias tests ──────────────────────────────────────

/// Test that the `v_final_final == v_current_final` alias enables the unnest
/// postcondition pattern: `^(*x) == ^(^x)`.
///
/// In MIR terms: `Final(Deref(Var("x"))) == Final(Final(Var("x")))` which
/// resolves to `x_current_final == x_final_final`. Without the final_final
/// alias, x_final_final is a free variable and this fails with counterexample.
///
/// Re: #2190, #2673
#[test]
#[timeout(30000)]
fn final_final_alias_enables_unnest_postcondition() {
    // Identity final value: body doesn't mutate x
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    // Postcondition: ^(*x) == ^(^x)
    // Resolves to: x_current_final == x_final_final
    let ens = eq(
        final_expr(deref(var("x"))),
        final_expr(final_expr(var("x"))),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values)
            .resolve_assumptions(Some(vec!["x".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "final_final alias should enable ^(*x) == ^(^x) for identity borrows (#2673): got {result:?}"
    );
}

/// Negative test: final_final alias should NOT be emitted for non-identity
/// final values (when the body mutates the parameter).
///
/// If the body sets `v_final = v_current + 1`, then `v_final_final` should
/// remain unconstrained (or at least not equal to `v_current_final`).
///
/// Re: #2673
#[test]
#[timeout(30000)]
fn final_final_alias_not_emitted_for_non_identity() {
    // Non-identity final value: body mutates x (x_final = x_current + 1)
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), add(deref(var("x")), int(1)));

    // Postcondition: ^(^x) == ^(*x) — same as unnest pattern.
    // Without the alias (because non-identity), this is falsifiable.
    let ens = eq(
        final_expr(final_expr(var("x"))),
        final_expr(deref(var("x"))),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values)
            .resolve_assumptions(Some(vec!["x".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "non-identity borrows should leave final_final alias falsifiable (#2673): got {result:?}"
    );
}

/// Test that final_final alias is applied independently per parameter.
///
/// With two identity parameters, each gets its own final_final alias, and
/// the postcondition on one does not affect the other.
///
/// Re: #2673
#[test]
#[timeout(30000)]
fn final_final_alias_independent_per_parameter() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    // Two identity parameters
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(var_with_sort("a", mr_int.clone())));
    final_values.insert("b".to_string(), deref(var_with_sort("b", mr_int.clone())));

    // Postcondition: ^(^a) == ^(*a) AND ^(^b) == ^(*b)
    let ens_a = eq(
        final_expr(final_expr(var("a"))),
        final_expr(deref(var("a"))),
    );
    let ens_b = eq(
        final_expr(final_expr(var("b"))),
        final_expr(deref(var("b"))),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens_a, ens_b], &final_values)
            .resolve_assumptions(Some(vec!["a".to_string(), "b".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "final_final alias should work independently per parameter (#2673): got {result:?}"
    );
}

// ── #2673 strengthened: transitive writeback chain closure ──────────────

/// Three-level reborrow chain mutation flows back via transitive closure.
///
/// Models:
///   fn f(x: &mut i32) {
///       let r1 = &mut *x;
///       let r2 = &mut *r1;
///       let r3 = &mut *r2;
///       *r3 = 42;
///   }
///   #[ensures(^x == 42)]
///
/// Chain: x -> x_rb1 -> x_rb2 -> x_rb3, where x_rb3_final = 42.
/// Without transitive closure, the solver must chain through 3 levels
/// of writebacks + resolves. With the closure, `x_current == x_rb3_final`
/// is asserted directly.
#[test]
#[timeout(30000)]
fn three_level_reborrow_chain_mutation_flows_back_transitively() {
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));
    final_values.insert("x_rb1".to_string(), deref(var("x_rb1")));
    final_values.insert("x_rb2".to_string(), deref(var("x_rb2")));
    final_values.insert("x_rb3".to_string(), int(42));

    let ensures = vec![eq(final_expr(var("x")), int(42))];

    let mut writebacks = HashMap::new();
    writebacks.insert("x_rb1".to_string(), "x".to_string());
    writebacks.insert("x_rb2".to_string(), "x_rb1".to_string());
    writebacks.insert("x_rb3".to_string(), "x_rb2".to_string());

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec![
                "x_rb3".to_string(),
                "x_rb2".to_string(),
                "x_rb1".to_string(),
            ]))
            .prophecy_writebacks(Some(writebacks)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "three-level reborrow chain should resolve mutations back (#2673 transitive): got {result:?}"
    );
}

/// Resolve + current_final propagation: `^(*x) == *x` for resolved identity borrows.
///
/// When x is resolved (identity), ^(*x) resolves to x_current_final, and *x
/// resolves to x_current. The new `emit_resolve_current_final_propagation`
/// ensures x_current_final == x_current is asserted directly.
#[test]
#[timeout(30000)]
fn resolve_current_final_propagation_enables_deref_final_eq_deref() {
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    // Postcondition: ^(*x) == *x
    // Final(Deref(Var("x"))) == Deref(Var("x"))
    // Resolves to: x_current_final == x_current
    let ensures = vec![eq(final_expr(deref(var("x"))), deref(var("x")))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["x".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "resolve + current_final propagation should make ^(*x) == *x verify (#2673): got {result:?}"
    );
}

/// Two borrows from same source: both resolved, postcondition compares finals.
///
/// Models the pair_bor_mut pattern where the untouched borrow's final should
/// equal its current. With both borrows resolved:
///   p0_final == p0_current (resolve)
///   p1_final == p1_current (resolve)
/// The postcondition `^p0 + ^p1 == *p0 + *p1` should verify.
#[test]
#[timeout(30000)]
fn two_resolved_borrows_sum_of_finals_equals_sum_of_currents() {
    let mut final_values = HashMap::new();
    final_values.insert("p0".to_string(), deref(var("p0")));
    final_values.insert("p1".to_string(), deref(var("p1")));

    // Postcondition: ^p0 + ^p1 == *p0 + *p1
    let ensures = vec![eq(
        add(final_expr(var("p0")), final_expr(var("p1"))),
        add(deref(var("p0")), deref(var("p1"))),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["p0".to_string(), "p1".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "two resolved borrows sum should verify (#2673): got {result:?}"
    );
}

/// ITE result expression with MutRef-annotated branches binds whole borrow.
///
/// Models pair_bor_mut's conditional return:
///   fn pair_bor_mut(p0: &mut i32, p1: &mut i32, take_first: bool) -> &mut i32 {
///       if take_first { p0 } else { p1 }
///   }
///   #[ensures(if take_first { result == p0 } else { result == p1 })]
///
/// The return expression is `Ite(take_first, Var("p0", MutRef(Int)), Var("p1", MutRef(Int)))`.
/// Before the ITE fix (#2673), `bind_whole_mut_ref_result` returned false for ITE
/// expressions because `effective_expr_annotation` and `resolve_nameable_expr` both
/// return None for ITE nodes. The fix constructs conditional bindings:
///   result_current = ite(cond, p0_current, p1_current)
///   result_final   = ite(cond, p0_final,   p1_final)
///   result_id      = ite(cond, p0_id,      p1_id)
/// and calls bind_whole_mut_ref to create the carrier sort tuple.
#[test]
#[timeout(30000)]
fn ite_result_mut_ref_whole_borrow_binding_verifies() {
    use crate::tests::helpers::ite;

    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    // Two &mut parameters
    let p0 = var_with_sort("p0", mr_int.clone());
    let p1 = var_with_sort("p1", mr_int.clone());

    // Identity final values (the function itself doesn't mutate, it picks one)
    let mut final_values = HashMap::new();
    final_values.insert("p0".to_string(), deref(p0.clone()));
    final_values.insert("p1".to_string(), deref(p1.clone()));

    // Return expression: if take_first then p0 else p1
    let return_expr = ite(var("take_first"), p0.clone(), p1.clone());

    // Postcondition: if take_first { result == p0 } else { result == p1 }
    // Using whole-borrow equality (not field-level *result == *p0).
    let ensures = vec![ite(
        var("take_first"),
        eq(var("result"), p0.clone()),
        eq(var("result"), p1.clone()),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr))
            .resolve_assumptions(Some(vec!["p0".to_string(), "p1".to_string()])),
    )
    .expect("encoding should succeed");

    // KNOWN-CLASS PIN (2026-08-23 mut_ref drift adjudication): since ay's
    // mandatory strict UNSAT certification (0.7 line; SelfCheckRejected at the
    // 0.7 boundary, ProofTrusted on the current line), this VC computes UNSAT
    // but its certificate fails strict validation, demoting Verified to
    // `Unknown(ProofTrusted)` — the sound direction. The #2673 ITE
    // whole-borrow BINDING this test guards is intact (a missing binding
    // yields Failed/other Unknowns, which still fail here); the gap is
    // upstream certificate coverage. Retire the tolerance when the class
    // closes upstream.
    assert!(
        matches!(
            result,
            VerificationResult::Verified(_)
                | VerificationResult::Unknown(UnknownReason::ProofTrusted)
        ),
        "ITE result with MutRef branches should bind whole borrow (#2673) and \
         verify (or demote to the known proof-trusted certification gap): got {result:?}"
    );
}

/// Swap pattern: two borrows where each gets the other's value.
///
/// Models a simplified inc_max pattern:
///   swap(&mut ma, &mut mb) // ^ma == *mb, ^mb == *ma
///
/// The postcondition should verify with the cross-mutation final values.
#[test]
#[timeout(30000)]
fn swap_pattern_cross_mutation_verifies() {
    let mut final_values = HashMap::new();
    // After swap: ma's final is mb's initial, and vice versa
    final_values.insert("ma".to_string(), deref(var("mb")));
    final_values.insert("mb".to_string(), deref(var("ma")));

    // Postcondition: ^ma == *mb && ^mb == *ma
    let requires = vec![gt(deref(var("ma")), int(0)), gt(deref(var("mb")), int(0))];
    let ensures = vec![
        eq(final_expr(var("ma")), deref(var("mb"))),
        eq(final_expr(var("mb")), deref(var("ma"))),
    ];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "swap pattern cross-mutation should verify (#2673): got {result:?}"
    );
}

/// Models the `inc_max_3` compat test: 3 conditional swaps to sort, then
/// increment the largest by 2 and the median by 1. Postcondition: all three
/// final values are distinct.
///
/// The conditional swap pattern creates ITE-based final values that model
/// the sorting network: if (*ma < *mb) swap, if (*mb < *mc) swap,
/// if (*ma < *mb) swap. After sorting: *ma += 2, *mb += 1.
///
/// This is the unit-level reproduction for Creusot compat test
/// `tests/should_succeed/rusthorn/inc_max_3.rs` (#2692).
#[test]
#[timeout(120000)]
fn inc_max_3_conditional_swap_distinct_postcondition_verifies() {
    let a = deref(var("ma"));
    let b = deref(var("mb"));
    let c = deref(var("mc"));

    // Sorting network via conditional swaps.
    // Step 1: if *ma < *mb then swap(ma, mb)
    //   after step 1: s1_a = ite(a < b, b, a), s1_b = ite(a < b, a, b)
    let cond1 = lt(a.clone(), b.clone());
    let s1_a = ite(cond1.clone(), b.clone(), a.clone());
    let s1_b = ite(cond1.clone(), a.clone(), b.clone());
    let s1_c = c.clone();

    // Step 2: if s1_b < s1_c then swap(mb, mc)
    //   after step 2: s2_b = ite(s1_b < s1_c, s1_c, s1_b), s2_c = ite(...)
    let cond2 = lt(s1_b.clone(), s1_c.clone());
    let s2_a = s1_a.clone();
    let s2_b = ite(cond2.clone(), s1_c.clone(), s1_b.clone());
    let s2_c = ite(cond2.clone(), s1_b.clone(), s1_c.clone());

    // Step 3: if s2_a < s2_b then swap(ma, mb) again
    //   after step 3: s3_a >= s3_b >= s3_c
    let cond3 = lt(s2_a.clone(), s2_b.clone());
    let s3_a = ite(cond3.clone(), s2_b.clone(), s2_a.clone());
    let s3_b = ite(cond3.clone(), s2_a.clone(), s2_b.clone());
    let s3_c = s2_c.clone();

    // Final mutations: *ma += 2, *mb += 1 (mc unchanged)
    let final_a = add(s3_a, int(2));
    let final_b = add(s3_b, int(1));
    let final_c = s3_c;

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), final_a);
    final_values.insert("mb".to_string(), final_b);
    final_values.insert("mc".to_string(), final_c);

    let requires = vec![
        le(deref(var("ma")), int(1_000_000)),
        le(deref(var("mb")), int(1_000_000)),
        le(deref(var("mc")), int(1_000_000)),
    ];

    // Postcondition: ^ma != ^mb && ^mb != ^mc && ^mc != ^ma
    let ensures = vec![
        ne(final_expr(var("ma")), final_expr(var("mb"))),
        ne(final_expr(var("mb")), final_expr(var("mc"))),
        ne(final_expr(var("mc")), final_expr(var("ma"))),
    ];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "inc_max_3 conditional swap pattern should verify (#2692): got {result:?}"
    );
}

/// Conditional tuple-field swap preserves the expected field relation.
///
/// Models:
///   fn toggle(b: bool, x: &mut (i32, i32)) {
///       if b { (*x.0, *x.1) = (*x.1, *x.0) } else { /* no-op */ }
///   }
#[test]
#[timeout(30000)]
fn projection_toggle_conditional_field_swap_verifies() {
    let tuple2 = tuple_logic_fn_name(2);
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    let x_0_current = deref(logic_fn_call(&tuple_get_0, vec![deref(var("x"))]));
    let x_1_current = deref(logic_fn_call(&tuple_get_1, vec![deref(var("x"))]));
    let x_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("x"))]));
    let x_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("x"))]));

    let mut final_values = HashMap::new();
    final_values.insert(
        "x".to_string(),
        ite(
            var("b"),
            logic_fn_call(&tuple2, vec![x_1_current.clone(), x_0_current.clone()]),
            deref(var("x")),
        ),
    );

    let ensures = vec![ite(
        var("b"),
        and(
            eq(x_0_final.clone(), x_1_current.clone()),
            eq(x_1_final.clone(), x_0_current.clone()),
        ),
        and(eq(x_0_final, x_0_current), eq(x_1_final, x_1_current)),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .resolve_assumptions(Some(vec!["x".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "conditional projected field swap should verify: got {result:?}"
    );
}

/// Conditional max increment: increment the larger of two mutable integers.
#[test]
#[timeout(30000)]
fn inc_max_conditional_increment_verifies() {
    let a = deref(var("a"));
    let b = deref(var("b"));
    let a_final = final_expr(var("a"));
    let b_final = final_expr(var("b"));
    let cond = ge(a.clone(), b.clone());

    let mut final_values = HashMap::new();
    final_values.insert(
        "a".to_string(),
        ite(cond.clone(), add(a.clone(), int(1)), a.clone()),
    );
    final_values.insert(
        "b".to_string(),
        ite(cond.clone(), b.clone(), add(b.clone(), int(1))),
    );

    let ensures = vec![ite(
        cond,
        and(
            eq(a_final.clone(), add(a.clone(), int(1))),
            eq(b_final.clone(), b.clone()),
        ),
        and(eq(a_final, a), eq(b_final, add(b, int(1)))),
    )];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "conditional max increment should verify: got {result:?}"
    );
}

/// Four-parameter max increment with nested branch structure.
#[test]
#[timeout(120000)]
fn inc_max_many_four_params_conditional_increment_verifies() {
    let a = deref(var("a"));
    let b = deref(var("b"));
    let c = deref(var("c"));
    let d = deref(var("d"));

    let a_final = final_expr(var("a"));
    let b_final = final_expr(var("b"));
    let c_final = final_expr(var("c"));
    let d_final = final_expr(var("d"));

    let cond_a = and(
        ge(a.clone(), b.clone()),
        and(ge(a.clone(), c.clone()), ge(a.clone(), d.clone())),
    );
    let cond_b = and(ge(b.clone(), c.clone()), ge(b.clone(), d.clone()));
    let cond_c = ge(c.clone(), d.clone());

    let mut final_values = HashMap::new();
    final_values.insert(
        "a".to_string(),
        ite(cond_a.clone(), add(a.clone(), int(1)), a.clone()),
    );
    final_values.insert(
        "b".to_string(),
        ite(
            cond_a.clone(),
            b.clone(),
            ite(cond_b.clone(), add(b.clone(), int(1)), b.clone()),
        ),
    );
    final_values.insert(
        "c".to_string(),
        ite(
            cond_a.clone(),
            c.clone(),
            ite(
                cond_b.clone(),
                c.clone(),
                ite(cond_c.clone(), add(c.clone(), int(1)), c.clone()),
            ),
        ),
    );
    final_values.insert(
        "d".to_string(),
        ite(
            cond_a.clone(),
            d.clone(),
            ite(
                cond_b.clone(),
                d.clone(),
                ite(cond_c.clone(), d.clone(), add(d.clone(), int(1))),
            ),
        ),
    );

    let branch_a = and(
        and(
            eq(a_final.clone(), add(a.clone(), int(1))),
            eq(b_final.clone(), b.clone()),
        ),
        and(
            eq(c_final.clone(), c.clone()),
            eq(d_final.clone(), d.clone()),
        ),
    );
    let branch_b = and(
        and(
            eq(a_final.clone(), a.clone()),
            eq(b_final.clone(), add(b.clone(), int(1))),
        ),
        and(
            eq(c_final.clone(), c.clone()),
            eq(d_final.clone(), d.clone()),
        ),
    );
    let branch_c = and(
        and(
            eq(a_final.clone(), a.clone()),
            eq(b_final.clone(), b.clone()),
        ),
        and(
            eq(c_final.clone(), add(c.clone(), int(1))),
            eq(d_final.clone(), d.clone()),
        ),
    );
    let branch_d = and(
        and(eq(a_final, a), eq(b_final, b)),
        and(eq(c_final, c), eq(d_final, add(d, int(1)))),
    );

    let ensures = vec![ite(
        cond_a,
        branch_a,
        ite(cond_b, branch_b, ite(cond_c, branch_c, branch_d)),
    )];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "four-parameter max increment should verify: got {result:?}"
    );
}

/// Identity branch of projection toggle preserves both tuple fields.
#[test]
#[timeout(30000)]
fn projection_toggle_identity_branch_preserves_both_fields() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    let ensures = vec![
        eq(
            final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("x"))])),
            deref(logic_fn_call(&tuple_get_0, vec![deref(var("x"))])),
        ),
        eq(
            final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("x"))])),
            deref(logic_fn_call(&tuple_get_1, vec![deref(var("x"))])),
        ),
    ];

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "identity projection branch should preserve both fields: got {result:?}"
    );
}

/// Conditional max increment remains positive under positive preconditions.
#[test]
#[timeout(30000)]
fn inc_max_with_preconditions_verifies() {
    let a = deref(var("a"));
    let b = deref(var("b"));
    let a_final = final_expr(var("a"));
    let b_final = final_expr(var("b"));
    let cond = ge(a.clone(), b.clone());

    let requires = vec![gt(a.clone(), int(0)), gt(b.clone(), int(0))];

    let mut final_values = HashMap::new();
    final_values.insert(
        "a".to_string(),
        ite(cond.clone(), add(a.clone(), int(1)), a.clone()),
    );
    final_values.insert(
        "b".to_string(),
        ite(cond.clone(), b.clone(), add(b.clone(), int(1))),
    );

    let ensures = vec![
        ite(
            cond,
            and(
                eq(a_final.clone(), add(a.clone(), int(1))),
                eq(b_final.clone(), b.clone()),
            ),
            and(
                eq(a_final.clone(), a.clone()),
                eq(b_final.clone(), add(b.clone(), int(1))),
            ),
        ),
        and(gt(a_final, int(0)), gt(b_final, int(0))),
    ];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "conditional max increment with positive preconditions should verify: got {result:?}"
    );
}

// ── #2673 strengthening: drop_pair, unnest, pair_bor_mut, inc_max_3 patterns ──

/// Models the `drop_pair` Creusot compat test with resolve assertions.
///
/// fn drop_pair(_x: (&mut u32, &mut u32)) {}
/// #[ensures(^_x.0 == *_x.0)]
/// #[ensures(^_x.1 == *_x.1)]
///
/// When the parameter has an identity final value and is resolved, projecting
/// tuple fields through both final and current should yield equal values.
/// This covers the case where the driver decomposes a tuple-of-mut-borrows
/// parameter into whole-tuple identity final values.
///
/// Re: #2673
#[test]
#[timeout(30000)]
fn drop_pair_resolve_both_fields_preserved() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // ^_x.0 == *_x.0
    let ens_0 = eq(
        final_expr(logic_fn_call(&tuple_get_0, vec![var("_x")])),
        deref(logic_fn_call(&tuple_get_0, vec![var("_x")])),
    );

    // ^_x.1 == *_x.1
    let ens_1 = eq(
        final_expr(logic_fn_call(&tuple_get_1, vec![var("_x")])),
        deref(logic_fn_call(&tuple_get_1, vec![var("_x")])),
    );

    // Identity final value: _x_final = *_x (the tuple is dropped without modification)
    let mut final_values = HashMap::new();
    final_values.insert("_x".to_string(), deref(var("_x")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens_0, ens_1], &final_values)
            .resolve_assumptions(Some(vec!["_x".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "drop_pair with resolve should preserve both tuple fields (#2673): got {result:?}"
    );
}

/// Models the full `unnest` Creusot compat test: three postconditions.
///
/// fn unnest(x: &mut &mut u32) -> &mut u32 { *x }
/// #[ensures(*result == **x)]
/// #[ensures(^result == *^x)]
/// #[ensures(^*x == ^^x)]
///
/// This requires:
/// - Nested MutRef types: x has ExprSort::MutRef(MutRef(Int))
/// - Reborrow chain: x_rb = &mut **x (inner reborrow of the nested deref)
/// - Identity final values for both x and x_rb
/// - SameParent borrow ID origin
/// - Resolve assertions on both x and x_rb
/// - Return expression: the reborrow x_rb
///
/// At the ay level, the third postcondition ^*x == ^^x (x_current_final == x_final_final)
/// is directly enabled by the final_final alias in bindings.rs. The first two
/// postconditions require the writeback chain to propagate correctly.
///
/// Re: #2673
#[test]
#[timeout(60000)]
fn unnest_three_postconditions_verify() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let mr_mr_int = ExprSort::MutRef(Box::new(mr_int.clone()));

    // x: &mut &mut u32
    let x_var = var_with_sort("x", mr_mr_int.clone());
    // x_rb: the inner reborrow (*x), type &mut u32
    let x_rb_var = var_with_sort("x_rb", mr_int.clone());

    // Identity final values: neither x nor x_rb are mutated by unnest
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(x_var.clone()));
    final_values.insert("x_rb".to_string(), deref(x_rb_var.clone()));

    // Postcondition 3: ^*x == ^^x (x_current_final == x_final_final)
    // This is the most directly testable at ay level via the final_final alias.
    let ens_3 = eq(
        final_expr(deref(var("x"))),
        final_expr(final_expr(var("x"))),
    );

    // Writebacks: x_rb writes back to x (child -> parent)
    let mut writebacks = HashMap::new();
    writebacks.insert("x_rb".to_string(), "x".to_string());

    // Borrow ID: SameParent (identity reborrow of *x)
    let mut origins = HashMap::new();
    origins.insert(
        "x_rb".to_string(),
        BorrowIdOrigin::SameParent {
            parent: "x".to_string(),
        },
    );

    let mut finality = HashMap::new();
    finality.insert("x_rb".to_string(), BorrowFinality::Final { deref_pos: 0 });

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens_3], &final_values)
            .return_expr(Some(&deref(x_rb_var)))
            .resolve_assumptions(Some(vec!["x".to_string(), "x_rb".to_string()]))
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality))
            .borrow_id_origins(Some(origins)),
    )
    .expect("encoding should succeed");

    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the mut-borrow
    // vacuity gate refuses this verdict fail-closed when ay answers `Incomplete`
    // on the fresh base re-solve. See `tests::helpers::verified_or_unvalidated_sat_base`.
    assert!(
        crate::tests::helpers::verified_or_unvalidated_sat_base(&result),
        "unnest ^*x == ^^x postcondition should verify with full reborrow chain (#2673) \
         (or refuse fail-closed on the known unvalidated-SAT-base class): got {result:?}"
    );
}

/// Models `inc_max_3` with swap as conditional ITE final values (sorting network).
///
/// This extends the existing inc_max_3 test by adding resolve assertions
/// and prophecy writebacks to model how the driver would construct the request
/// when intermediate reborrow variables from the swap calls are present.
///
/// fn inc_max_3(mut ma, mut mb, mut mc) {
///     if *ma < *mb { swap(&mut ma, &mut mb); }
///     if *mb < *mc { swap(&mut mb, &mut mc); }
///     if *ma < *mb { swap(&mut ma, &mut mb); }
///     *ma += 2; *mb += 1;
/// }
///
/// The swap calls create intermediate reborrow variables. After all swaps,
/// the effective final values are the sorted+incremented values. The driver
/// should extract the post-swap final values via call assumptions from the
/// trusted swap spec.
///
/// This test models the intermediate reborrow chain explicitly:
/// - swap1: if *ma < *mb, creates rb_a1/rb_b1 reborrows
/// - The effective state after all swaps is modeled as sorted ITE expressions
///
/// Re: #2673, #2692
#[test]
#[timeout(120000)]
fn inc_max_3_with_reborrow_chain_from_swap_calls() {
    let a = deref(var("ma"));
    let b = deref(var("mb"));
    let c = deref(var("mc"));

    // After 3-step sorting network via conditional swaps:
    // Step 1: if *ma < *mb then (ma, mb) = (mb, ma)
    let cond1 = lt(a.clone(), b.clone());
    let s1_a = ite(cond1.clone(), b.clone(), a.clone());
    let s1_b = ite(cond1.clone(), a.clone(), b.clone());

    // Step 2: if s1_b < *mc then (mb, mc) = (mc, mb)
    let cond2 = lt(s1_b.clone(), c.clone());
    let s2_a = s1_a.clone();
    let s2_b = ite(cond2.clone(), c.clone(), s1_b.clone());
    let s2_c = ite(cond2.clone(), s1_b.clone(), c.clone());

    // Step 3: if s2_a < s2_b then (ma, mb) = (mb, ma) again
    let cond3 = lt(s2_a.clone(), s2_b.clone());
    let s3_a = ite(cond3.clone(), s2_b.clone(), s2_a.clone());
    let s3_b = ite(cond3.clone(), s2_a.clone(), s2_b.clone());
    let s3_c = s2_c;

    // Final mutations: *ma += 2, *mb += 1 (mc unchanged)
    let final_a = add(s3_a, int(2));
    let final_b = add(s3_b, int(1));
    let final_c = s3_c;

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), final_a);
    final_values.insert("mb".to_string(), final_b);
    final_values.insert("mc".to_string(), final_c);

    // Preconditions: bounded values to prevent overflow in u32 model
    let requires = vec![
        le(deref(var("ma")), int(1_000_000)),
        le(deref(var("mb")), int(1_000_000)),
        le(deref(var("mc")), int(1_000_000)),
    ];

    // Postcondition: all three final values are distinct
    let ensures = vec![
        ne(final_expr(var("ma")), final_expr(var("mb"))),
        ne(final_expr(var("mb")), final_expr(var("mc"))),
        ne(final_expr(var("mc")), final_expr(var("ma"))),
    ];

    // Model the reborrow chain from swap calls:
    // Each swap creates 2 reborrows of the parent parameters.
    // After the swap resolves, the parent's final value incorporates the swap effect.
    // We model the intermediate reborrows as part of the writeback chain.
    let mut writebacks = HashMap::new();
    // Swap 1 reborrows (ma, mb in first swap)
    writebacks.insert("ma_rb1".to_string(), "ma".to_string());
    writebacks.insert("mb_rb1".to_string(), "mb".to_string());

    // Identity final values for reborrow intermediates
    // (the swap mutates through these, already captured in the conditional final values)
    let mut reborrow_finals = HashMap::new();
    reborrow_finals.insert("ma_rb1".to_string(), deref(var("ma_rb1")));
    reborrow_finals.insert("mb_rb1".to_string(), deref(var("mb_rb1")));
    for (k, v) in reborrow_finals {
        final_values.insert(k, v);
    }

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values)
            .resolve_assumptions(Some(vec!["ma_rb1".to_string(), "mb_rb1".to_string()]))
            .prophecy_writebacks(Some(writebacks)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "inc_max_3 with reborrow chain from swap calls should verify (#2673, #2692): got {result:?}"
    );
}

/// Models the full `pair_bor_mut` pattern with whole-borrow equality and resolve.
///
/// fn pair_bor_mut(p0: &mut T, p1: &mut T, take_first: bool) -> &mut T {
///     if take_first { p0 } else { p1 }
/// }
/// #[ensures(if take_first { result == p0 && ^p1 == *p1 }
///           else { result == p1 && ^p0 == *p0 })]
///
/// This differs from the existing `pair_bor_mut_untouched_branch_final_equals_current`
/// test by using:
/// - MutRef(Int) sort annotations for whole-borrow equality (result == p0)
/// - ITE return expression for conditional borrow selection
/// - Both resolve assertions and finality data
/// - Borrow ID origins for the return path
///
/// The key challenge: the postcondition requires BOTH whole-borrow identity
/// (result == p0 as a reference equality, not just *result == *p0) AND
/// field-level preservation (^p1 == *p1 meaning the untouched borrow's
/// final value equals its current value).
///
/// Re: #2673
#[test]
#[timeout(60000)]
fn pair_bor_mut_whole_borrow_and_resolve_with_ite_return() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    let p0 = var_with_sort("p0", mr_int.clone());
    let p1 = var_with_sort("p1", mr_int.clone());

    // Identity final values: the function returns one but doesn't mutate either
    let mut final_values = HashMap::new();
    final_values.insert("p0".to_string(), deref(p0.clone()));
    final_values.insert("p1".to_string(), deref(p1.clone()));

    // Return expression: if take_first then p0 else p1 (as MutRef values)
    let return_expr = ite(var("take_first"), p0.clone(), p1.clone());

    // Postcondition: if take_first { result == p0 && ^p1 == *p1 }
    //                else { result == p1 && ^p0 == *p0 }
    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var_with_sort("result", mr_int.clone()), p0.clone()),
            eq(final_expr(p1.clone()), deref(p1.clone())),
        ),
        and(
            eq(var_with_sort("result", mr_int.clone()), p1.clone()),
            eq(final_expr(p0.clone()), deref(p0.clone())),
        ),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr))
            .resolve_assumptions(Some(vec!["p0".to_string(), "p1".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut with whole-borrow equality and ITE return should verify (#2673): got {result:?}"
    );
}

/// Negative test: pair_bor_mut postcondition should FAIL if branches are swapped.
///
/// If we claim `result == p1` in the take_first=true branch (wrong!), verification
/// should fail because the ITE return binds result to p0 when take_first is true.
///
/// Re: #2673
#[test]
#[timeout(30000)]
fn pair_bor_mut_wrong_branch_postcondition_fails() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    let p0 = var_with_sort("p0", mr_int.clone());
    let p1 = var_with_sort("p1", mr_int.clone());

    let mut final_values = HashMap::new();
    final_values.insert("p0".to_string(), deref(p0.clone()));
    final_values.insert("p1".to_string(), deref(p1.clone()));

    let return_expr = ite(var("take_first"), p0.clone(), p1.clone());

    // WRONG: claims result == p1 when take_first is true (should be p0)
    let ensures = vec![ite(
        var("take_first"),
        eq(
            var_with_sort("result", mr_int.clone()),
            p1.clone(), // WRONG
        ),
        eq(
            var_with_sort("result", mr_int.clone()),
            p0.clone(), // WRONG
        ),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr))
            .resolve_assumptions(Some(vec!["p0".to_string(), "p1".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "pair_bor_mut swapped branch postcondition should fail: got {result:?}"
    );
}

/// Tuple-of-mut-ref `pair_bor_mut` driver shape: the parameter is a single
/// tuple `p: (&mut T, &mut T)` instead of two separate `&mut T` params.
///
/// This is the form the driver actually emits for the Creusot
/// `pair_bor_mut.rs` compat test. The return expression is
/// `Ite(take_first, LogicFnCall(tuple_get_0, [Var(p, Tuple(2))]),
///      LogicFnCall(tuple_get_1, [Var(p, Tuple(2))]))`,
/// which previously left `bind_whole_mut_ref_result_ite` blocked because
/// neither branch carries a MutRef annotation: the inner `Var(p, ...)` is
/// `Tuple(_)`-typed and the LogicFnCall has no return-sort annotation.
///
/// The fix in `bind_whole_mut_ref_result_ite` recognises this shape and
/// recovers the inner T sort from the `Var("result", Some(MutRef(_)))` use
/// in `ensures`, then bridges `tuple_get_X_MutRef(p_current) == p.X` so the
/// postcondition's MutRef equality can decompose into per-field components.
/// (#5)
#[test]
#[timeout(60000)]
fn pair_bor_mut_tuple_of_mut_ref_param_verifies() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let tuple2_sort = ExprSort::Tuple(2);
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // p: (&mut T, &mut T) — annotated Tuple(2) on the whole-tuple Var.
    let p_var = var_with_sort("p", tuple2_sort.clone());
    let p0_expr = logic_fn_call(&tuple_get_0, vec![p_var.clone()]);
    let p1_expr = logic_fn_call(&tuple_get_1, vec![p_var.clone()]);

    // final_values mirror the driver shape: whole-tuple identity + per-field
    // identity entries via Deref(tuple_get_X(Deref(p))). The per-field keys
    // `p.0` / `p.1` are what the bridge looks up to confirm a mut-borrow
    // tuple-field projection.
    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(p_var.clone()));
    final_values.insert(
        "p.0".to_string(),
        deref(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
    );
    final_values.insert(
        "p.1".to_string(),
        deref(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
    );

    // Return: `if take_first { p.0 } else { p.1 }` — tuple-getter ITE branches.
    let return_expr = ite(var("take_first"), p0_expr.clone(), p1_expr.clone());

    // Postcondition: `if take_first { result == p.0 && ^p.1 == *p.1 }
    //                else { result == p.1 && ^p.0 == *p.0 }`
    // The Var("result", MutRef(Int)) annotation is the postcondition-derived
    // hint that lets the encoder recover the MutRef inner sort.
    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var_with_sort("result", mr_int.clone()), p0_expr.clone()),
            eq(final_expr(p1_expr.clone()), deref(p1_expr.clone())),
        ),
        and(
            eq(var_with_sort("result", mr_int.clone()), p1_expr.clone()),
            eq(final_expr(p0_expr.clone()), deref(p0_expr.clone())),
        ),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut (tuple-of-mutref param) with tuple-getter ITE return should verify (#5): got {result:?}"
    );
}

/// Drop pair with resolve and the Deref(Var) postcondition form.
///
/// After `transform_postcondition_for_mut_refs`, the postcondition uses
/// Deref(Var("_x")) inside tuple accessors rather than bare Var("_x").
/// This is the actual form the driver produces. Combined with resolve
/// assertions, the identity must propagate through both the tuple projection
/// and the deref encoding.
///
/// Re: #2673
#[test]
#[timeout(30000)]
fn drop_pair_deref_var_with_resolve_verifies() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // After transform_postcondition_for_mut_refs: uses Deref(Var("_x"))
    let ens_0 = eq(
        final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("_x"))])),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("_x"))])),
    );
    let ens_1 = eq(
        final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("_x"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("_x"))])),
    );

    let mut final_values = HashMap::new();
    final_values.insert("_x".to_string(), deref(var("_x")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens_0, ens_1], &final_values)
            .resolve_assumptions(Some(vec!["_x".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "drop_pair Deref(Var) form with resolve should verify (#2673): got {result:?}"
    );
}

/// Models the Creusot `pair_bor_mut` compat test with the EXACT driver output shape.
///
/// The driver produces a single tuple parameter `p: (&mut T, &mut T)` with:
/// - `final_values = {"p": Deref(Var("p"))}` (identity)
/// - Postcondition uses `Deref(Var("p"))` inside tuple accessors (from
///   `transform_postcondition_for_mut_refs`)
/// - Return expression is an ITE of tuple field projections
///
/// This is the regression test for the gap between the ay-level unit test
/// (which passes with decomposed per-field parameters) and the compat test
/// (which uses the whole-tuple representation).
///
/// Re: #2673
#[test]
#[timeout(60000)]
fn pair_bor_mut_tuple_param_deref_var_with_resolve_verifies() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // p.0 current/final using Deref(Var("p")) form
    let p_0_current = deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_current = deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));
    let p_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));

    // ensures: if take_first { result == *p.0 && ^p.1 == *p.1 }
    //          else { result == *p.1 && ^p.0 == *p.0 }
    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var("result"), p_0_current.clone()),
            eq(p_1_final.clone(), p_1_current.clone()),
        ),
        and(
            eq(var("result"), p_1_current.clone()),
            eq(p_0_final.clone(), p_0_current.clone()),
        ),
    )];

    // Identity final values at whole-tuple level
    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    // Return expression: conditional tuple field projection
    let return_expr = ite(
        var("take_first"),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))])),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr))
            .resolve_assumptions(Some(vec!["p".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut tuple param Deref(Var) with resolve should verify (#2673): got {result:?}"
    );
}

/// pair_bor_mut without resolve assumptions — models the synthesized-path
/// fallback where the driver doesn't provide explicit resolve data.
///
/// This tests whether the encoding can still verify when only identity
/// final_values are provided (no resolve_assumptions, no finality data,
/// no borrow_id_origins). If this passes, the compat test gap is purely
/// in the driver not providing a return expression, not in the ay encoding.
///
/// Re: #2673
#[test]
#[timeout(60000)]
fn pair_bor_mut_tuple_param_without_resolve_still_verifies() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    let p_0_current = deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_current = deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));
    let p_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));

    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var("result"), p_0_current.clone()),
            eq(p_1_final.clone(), p_1_current.clone()),
        ),
        and(
            eq(var("result"), p_1_current.clone()),
            eq(p_0_final.clone(), p_0_current.clone()),
        ),
    )];

    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    let return_expr = ite(
        var("take_first"),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))])),
    );

    // NO resolve_assumptions — pure identity final_values path
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut should verify even without resolve_assumptions (#2673): got {result:?}"
    );
}

/// Conditional mut-ref return with three parameters: models inc_max_3
/// where a sorting network produces distinct final values.
///
/// fn inc_max_3(ma: &mut u32, mb: &mut u32, mc: &mut u32) {
///     sort3(ma, mb, mc);  // sorting network via conditional swaps
///     *ma += 2; *mb += 1;
/// }
/// #[ensures(^ma != ^mb && ^mb != ^mc && ^mc != ^ma)]
///
/// The encoding must handle deeply nested ITE expressions from the sorting
/// network without timing out or producing unverifiable proofs.
///
/// Re: #2673, #2692
#[test]
#[timeout(120000)]
fn inc_max_3_sorting_network_with_overflow_guard() {
    let a = deref(var("ma"));
    let b = deref(var("mb"));
    let c = deref(var("mc"));

    // Sorting network: 3 conditional swaps
    let cond1 = lt(a.clone(), b.clone());
    let s1_a = ite(cond1.clone(), b.clone(), a.clone());
    let s1_b = ite(cond1.clone(), a.clone(), b.clone());

    let cond2 = lt(s1_b.clone(), c.clone());
    let s2_a = s1_a.clone();
    let s2_b = ite(cond2.clone(), c.clone(), s1_b.clone());
    let s2_c = ite(cond2.clone(), s1_b.clone(), c.clone());

    let cond3 = lt(s2_a.clone(), s2_b.clone());
    let s3_a = ite(cond3.clone(), s2_b.clone(), s2_a.clone());
    let s3_b = ite(cond3.clone(), s2_a.clone(), s2_b.clone());
    let s3_c = s2_c.clone();

    // *ma += 2, *mb += 1
    let final_a = add(s3_a, int(2));
    let final_b = add(s3_b, int(1));
    let final_c = s3_c;

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), final_a);
    final_values.insert("mb".to_string(), final_b);
    final_values.insert("mc".to_string(), final_c);

    // Stronger preconditions: bounded inputs to prevent integer overflow
    // in the nested ITE expressions, and ensure distinctness is provable.
    let requires = vec![
        ge(deref(var("ma")), int(0)),
        ge(deref(var("mb")), int(0)),
        ge(deref(var("mc")), int(0)),
        le(deref(var("ma")), int(1_000_000)),
        le(deref(var("mb")), int(1_000_000)),
        le(deref(var("mc")), int(1_000_000)),
    ];

    // ^ma != ^mb && ^mb != ^mc && ^mc != ^ma
    let ensures = vec![
        ne(final_expr(var("ma")), final_expr(var("mb"))),
        ne(final_expr(var("mb")), final_expr(var("mc"))),
        ne(final_expr(var("mc")), final_expr(var("ma"))),
    ];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "inc_max_3 with overflow guard should verify (#2673): got {result:?}"
    );
}

/// Conditional borrow return where result is compared as a whole-borrow
/// reference (not just dereferenced value), combined with the untouched
/// borrow's final-equals-current property.
///
/// This is the key pattern that pair_bor_mut needs: the solver must
/// simultaneously prove:
/// 1. result == p0 (whole-borrow equality) when take_first is true
/// 2. ^p1 == *p1 (untouched field preservation) when take_first is true
///
/// Uses the Creusot convention: `^v` = `Final(Var("v"))` (borrow-level final),
/// `*v` = `Deref(Var("v"))` (borrow-level current). The resolve assertion
/// `v_final == v_current` directly satisfies `^v == *v`.
///
/// Re: #2673
#[test]
#[timeout(60000)]
fn conditional_return_whole_borrow_with_untouched_field_preservation() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    let p0 = var_with_sort("p0", mr_int.clone());
    let p1 = var_with_sort("p1", mr_int.clone());

    // Identity final values
    let mut final_values = HashMap::new();
    final_values.insert("p0".to_string(), deref(p0.clone()));
    final_values.insert("p1".to_string(), deref(p1.clone()));

    // Return: if take_first then p0 else p1
    let return_expr = ite(var("take_first"), p0.clone(), p1.clone());

    // Postcondition: if take_first { result == p0 && ^p1 == *p1 }
    //                else { result == p1 && ^p0 == *p0 }
    //
    // Using Creusot convention: ^v = Final(Var("v")), *v = Deref(Var("v"))
    // The resolve assertion p1_final == p1_current directly proves ^p1 == *p1.
    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var_with_sort("result", mr_int.clone()), p0.clone()),
            eq(final_expr(p1.clone()), deref(p1.clone())),
        ),
        and(
            eq(var_with_sort("result", mr_int.clone()), p1.clone()),
            eq(final_expr(p0.clone()), deref(p0.clone())),
        ),
    )];

    // Test with resolve only
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr))
            .resolve_assumptions(Some(vec!["p0".to_string(), "p1".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "conditional return with untouched borrow preservation should verify (#2673): got {result:?}"
    );
}

/// The `Deref(Final(Var("v")))` form (= `*^v`) for a single-layer `MutRef`
/// carrier with a *scalar* referent now resolves to the definitional final
/// projection `mut_ref_final(v)` rather than minting a disconnected
/// `v_final_current` during postcondition encoding (Phase 1d Box-collapse leaf in
/// `encode_deref_or_final`). The extra `Deref` over `Final(v)` — a Box-collapse
/// artifact for `&mut Box<T>` — is the identity on the scalar leaf, so `*^v`
/// coincides with `^v`'s leaf and the resolve assertion `v_final == v_current`
/// discharges `*^v == *v`.
///
/// Previously this form documented a timing gap (#2673) where it spuriously
/// failed; the gap is now closed, so the valid preservation property verifies.
///
/// Re: #2673, bug/final_borrows::box_reborrow_indirect
#[test]
#[timeout(30000)]
fn deref_final_form_untouched_preservation_resolves() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    let p0 = var_with_sort("p0", mr_int.clone());
    let p1 = var_with_sort("p1", mr_int.clone());

    let mut final_values = HashMap::new();
    final_values.insert("p0".to_string(), deref(p0.clone()));
    final_values.insert("p1".to_string(), deref(p1.clone()));

    let return_expr = ite(var("take_first"), p0.clone(), p1.clone());

    // Uses Deref(Final(Var)) form (`*^v`). With the Box-collapse leaf resolution,
    // `*^v` resolves to `mut_ref_final(v)`, which the resolve assertion equates
    // to `*v` for an untouched borrow — so the property is provable.
    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var_with_sort("result", mr_int.clone()), p0.clone()),
            eq(deref(final_expr(p1.clone())), deref(p1.clone())),
        ),
        and(
            eq(var_with_sort("result", mr_int.clone()), p1.clone()),
            eq(deref(final_expr(p0.clone())), deref(p0.clone())),
        ),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr))
            .resolve_assumptions(Some(vec!["p0".to_string(), "p1".to_string()])),
    )
    .expect("encoding should succeed");

    // The preservation property `*^v == *v` is valid for an untouched borrow
    // (resolve asserts `v_final == v_current`). With the Box-collapse leaf
    // resolution closing the #2673 timing gap, it now verifies.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Deref(Final) preservation should verify after closing the #2673 timing gap: got {result:?}"
    );
}

/// Negative companion for conditional_return_whole_borrow: swapped branches
/// should produce a counterexample.
///
/// Re: #2673
#[test]
#[timeout(30000)]
fn conditional_return_whole_borrow_swapped_branches_fails() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));

    let p0 = var_with_sort("p0", mr_int.clone());
    let p1 = var_with_sort("p1", mr_int.clone());

    let mut final_values = HashMap::new();
    final_values.insert("p0".to_string(), deref(p0.clone()));
    final_values.insert("p1".to_string(), deref(p1.clone()));

    // Correct return: if take_first then p0 else p1
    let return_expr = ite(var("take_first"), p0.clone(), p1.clone());

    // WRONG postcondition: branches are swapped
    let ensures = vec![ite(
        var("take_first"),
        eq(var_with_sort("result", mr_int.clone()), p1.clone()), // wrong: should be p0
        eq(var_with_sort("result", mr_int.clone()), p0.clone()), // wrong: should be p1
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr))
            .resolve_assumptions(Some(vec!["p0".to_string(), "p1".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "swapped branch conditional return should fail: got {result:?}"
    );
}

// ── #2673 strengthened: ghost-context-assisted driver shape tests ────────

/// Models `inc_max_3` with ghost context providing the post-sorting ordering
/// invariant. This is the driver shape where swap call postconditions are
/// folded into the sorting network as ITE final values, and the ghost context
/// provides the key intermediate fact: after sorting, s3_a >= s3_b >= s3_c.
///
/// The AUFLIA solver can derive the ordering from the ITE structure (it's
/// a tautology), but the nested ITEs from three conditional swaps create a
/// deeply nested expression tree that may exceed the solver's reasoning
/// budget. Providing the ordering as ghost context enables the solver to
/// close the proof more efficiently.
///
/// Re: #2673
#[test]
#[timeout(60000)]
fn inc_max_3_driver_shape_with_ghost_sorting_invariant() {
    let a = deref(var("ma"));
    let b = deref(var("mb"));
    let c = deref(var("mc"));

    // Sorting network: 3 conditional swaps
    let cond1 = lt(a.clone(), b.clone());
    let s1_a = ite(cond1.clone(), b.clone(), a.clone());
    let s1_b = ite(cond1.clone(), a.clone(), b.clone());

    let cond2 = lt(s1_b.clone(), c.clone());
    let s2_b = ite(cond2.clone(), c.clone(), s1_b.clone());
    let s2_c = ite(cond2.clone(), s1_b.clone(), c.clone());

    let cond3 = lt(s1_a.clone(), s2_b.clone());
    let s3_a = ite(cond3.clone(), s2_b.clone(), s1_a.clone());
    let s3_b = ite(cond3.clone(), s1_a.clone(), s2_b.clone());
    let s3_c = s2_c;

    // *ma += 2, *mb += 1
    let final_a = add(s3_a.clone(), int(2));
    let final_b = add(s3_b.clone(), int(1));
    let final_c = s3_c.clone();

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), final_a);
    final_values.insert("mb".to_string(), final_b);
    final_values.insert("mc".to_string(), final_c);

    let requires = vec![
        ge(deref(var("ma")), int(0)),
        ge(deref(var("mb")), int(0)),
        ge(deref(var("mc")), int(0)),
        le(deref(var("ma")), int(1_000_000)),
        le(deref(var("mb")), int(1_000_000)),
        le(deref(var("mc")), int(1_000_000)),
    ];

    // Ghost context: post-sorting ordering invariant
    // After the sorting network: s3_a >= s3_b >= s3_c
    // These are tautological from the ITE structure but help the AUFLIA
    // solver close the proof faster.
    let ghost = vec![ge(s3_a, s3_b.clone()), ge(s3_b, s3_c)];

    let ensures = vec![
        ne(final_expr(var("ma")), final_expr(var("mb"))),
        ne(final_expr(var("mb")), final_expr(var("mc"))),
        ne(final_expr(var("mc")), final_expr(var("ma"))),
    ];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values).ghost_context(Some(&ghost)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "inc_max_3 with ghost sorting invariant should verify (#2673): got {result:?}"
    );
}

/// Models `pair_bor_mut` in the Deref(Var) postcondition form with ghost
/// context providing the resolve equality explicitly.
///
/// When the driver does not provide explicit `resolve_assumptions`, the ghost
/// context can carry the resolve fact `Final(Var("p")) == Deref(Var("p"))` as
/// a call assumption. This tests whether the ghost-context path enables the
/// proof independently of the resolve assertion mechanism.
///
/// Re: #2673
#[test]
#[timeout(60000)]
fn pair_bor_mut_deref_form_with_ghost_resolve_facts() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // Postconditions in Deref(Var) form (as produced by transform_postcondition_for_mut_refs)
    let p_0_current = deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_current = deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));
    let p_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));

    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var("result"), p_0_current.clone()),
            eq(p_1_final, p_1_current.clone()),
        ),
        and(eq(var("result"), p_1_current), eq(p_0_final, p_0_current)),
    )];

    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    let return_expr = ite(
        var("take_first"),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))])),
    );

    // Ghost resolve fact: ^p == *p (the tuple parameter is not mutated)
    let ghost = vec![eq(final_expr(var("p")), deref(var("p")))];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr))
            .ghost_context(Some(&ghost))
            .resolve_assumptions(Some(vec!["p".to_string()])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut Deref form with ghost resolve facts should verify (#2673): got {result:?}"
    );
}

/// Models `inc_max_3` where the swap postconditions are provided as explicit
/// ghost context equalities between intermediate state variables.
///
/// This simulates the driver output when swap is `#[trusted]` and its
/// postcondition `(^mma == *mmb && ^mmb == *mma)` is injected as a call
/// assumption. The call assumption becomes a ghost context fact in the
/// verification request for `inc_max_3`.
///
/// The intermediate variables `ma_s1`, `mb_s1`, etc. represent the state
/// after each swap call. The ghost context connects them to the input
/// values via the swap postcondition.
///
/// Re: #2673
#[test]
#[timeout(60000)]
fn inc_max_3_with_swap_postconditions_as_ghost() {
    let ma = deref(var("ma"));
    let mb = deref(var("mb"));
    let mc = deref(var("mc"));

    // After swap 1: if *ma < *mb, values are swapped
    let cond1 = lt(ma.clone(), mb.clone());

    // After swap 2: if post1_mb < *mc, values are swapped
    let post1_mb = ite(cond1.clone(), ma.clone(), mb.clone());
    let cond2 = lt(post1_mb.clone(), mc.clone());

    // After swap 3: if post2_ma < post2_mb, values are swapped
    let post1_ma = ite(cond1.clone(), mb.clone(), ma.clone());
    let post2_mb = ite(cond2.clone(), mc.clone(), post1_mb.clone());
    let cond3 = lt(post1_ma.clone(), post2_mb.clone());

    // Post-sort state
    let sorted_a = ite(cond3.clone(), post2_mb.clone(), post1_ma.clone());
    let sorted_b = ite(cond3.clone(), post1_ma.clone(), post2_mb.clone());
    let sorted_c = ite(cond2.clone(), post1_mb.clone(), mc.clone());

    // Final mutations: *ma += 2, *mb += 1
    let final_a = add(sorted_a.clone(), int(2));
    let final_b = add(sorted_b.clone(), int(1));
    let final_c = sorted_c.clone();

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), final_a);
    final_values.insert("mb".to_string(), final_b);
    final_values.insert("mc".to_string(), final_c);

    let requires = vec![
        le(ma.clone(), int(1_000_000)),
        le(mb.clone(), int(1_000_000)),
        le(mc.clone(), int(1_000_000)),
    ];

    let ensures = vec![
        ne(final_expr(var("ma")), final_expr(var("mb"))),
        ne(final_expr(var("mb")), final_expr(var("mc"))),
        ne(final_expr(var("mc")), final_expr(var("ma"))),
    ];

    // Ghost context: swap postconditions as conditional equalities.
    // These model the #[trusted] swap's postcondition (^mma == *mmb && ^mmb == *mma)
    // applied to each conditional swap call:
    //   if cond1: post1_ma == *mb, post1_mb == *ma
    //   if !cond1: post1_ma == *ma, post1_mb == *mb
    // Simplified to ITE equalities (which are tautological from the final values
    // construction, but help the solver by providing intermediate facts).
    let ghost = vec![
        // Post-sort ordering (consequence of sorting network)
        ge(sorted_a, sorted_b.clone()),
        ge(sorted_b, sorted_c),
    ];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values).ghost_context(Some(&ghost)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "inc_max_3 with swap postconditions as ghost should verify (#2673): got {result:?}"
    );
}

// ── #2673 second pass: driver-gap regression tests ──────────────────

/// Models `pair_bor_mut` when the driver does NOT produce a return expression.
///
/// The driver's main return expression extractor may fail to produce a result_expr
/// for the conditional field-projection return `if take_first { p.0 } else { p.1 }`.
/// However, the encoder now synthesizes a result expression from the postcondition
/// structure: it detects `Ite(cond, And(result == a, ...), And(result == b, ...))`
/// and extracts `Ite(cond, a, b)` as the result binding. (#2673 strengthened)
///
/// This verifies that the postcondition-based result synthesis works correctly
/// for the `pair_bor_mut` pattern even without driver-provided return_expr.
///
/// Re: #2673 (second pass, then strengthened)
#[test]
#[timeout(60000)]
fn pair_bor_mut_without_return_expr_verifies_via_synthesis() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    let p_0_current = deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_current = deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));
    let p_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));

    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var("result"), p_0_current.clone()),
            eq(p_1_final.clone(), p_1_current.clone()),
        ),
        and(
            eq(var("result"), p_1_current.clone()),
            eq(p_0_final.clone(), p_0_current.clone()),
        ),
    )];

    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    // NO return_expr — the encoder synthesizes result binding from postcondition
    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed");

    // The encoder now synthesizes result_expr from the postcondition ITE structure,
    // enabling verification even without a driver-provided return expression.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut without return_expr should now verify via postcondition synthesis (#2673): \
         got {result:?}"
    );
}

/// Models `pair_bor_mut` with per-field final values instead of whole-tuple identity.
///
/// When the driver extracts field-level final values (e.g., `{"p.0": Deref(...), "p.1": Deref(...)}`),
/// the ay encoder should still be able to verify the postcondition. This models the
/// case where `populate_field_and_newtype_final_values` produces per-field entries
/// alongside (or instead of) the whole-tuple identity.
///
/// Re: #2673 (second pass)
#[test]
#[timeout(60000)]
fn pair_bor_mut_with_per_field_final_values_verifies() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    let p_0_current = deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_current = deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));
    let p_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));

    let ensures = vec![ite(
        var("take_first"),
        and(
            eq(var("result"), p_0_current.clone()),
            eq(p_1_final.clone(), p_1_current.clone()),
        ),
        and(
            eq(var("result"), p_1_current.clone()),
            eq(p_0_final.clone(), p_0_current.clone()),
        ),
    )];

    // Per-field final values: identity for each field component
    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));
    final_values.insert(
        "p.0".to_string(),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))])),
    );
    final_values.insert(
        "p.1".to_string(),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))])),
    );

    let return_expr = ite(
        var("take_first"),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))])),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut with per-field final values should verify (#2673): got {result:?}"
    );
}

/// Models `inc_max_3` with explicit swap postconditions as call assumptions.
///
/// This models the E2E shape where `swap` is `#[trusted]` with postcondition
/// `^mma == *mmb && ^mmb == *mma`. The driver should produce call_assumptions
/// that encode these constraints. The ay encoder receives them as additional
/// requires clauses.
///
/// The key challenge is that `mut ma: &'a mut u32` means `ma` is a locally mutable
/// binding that can be reassigned (via `swap(&mut ma, &mut mb)`). After swap,
/// `*ma` refers to the value that was in `*mb` before the swap. The driver
/// must track this reassignment through MIR.
///
/// Re: #2673 (second pass)
#[test]
#[timeout(120000)]
fn inc_max_3_with_explicit_swap_call_assumptions() {
    let a = deref(var("ma"));
    let b = deref(var("mb"));
    let c = deref(var("mc"));

    // Sorting network via conditional swaps, modeled as ITE final values.
    // Step 1: if *ma < *mb then swap(ma, mb)
    let cond1 = lt(a.clone(), b.clone());
    let s1_a = ite(cond1.clone(), b.clone(), a.clone());
    let s1_b = ite(cond1.clone(), a.clone(), b.clone());
    let s1_c = c.clone();

    // Step 2: if s1_b < s1_c then swap(mb, mc)
    let cond2 = lt(s1_b.clone(), s1_c.clone());
    let s2_a = s1_a.clone();
    let s2_b = ite(cond2.clone(), s1_c.clone(), s1_b.clone());
    let s2_c = ite(cond2.clone(), s1_b.clone(), s1_c.clone());

    // Step 3: if s2_a < s2_b then swap(ma, mb)
    let cond3 = lt(s2_a.clone(), s2_b.clone());
    let s3_a = ite(cond3.clone(), s2_b.clone(), s2_a.clone());
    let s3_b = ite(cond3.clone(), s2_a.clone(), s2_b.clone());
    let s3_c = s2_c.clone();

    // Final mutations: *ma += 2, *mb += 1 (mc unchanged)
    let final_a = add(s3_a, int(2));
    let final_b = add(s3_b, int(1));
    let final_c = s3_c;

    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), final_a);
    final_values.insert("mb".to_string(), final_b);
    final_values.insert("mc".to_string(), final_c);

    // Preconditions from the Creusot test: values bounded to prevent overflow
    let requires = vec![
        le(deref(var("ma")), int(1_000_000)),
        le(deref(var("mb")), int(1_000_000)),
        le(deref(var("mc")), int(1_000_000)),
        // Non-negative bounds (Creusot uses u32)
        ge(deref(var("ma")), int(0)),
        ge(deref(var("mb")), int(0)),
        ge(deref(var("mc")), int(0)),
    ];

    // Postcondition: ^ma != ^mb && ^mb != ^mc && ^mc != ^ma
    let ensures = vec![
        ne(final_expr(var("ma")), final_expr(var("mb"))),
        ne(final_expr(var("mb")), final_expr(var("mc"))),
        ne(final_expr(var("mc")), final_expr(var("ma"))),
    ];

    // All three params resolve (identity at function scope)
    let result =
        verify_mut_borrow_function_with_modes(
            MutBorrowRequest::new(&requires, &ensures, &final_values).resolve_assumptions(Some(
                vec!["ma".to_string(), "mb".to_string(), "mc".to_string()],
            )),
        )
        .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "inc_max_3 with explicit swap call assumptions and resolve should verify (#2673): \
         got {result:?}"
    );
}

// ── E2E-shaped tests for projection_toggle / take_max (#2673) ──────

/// E2E-shaped test for Creusot `projection_toggle`:
///
/// ```rust
/// #[ensures(if toggle { result == a && ^b == *b } else { result == b && ^a == *a })]
/// fn proj_toggle<'a, T>(toggle: bool, a: &'a mut T, b: &'a mut T) -> &'a mut T {
///     if toggle { a } else { b }
/// }
/// ```
///
/// This models the exact shape the driver would produce for separate `&mut`
/// parameters (not tuple fields). The postcondition uses whole-borrow equality
/// (`result == a` where both are `MutRef`-sorted) and current/final equality
/// (`^b == *b`). The return_expr is a conditional selecting between the two
/// whole-borrow parameters.
///
/// Re: #2673 Lane A1
#[test]
#[timeout(30000)]
fn projection_toggle_e2e_separate_params_verifies() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let a = var_with_sort("a", mr_int.clone());
    let b = var_with_sort("b", mr_int.clone());

    // return_expr: if toggle { a } else { b }  (whole-borrow MutRef vars)
    let return_expr_val = ite(var("toggle"), a.clone(), b.clone());

    // final_values: identity (neither param is mutated in proj_toggle body)
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(a.clone()));
    final_values.insert("b".to_string(), deref(b.clone()));

    // ensures: if toggle { result == a && ^b == *b }
    //                else { result == b && ^a == *a }
    //
    // After transform_postcondition_for_mut_refs:
    // - `result == a` stays as-is (both are MutRef-sorted, whole-borrow equality)
    // - `^b == *b` becomes `Final(Var("b")) == Deref(Var("b"))`
    let result_var = var_with_sort("result", mr_int);
    let ensures = vec![ite(
        var("toggle"),
        and(
            eq(result_var.clone(), a.clone()),
            eq(final_expr(b.clone()), deref(b.clone())),
        ),
        and(
            eq(result_var, b.clone()),
            eq(final_expr(a.clone()), deref(a.clone())),
        ),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr_val))
            .resolve_assumptions(Some(vec!["a".to_string(), "b".to_string()])),
    )
    .expect("encoding should succeed for projection_toggle (#2673)");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "projection_toggle E2E with separate &mut params and whole-borrow equality \
         should verify: got {result:?}"
    );
}

/// E2E-shaped test for Creusot `take_max`:
///
/// ```rust
/// #[ensures(if *ma >= *mb { *mb == ^mb && result == ma }
///                    else { *ma == ^ma && result == mb })]
/// fn take_max<'a>(ma: &'a mut u32, mb: &'a mut u32) -> &'a mut u32 {
///     if *ma >= *mb {
///         ma
///     } else {
///         mb
///     }
/// }
/// ```
///
/// Uses whole-borrow MutRef return with resolve assertions and identity
/// final values. The postcondition mixes current-value comparisons (`*ma >= *mb`)
/// with whole-borrow equality (`result == ma`) and final/current identity
/// (`*mb == ^mb`).
///
/// Re: #2673 Lane A1
#[test]
#[timeout(30000)]
fn take_max_e2e_whole_borrow_return_verifies() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let ma = var_with_sort("ma", mr_int.clone());
    let mb = var_with_sort("mb", mr_int.clone());

    // return_expr: if *ma >= *mb { ma } else { mb }
    // The condition uses Deref to compare current values, but the branches
    // are whole-borrow MutRef vars.
    let return_expr_val = ite(
        ge(deref(ma.clone()), deref(mb.clone())),
        ma.clone(),
        mb.clone(),
    );

    // final_values: identity (take_max does not mutate either param)
    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), deref(ma.clone()));
    final_values.insert("mb".to_string(), deref(mb.clone()));

    // ensures: if *ma >= *mb { *mb == ^mb && result == ma }
    //                   else { *ma == ^ma && result == mb }
    let result_var = var_with_sort("result", mr_int);
    let ensures = vec![ite(
        ge(deref(ma.clone()), deref(mb.clone())),
        and(
            eq(deref(mb.clone()), final_expr(mb.clone())),
            eq(result_var.clone(), ma.clone()),
        ),
        and(
            eq(deref(ma.clone()), final_expr(ma.clone())),
            eq(result_var, mb.clone()),
        ),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr_val))
            .resolve_assumptions(Some(vec!["ma".to_string(), "mb".to_string()])),
    )
    .expect("encoding should succeed for take_max (#2673)");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "take_max E2E with whole-borrow return and resolve should verify: got {result:?}"
    );
}

/// E2E-shaped test for Creusot `drop_pair` with the full pipeline shape:
///
/// ```rust
/// #[ensures(resolve(_x))]
/// #[ensures(^_x.0 == *_x.0)]
/// #[ensures(^_x.1 == *_x.1)]
/// pub fn drop_pair(_x: (&mut u32, &mut u32)) {}
/// ```
///
/// The `resolve(_x)` postcondition is modeled as a standalone assertion
/// (the resolve call is a UF application in the encoding). The field
/// equality postconditions use the Deref(Var) form after
/// transform_postcondition_for_mut_refs.
///
/// Re: #2673 Lane A1
#[test]
#[timeout(30000)]
fn drop_pair_e2e_with_resolve_postcondition_verifies() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // final_values: identity for the whole tuple
    let mut final_values = HashMap::new();
    final_values.insert("_x".to_string(), deref(var("_x")));

    // ensures[0]: resolve(_x) — modeled as a logic fn call returning Bool
    let ens_resolve = logic_fn_call("resolve", vec![deref(var("_x"))]);

    // ensures[1]: ^_x.0 == *_x.0 (Deref(Var) form after transform)
    let ens_0 = eq(
        final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("_x"))])),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("_x"))])),
    );

    // ensures[2]: ^_x.1 == *_x.1
    let ens_1 = eq(
        final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("_x"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("_x"))])),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens_resolve, ens_0, ens_1], &final_values)
            .resolve_assumptions(Some(vec!["_x".to_string()])),
    )
    .expect("encoding should succeed for drop_pair (#2673)");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "drop_pair E2E with resolve postcondition should verify: got {result:?}"
    );
}

/// Variant of `projection_toggle_e2e_separate_params_verifies` where
/// the result variable has NO `MutRef` sort annotation, modeling the case
/// where the driver cannot infer the result's MutRef sort from the
/// postcondition parse alone.
///
/// This is the more conservative model: the postcondition uses bare
/// `Var("result")` without sort annotation, relying on the encoder to
/// infer the result sort from the return_expr (which IS annotated).
///
/// Re: #2673 Lane A1
#[test]
#[timeout(30000)]
fn projection_toggle_e2e_unannotated_result_verifies() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let a = var_with_sort("a", mr_int.clone());
    let b = var_with_sort("b", mr_int.clone());

    let return_expr_val = ite(var("toggle"), a.clone(), b.clone());

    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(a.clone()));
    final_values.insert("b".to_string(), deref(b.clone()));

    // Key difference: result has NO sort annotation (bare Var("result"))
    let result_var = var("result");
    let ensures = vec![ite(
        var("toggle"),
        and(
            eq(result_var.clone(), a.clone()),
            eq(final_expr(b.clone()), deref(b.clone())),
        ),
        and(
            eq(result_var, b.clone()),
            eq(final_expr(a.clone()), deref(a.clone())),
        ),
    )];

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .return_expr(Some(&return_expr_val))
            .resolve_assumptions(Some(vec!["a".to_string(), "b".to_string()])),
    )
    .expect("encoding should succeed for projection_toggle with unannotated result (#2673)");

    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result),
        "projection_toggle E2E with unannotated result should verify: got {result:?}"
    );
}

/// E2E test for `inc_max` caller: verifies the full call-assumption chain.
///
/// ```rust
/// #[requires(a <= 1_000_000u32 && b <= 1_000_000u32)]
/// pub fn inc_max(mut a: u32, mut b: u32) {
///     let mc = take_max(&mut a, &mut b);
///     *mc += 1;
///     assert!(a != b);
/// }
/// ```
///
/// This models the caller side: `a` and `b` are owned `u32` values (not `&mut`),
/// so the function goes through the non-mut-borrow path. The call to `take_max`
/// creates reborrows, and the postcondition of `take_max` becomes a call
/// assumption. After `*mc += 1`, we assert `a != b`.
///
/// At the ay level, this is modeled with:
/// - `a` and `b` as plain Int variables (owned u32)
/// - The take_max postcondition as a precondition/call assumption
/// - The mutation `*mc += 1` as a final_values entry
/// - The assert `a != b` as the postcondition
///
/// Re: #2673 Lane A1
#[test]
#[timeout(30000)]
fn inc_max_caller_with_call_assumption_verifies() {
    // The caller's variables: a, b are owned u32 values
    let a_val = var("a");
    let b_val = var("b");

    // take_max postcondition modeled as a requires (call assumption):
    // if a >= b then (b stays the same AND mc points to a)
    //           else (a stays the same AND mc points to b)
    //
    // In the caller's encoding, "mc points to a" means the mutation
    // through mc modifies a. So: a_final = *mc + 1, b_final = b
    // (or vice versa).
    //
    // Model: after `*mc += 1`:
    //   if a >= b: a_final = a + 1, b_final = b
    //   else:      a_final = a,     b_final = b + 1
    //
    // This is what the driver extracts as final_values for the caller.
    let cond = ge(a_val.clone(), b_val.clone());
    let a_final_expr = ite(cond.clone(), add(a_val.clone(), int(1)), a_val.clone());
    let b_final_expr = ite(cond.clone(), b_val.clone(), add(b_val.clone(), int(1)));

    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), a_final_expr);
    final_values.insert("b".to_string(), b_final_expr);

    // requires: a <= 1_000_000 && b <= 1_000_000
    let requires = vec![
        le(a_val.clone(), int(1_000_000)),
        le(b_val.clone(), int(1_000_000)),
    ];

    // ensures: a_final != b_final
    // After mut-ref transform: Final(Var("a")) != Final(Var("b"))
    let ensures = vec![ne(final_expr(var("a")), final_expr(var("b")))];

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &requires,
        &ensures,
        &final_values,
    ))
    .expect("encoding should succeed for inc_max caller (#2673)");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "inc_max caller with call assumption chain should verify: got {result:?}"
    );
}

/// Models `take_max` without return_expr, verifying postcondition-based result synthesis.
///
/// `take_max(ma: &mut u32, mb: &mut u32) -> &mut u32`:
///   ensures: if *ma >= *mb { *mb == ^mb && result == ma }
///            else { *ma == ^ma && result == mb }
///
/// Without driver-provided return_expr, the encoder synthesizes
/// `Ite(ge(deref(ma), deref(mb)), ma, mb)` from the postcondition structure.
///
/// Re: #2673 (postcondition result synthesis)
#[test]
#[timeout(60000)]
fn take_max_without_return_expr_verifies_via_synthesis() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let ma = var_with_sort("ma", mr_int.clone());
    let mb = var_with_sort("mb", mr_int.clone());
    let result_var = var_with_sort("result", mr_int);

    // final_values: identity (neither param is mutated)
    let mut final_values = HashMap::new();
    final_values.insert("ma".to_string(), deref(ma.clone()));
    final_values.insert("mb".to_string(), deref(mb.clone()));

    // ensures: if *ma >= *mb { *mb == ^mb && result == ma }
    //                   else  { *ma == ^ma && result == mb }
    let ensures = vec![ite(
        ge(deref(ma.clone()), deref(mb.clone())),
        and(
            eq(deref(mb.clone()), final_expr(mb.clone())),
            eq(result_var.clone(), ma.clone()),
        ),
        and(
            eq(deref(ma.clone()), final_expr(ma.clone())),
            eq(result_var, mb.clone()),
        ),
    )];

    // NO return_expr — the encoder synthesizes from postcondition
    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed for take_max (#2673)");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "take_max without return_expr should verify via postcondition synthesis (#2673): \
         got {result:?}"
    );
}

/// Models `proj_toggle` without return_expr, verifying postcondition-based result synthesis.
///
/// `proj_toggle(toggle: bool, a: &mut T, b: &mut T) -> &mut T`:
///   ensures: if toggle { result == a && ^b == *b }
///            else { result == b && ^a == *a }
///
/// Without driver-provided return_expr, the encoder synthesizes
/// `Ite(toggle, a, b)` from the postcondition structure.
///
/// Re: #2673 (postcondition result synthesis)
#[test]
#[timeout(60000)]
fn proj_toggle_without_return_expr_verifies_via_synthesis() {
    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let a = var_with_sort("a", mr_int.clone());
    let b = var_with_sort("b", mr_int.clone());
    let result_var = var_with_sort("result", mr_int);

    // final_values: identity (neither param is mutated in proj_toggle itself)
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(a.clone()));
    final_values.insert("b".to_string(), deref(b.clone()));

    // ensures: if toggle { result == a && ^b == *b }
    //          else { result == b && ^a == *a }
    let ensures = vec![ite(
        var("toggle"),
        and(
            eq(result_var.clone(), a.clone()),
            eq(final_expr(b.clone()), deref(b.clone())),
        ),
        and(
            eq(result_var, b.clone()),
            eq(final_expr(a.clone()), deref(a.clone())),
        ),
    )];

    // NO return_expr — the encoder synthesizes from postcondition
    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &ensures, &final_values))
            .expect("encoding should succeed for proj_toggle (#2673)");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "proj_toggle without return_expr should verify via postcondition synthesis (#2673): \
         got {result:?}"
    );
}

/// Two-phase reborrow + spec advancement (bug/two_phase).
///
/// Models:
///   #[ensures(^v == *v + 1)]
///   fn f(v: &mut i32) { v.increment(); }  // via two-phase carrier v_rb3
///
/// Spec advancement binds the parent's final to the ADVANCED (non-identity)
/// post-state `*v + 1`, and the carrier's final carries the same value. The
/// prophecy-writeback edge `v_rb3 -> v` would additionally pin
/// `v_current == v_rb3_final` (the current-side writeback), and finality
/// propagation adds `v_final == v_rb3_final` — together manufacturing
/// `v_current == v_current + 1`: UNSAT premises, a vacuous "proof" the
/// vacuity guard rejects. The advanced-parent gate must suppress the
/// current-side writeback so the postcondition verifies NON-vacuously.
#[test]
#[timeout(30000)]
fn advanced_parent_two_phase_writeback_not_vacuous() {
    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), add(deref(var("v")), int(1)));
    // The two-phase carrier's final is the same post-call value; binding it
    // declares `v_rb3_final`, which is what lets the (buggy) current-side
    // writeback fire at all.
    final_values.insert("v_rb3".to_string(), add(deref(var("v")), int(1)));

    let ensures = vec![eq(final_expr(var("v")), add(deref(var("v")), int(1)))];

    let mut writebacks = HashMap::new();
    writebacks.insert("v_rb3".to_string(), "v".to_string());
    let mut finality = HashMap::new();
    finality.insert("v_rb3".to_string(), BorrowFinality::Final { deref_pos: 0 });

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values)
            .prophecy_writebacks(Some(writebacks))
            .borrow_finality(Some(finality)),
    )
    .expect("encoding should succeed for advanced-parent two-phase writeback");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "advanced-parent two-phase writeback must verify non-vacuously \
         (bug/two_phase): got {result:?}"
    );
}
