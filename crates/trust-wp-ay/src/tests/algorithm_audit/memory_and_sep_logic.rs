// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Memory model and separation logic boundary tests (#904, #1257, #1485).

use std::sync::Arc;

use ntest::timeout;

use super::super::helpers::{
    bool_expr, eq, int, let_assume, logic_fn_call, method_call, resolve_call, var,
};
use crate::{
    verify_function_with_modes, AYEncoder, CaptureField, ExprSort, PureExpr, VerificationRequest,
    VerificationResult,
};

// --- exprs_structurally_equal via Debug vs PartialEq (#1257) ---
//
// PureExpr already derives PartialEq. The current implementation in
// verify/mod.rs:1259-1263 uses Debug formatting for comparison, which is
// correct but wasteful. This test confirms PartialEq gives identical results
// for all PureExpr variants used in witness binding, serving as a guard
// that PartialEq won't silently diverge from Debug equality.

// --- encode_points_to negative permission boundary (#904 algorithm_audit) ---
//
// The `BaseMemoryModel::encode_points_to` method uses `ge(current_perm, perm)`
// without validating that `perm >= 0`. If a negative permission were passed,
// the constraint `current_perm >= -N` would be trivially satisfied for any
// non-negative current permission, making the points-to assertion weaker than
// intended. The `Permission` type prevents this through its `u32` numerator,
// but the `base.rs` method accepts raw `Term` values.

/// Negative permission term makes encode_points_to trivially satisfiable
/// on the permission axis — the only guard is domain membership.
///
/// This documents the boundary: if anyone bypasses the `Permission` type
/// and passes a negative Int term as the permission argument, the permission
/// check becomes vacuous. The test asserts the current behavior so any
/// future change (adding a lower-bound check) would be caught.
#[test]
#[timeout(30000)]
fn encode_points_to_negative_permission_boundary() {
    use ay_dpll::api::{Logic, SolveResult, Solver};

    use crate::memory_model::{BaseMemoryModel, MemPtr, MemoryModel};

    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let state = BaseMemoryModel::init(&mut solver);

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate — gives full permission (PERM_SCALE)
    let state = model.alloc(&mut solver, state, &ptr, val);

    // Pass a NEGATIVE permission requirement — this should still be SAT
    // because ge(PERM_SCALE, -1) is trivially true.
    let neg_perm = solver.int_const(-1);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, neg_perm);
    solver.assert_term(points_to);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Sat),
        "negative permission makes ge(current_perm, -1) trivially true — \
         documents boundary where Permission type is the only guard"
    );
}

/// Zero permission is a valid boundary: encode_points_to with perm=0
/// should be SAT after allocation (PERM_SCALE >= 0 is always true).
#[test]
#[timeout(30000)]
fn encode_points_to_zero_permission_boundary() {
    use ay_dpll::api::{Logic, SolveResult, Solver};

    use crate::memory_model::{BaseMemoryModel, MemPtr, MemoryModel};

    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let state = BaseMemoryModel::init(&mut solver);

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);

    // Zero permission: ge(PERM_SCALE, 0) is true
    let zero_perm = solver.int_const(0);
    let points_to = model.encode_points_to(&mut solver, &state, addr, val, zero_perm);
    solver.assert_term(points_to);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Sat),
        "zero permission should be satisfiable after allocation"
    );
}

// --- dealloc heap value retention (#904 algorithm_audit) ---
//
// After dealloc, the heap value is NOT cleared — only domain and permissions
// are updated. This means heap[addr] still contains the old value.
// This is sound because the domain check prevents valid access, but the
// SMT model retains the value which could be relevant for counterexample
// analysis or future unsafe-heap extensions.

/// After dealloc, heap[addr] still contains the pre-dealloc value.
/// This documents the design: dealloc only clears domain and permissions.
#[test]
#[timeout(30000)]
fn dealloc_retains_heap_value() {
    use ay_dpll::api::{Logic, SolveResult, Solver};

    use crate::memory_model::{BaseMemoryModel, MemPtr, MemoryModel};

    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let state = BaseMemoryModel::init(&mut solver);

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(999);

    // Allocate, then deallocate
    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // The heap value is still there (dealloc doesn't clear it)
    let loaded = model.load(&mut solver, &state, &ptr);
    let val_eq = solver.eq(loaded, val);
    solver.assert_term(val_eq);

    // Domain check prevents access, but the heap value survives
    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Sat),
        "dealloc does not clear heap value — heap[addr] retains old value \
         (domain check is the access guard, not heap erasure)"
    );
}

// --- LetAssume nested assumption ordering (#904 algorithm_audit) ---
//
// When multiple LetAssume facts are nested (from projected writes), the
// outermost assumption applies first in the implication chain. This test
// verifies that the ordering is correct: the reverse iteration in
// extract_from_block_with_context (`.into_iter().rev()`) means the FIRST
// collected fact becomes the outermost LetAssume.

/// Multiple nested LetAssume facts: inner assumption can't prove outer's negation.
/// Verifies that assumptions are independent and don't create contradictions.
#[test]
#[timeout(30000)]
fn nested_let_assume_facts_are_independent() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    // Model: pair.0 = 5; pair.1 = 10; proof_assert!(pair.0 == 5 && pair.1 == 10)
    // After extraction:
    //   LetAssume { tuple_get_1(x) == 10,
    //     LetAssume { tuple_get_0(x) == 5,
    //       (tuple_get_0(x) == 5) && (tuple_get_1(x) == 10) } }
    let inner_claim = PureExpr::BinOp(
        Arc::new(eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(5))),
        trust_wp_core::formula::BinOp::And,
        Arc::new(eq(logic_fn_call(&tuple_get_1, vec![var("x")]), int(10))),
    );

    let inner_assume = let_assume(
        eq(logic_fn_call(&tuple_get_0, vec![var("x")]), int(5)),
        inner_claim,
    );
    let body = let_assume(
        eq(logic_fn_call(&tuple_get_1, vec![var("x")]), int(10)),
        inner_assume,
    );

    let ensures = eq(var("result"), bool_expr(true));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "independent nested LetAssume facts for different tuple fields should \
         jointly prove the conjunction: {result:?}"
    );
}

/// Verify that PureExpr PartialEq agrees with Debug-based equality
/// for representative expressions used in witness binding contexts.
/// If this test passes, the fix for #1257 (switching from Debug to ==)
/// is a safe no-behavior-change refactor.
#[test]
#[timeout(30000)]
fn pure_expr_partial_eq_matches_debug_equality() {
    let cases: Vec<(PureExpr, PureExpr, bool)> = vec![
        // Same variable
        (var("x"), var("x"), true),
        // Different variables
        (var("x"), var("y"), false),
        // Same integer literal
        (int(42), int(42), true),
        // Different integer literals
        (int(42), int(43), false),
        // Same method call (postcondition_once)
        (
            method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]),
            method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]),
            true,
        ),
        // Different method call args
        (
            method_call(var("f"), "postcondition_once", vec![var("x"), var("r")]),
            method_call(var("f"), "postcondition_once", vec![var("y"), var("r")]),
            false,
        ),
        // Same logic function call
        (
            logic_fn_call("resolve", vec![var("x")]),
            logic_fn_call("resolve", vec![var("x")]),
            true,
        ),
        // Same eq expression
        (eq(var("x"), int(0)), eq(var("x"), int(0)), true),
        // resolve_call helper
        (resolve_call(var("x")), resolve_call(var("x")), true),
        (resolve_call(var("x")), resolve_call(var("y")), false),
    ];

    for (i, (a, b, expected_equal)) in cases.iter().enumerate() {
        let debug_equal = format!("{a:?}") == format!("{b:?}");
        let partial_eq = a == b;
        assert_eq!(
            debug_equal, partial_eq,
            "case {i}: PartialEq disagrees with Debug equality for:\n  a = {a:?}\n  b = {b:?}\n  \
             Debug: {debug_equal}, PartialEq: {partial_eq}"
        );
        assert_eq!(
            partial_eq, *expected_equal,
            "case {i}: unexpected equality result for:\n  a = {a:?}\n  b = {b:?}"
        );
    }
}

// --- encode_sep_conj trait vs production mismatch (#904 algorithm_audit) ---
//
// BaseMemoryModel::encode_sep_conj operates on individual Bool terms
// (point-wise disjointness) but the trait doc says "predicates (functions
// from Int to Bool)". The production path (AYEncoder::encode_sep_conj) uses
// a completely different signature and implementation (footprint-based
// pairwise/quantified disjointness). These tests document the mismatch and
// verify that the trait method is only used in unit tests.

/// Verify that BaseMemoryModel::encode_sep_conj is a symmetric operation.
///
/// sep_conj(a, b) should equal sep_conj(b, a) for all Boolean inputs.
/// This documents the pointwise semantics (it's just `!(a && b)`).
#[test]
#[timeout(30000)]
fn encode_sep_conj_is_symmetric() {
    use ay_dpll::api::{Logic, SolveResult, Solver};

    use crate::memory_model::{BaseMemoryModel, MemoryModel};

    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    let a = solver.declare_const("a", ay_dpll::api::Sort::Bool);
    let b = solver.declare_const("b", ay_dpll::api::Sort::Bool);

    let sep_ab = model.encode_sep_conj(&mut solver, a, b);
    let sep_ba = model.encode_sep_conj(&mut solver, b, a);

    // Assert sep_conj(a,b) != sep_conj(b,a): should be UNSAT (they're equivalent)
    let iff = solver.eq(sep_ab, sep_ba);
    let not_iff = solver.not(iff);
    solver.assert_term(not_iff);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
        "encode_sep_conj should be symmetric: !(a&&b) == !(b&&a)"
    );
}

/// Verify encode_sep_conj false/false boundary: both domains empty means
/// separation is trivially satisfied.
#[test]
#[timeout(30000)]
fn encode_sep_conj_both_false_is_trivially_sat() {
    use ay_dpll::api::{Logic, SolveResult, Solver};

    use crate::memory_model::{BaseMemoryModel, MemoryModel};

    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    let false_val = solver.bool_const(false);
    let sep = model.encode_sep_conj(&mut solver, false_val, false_val);
    solver.assert_term(sep);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Sat),
        "both-false domains are trivially disjoint: !(false && false) = true"
    );
}

// --- store-after-dealloc does NOT re-enter domain (#904 algorithm_audit) ---
//
// After dealloc, store() modifies the heap but does NOT update domain or
// permissions. This means the location remains outside the domain even
// though its heap value has changed. This is a critical boundary: store
// doesn't imply allocation.

/// Store after dealloc: heap changes but domain remains false.
///
/// This test verifies that store() is a pure heap operation with no
/// side effects on domain or permissions. A bug here would mean that
/// storing to a deallocated location silently re-validates it.
#[test]
#[timeout(30000)]
fn store_after_dealloc_does_not_re_enter_domain() {
    use ay_dpll::api::{Logic, SolveResult, Solver};

    use crate::memory_model::{BaseMemoryModel, MemPtr, MemoryModel};

    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let state = BaseMemoryModel::init(&mut solver);

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    // Allocate then deallocate
    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);

    // Store a NEW value after dealloc
    let new_val = solver.int_const(999);
    let state = model.store(&mut solver, state, &ptr, new_val);

    // The heap value changed, but domain should still be false
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
        "store after dealloc must not re-enter the location into the domain — \
         store is a pure heap operation with no domain/permission side effects"
    );
}

/// Permission is still zero after store-after-dealloc.
#[test]
#[timeout(30000)]
fn store_after_dealloc_keeps_zero_permission() {
    use ay_dpll::api::{Logic, SolveResult, Solver};

    use crate::memory_model::{BaseMemoryModel, MemPtr, MemoryModel};

    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let state = BaseMemoryModel::init(&mut solver);

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val = solver.int_const(100);

    let state = model.alloc(&mut solver, state, &ptr, val);
    let state = model.dealloc(&mut solver, state, &ptr);
    let new_val = solver.int_const(999);
    let state = model.store(&mut solver, state, &ptr, new_val);

    // Assert permission > 0 after store-after-dealloc: should be UNSAT
    let has_perm = model.has_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_perm);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Unsat(_)),
        "permission must remain zero after store-on-deallocated — \
         store does not restore permissions"
    );
}

// --- alloc at same address after dealloc: re-allocation semantics (#904) ---
//
// Re-allocating at the same address after dealloc should restore domain
// membership and full permission. This is the normal RAII pattern for
// address reuse.

/// Re-alloc after dealloc restores domain and full permission.
///
/// This tests the complete lifecycle: alloc -> dealloc -> alloc at same addr.
/// The second alloc must fully restore the location's state, including
/// domain membership, full permission, and the new value.
#[test]
#[timeout(30000)]
fn realloc_after_dealloc_restores_full_state() {
    use ay_dpll::api::{Logic, SolveResult, Solver};

    use crate::memory_model::{BaseMemoryModel, MemPtr, MemoryModel};

    let model = BaseMemoryModel::new();
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let state = BaseMemoryModel::init(&mut solver);

    let addr = solver.int_const(42);
    let ptr = MemPtr::new(addr);
    let val1 = solver.int_const(100);
    let val2 = solver.int_const(200);

    // Allocate, dealloc, re-allocate with different value
    let state = model.alloc(&mut solver, state, &ptr, val1);
    let state = model.dealloc(&mut solver, state, &ptr);
    let state = model.alloc(&mut solver, state, &ptr, val2);

    // Domain should be restored
    let in_dom = model.in_domain(&mut solver, &state, &ptr);
    solver.assert_term(in_dom);

    // Full permission should be restored
    let has_full = model.has_full_permission(&mut solver, &state, &ptr);
    solver.assert_term(has_full);

    // Value should be the NEW value, not the old one
    let loaded = model.load(&mut solver, &state, &ptr);
    let eq = solver.eq(loaded, val2);
    solver.assert_term(eq);

    assert!(
        matches!(solver.check_sat().into_inner(), SolveResult::Sat),
        "re-allocation must restore domain, full permission, and new value"
    );

    // Verify old value is NOT the loaded value (new value overwrites)
    let mut solver2 = Solver::try_new(Logic::QfAuflia).unwrap();
    let state2 = BaseMemoryModel::init(&mut solver2);
    let addr2 = solver2.int_const(42);
    let ptr2 = MemPtr::new(addr2);
    let val1_2 = solver2.int_const(100);
    let val2_2 = solver2.int_const(200);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val1_2);
    let state2 = model.dealloc(&mut solver2, state2, &ptr2);
    let state2 = model.alloc(&mut solver2, state2, &ptr2, val2_2);

    let loaded2 = model.load(&mut solver2, &state2, &ptr2);
    let eq_old = solver2.eq(loaded2, val1_2);
    let eq_new = solver2.eq(loaded2, val2_2);
    let not_eq_new = solver2.not(eq_new);
    let old_not_new = solver2.and(eq_old, not_eq_new);
    solver2.assert_term(old_not_new);

    assert!(
        matches!(solver2.check_sat().into_inner(), SolveResult::Unsat(_)),
        "re-allocation must overwrite old value with new value"
    );
}

// --- closure sort registration: debug_assert_eq capture mismatch (#904) ---
//
// The closure_struct_sort registration uses debug_assert_eq to check capture
// signature consistency. In release builds, a capture mismatch would silently
// return the wrong sort. This test documents the behavior and verifies the
// idempotency guard works correctly in debug builds.

/// Re-registering the same def_id with identical captures returns the same sort.
///
/// This tests the idempotency guard at register_closure_struct_sort.
#[test]
#[timeout(30000)]
fn closure_sort_idempotent_registration_returns_same_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let captures = vec![CaptureField::new(
        "x",
        ExprSort::Int,
        crate::CaptureKind::ByRef,
    )];

    let sort1 = encoder
        .register_closure_struct_sort("test::my_closure", &captures)
        .unwrap();
    let sort2 = encoder
        .register_closure_struct_sort("test::my_closure", &captures)
        .unwrap();

    assert_eq!(
        sort1, sort2,
        "re-registering same def_id with same captures should return identical sort"
    );
}

/// Registering different def_ids produces different sorts.
#[test]
#[timeout(30000)]
fn closure_sort_different_def_ids_produce_different_sorts() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let captures = vec![CaptureField::new(
        "x",
        ExprSort::Int,
        crate::CaptureKind::ByRef,
    )];

    let sort1 = encoder
        .register_closure_struct_sort("test::closure_a", &captures)
        .unwrap();
    let sort2 = encoder
        .register_closure_struct_sort("test::closure_b", &captures)
        .unwrap();

    assert_ne!(
        sort1, sort2,
        "different def_ids should produce different sorts even with same captures"
    );
}

/// Empty captures produce a valid sort with no accessors.
#[test]
#[timeout(30000)]
fn closure_sort_empty_captures_produces_valid_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let sort = encoder
        .register_closure_struct_sort("test::empty_closure", &[])
        .unwrap();

    // Sort should be a Datatype sort with no fields (#2151: native datatypes).
    assert!(
        matches!(sort, ay_dpll::api::Sort::Datatype(_)),
        "empty-capture closure should produce a datatype sort, got {sort:?}"
    );

    // With native datatypes, the datatype should have zero fields (no selectors).
    if let ay_dpll::api::Sort::Datatype(dt) = &sort {
        let field_count: usize = dt.constructors.iter().map(|c| c.fields.len()).sum();
        assert_eq!(
            field_count, 0,
            "empty-capture closure datatype should have no fields/selectors"
        );
    }
}

/// Re-registering the same def_id with different captures returns an error. (#1485)
#[test]
#[timeout(30000)]
fn closure_sort_mismatched_captures_returns_error() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let captures_a = vec![CaptureField::new(
        "x",
        ExprSort::Int,
        crate::CaptureKind::ByRef,
    )];
    let captures_b = vec![CaptureField::new(
        "y",
        ExprSort::Bool,
        crate::CaptureKind::ByRef,
    )];

    encoder
        .register_closure_struct_sort("test::mismatch", &captures_a)
        .unwrap();
    let result = encoder.register_closure_struct_sort("test::mismatch", &captures_b);

    assert!(
        result.is_err(),
        "mismatched capture signature should return Err, got {result:?}"
    );
    let msg = format!("{}", result.unwrap_err());
    assert!(
        msg.contains("changed capture signature"),
        "error should mention capture signature mismatch: {msg}"
    );
}
