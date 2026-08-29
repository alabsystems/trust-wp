// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for adt_axioms.rs coverage gaps identified in Phase 4 (#1946).
//!
//! Targets:
//! - `assert_unit_singleton_axioms()`: empty set, single var, multiple vars,
//!   unregistered var, interaction with tuple axioms
//! - `assert_qualified_constructor_axioms()`: Some/None qualified constructors,
//!   early exit paths, cross-type disjointness

use trust_wp_core::formula::{internal::tuple_lowering::tuple_logic_fn_name, ExprSort};

use super::*;

// ── Unit singleton axiom tests ────────────────────────────────────

/// Empty `unit_sorted_vars` → `assert_unit_singleton_axioms()` is a no-op.
/// Calling it on a fresh encoder should not panic or add any constraints.
#[test]
#[timeout(30000)]
fn test_unit_singleton_axioms_empty_set_is_noop() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    assert!(encoder.unit_sorted_vars_for_test().is_empty());

    // Should not panic
    encoder.assert_unit_singleton_axioms();

    // Solver should still be SAT (no constraints added)
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "empty unit_sorted_vars should add no constraints"
    );
}

/// A single unit-sorted variable gets constrained to the Unit singleton.
///
/// Steps: encode `x` with Unit sort annotation, assert unit axioms,
/// then check that `x != __trust_wp_unit` is UNSAT. (#2059 Phase 2)
#[test]
#[timeout(30000)]
fn test_unit_singleton_single_var_constrained_to_zero() {
    use ay_dpll::api::Sort;
    let unit_sort = || Sort::Uninterpreted("Unit".to_string());
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode variable with Unit annotation — this adds to unit_sorted_vars
    let x_expr = var_with_sort("x", ExprSort::Unit);
    let x_term = encoder
        .encode_pure(&x_expr)
        .expect("unit-annotated var should encode");

    assert!(
        encoder.unit_sorted_vars_for_test().contains("x"),
        "encoding Unit-annotated var should track it in unit_sorted_vars"
    );

    encoder.assert_unit_singleton_axioms();

    // x != __trust_wp_unit should be UNSAT after the singleton constraint (#2059)
    let unit_val = encoder.solver.declare_const("__trust_wp_unit", unit_sort());
    let neq = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(x_term, unit_val);
        solver.not(eq)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unit-sorted var must equal __trust_wp_unit after singleton axiom"
    );
}

/// Multiple unit-sorted variables are all constrained independently.
///
/// If `x` and `y` are both unit-sorted, both must equal 0, so `x != y` is UNSAT.
#[test]
#[timeout(30000)]
fn test_unit_singleton_multiple_vars_all_equal_zero() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let x_term = encoder
        .encode_pure(&var_with_sort("x", ExprSort::Unit))
        .expect("unit x should encode");
    let y_term = encoder
        .encode_pure(&var_with_sort("y", ExprSort::Unit))
        .expect("unit y should encode");

    assert_eq!(encoder.unit_sorted_vars_for_test().len(), 2);

    encoder.assert_unit_singleton_axioms();

    // x != y should be UNSAT since both equal 0
    let neq = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(x_term, y_term);
        solver.not(eq)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "two unit-sorted vars must be equal (both = __trust_wp_unit)"
    );
}

/// A variable registered in `unit_sorted_vars` but not declared via
/// `encode_pure` (i.e., not in `self.vars`) is silently skipped.
/// This exercises the `if let Some(&var_term) = self.vars_for_test().get(var_name)` guard.
#[test]
#[timeout(30000)]
fn test_unit_singleton_unregistered_var_skipped() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Manually insert a name into unit_sorted_vars WITHOUT encoding it
    encoder
        .unit_sorted_vars_mut_for_test()
        .insert("phantom".to_string());

    // Should not panic — the var lookup silently skips missing vars
    encoder.assert_unit_singleton_axioms();

    // Solver should remain SAT (no actual constraints were added)
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "phantom unit var should be silently skipped"
    );
}

/// Unit singleton + tuple axiom interaction: tuple0() returns 0, and a
/// unit-sorted variable equals 0, so they should be equal.
#[test]
#[timeout(30000)]
fn test_unit_singleton_equals_tuple0() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode a unit-sorted variable
    let u_term = encoder
        .encode_pure(&var_with_sort("u", ExprSort::Unit))
        .expect("unit var should encode");

    // Encode tuple0() — the 0-arity tuple constructor
    let tuple0_expr = logic_fn_call(&tuple_logic_fn_name(0), vec![]);
    let tuple0_term = encoder
        .encode_pure(&tuple0_expr)
        .expect("tuple0() should encode");

    encoder.assert_unit_singleton_axioms();
    encoder.assert_tuple_axioms();

    // u != tuple0() should be UNSAT since both map to int 0
    let neq = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(u_term, tuple0_term);
        solver.not(eq)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "unit var and tuple0() must be equal (both = __trust_wp_unit)"
    );
}

// ── Qualified constructor axiom tests (Some/None) ─────────────────

/// Qualified Some constructor: `OwnOption::Some(v).is_some()` should hold.
///
/// This tests the `assert_some_constructor_axioms` path for qualified names,
/// which is untested — existing tests only cover qualified Ok/Err.
#[test]
#[timeout(30000)]
fn test_qualified_some_is_some_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register qualified Some via UF path: "OwnOption::Some" → "logic_OwnOption_P__P_Some"
    let is_some_qsome = method_call(
        logic_fn_call("OwnOption::Some", vec![int(5)]),
        "is_some",
        vec![],
    );

    let is_some_term = encoder
        .encode_pure(&is_some_qsome)
        .expect("OwnOption::Some(5).is_some() should encode");
    encoder.assert_option_result_axioms();

    // Negate: !is_some(OwnOption::Some(5)) should be UNSAT
    let negated = {
        let solver = encoder.solver_mut();
        solver.not(is_some_term)
    };
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "negation of OwnOption::Some(5).is_some() should be UNSAT — \
         qualified Some constructor gets tester axiom"
    );
}

/// Qualified Some constructor: `OwnOption::Some(42).unwrap()` should equal 42.
#[test]
#[timeout(30000)]
fn test_qualified_some_unwrap_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let unwrap_qsome = method_call(
        logic_fn_call("OwnOption::Some", vec![int(42)]),
        "unwrap",
        vec![],
    );

    let unwrap_term = encoder
        .encode_pure(&unwrap_qsome)
        .expect("OwnOption::Some(42).unwrap() should encode");
    let forty_two = encoder.encode_pure(&int(42)).unwrap();
    encoder.assert_option_result_axioms();

    let neq = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(unwrap_term, forty_two);
        solver.not(eq_term)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "OwnOption::Some(42).unwrap() != 42 should be UNSAT — \
         qualified Some gets accessor axiom"
    );
}

/// Qualified None constructor: `!is_some(OwnOption::None())` should hold.
#[test]
#[timeout(30000)]
fn test_qualified_none_not_is_some_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register qualified None and is_some tester
    let is_some_qnone = method_call(logic_fn_call("OwnOption::None", vec![]), "is_some", vec![]);

    let is_some_term = encoder
        .encode_pure(&is_some_qnone)
        .expect("OwnOption::None().is_some() should encode");
    encoder.assert_option_result_axioms();

    // Assert is_some(OwnOption::None()) — should be UNSAT by tester axiom
    encoder.assert_term(is_some_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(OwnOption::None()) must be false — qualified None tester axiom"
    );
}

/// Cross-type disjointness for qualified Some: `!is_ok(OwnOption::Some(v))`.
///
/// The qualified Some axioms (including cross-type disjointness) only fire
/// when at least one Option-specific tester/accessor (`is_some`, `spec_unwrap`,
/// or `is_option`) is registered. Without these, the early-exit guard in
/// `assert_some_constructor_axioms` returns before asserting `!is_ok(ctor(v))`.
#[test]
#[timeout(30000)]
fn test_qualified_some_not_is_ok_disjointness() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register is_ok via Ok expression
    let _ = encoder.encode_pure(&method_call(
        logic_fn_call("Ok", vec![int(1)]),
        "is_ok",
        vec![],
    ));

    // Register is_some — required for qualified Some axioms to fire
    let _ = encoder.encode_pure(&method_call(
        logic_fn_call("OwnOption::Some", vec![int(5)]),
        "is_some",
        vec![],
    ));

    // Now encode is_ok(OwnOption::Some(5))
    let is_ok_qsome = method_call(
        logic_fn_call("OwnOption::Some", vec![int(5)]),
        "is_ok",
        vec![],
    );
    let is_ok_term = encoder
        .encode_pure(&is_ok_qsome)
        .expect("OwnOption::Some(5).is_ok() should encode");

    encoder.assert_option_result_axioms();

    // Assert is_ok(OwnOption::Some(5)) — should be UNSAT by cross-type disjointness
    encoder.assert_term(is_ok_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(OwnOption::Some(v)) must be false — cross-type disjointness"
    );
}

/// Cross-type disjointness for qualified None: `!is_ok(OwnOption::None())`.
#[test]
#[timeout(30000)]
fn test_qualified_none_not_is_ok_disjointness() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register is_ok
    let _ = encoder.encode_pure(&method_call(
        logic_fn_call("Ok", vec![int(1)]),
        "is_ok",
        vec![],
    ));

    let is_ok_qnone = method_call(logic_fn_call("OwnOption::None", vec![]), "is_ok", vec![]);
    let is_ok_term = encoder
        .encode_pure(&is_ok_qnone)
        .expect("OwnOption::None().is_ok() should encode");

    encoder.assert_option_result_axioms();

    encoder.assert_term(is_ok_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(OwnOption::None()) must be false — cross-type disjointness"
    );
}

/// No qualified constructors → `assert_qualified_constructor_axioms` is a no-op.
/// Only standard Option/Result symbols exist. Should not panic.
#[test]
#[timeout(60000)]
fn test_qualified_constructors_noop_when_only_standard_names() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Only standard Some and None — no qualified names
    let _ = encoder.encode_pure(&logic_fn_call("Some", vec![int(1)]));
    let _ = encoder.encode_pure(&logic_fn_call("None", vec![]));
    let _ = encoder.encode_pure(&method_call(var("x"), "is_some", vec![]));

    // Should not panic and should work normally. The axioms introduce
    // universally quantified Option/Result lemmas; the solver may return
    // `Unknown` for the resulting quantified set without violating soundness.
    // The test only guards against `Unsat` (which would indicate a spurious
    // contradiction added by axiom assertion) and panics.
    encoder.assert_option_result_axioms();
    let result = encoder.check_sat();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "axiom assertion must not introduce a spurious contradiction, got {result:?}",
    );
}

/// Mixed standard + qualified Ok: both get axioms independently.
///
/// Standard Ok(1).is_ok() and OwnResult::Ok(1).is_ok() should both hold.
#[test]
#[timeout(30000)]
fn test_mixed_standard_and_qualified_ok_both_get_axioms() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Standard Ok
    let std_is_ok = method_call(logic_fn_call("Ok", vec![int(1)]), "is_ok", vec![]);
    let std_term = encoder
        .encode_pure(&std_is_ok)
        .expect("standard Ok(1).is_ok() should encode");

    // Qualified Ok
    let qual_is_ok = method_call(
        logic_fn_call("OwnResult::Ok", vec![int(2)]),
        "is_ok",
        vec![],
    );
    let qual_term = encoder
        .encode_pure(&qual_is_ok)
        .expect("OwnResult::Ok(2).is_ok() should encode");

    encoder.assert_option_result_axioms();

    // Negate both: !(std && qual) should be UNSAT
    let both_ok = {
        let solver = encoder.solver_mut();
        let both = solver.and(std_term, qual_term);
        solver.not(both)
    };
    encoder.assert_term(both_ok);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "both standard and qualified Ok should have tester axioms"
    );
}

/// Qualified Err constructor: `!is_ok(OwnResult::Err(v))` should hold.
/// This covers the `assert_err_constructor_axioms` qualified path.
#[test]
#[timeout(30000)]
fn test_qualified_err_not_is_ok_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register is_ok via standard Ok
    let _ = encoder.encode_pure(&method_call(
        logic_fn_call("Ok", vec![int(0)]),
        "is_ok",
        vec![],
    ));

    let is_ok_qerr = method_call(
        logic_fn_call("OwnResult::Err", vec![int(99)]),
        "is_ok",
        vec![],
    );
    let is_ok_term = encoder
        .encode_pure(&is_ok_qerr)
        .expect("OwnResult::Err(99).is_ok() should encode");

    encoder.assert_option_result_axioms();

    // Assert is_ok(OwnResult::Err(99)) — should be UNSAT
    encoder.assert_term(is_ok_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(OwnResult::Err(99)) must be false — qualified Err tester axiom"
    );
}

/// Qualified Err cross-type disjointness: `!is_some(OwnResult::Err(v))`.
///
/// The qualified Err axioms (including cross-type disjointness) only fire
/// when `is_ok` or `result_err_error` is registered. Without these, the
/// early-exit guard in `assert_err_constructor_axioms` returns before
/// asserting `!is_some(ctor(v))`.
#[test]
#[timeout(30000)]
fn test_qualified_err_not_is_some_disjointness() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register is_some
    let _ = encoder.encode_pure(&method_call(
        logic_fn_call("Some", vec![int(0)]),
        "is_some",
        vec![],
    ));

    // Register is_ok — required for qualified Err axioms to fire
    let _ = encoder.encode_pure(&method_call(
        logic_fn_call("OwnResult::Err", vec![int(77)]),
        "is_ok",
        vec![],
    ));

    let is_some_qerr = method_call(
        logic_fn_call("OwnResult::Err", vec![int(77)]),
        "is_some",
        vec![],
    );
    let is_some_term = encoder
        .encode_pure(&is_some_qerr)
        .expect("OwnResult::Err(77).is_some() should encode");

    encoder.assert_option_result_axioms();

    encoder.assert_term(is_some_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(OwnResult::Err(v)) must be false — cross-type disjointness"
    );
}

/// Qualified Err accessor: `OwnResult::Err(77).unwrap_err()` should equal 77.
#[test]
#[timeout(30000)]
fn test_qualified_err_unwrap_err_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let unwrap_err_qerr = method_call(
        logic_fn_call("OwnResult::Err", vec![int(77)]),
        "unwrap_err",
        vec![],
    );

    let unwrap_err_term = encoder
        .encode_pure(&unwrap_err_qerr)
        .expect("OwnResult::Err(77).unwrap_err() should encode");
    let seventy_seven = encoder.encode_pure(&int(77)).unwrap();

    // Also register is_ok to trigger qualified axiom generation
    let _ = encoder.encode_pure(&method_call(
        logic_fn_call("Ok", vec![int(0)]),
        "is_ok",
        vec![],
    ));

    encoder.assert_option_result_axioms();

    let neq = {
        let solver = encoder.solver_mut();
        let eq = solver.eq(unwrap_err_term, seventy_seven);
        solver.not(eq)
    };
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "OwnResult::Err(77).unwrap_err() != 77 should be UNSAT — \
         qualified Err gets accessor axiom"
    );
}
