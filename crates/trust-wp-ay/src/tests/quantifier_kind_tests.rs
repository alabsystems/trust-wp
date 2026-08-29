// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::encoder::quantifier::QuantifierKind`].
//!
//! Coverage gap: `QuantifierKind::apply_simple`, `apply_with_triggers`, and
//! `apply_with_optional_invalid_trigger_fallback` had zero direct tests despite
//! being `pub(crate)`. The `apply_with_optional_invalid_trigger_fallback` method
//! has non-trivial error-handling logic (catches `InvalidTrigger` and falls back
//! to triggerless form when `allow_invalid_trigger_fallback` is true).

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;

use crate::{encoder::quantifier::QuantifierKind, AYEncoder};

// --- apply_simple ---

#[test]
#[timeout(30000)]
fn apply_simple_forall_creates_universally_quantified_term() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    let zero = solver.int_const(0);
    let body = solver.ge(x, zero);

    let forall_term = QuantifierKind::Forall
        .apply_simple(solver, &[x], body)
        .expect("forall should succeed");

    // Assert the negation: exists x such that x < 0. This should be SAT.
    let neg = encoder.solver_mut().not(forall_term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "negated forall(x >= 0) should be SAT (integers include negatives)"
    );
}

#[test]
#[timeout(30000)]
fn apply_simple_exists_creates_existentially_quantified_term() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    let five = solver.int_const(5);
    let body = solver.eq(x, five);

    let exists_term = QuantifierKind::Exists
        .apply_simple(solver, &[x], body)
        .expect("exists should succeed");

    // Assert the existential: there exists x == 5. Should be SAT.
    encoder.assert_term(exists_term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "exists(x == 5) should be SAT"
    );
}

#[test]
#[timeout(30000)]
fn apply_simple_forall_trivially_true() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    // forall x: x == x (tautology)
    let body = solver.eq(x, x);

    let forall_term = QuantifierKind::Forall
        .apply_simple(solver, &[x], body)
        .expect("forall x == x should succeed");

    let neg = encoder.solver_mut().not(forall_term);
    encoder.assert_term(neg);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "negated forall(x == x) tautology should be Unsat"
    );
}

#[test]
#[timeout(30000)]
fn apply_simple_exists_negated_tautology_is_unsat() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    // exists x: x != x (contradiction)
    let x_eq_x = solver.eq(x, x);
    let body = solver.not(x_eq_x);

    let exists_term = QuantifierKind::Exists
        .apply_simple(solver, &[x], body)
        .expect("exists should succeed");

    encoder.assert_term(exists_term);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "exists(x != x) should be Unsat"
    );
}

// --- apply_with_triggers ---

#[test]
#[timeout(30000)]
fn apply_with_triggers_forall_creates_triggered_quantifier() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    let f = solver
        .try_declare_fun("f_trigger", &[int_sort.clone()], int_sort.clone())
        .expect("f_trigger declaration should succeed");
    let f_x = solver
        .try_apply(&f, &[x])
        .expect("f_trigger(x_q) application should succeed");
    let zero = solver.int_const(0);
    let body = solver.ge(f_x, zero);
    let a = solver.declare_const("a_trigger", int_sort.clone());
    let f_a = solver
        .try_apply(&f, &[a])
        .expect("f_trigger(a_trigger) application should succeed");
    let counterexample = solver.lt(f_a, zero);

    // Use f(x) as the trigger pattern
    let trigger_pattern: &[_] = &[f_x];
    let result = QuantifierKind::Forall
        .apply_with_triggers(solver, &[x], body, &[trigger_pattern])
        .expect("triggered forall should succeed");

    // Assert it with a concrete counterexample. The trigger must instantiate at f(a).
    encoder.assert_term(result);
    encoder.assert_term(counterexample);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "triggered forall(f(x) >= 0) plus f(a) < 0 should be Unsat"
    );
}

#[test]
#[timeout(30000)]
fn apply_with_triggers_exists_creates_triggered_quantifier() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    let f = solver
        .try_declare_fun("f_trigger_e", &[int_sort.clone()], int_sort.clone())
        .expect("f_trigger_e declaration should succeed");
    let f_x = solver
        .try_apply(&f, &[x])
        .expect("f_trigger_e(x_q) application should succeed");
    let ten = solver.int_const(10);
    let body = solver.eq(f_x, ten);

    let trigger_pattern: &[_] = &[f_x];
    let result = QuantifierKind::Exists
        .apply_with_triggers(solver, &[x], body, &[trigger_pattern])
        .expect("triggered exists should succeed");

    encoder.assert_term(result);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "triggered exists(f(x) == 10) should be SAT"
    );
}

// --- apply_with_optional_invalid_trigger_fallback ---

#[test]
#[timeout(30000)]
fn fallback_with_valid_triggers_does_not_fall_back() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    let f = solver
        .try_declare_fun("f_fb", &[int_sort.clone()], int_sort.clone())
        .expect("f_fb declaration should succeed");
    let f_x = solver
        .try_apply(&f, &[x])
        .expect("f_fb(x_q) application should succeed");
    let zero = solver.int_const(0);
    let body = solver.ge(f_x, zero);
    let a = solver.declare_const("a_fb", int_sort.clone());
    let f_a = solver
        .try_apply(&f, &[a])
        .expect("f_fb(a_fb) application should succeed");
    let counterexample = solver.lt(f_a, zero);

    let trigger_pattern: &[_] = &[f_x];
    let (term, did_fallback) = QuantifierKind::Forall
        .apply_with_optional_invalid_trigger_fallback(solver, &[x], body, &[trigger_pattern], true)
        .expect("should succeed with valid trigger");

    assert!(!did_fallback, "valid trigger should not cause fallback");
    encoder.assert_term(term);
    encoder.assert_term(counterexample);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "quantifier with valid trigger plus f(a) < 0 should be Unsat"
    );
}

#[test]
#[timeout(30000)]
fn fallback_disabled_with_valid_triggers_succeeds() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    let f = solver
        .try_declare_fun("f_fb2", &[int_sort.clone()], int_sort.clone())
        .expect("f_fb2 declaration should succeed");
    let f_x = solver
        .try_apply(&f, &[x])
        .expect("f_fb2(x_q) application should succeed");
    let zero = solver.int_const(0);
    let body = solver.ge(f_x, zero);
    let a = solver.declare_const("a_fb2", int_sort.clone());
    let f_a = solver
        .try_apply(&f, &[a])
        .expect("f_fb2(a_fb2) application should succeed");
    let counterexample = solver.lt(f_a, zero);

    let trigger_pattern: &[_] = &[f_x];
    let (term, did_fallback) = QuantifierKind::Forall
        .apply_with_optional_invalid_trigger_fallback(
            solver,
            &[x],
            body,
            &[trigger_pattern],
            false, // fallback disabled
        )
        .expect("should succeed with valid trigger even without fallback");

    assert!(!did_fallback);
    encoder.assert_term(term);
    encoder.assert_term(counterexample);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "quantifier with valid trigger plus f(a) < 0 should be Unsat"
    );
}

#[test]
#[timeout(30000)]
fn fallback_exists_variant_with_valid_triggers() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let solver = encoder.solver_mut();
    let int_sort = Sort::Int;
    let x = solver.declare_const("x_q", int_sort.clone());
    let f = solver
        .try_declare_fun("f_fb_e", &[int_sort.clone()], int_sort.clone())
        .expect("f_fb_e declaration should succeed");
    let f_x = solver
        .try_apply(&f, &[x])
        .expect("f_fb_e(x_q) application should succeed");
    let ten = solver.int_const(10);
    let body = solver.eq(f_x, ten);

    let trigger_pattern: &[_] = &[f_x];
    let (term, did_fallback) = QuantifierKind::Exists
        .apply_with_optional_invalid_trigger_fallback(solver, &[x], body, &[trigger_pattern], true)
        .expect("exists with valid trigger should succeed");

    assert!(!did_fallback);
    encoder.assert_term(term);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "exists(f(x) == 10) should be SAT"
    );
}

// --- QuantifierKind enum properties ---

#[test]
#[timeout(30000)]
fn quantifier_kind_debug_format() {
    assert_eq!(format!("{:?}", QuantifierKind::Forall), "Forall");
    assert_eq!(format!("{:?}", QuantifierKind::Exists), "Exists");
}

#[test]
#[timeout(30000)]
fn quantifier_kind_equality_and_copy() {
    let a = QuantifierKind::Forall;
    let b = a; // Copy
    assert_eq!(a, b);
    assert_ne!(QuantifierKind::Forall, QuantifierKind::Exists);
}

#[test]
#[timeout(30000)]
fn quantifier_kind_clone() {
    let orig = QuantifierKind::Exists;
    let copied = orig;
    assert_eq!(orig, copied);
}
