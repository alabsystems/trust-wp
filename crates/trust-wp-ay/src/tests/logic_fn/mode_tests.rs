// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// Helper: create a simple `max(a, b)` logic function with the given mode.
fn make_max_fn(mode: LogicMode) -> LogicFnDef {
    LogicFnDef::new(
        "max".to_string(),
        "test::max".to_string(),
        vec!["a".to_string(), "b".to_string()],
        ite(ge(var("a"), var("b")), var("a"), var("b")),
    )
    .with_mode(mode)
}

/// Helper: create a nullary `answer()` = 42 logic function with the given mode.
fn make_answer_fn(mode: LogicMode) -> LogicFnDef {
    LogicFnDef::new(
        "answer".to_string(),
        "test::answer".to_string(),
        vec![],
        int(42),
    )
    .with_mode(mode)
}

/// Returns true iff the solver can prove `logic_fn(args) = expected_value`.
/// When the defining axiom is emitted, this should succeed (UNSAT on negation).
/// When opaque, the function is uninterpreted and the solver cannot prove it (SAT).
fn axiom_constrains_value(encoder: &mut AYEncoder, call_expr: &PureExpr, expected: i64) -> bool {
    let call_term = encoder.encode_pure(call_expr).expect("Call should encode");
    let expected_term = encoder.solver.int_const(expected);
    let eq = encoder.solver.eq(call_term, expected_term);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    matches!(encoder.check_sat(), SolveResult::Unsat(_))
}

/// Default mode: the defining axiom should be suppressed.
/// `answer()` has body 42, but Default mode makes it opaque — the solver
/// cannot prove `answer() == 42`, so asserting `answer() != 42` is SAT.
#[test]
#[timeout(30000)]
fn test_default_mode_suppresses_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = make_answer_fn(LogicMode::Default);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("Registration should succeed");

    // Function should be declared but unconstrained
    assert!(
        encoder.decls().has_logic_func("logic_answer"),
        "Default-mode function should still be declared"
    );

    let call = logic_fn_call("answer", vec![]);
    assert!(
        !axiom_constrains_value(&mut encoder, &call, 42),
        "Default mode should suppress axiom — answer() should be unconstrained"
    );
}

/// Default mode with parameters: max(a, b) should be uninterpreted.
/// The solver cannot derive max(5, 3) == 5 without the defining axiom.
#[test]
#[timeout(30000)]
fn test_default_mode_suppresses_parameterized_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = make_max_fn(LogicMode::Default);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("Registration should succeed");

    let call = logic_fn_call("max", vec![int(5), int(3)]);
    assert!(
        !axiom_constrains_value(&mut encoder, &call, 5),
        "Default mode should suppress axiom — max(5,3) should be unconstrained"
    );
}

/// Open mode: the defining axiom is emitted.
/// The solver CAN prove `answer() == 42`.
#[test]
#[timeout(30000)]
fn test_open_mode_emits_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = make_answer_fn(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("Registration should succeed");

    let call = logic_fn_call("answer", vec![]);
    assert!(
        axiom_constrains_value(&mut encoder, &call, 42),
        "Open mode should emit axiom — answer() == 42 should be provable"
    );
}

/// Open mode with parameters: max(5, 3) should evaluate to 5.
#[test]
#[timeout(30000)]
fn test_open_mode_emits_parameterized_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = make_max_fn(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("Registration should succeed");

    let call = logic_fn_call("max", vec![int(5), int(3)]);
    assert!(
        axiom_constrains_value(&mut encoder, &call, 5),
        "Open mode should emit axiom — max(5,3) == 5 should be provable"
    );
}

/// `OpenSelf` mode: currently treated as Open (scoping is future work).
/// Verifies that the axiom IS emitted for `OpenSelf` functions.
#[test]
#[timeout(30000)]
fn test_open_self_mode_emits_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = make_answer_fn(LogicMode::OpenSelf);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("Registration should succeed");

    let call = logic_fn_call("answer", vec![]);
    assert!(
        axiom_constrains_value(&mut encoder, &call, 42),
        "OpenSelf mode should emit axiom (treated as Open for now)"
    );
}

/// Prophetic mode: treated as Open — defining axiom is emitted.
/// Verifies that the axiom IS emitted for Prophetic functions.
#[test]
#[timeout(30000)]
fn test_prophetic_mode_emits_axiom() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = make_answer_fn(LogicMode::Prophetic);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("Registration should succeed");

    let call = logic_fn_call("answer", vec![]);
    assert!(
        axiom_constrains_value(&mut encoder, &call, 42),
        "Prophetic mode should emit axiom — answer() == 42 should be provable"
    );
}

/// Explicit `is_opaque` overrides mode: even Open-mode functions
/// should suppress axioms when `is_opaque` is set.
#[test]
#[timeout(30000)]
fn test_is_opaque_overrides_open_mode() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = make_answer_fn(LogicMode::Open).with_opaque(true);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("Registration should succeed");

    let call = logic_fn_call("answer", vec![]);
    assert!(
        !axiom_constrains_value(&mut encoder, &call, 42),
        "is_opaque should override Open mode — answer() should be unconstrained"
    );
}

/// Integration test: Default-mode function in a verification context.
/// A postcondition that depends on the opaque function's body should fail.
#[test]
#[timeout(30000)]
fn test_default_mode_verification_fails() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = make_answer_fn(LogicMode::Default);

    // requires: true
    // ensures: answer() == 42
    // body: 0 (irrelevant)
    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(logic_fn_call("answer", vec![]), int(42))];
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "Default-mode function body should be invisible — cannot prove answer() == 42: {result:?}"
    );
}

/// Integration test: Open-mode function in a verification context.
/// The postcondition that depends on the function's body should succeed.
#[test]
#[timeout(30000)]
fn test_open_mode_verification_succeeds() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = make_answer_fn(LogicMode::Open);

    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(logic_fn_call("answer", vec![]), int(42))];
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Open-mode function body should be visible — answer() == 42 provable: {result:?}"
    );
}

/// Law function test: `#[law]` maps to Open mode, emitting a defining axiom.
///
/// Tests both directions:
/// - Default mode (no law): `double(5) == 10` is NOT provable (body is opaque)
/// - Open mode (law): `double(5) == 10` IS provable (defining axiom emitted)
#[test]
#[timeout(30000)]
fn test_law_axiom_constrains_opaque_function() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Default mode: double(x) = x + x, but body is opaque — axiom suppressed
    let double_default = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    );

    // Open mode (law): same function, but body is visible as a defining axiom
    let double_as_law = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // Verify: double(5) == 10 should be provable with Open-mode (law) axiom
    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(logic_fn_call("double", vec![int(5)]), int(10))];
    let body = int(0);

    // With Default mode (no law), verification should fail
    let result_no_law = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&double_default))),
    );
    assert!(
        matches!(result_no_law, Ok(VerificationResult::Failed(_))),
        "Without law (Default mode), double(5) == 10 should NOT be provable: {result_no_law:?}"
    );

    // With Open mode (law), verification should succeed
    let result_with_law = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&double_as_law))),
    );
    assert!(
        matches!(result_with_law, Ok(VerificationResult::Verified(_))),
        "With law (Open mode), double(5) == 10 should be provable: {result_with_law:?}"
    );
}

/// Law function with requires guard: the axiom is conditional.
///
/// Axiom: `forall x. (x > 0) => positive_double(x) = x + x`
///
/// Positive case: `positive_double(5) == 10` is provable (guard satisfied).
/// Negative case: `positive_double(-1) == -2` is NOT provable (guard unsatisfied,
/// so the axiom is vacuously true and the function value is unconstrained).
#[test]
#[timeout(30000)]
fn test_law_axiom_with_requires_guard() {
    let law_fn = || {
        LogicFnDef::new_with_requires(
            "positive_double".to_string(),
            "test::positive_double".to_string(),
            vec!["x".to_string()],
            vec![gt(var("x"), int(0))],
            add(var("x"), var("x")),
        )
        .with_mode(LogicMode::Open)
    };

    // Positive case: x=5 > 0, guard satisfied, axiom applies
    {
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder
            .register_logic_fn(&law_fn())
            .expect("Registration should succeed");
        let call_5 = logic_fn_call("positive_double", vec![int(5)]);
        assert!(
            axiom_constrains_value(&mut encoder, &call_5, 10),
            "Guard satisfied: positive_double(5) == 10 should be provable"
        );
    }

    // Negative case: x=-1, guard unsatisfied, function unconstrained
    {
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder
            .register_logic_fn(&law_fn())
            .expect("Registration should succeed");
        let call_neg = logic_fn_call("positive_double", vec![int(-1)]);
        assert!(
            !axiom_constrains_value(&mut encoder, &call_neg, -2),
            "Guard unsatisfied: positive_double(-1) == -2 should NOT be provable"
        );
    }
}

// ---- Prophetic logic function with Final expressions (#2683) ----
//
// These tests exercise the core prophetic use case: logic functions whose body
// references `^param` (Final values, i.e., the prophecy/future value of &mut refs).
// In trust-wp's RustHorn encoding, `^x` is `Final(Var("x"))` in PureExpr.
//
// In Creusot, `#[logic(prophetic)]` allows `^x` in the body. At the encoder level,
// quantifier-bound parameters collapse: `Final(Var(x))` and `Deref(Var(x))` both
// resolve to the same bound variable. This is correct because at the logical level,
// a logic function operates on pure values — the temporal distinction between *x
// and ^x is handled by the driver, which creates separate current/final variables
// before calling the logic function.
//
// Reference: Creusot `tests/should_succeed/lang/logic_vcgen.rs`

/// Prophetic logic function with `Final(Var(x))` in its body.
///
/// Models: `#[logic(prophetic)] fn prophecy(x: &mut i32) -> Int { ^x }`
/// (where `^x` is `Final(Var("x"))`).
///
/// In quantifier scope, `Final(Var("x"))` collapses to the bound variable,
/// so `prophecy(v)` = `v` (identity function). This verifies that the
/// defining axiom is correctly emitted with collapsed Final references.
#[test]
#[timeout(30000)]
fn test_prophetic_final_body_registers_correctly() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "prophecy".to_string(),
        "test::prophecy".to_string(),
        vec!["x".to_string()],
        final_expr(var("x")), // body = ^x
    )
    .with_mode(LogicMode::Prophetic);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("Prophetic function with Final body should register without error");

    // In quantifier scope, Final(Var("x")) collapses to x, so prophecy(v) = v
    let call = logic_fn_call("prophecy", vec![int(7)]);
    assert!(
        axiom_constrains_value(&mut encoder, &call, 7),
        "prophecy(7) should equal 7 (Final collapses to identity in quantifier scope)"
    );
}

/// Prophetic logic function with arithmetic involving both current and final values.
///
/// Models: `#[logic(prophetic)] fn bor_diff(x: &mut i32) -> Int { *x - ^x }`
///
/// In the RustHorn encoding, both `*x` and `^x` are available. But in logic
/// function quantifier scope, both collapse to the same bound variable.
/// So `bor_diff(v)` = `v - v` = 0 for all v.
#[test]
#[timeout(30000)]
fn test_prophetic_deref_minus_final_collapses_to_zero() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "bor_diff".to_string(),
        "test::bor_diff".to_string(),
        vec!["x".to_string()],
        sub(deref(var("x")), final_expr(var("x"))), // body = *x - ^x
    )
    .with_mode(LogicMode::Prophetic);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("Prophetic function with Deref-Final body should register");

    // Both *x and ^x collapse to x in quantifier scope, so bor_diff(v) = v - v = 0
    let call = logic_fn_call("bor_diff", vec![int(42)]);
    assert!(
        axiom_constrains_value(&mut encoder, &call, 0),
        "bor_diff(42) should equal 0 (Deref and Final both collapse in quantifier scope)"
    );
}

/// Prophetic logic function in a verification context.
///
/// Confirms Prophetic mode is visible (like Open) in the full verification
/// pipeline: `prophetic_id(5) == 5` is provable because the defining axiom
/// is emitted.
#[test]
#[timeout(30000)]
fn test_prophetic_verification_with_final_body() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let logic_fn = LogicFnDef::new(
        "prophetic_id".to_string(),
        "test::prophetic_id".to_string(),
        vec!["x".to_string()],
        final_expr(var("x")), // body = ^x (collapses to x)
    )
    .with_mode(LogicMode::Prophetic);

    // Verify: prophetic_id(5) == 5
    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(logic_fn_call("prophetic_id", vec![int(5)]), int(5))];
    let body = int(0); // irrelevant return

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Prophetic function should be visible (like Open) — prophetic_id(5) == 5 provable: {result:?}"
    );
}

/// Non-prophetic (Default mode) function with Final body should be opaque.
///
/// The same function body as `test_prophetic_final_body_registers_correctly`,
/// but in Default mode the axiom is suppressed — the function value is
/// unconstrained, so `default_fn(7) == 7` is NOT provable.
#[test]
#[timeout(30000)]
fn test_default_mode_final_body_is_opaque() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "default_prophecy".to_string(),
        "test::default_prophecy".to_string(),
        vec!["x".to_string()],
        final_expr(var("x")), // body = ^x
    )
    .with_mode(LogicMode::Default);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("Default function with Final body should register");

    // Default mode suppresses axiom — value is unconstrained
    let call = logic_fn_call("default_prophecy", vec![int(7)]);
    assert!(
        !axiom_constrains_value(&mut encoder, &call, 7),
        "Default mode should suppress axiom even when body uses Final"
    );
}

/// Prophetic function with `is_opaque` should suppress axiom.
///
/// Confirms that the `is_opaque` flag overrides Prophetic mode, same as
/// it overrides Open mode in `test_is_opaque_overrides_open_mode`.
#[test]
#[timeout(30000)]
fn test_is_opaque_overrides_prophetic_mode() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "opaque_prophecy".to_string(),
        "test::opaque_prophecy".to_string(),
        vec!["x".to_string()],
        final_expr(var("x")),
    )
    .with_mode(LogicMode::Prophetic)
    .with_opaque(true);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("Registration should succeed");

    let call = logic_fn_call("opaque_prophecy", vec![int(7)]);
    assert!(
        !axiom_constrains_value(&mut encoder, &call, 7),
        "is_opaque should override Prophetic mode — value should be unconstrained"
    );
}
