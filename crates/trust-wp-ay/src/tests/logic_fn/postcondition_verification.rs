// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic Function Postcondition Verification Tests (#893)
//!
//! Demonstrates that the ay layer CAN verify logic function postconditions.
//! The #893 bug is in the driver layer which skips all logic functions, even
//! those with #[ensures]. These tests prove the ay engine handles this correctly.
//!
//! AY integration tests (ITE/UF primitives, Seq params, structural induction,
//! Bool-result pollution) are in postcondition_ay_integration.rs.

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::{
    formula::ExprSort,
    logic::{LogicFnDef, LogicMode},
};

use super::*;

/// Verify logic function postcondition using the `ensures` field on `LogicFnDef` (#893).
///
/// This tests the data model change: `LogicFnDef` now carries `ensures` clauses
/// that the driver uses to build VCs for logic function postconditions.
#[test]
#[timeout(30000)]
fn test_logic_fn_def_ensures_field_used_for_verification() {
    // Logic function: fn double(x: Int) -> Int { x + x }
    // with ensures(result == x + x) stored on the LogicFnDef itself
    let mut logic_fn = LogicFnDef::new(
        "double".to_string(),
        "crate::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // Set the ensures field (the new #893 addition)
    logic_fn.set_ensures(vec![eq(var("result"), add(var("x"), var("x")))]);

    // The driver builds this VC: requires=[], ensures=logic_fn.ensures, body=logic_fn.body
    let result = verify_function_with_modes(
        VerificationRequest::new(logic_fn.requires(), logic_fn.ensures())
            .return_expr(Some(logic_fn.body())),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Logic fn with ensures(result == x + x) and body x + x should verify: {result:?}"
    );
}

/// A logic function with `ensures(result == x + x)` and `body: x + x`
/// should verify when the axiom is available and the postcondition matches.
///
/// This models the quant.rs pattern: a #[logic] fn with a postcondition.
/// The ay layer can verify this — the gap is at the driver layer (#893).
#[test]
#[timeout(30000)]
fn test_logic_fn_postcondition_verifies_when_body_matches() {
    // Logic function: fn double(x: Int) -> Int { x + x }
    let logic_fn = LogicFnDef::new(
        "double".to_string(),
        "crate::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // Verify postcondition: ensures(double(n) == n + n)
    // This is what the driver SHOULD generate for a logic fn with #[ensures]
    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(
        logic_fn_call("double", vec![var("n")]),
        add(var("n"), var("n")),
    )];
    // Body: the logic fn application itself (the "result" is double(n))
    let body = logic_fn_call("double", vec![var("n")]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Logic fn postcondition double(n) == n + n should verify with Open axiom: {result:?}"
    );
}

/// Negative control: wrong postcondition for a logic function should fail.
///
/// Ensures the verification is non-vacuous — the axiom constrains the result.
#[test]
#[timeout(30000)]
fn test_logic_fn_postcondition_fails_when_body_mismatches() {
    // Logic function: fn double(x: Int) -> Int { x + x }
    let logic_fn = LogicFnDef::new(
        "double".to_string(),
        "crate::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // Wrong postcondition under n == 1: ensures(double(n) == n * 3)
    let requires = vec![eq(var("n"), int(1))];
    let ensures = vec![eq(
        logic_fn_call("double", vec![var("n")]),
        mul(var("n"), int(3)),
    )];
    let body = logic_fn_call("double", vec![var("n")]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    // ay rev 40ed0b restored E-matching — solver now finds the counterexample.
    assert!(
        crate::tests::rejected_ok(&result),
        "Wrong postcondition double(n) == n*3 should fail: {result:?}"
    );
}

/// Without the axiom (Default mode), the postcondition should fail because
/// double() is uninterpreted — the solver finds a counterexample where
/// double(n) != n + n (e.g., double(n) = 0, n = 1).
///
/// This models the current quant.rs behavior where logic functions are
/// axiomatized but their postconditions are not generated as VCs.
#[test]
#[timeout(30000)]
fn test_logic_fn_postcondition_fails_without_axiom() {
    // Logic function in Default mode (opaque)
    let logic_fn = LogicFnDef::new(
        "double".to_string(),
        "crate::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Default);

    // Postcondition: ensures(double(n) == n + n) — correct but unprovable without axiom
    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(
        logic_fn_call("double", vec![var("n")]),
        add(var("n"), var("n")),
    )];
    let body = logic_fn_call("double", vec![var("n")]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    // Without the axiom, double(n) is uninterpreted — the solver finds a
    // counterexample. Pinned to Failed(_) per #774 convention.
    assert!(
        crate::tests::rejected_ok(&result),
        "Without axiom, postcondition should fail with counterexample: {result:?}"
    );
}

/// Models the quant.rs `invariant` function pattern:
/// A logic function with trivial body (true) and no postcondition
/// generates 0 VCs — this is the vacuous pass pattern.
///
/// This test documents that when no postcondition is provided,
/// an empty ensures list causes the verifier to trivially succeed.
#[test]
#[timeout(30000)]
fn test_logic_fn_trivial_body_empty_ensures_vacuously_passes() {
    // Logic function: fn invariant(self) -> bool { true }
    let logic_fn = LogicFnDef::new(
        "invariant".to_string(),
        "crate::invariant".to_string(),
        vec!["self_".to_string()],
        bool_expr(true),
    )
    .with_mode(LogicMode::Open);

    // No postcondition — this is the gap: the driver doesn't generate one
    let requires: Vec<PureExpr> = vec![];
    let ensures: Vec<PureExpr> = vec![];
    let body = bool_expr(true);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Empty ensures trivially verifies — this is the vacuous pass pattern (#893): {result:?}"
    );
}

// =========================================================================
// Recursive Logic Function Axiom Tests (#1292)
// =========================================================================

/// Reproduce Creusot `simple_trigger.rs`: recursive logic function `id(i)`
/// with defining axiom, verified at call site via `id(1) == 1`.
///
/// The axiom `forall i. i >= 0 => id(i) = if i == 0 { 0 } else { id(i-1) + 1 }`
/// must be instantiated twice: once for `id(1)` and once for `id(0)`.
/// This exercises ay's multi-round E-matching capability.
///
/// Part of #1292
#[test]
#[timeout(30000)]
fn test_recursive_logic_fn_axiom_id_one() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // id(i) = if i == 0 { 0 } else { id(i-1) + 1 }
    let id_body = ite(
        eq(var("i"), int(0)),
        int(0),
        add(logic_fn_call("id", vec![sub(var("i"), int(1))]), int(1)),
    );

    let id_fn = LogicFnDef::new_with_requires(
        "id".to_string(),
        "test::id".to_string(),
        vec!["i".to_string()],
        vec![ge(var("i"), int(0))],
        id_body,
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int)])
    .detect_recursion();

    // Verify: ensures id(1) == 1 (body is irrelevant, empty function)
    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(logic_fn_call("id", vec![int(1)]), int(1))];
    let body = int(0); // test() has no meaningful body

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&id_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Recursive axiom id(1) = id(0) + 1 = 0 + 1 = 1 should be provable \
         via two E-matching rounds. Got: {result:?}"
    );
}

/// Verifies ay handles UF+LIA chaining: multi-step UF-arithmetic.
///
/// `id(0) = 0 ∧ id(1) = id(0) + 1 ∧ ¬(id(1) = 1)` is UNSAT
/// (because id(1) = id(0) + 1 = 0 + 1 = 1). ay now correctly chains
/// the UF equality through arithmetic (previously returned Sat/Unknown).
///
/// Part of #1292
#[test]
#[timeout(30000)]
fn test_ay_dpll_uf_lia_gap_documents_known_limitation() {
    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();

    // Declare logic_id as uninterpreted function: (Int) -> Int
    let id_decl = encoder
        .solver_mut()
        .declare_fun("logic_id", &[Sort::Int], Sort::Int);

    // Create concrete terms
    let zero = encoder.solver_mut().int_const(0);
    let one = encoder.solver_mut().int_const(1);

    // id(0) and id(1)
    let id_0 = encoder.solver_mut().apply(&id_decl, &[zero]);
    let id_1 = encoder.solver_mut().apply(&id_decl, &[one]);

    // Ground instance 1: id(0) = 0
    let eq_id0 = encoder.solver_mut().eq(id_0, zero);
    encoder.assert_term(eq_id0);

    // Ground instance 2: id(1) = id(0) + 1
    let id_0_again = encoder.solver_mut().apply(&id_decl, &[zero]);
    let id_0_plus_1 = encoder.solver_mut().add(id_0_again, one);
    let eq_id1 = encoder.solver_mut().eq(id_1, id_0_plus_1);
    encoder.assert_term(eq_id1);

    // Negated postcondition: NOT(id(1) == 1)
    let id_1_again = encoder.solver_mut().apply(&id_decl, &[one]);
    let post = encoder.solver_mut().eq(id_1_again, one);
    let neg_post = encoder.solver_mut().not(post);
    encoder.assert_term(neg_post);

    use ay_dpll::api::SolveResult as SR;
    let result = encoder.check_sat();
    // ay now correctly chains id(0) = 0 through id(0) + 1 to derive id(1) = 1.
    // Previously returned Sat/Unknown (UF+LIA limitation), fixed in ay pin bump.
    assert_eq!(
        result,
        SR::unsat(),
        "ay should prove UF+LIA combination: id(0)=0, id(1)=id(0)+1 implies id(1)=1. Got: {result:?}"
    );
}

/// Non-recursive base case: `id(0) == 0` should be provable from a single
/// axiom instantiation.
///
/// Part of #1292
#[test]
#[timeout(30000)]
fn test_recursive_logic_fn_axiom_id_zero() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let id_body = ite(
        eq(var("i"), int(0)),
        int(0),
        add(logic_fn_call("id", vec![sub(var("i"), int(1))]), int(1)),
    );

    let id_fn = LogicFnDef::new_with_requires(
        "id".to_string(),
        "test::id".to_string(),
        vec!["i".to_string()],
        vec![ge(var("i"), int(0))],
        id_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(logic_fn_call("id", vec![int(0)]), int(0))];
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&id_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Base case id(0) = 0 should be provable from single axiom instantiation. \
         Got: {result:?}"
    );
}

/// Recursive logic function with Default mode + mode_overrides upgrading to
/// Open. This reproduces the simple_trigger.rs scenario where a `#[logic]`
/// function (Default mode) is called from the same module, and
/// `scope_logic_fn_modes` upgrades it to Open. Without mode_overrides
/// awareness in `assert_recursive_logic_fn_ground_instances`, the ground
/// instances are not evaluated and the caller cannot prove `id(1) == 1`.
///
/// Part of #1292
#[test]
#[timeout(30000)]
fn test_recursive_logic_fn_default_mode_with_open_override() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let id_body = ite(
        eq(var("i"), int(0)),
        int(0),
        add(logic_fn_call("id", vec![sub(var("i"), int(1))]), int(1)),
    );

    // Default mode — would be opaque without mode override
    let id_fn = LogicFnDef::new_with_requires(
        "id".to_string(),
        "test::id".to_string(),
        vec!["i".to_string()],
        vec![ge(var("i"), int(0))],
        id_body,
    )
    .with_param_sorts(vec![Some(ExprSort::Int)])
    .detect_recursion();

    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(logic_fn_call("id", vec![int(1)]), int(1))];
    let body = int(0);

    // Override to Open (simulates scope_logic_fn_modes for same-module caller)
    let mode_overrides = vec![LogicMode::Open];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&id_fn)))
            .mode_overrides(Some(&mode_overrides)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Default-mode recursive fn with Open override should be provable \
         via ground instance evaluation. Got: {result:?}"
    );
}

/// Offset symbolic recursive calls must still collapse to the base cases when
/// the caller precondition pins the argument. This mirrors the `lemma_fib_bound`
/// proof state's `fib(i - 1)` / `fib(i - 2)` obligations under `i == 2`. (#994)
///
/// The recursive offset instances should be discharged directly; a solver hang
/// or Unknown result is a regression.
#[test]
#[timeout(15000)]
fn test_recursive_logic_fn_offset_base_cases_under_symbolic_precondition() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let fib_body = ite(
        le(var("i"), int(0)),
        int(0),
        ite(
            eq(var("i"), int(1)),
            int(1),
            add(
                logic_fn_call("fib", vec![sub(var("i"), int(1))]),
                logic_fn_call("fib", vec![sub(var("i"), int(2))]),
            ),
        ),
    );
    let fib_fn = LogicFnDef::new(
        "fib".to_string(),
        "test::fib".to_string(),
        vec!["i".to_string()],
        fib_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    let requires = vec![eq(var("i"), int(2))];
    let ensures = vec![and(
        eq(logic_fn_call("fib", vec![sub(var("i"), int(1))]), int(1)),
        eq(logic_fn_call("fib", vec![sub(var("i"), int(2))]), int(0)),
    )];
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&fib_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "offset recursive base cases should verify under i == 2. Got: {result:?}"
    );
}

/// With the predecessor bounds available as explicit assumptions, the
/// Fibonacci step at `i == 2` should be provable without any proof-call
/// machinery. This isolates the remaining `lemma_fib_bound` failure to the
/// proof-call assumption path if it succeeds. (#994)
///
/// With equality-constraint ground instance extraction (#1192), the
/// precondition `i == 2` enables direct evaluation of `fib(i)`, `fib(i-1)`,
/// and `fib(i-2)` to concrete values, reducing solve time from 30s+ to <10s.
///
/// The explicit predecessor bounds should close the Fibonacci step directly; a
/// solver hang or Unknown result is a regression.
#[test]
#[timeout(15000)]
fn test_recursive_fib_step_verifies_with_explicit_predecessor_bounds() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    let fib_body = ite(
        le(var("i"), int(0)),
        int(0),
        ite(
            eq(var("i"), int(1)),
            int(1),
            add(
                logic_fn_call("fib", vec![sub(var("i"), int(1))]),
                logic_fn_call("fib", vec![sub(var("i"), int(2))]),
            ),
        ),
    );
    let fib_fn = LogicFnDef::new(
        "fib".to_string(),
        "test::fib".to_string(),
        vec!["i".to_string()],
        fib_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    let unit = PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(0),
        args: vec![],
    };
    let requires = vec![
        eq(var("i"), int(2)),
        le(
            logic_fn_call("fib", vec![sub(var("i"), int(1))]),
            method_call(sub(var("i"), int(1)), "pow2", vec![]),
        ),
        le(
            logic_fn_call("fib", vec![sub(var("i"), int(2))]),
            method_call(sub(var("i"), int(2)), "pow2", vec![]),
        ),
    ];
    let ensures = vec![le(
        logic_fn_call("fib", vec![var("i")]),
        method_call(var("i"), "pow2", vec![]),
    )];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&unit))
            .logic_fns(Some(std::slice::from_ref(&fib_fn))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "explicit predecessor bounds should verify the i == 2 fib step. Got: {result:?}"
    );
}

/// Regression test for #1310: max_logic with conditional body should verify
/// when used in ensures clause. The e2e test times out.
#[test]
#[timeout(30000)]
fn test_max_logic_conditional_body_verifies() {
    // max_logic(a, b) = if a >= b { a } else { b }
    let max_logic = LogicFnDef::new(
        "max_logic".to_string(),
        "simple_examples::max_logic".to_string(),
        vec!["a".to_string(), "b".to_string()],
        ite(ge(var("a"), var("b")), var("a"), var("b")),
    )
    .with_mode(LogicMode::Open);

    // ensures: result == max_logic(a, b)
    let ensures = vec![eq(
        var("result"),
        logic_fn_call("max_logic", vec![var("a"), var("b")]),
    )];

    // body: if a >= b { a } else { b }
    let body = ite(ge(var("a"), var("b")), var("a"), var("b"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&max_logic))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "max_logic conditional body should verify. Got: {result:?}"
    );
}

/// Negative test: a logic function with body `x + x` (correct) but ensures
/// claiming `result > x + x` (wrong — double(x) is never strictly greater
/// than itself) should fail verification. Ensures the encoder doesn't
/// unsoundly accept wrong postconditions. (#904 assertion quality)
#[test]
#[timeout(30000)]
fn test_logic_fn_wrong_postcondition_rejected() {
    // Logic function: fn double(x: Int) -> Int { x + x }
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "crate::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // Wrong ensures: result > x + x (impossible — body IS x + x)
    let ensures = vec![gt(var("result"), add(var("x"), var("x")))];

    // Correct body: x + x
    let body = add(var("x"), var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&double_fn))),
    );
    assert!(
        crate::tests::rejected_ok(&result),
        "Wrong postcondition (result > x+x when body is x+x) should be rejected. Got: {result:?}"
    );
}
