// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

/// Regression test for #1179: short-circuit `&&` encoding.
///
/// When the body expression is `Ite(a, Ite(b, c, false), false)` (the MIR
/// encoding of `a && b && c`), the `result` variable must be constrained to
/// the body expression. Without this constraint, the solver can produce
/// inconsistent counterexamples where all operands are true but `result` is
/// false.
#[test]
#[timeout(30000)]
fn test_short_circuit_and_constrains_result() {
    // Body: Ite(call_0, Ite(call_1, call_2, false), false)
    // This is the MIR encoding of `call_0 && call_1 && call_2`
    let body = ite(
        var("call_0"),
        ite(var("call_1"), var("call_2"), bool_expr(false)),
        bool_expr(false),
    );

    // Postcondition: result == false
    // This should FAIL (not verified) because the operands are unconstrained
    // and could all be true, making result true. But the counterexample must
    // be CONSISTENT: if call_0=true, call_1=true, call_2=true then result=true.
    let ens = eq(var("result"), bool_expr(false));
    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .unwrap();

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "short-circuit && with unconstrained operands should fail to prove result==false: {result:?}"
    );

    // Now verify the opposite: with body present, result == Ite(a, Ite(b, c, false), false)
    // So if we add preconditions a=true, b=true, c=true, then result should be true.
    let pre = vec![
        eq(var("call_0"), bool_expr(true)),
        eq(var("call_1"), bool_expr(true)),
        eq(var("call_2"), bool_expr(true)),
    ];
    let ens_true = eq(var("result"), bool_expr(true));
    let result = verify_function_with_modes(
        VerificationRequest::new(&pre, &[ens_true]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "short-circuit && with all operands true should verify result==true: {result:?}"
    );
}

/// Regression test for #1179: without return_expr, result is unconstrained.
///
/// This demonstrates the bug: when return_expr is None, the `result` variable
/// has no relationship to the function body, allowing inconsistent models.
#[test]
#[timeout(30000)]
fn test_no_return_expr_leaves_result_unconstrained() {
    // No body — result is unconstrained
    let ens = eq(var("result"), bool_expr(false));
    let result = verify_function_with_modes(VerificationRequest::new(&[], &[ens])).unwrap();

    // Without body, result is unconstrained. The postcondition `result == false`
    // becomes `not(result == false)`, i.e., `result != false`. The solver finds
    // `result = true`, so this FAILS.
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without return_expr, result==false should fail because result is unconstrained: {result:?}"
    );
}

/// Regression test for #1179: short-circuit `||` encoding.
#[test]
#[timeout(30000)]
fn test_short_circuit_or_constrains_result() {
    // Body: Ite(call_0, true, Ite(call_1, true, call_2))
    // This is the MIR encoding of `call_0 || call_1 || call_2`
    let body = ite(
        var("call_0"),
        bool_expr(true),
        ite(var("call_1"), bool_expr(true), var("call_2")),
    );

    // With all operands false, result should be false
    let pre = vec![
        eq(var("call_0"), bool_expr(false)),
        eq(var("call_1"), bool_expr(false)),
        eq(var("call_2"), bool_expr(false)),
    ];
    let ens = eq(var("result"), bool_expr(false));
    let result =
        verify_function_with_modes(VerificationRequest::new(&pre, &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "short-circuit || with all operands false should verify result==false: {result:?}"
    );
}

/// Regression test for #1179: Bool equality in postconditions must use iff encoding.
///
/// ay-dpll's `eq` (mk_eq) treats Bool equality as uninterpreted, so
/// `NOT(result == false)` could be satisfied by `result = false`. The fix
/// uses `(result => false) AND (false => result)` instead of `eq(result, false)`.
///
/// Without the iff encoding fix, the postcondition `result == false` with no
/// return_expr produces a counterexample where `result = false` — an
/// inconsistent model because `NOT(result == false)` should force `result = true`.
#[test]
#[timeout(30000)]
fn test_bool_eq_postcondition_uses_iff_encoding() {
    // Postcondition: result == true (a tautology when result IS true)
    // With body = true, this should verify.
    let body = bool_expr(true);
    let ens = eq(var("result"), bool_expr(true));
    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result == true with body = true should verify: {result:?}"
    );

    // Postcondition: result == false (contradicts body = true)
    // With body = true, this should FAIL.
    let ens_false = eq(var("result"), bool_expr(false));
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_false]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "result == false with body = true should fail: {result:?}"
    );

    // Postcondition: result != true with body = true should FAIL.
    let ens_ne_true = ne(var("result"), bool_expr(true));
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ne_true]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "result != true with body = true should fail: {result:?}"
    );

    // Postcondition: result != false with body = true should verify.
    let ens_ne_false = ne(var("result"), bool_expr(false));
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_ne_false]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result != false with body = true should verify: {result:?}"
    );
}

/// Regression test for #1179: Bool Ne in postconditions uses iff negation.
///
/// Ensures `result != true` with body returning `true` fails (not Unknown).
/// Covers the `BinOp::Ne` Bool encoding path.
#[test]
#[timeout(30000)]
fn test_bool_ne_postcondition_uses_iff_encoding() {
    // Body: Ite(call_0, true, false) — a simple bool function
    let body = ite(var("call_0"), bool_expr(true), bool_expr(false));

    // Precondition: call_0 is true, so body = true, so result = true
    let pre = vec![eq(var("call_0"), bool_expr(true))];
    // Postcondition: result != true — should FAIL because result is forced to true
    let ens = ne(var("result"), bool_expr(true));
    let result =
        verify_function_with_modes(VerificationRequest::new(&pre, &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "result != true with call_0=true body should fail: {result:?}"
    );

    // Postcondition: result != false with call_0=true — should verify
    let ens = ne(var("result"), bool_expr(false));
    let result =
        verify_function_with_modes(VerificationRequest::new(&pre, &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result != false with call_0=true body should verify: {result:?}"
    );
}

/// Regression test for #1227: Bool iff postcondition encoding path coverage.
///
/// The iff path in `encode_pure_impl` (encoder/mod.rs:792-803) is triggered
/// when `infer_expr_sort(l)` returns `Sort::Bool`. Tests above use
/// `var("result")` as LHS, which returns `Sort::Int` and does NOT reach the
/// iff path. This test uses Bool-sorted expressions as LHS of `Eq`/`Ne`.
#[test]
#[timeout(30000)]
fn test_bool_eq_postcondition_bool_sorted_lhs_exercises_iff_path() {
    // Body returns true when x > 0.
    let body = gt(var("x"), int(0));

    // Precondition: x = 5, so body = true, result = true.
    let pre = vec![eq(var("x"), int(5))];

    // Postcondition: (x > 0) == result.
    // LHS `gt(var("x"), int(0))` has infer_expr_sort = Sort::Bool, so the
    // iff encoding path at mod.rs:792-803 IS reached. With x = 5, (x > 0)
    // is true, and result is true (from body), so this should verify.
    let ens = eq(gt(var("x"), int(0)), var("result"));
    let result =
        verify_function_with_modes(VerificationRequest::new(&pre, &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "(x > 0) == result with x=5, body=(x > 0) should verify: {result:?}"
    );

    // Postcondition: (x > 0) != result — should FAIL because both are true.
    let ens_ne = ne(gt(var("x"), int(0)), var("result"));
    let result = verify_function_with_modes(
        VerificationRequest::new(&pre, &[ens_ne]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "(x > 0) != result with x=5, body=(x > 0) should fail: {result:?}"
    );
}

/// Regression test for #1227: Bool Ne with Bool-sorted LHS.
///
/// Exercises the `BinOp::Ne` branch of the iff encoding with a Bool-sorted
/// LHS expression, ensuring the negated iff `NOT((a => b) AND (b => a))` is
/// used instead of uninterpreted `ne`.
#[test]
#[timeout(30000)]
fn test_bool_ne_postcondition_bool_sorted_lhs_exercises_iff_path() {
    // Body returns NOT(x > 0), i.e., x <= 0.
    let body = not(gt(var("x"), int(0)));

    // Precondition: x = 5, so body = false.
    let pre = vec![eq(var("x"), int(5))];

    // Postcondition: (x > 0) != result.
    // LHS `gt(var("x"), int(0))` has Sort::Bool. x > 0 = true, result = false.
    // true != false = true, so this should verify.
    let ens = ne(gt(var("x"), int(0)), var("result"));
    let result =
        verify_function_with_modes(VerificationRequest::new(&pre, &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "(x > 0) != result with x=5, body=NOT(x > 0) should verify: {result:?}"
    );

    // Postcondition: (x > 0) == result — should FAIL (true != false).
    let ens_eq = eq(gt(var("x"), int(0)), var("result"));
    let result = verify_function_with_modes(
        VerificationRequest::new(&pre, &[ens_eq]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "(x > 0) == result with x=5, body=NOT(x > 0) should fail: {result:?}"
    );

    // Strengthened Ne coverage (#1227): (x > 0) != result where body = (x > 0).
    // Both sides are true, so ne should FAIL. This specifically requires the
    // negated-iff Ne encoding to produce the correct result.
    let body_same = gt(var("x"), int(0));
    let ens_ne_same = ne(gt(var("x"), int(0)), var("result"));
    let result = verify_function_with_modes(
        VerificationRequest::new(&pre, &[ens_ne_same]).return_expr(Some(&body_same)),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "(x > 0) != result with x=5, body=(x > 0) should fail (both true): {result:?}"
    );
}

/// Trivial invariant optimization (#1296): `#[invariant(true)]` skips quantified axiom.
///
/// Models Creusot `type_invariants/quant.rs`:
/// ```rust
/// #[invariant(true)]
/// struct WithInvariant;
///
/// #[logic]
/// #[ensures(forall<x: WithInvariant> x.invariant())]
/// fn forall_fn() {}
/// ```
///
/// Before the optimization, `forall<x> inv(x)` required ay to prove
/// `NOT(exists x. NOT inv(x))` via E-matching against the axiom
/// `forall x. inv(x) = true` — a two-step chain that ay couldn't solve.
/// With the optimization, `inv(x)` inlines to `true`, making the formula
/// `forall<x> true` trivially true.
#[test]
#[timeout(30000)]
fn test_trivial_invariant_skips_quantified_axiom() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("WithInvariant");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "WithInvariant".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: true,
        element_invariant_method: None,
    };

    // ensures: forall<x: WithInvariant> x.invariant()
    // With trivial invariant, this becomes forall<x> true, which is trivially verified.
    let forall_ens = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(method_call(var("x"), &inv_method, vec![])),
        triggers: vec![],
    };

    // No requires, no body (logic function)
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[forall_ens]).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    // InvariantTrueShortCircuit is LOW risk (non-demoting) per #2201,
    // so Verified passes through without demotion.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "forall<x> x.invariant() with trivial invariant(true) should verify: got {result:?}"
    );
}

/// Trivial invariant: identity function with `#[invariant(true)]` (#1296).
///
/// Models Creusot `bug/1208.rs` and `bug/464.rs` pattern:
/// ```rust
/// #[invariant(true)]
/// struct Q;
///
/// fn id(x: Q) -> Q {
///     x
/// }
/// // requires: x.invariant(), ensures: result.invariant()
/// ```
///
/// With the optimization, both `x.invariant()` and `result.invariant()`
/// inline to `true`, making the verification trivial.
#[test]
#[timeout(30000)]
fn test_trivial_invariant_identity_function() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Q");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Q".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant()  (trivially true)
    let req = method_call(var("x"), &inv_method, vec![]);
    // ensures: result.invariant()  (trivially true)
    let ens = method_call(var("result"), &inv_method, vec![]);
    // body: result = x
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    // InvariantTrueShortCircuit is LOW risk (non-demoting) per #2201.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "trivial invariant identity function should verify: got {result:?}"
    );
}

/// Trivial invariant with UN-QUALIFIED method name (#1296).
///
/// When a quantifier-bound variable calls `.invariant()` without type
/// qualification (as happens in `forall<x: WithInvariant> x.invariant()`
/// from `type_invariants/quant.rs`), the method name is just `"invariant"`
/// rather than the type-qualified `"__trust_wp_invariant_WithInvariant_..."`.
/// The fallback in `encode_bool_method_predicate` should detect that all
/// registered type invariants are trivially true and short-circuit to `true`.
#[test]
#[timeout(30000)]
fn test_trivial_invariant_unqualified_method_in_forall() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "WithInvariant".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: false,
        element_invariant_method: None,
    };

    // ensures: forall<x> x.invariant()
    // NOTE: uses un-qualified "invariant" (not __trust_wp_invariant_WithInvariant)
    let forall_ens = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(method_call(var("x"), "invariant", vec![])),
        triggers: vec![],
    };

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[forall_ens]).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    // InvariantTrueShortCircuit is LOW risk (non-demoting) per #2201.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "forall<x> x.invariant() with un-qualified method name and trivial invariant \
         should verify. Got: {result:?}"
    );
}

/// Mixed trivial + non-trivial invariants must NOT resolve un-qualified
/// `.invariant()` to `true` (#1296 soundness fix).
///
/// If TypeA has `invariant(self) = true` (trivial) and TypeB has
/// `invariant(self) = self > 0` (non-trivial), then an un-qualified
/// `.invariant()` call on a quantifier-bound variable CANNOT be assumed
/// `true` — it might refer to TypeB. The `all_type_invariants_trivially_true`
/// check must return false when any non-trivial invariant exists.
#[test]
#[timeout(30000)]
fn test_mixed_trivial_nontrivial_invariants_not_resolved_to_true() {
    // TypeA: trivial invariant (body = true)
    let trivial_inv = trust_wp_core::type_invariant_def! {
        type_name: "TypeA".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: bool_expr(true),
        is_newtype: false,
        element_invariant_method: None,
    };

    // TypeB: non-trivial invariant (body = self > 0)
    let nontrivial_inv = trust_wp_core::type_invariant_def! {
        type_name: "TypeB".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    // ensures: forall<x> x.invariant()
    // With mixed invariants, this should NOT verify — the un-qualified
    // `.invariant()` might refer to TypeB which is not trivially true.
    let forall_ens = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(method_call(var("x"), "invariant", vec![])),
        triggers: vec![],
    };

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[forall_ens])
            .type_invariants(Some(&[trivial_inv, nontrivial_inv])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "forall<x> x.invariant() with mixed trivial/non-trivial invariants \
         must fail instead of verifying as trivially true — un-qualified call might refer \
         to the non-trivial invariant. Got: {result:?}"
    );
}
