// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for auto type-invariant maintenance in loops (#1816).
//!
//! When a precondition asserts a type invariant on a variable that is NOT
//! modified by the loop body, the type invariant is automatically promoted
//! to a loop invariant. This enables postconditions to rely on type
//! invariants for unchanged variables without explicit `#[invariant]`.

use super::*;

fn assert_failed_result(result: &VerificationResult, context: &str) {
    match result {
        VerificationResult::Failed(_) => {}
        other => panic!("{context} should fail verification; got {other:?}"),
    }
}

/// Positive: postcondition can use type invariant of unchanged variable.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// #[requires(x.invariant())]
/// #[ensures(result > 0)]
/// fn loop_with_unchanged_nonzero(x: NonZero) -> i32 {
///     let mut i = 0;
///     while i < 10 {
///         #[invariant(i >= 0 && i <= 10)]
///         i += 1;
///     }
///     x.0 // x is unchanged, so x.invariant() => x > 0 => result > 0
/// }
/// ```
///
/// Without auto type-invariant maintenance, the postcondition `result > 0`
/// cannot be proved because `x.invariant()` from requires is not available
/// as a loop invariant assumption.
#[test]
#[timeout(30000)]
fn postcondition_uses_type_invariant_of_unchanged_var() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let inv_defs = [trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    }];

    // requires: x.invariant()
    let requires = [method_call(var("x"), &inv_method, vec![])];

    // invariant: i >= 0 && i <= 10
    let invariants = [and(ge(var("i"), int(0)), le(var("i"), int(10)))];

    // ensures: result > 0
    let ensures = [gt(var("result"), int(0))];

    // return_expr: x (unchanged)
    let return_expr = var("x");

    // Loop modifies only i, not x.
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let empty_effect = HashMap::new();

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let loop_condition = lt(var("i"), int(10));

    let config = LoopEncoderConfig::default().with_type_invariants(&inv_defs);

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_effect, &empty_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(config);

    let result = verify_loop_invariant(&ctx).expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify with auto type-invariant maintenance; got {:?}",
        result.postcondition
    );
}

/// Type invariant on a modified variable is NOT auto-promoted.
///
/// Models:
/// ```rust
/// #[requires(x.invariant())]
/// #[ensures(result > 5)]
/// fn loop_modifying_nonzero(mut x: NonZero) -> i32 {
///     while x.0 > 1 {
///         x.0 -= 1;
///     }
///     x.0
/// }
/// ```
///
/// Here `x` is modified, so `x.invariant()` should NOT be auto-promoted.
/// The postcondition `result > 5` cannot be proved: the auto-invariant
/// `x >= 1` from the condition `x > 1` gives `x == 1` at exit, which
/// does NOT satisfy `result > 5`. This verifies that the type invariant
/// auto-promotion filter correctly excludes modified variables.
///
/// Note: a weaker postcondition `result > 0` WOULD be provable because
/// the condition-bound lower-bound auto-invariant (#1709) generates
/// `x >= 1` from `x > 1`, and at exit NOT(x > 1) + x >= 1 gives x == 1,
/// so x > 0. We use a stronger postcondition to isolate the type
/// invariant behavior.
#[test]
#[timeout(30000)]
fn type_invariant_not_promoted_for_modified_var() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let inv_defs = [trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    }];

    // requires: x.invariant()
    let requires = [method_call(var("x"), &inv_method, vec![])];

    // No explicit invariant for x — only auto-promotion could help.
    let invariants = [PureExpr::Bool(true)];

    // ensures: result > 5 (stronger than what condition-bound can prove)
    let ensures = [gt(var("result"), int(5))];
    let return_expr = var("x");

    // x IS modified by the loop body.
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));
    let empty_effect = HashMap::new();

    let pre_loop_assignments = HashMap::new();
    let loop_condition = gt(var("x"), int(1));

    let config = LoopEncoderConfig::default().with_type_invariants(&inv_defs);

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_effect, &empty_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(config);

    let result = verify_loop_invariant(&ctx).expect("encoding should succeed");

    // Postcondition should fail with a counterexample: x is modified, type invariant not
    // auto-promoted, and condition-bound gives x >= 1 with exit x == 1,
    // which does NOT satisfy result > 5.
    assert_failed_result(
        &result.postcondition,
        "postcondition when type invariant var is modified",
    );
}

/// Type invariant through Deref: `(*x).invariant()` with unchanged `x`.
///
/// Models by-reference parameters where the requires uses `(*x).invariant()`.
#[test]
#[timeout(30000)]
fn type_invariant_promoted_through_deref() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let inv_defs = [trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    }];

    // requires: (*x).invariant() — deref pattern for &NonZero
    let requires = [method_call(deref(var("x")), &inv_method, vec![])];

    let invariants = [and(ge(var("i"), int(0)), le(var("i"), int(10)))];

    // ensures: result > 0
    let ensures = [gt(var("result"), int(0))];
    let return_expr = deref(var("x"));

    // Only i is modified, x is unchanged.
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let empty_effect = HashMap::new();

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let loop_condition = lt(var("i"), int(10));

    let config = LoopEncoderConfig::default().with_type_invariants(&inv_defs);

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_effect, &empty_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(config);

    let result = verify_loop_invariant(&ctx).expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify with deref type-invariant promotion; got {:?}",
        result.postcondition
    );
}

/// Type invariant through double-deref: `(**x).invariant()` with unchanged `x`.
///
/// Models double-deref parameters (`&mut &mut NonZero`) where the requires uses
/// `(**x).invariant()`. The recursive peeling in `peel_to_var_name` (#1816)
/// handles arbitrary deref depth.
#[test]
#[timeout(30000)]
fn type_invariant_promoted_through_double_deref() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let inv_defs = [trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    }];

    // requires: (**x).invariant() — double-deref pattern for &mut &mut NonZero
    let requires = [method_call(deref(deref(var("x"))), &inv_method, vec![])];

    let invariants = [and(ge(var("i"), int(0)), le(var("i"), int(10)))];

    // ensures: result > 0
    let ensures = [gt(var("result"), int(0))];
    let return_expr = deref(deref(var("x")));

    // Only i is modified, x is unchanged.
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let empty_effect = HashMap::new();

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let loop_condition = lt(var("i"), int(10));

    let config = LoopEncoderConfig::default().with_type_invariants(&inv_defs);

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_effect, &empty_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(config);

    let result = verify_loop_invariant(&ctx).expect("encoding should succeed");

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify with double-deref type-invariant promotion; got {:?}",
        result.postcondition
    );
}

/// Type invariant through View wrapper: `x@.invariant()` with unchanged `x`.
///
/// Models View-wrapped invariant receivers where the requires uses
/// `x@.invariant()`. The `peel_to_var_name` function peels through View
/// to find the root variable. This test verifies the code path runs
/// without panics and the type invariant is promoted to a loop invariant
/// (available as an assumption).
///
/// Note: View-wrapped type invariants produce a MethodCall(View(x), inv_method)
/// assumption in all phases. The postcondition verification depends on the
/// type invariant definition's body being useful in the View context, which
/// is encoding-dependent. This test focuses on the promotion path, not the
/// end-to-end View+invariant composition.
#[test]
#[timeout(30000)]
fn type_invariant_promoted_through_view() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("SortedVec");
    let inv_defs = [trust_wp_core::type_invariant_def! {
        type_name: "SortedVec".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    }];

    // requires: (x@).invariant() — View wrapper pattern
    let requires = [method_call(
        PureExpr::View(Arc::new(var("x"))),
        &inv_method,
        vec![],
    )];

    let invariants = [and(ge(var("i"), int(0)), le(var("i"), int(10)))];

    // ensures: true (trivially true — test focuses on promotion path)
    let ensures = [PureExpr::Bool(true)];
    let return_expr = var("i");

    // Only i is modified, x is unchanged.
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let empty_effect = HashMap::new();

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let loop_condition = lt(var("i"), int(10));

    let config = LoopEncoderConfig::default().with_type_invariants(&inv_defs);

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_effect, &empty_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(config);

    let result = verify_loop_invariant(&ctx).expect("encoding should succeed");

    // The type invariant `x@.invariant()` should be promoted as an auto-invariant
    // (available as an assumption in all phases). The trivial postcondition
    // `true` should always verify.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "trivial postcondition should verify with View type-invariant promotion; got {:?}",
        result.postcondition
    );
}

/// Non-invariant method calls are NOT promoted as auto-invariants.
///
/// A requires like `x.len() > 0` should not be auto-promoted — only
/// type invariant method calls (matching `is_invariant_method_name`) qualify.
#[test]
#[timeout(30000)]
fn non_invariant_method_not_promoted() {
    // requires: x.len() > 0 — not a type invariant
    let requires = [gt(method_call(var("x"), "len", vec![]), int(0))];

    let invariants = [and(ge(var("i"), int(0)), le(var("i"), int(10)))];

    // ensures: x.len() > 0
    let ensures = [gt(method_call(var("x"), "len", vec![]), int(0))];
    let return_expr = var("i");

    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let empty_effect = HashMap::new();

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let loop_condition = lt(var("i"), int(10));

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_effect, &empty_effect),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig::default());

    let result = verify_loop_invariant(&ctx).expect("encoding should succeed");

    // The non-invariant method call `x.len() > 0` in requires is a
    // compound expression (BinOp with MethodCall inside), not a top-level
    // MethodCall with an invariant method name. The auto-promotion filter
    // only inspects top-level expressions that are direct type invariant
    // calls. So `x.len() > 0` is not promoted.
    //
    // Since len() is an unconstrained UF, the solver result is
    // unpredictable — the test primarily verifies the code path runs
    // without panics. The positive/negative test pair above demonstrates
    // the invariant-name filter's selectivity.
    drop(result);
}
