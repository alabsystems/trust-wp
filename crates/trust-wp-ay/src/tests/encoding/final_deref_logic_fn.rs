// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Tests for Final/Deref of LogicFnCall rewrite (tuple field accessors and struct fields)
use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encode_final_of_tuple_get_succeeds() {
    // ^(x.0) encoded as Final(LogicFnCall{tuple_get_0, [Var("x")]})
    // should succeed by rewriting to LogicFnCall{tuple_get_0, [Final(Var("x"))]}
    // i.e., tuple_get_0(^x)
    let mut encoder = AYEncoder::new();

    let expr = final_expr(logic_fn_call("__trust_wp_tuple_get_0", vec![var("x")]));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of tuple_get_0 should succeed via rewrite");
    // The rewrite pushes Final inside: tuple_get_0(^x)
    // ^x -> x_final variable
    assert!(
        encoder.vars_for_test().contains_key("x_final"),
        "Should create x_final variable for ^x inside tuple_get_0"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_tuple_get_1_succeeds() {
    // ^(p.1) encoded as Final(LogicFnCall{tuple_get_1, [Var("p")]})
    let mut encoder = AYEncoder::new();

    let expr = final_expr(logic_fn_call("__trust_wp_tuple_get_1", vec![var("p")]));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of tuple_get_1 should succeed via rewrite");
    assert!(
        encoder.vars_for_test().contains_key("p_final"),
        "Should create p_final variable for ^p inside tuple_get_1"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_tuple_get_deref_succeeds() {
    // ^((*b).1) encoded as Final(LogicFnCall{tuple_get_1, [Deref(Var("b"))]})
    // should rewrite to tuple_get_1(^(*b)) = tuple_get_1(Final(Deref(Var("b"))))
    // ^(*b) -> b_current_final
    let mut encoder = AYEncoder::new();

    let expr = final_expr(logic_fn_call(
        "__trust_wp_tuple_get_1",
        vec![deref(var("b"))],
    ));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of tuple_get_1 with deref arg should succeed");
    assert!(
        encoder.vars_for_test().contains_key("b_current_final"),
        "Should create b_current_final variable for ^(*b)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_deref_of_tuple_get_succeeds() {
    // *(x.0) encoded as Deref(LogicFnCall{tuple_get_0, [Var("x")]})
    // should rewrite to tuple_get_0(*x)
    let mut encoder = AYEncoder::new();

    let expr = deref(logic_fn_call("__trust_wp_tuple_get_0", vec![var("x")]));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Deref of tuple_get_0 should succeed via rewrite");
    assert!(
        encoder.vars_for_test().contains_key("x_current"),
        "Should create x_current variable for *x inside tuple_get_0"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_struct_field_succeeds() {
    // ^(x.a) encoded as Final(LogicFnCall{__trust_wp_field_a, [Var("x")]})
    // should rewrite to __trust_wp_field_a(^x)
    let mut encoder = AYEncoder::new();

    let expr = final_expr(logic_fn_call("__trust_wp_field_a", vec![var("x")]));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of struct field accessor should succeed via rewrite");
    assert!(
        encoder.vars_for_test().contains_key("x_final"),
        "Should create x_final variable for ^x inside field accessor"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_deref_of_struct_field_succeeds() {
    // *(x.a) encoded as Deref(LogicFnCall{__trust_wp_field_a, [Var("x")]})
    // should rewrite to __trust_wp_field_a(*x)
    let mut encoder = AYEncoder::new();

    let expr = deref(logic_fn_call("__trust_wp_field_a", vec![var("x")]));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Deref of struct field accessor should succeed via rewrite");
    assert!(
        encoder.vars_for_test().contains_key("x_current"),
        "Should create x_current variable for *x inside field accessor"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_deref_of_view_succeeds() {
    // *(rc@) encoded as Deref(View(Var("rc")))
    // should rewrite to View(Deref(Var("rc"))) = (*rc)@
    // which resolves to "rc_current_view" via the View arm
    let mut encoder = AYEncoder::new();

    let expr = deref(view(var("rc")));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Deref of view should succeed via rewrite to View(Deref(..))");
    assert!(
        encoder.vars_for_test().contains_key("rc_current_view"),
        "Should create rc_current_view variable for (*rc)@"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_deref_of_method_call_succeeds() {
    // *(x.len()) encoded as Deref(MethodCall{receiver: Var("x"), method: "len", args: []})
    // should rewrite to (*x).len()
    // Seq normalize wraps receiver in View: View(Deref(Var("x"))) => x_current_view
    // Requires prescan of the rewritten form for is_seq_receiver dispatch (#756).
    let mut encoder = AYEncoder::new();

    let expr = deref(method_call(var("x"), "len", vec![]));

    // Prescan the rewritten form: (*x).len() so is_seq_receiver finds x_current_view as Seq
    let rewritten = method_call(deref(var("x")), "len", vec![]);
    encoder.register_sort_hints(std::slice::from_ref(&rewritten));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Deref of method call should succeed via rewrite");
    assert!(
        encoder.vars_for_test().contains_key("x_current_view"),
        "Should create x_current_view for (*x)@ via Seq receiver normalization"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_binop_distributes() {
    // ^(x + y) distributes Final into BinOp operands: Final(x) + Final(y)
    // → x_final + y_final (#2700).
    let mut encoder = AYEncoder::new();

    let expr = final_expr(add(var("x"), var("y")));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Final(BinOp) should succeed via BinOp distribution (#2700): {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_method_call_succeeds() {
    // ^(x.len()) encoded as Final(MethodCall{receiver: Var("x"), method: "len", args: []})
    // should rewrite to MethodCall{receiver: Final(Var("x")), method: "len", args: []}
    // i.e., (^x).len()
    //
    // For Seq methods, normalize_seq_receiver wraps the receiver in View,
    // so Final(Var("x")) becomes View(Final(Var("x"))) => "final_x_view".
    // Requires prescan to mark receiver as Seq (#756 dispatch).
    let mut encoder = AYEncoder::new();

    let expr = final_expr(method_call(var("x"), "len", vec![]));

    // Prescan the rewritten form: (^x).len() so is_seq_receiver finds final_x_view as Seq.
    // The encoding rewrites ^(x.len()) → (^x).len(), changing the receiver name (#756).
    let rewritten = method_call(final_expr(var("x")), "len", vec![]);
    encoder.register_sort_hints(std::slice::from_ref(&rewritten));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of method call should succeed via rewrite");
    // Seq method normalize wraps receiver in View: View(Final(Var("x"))) => final_x_view
    assert!(
        encoder.vars_for_test().contains_key("final_x_view"),
        "Should create final_x_view variable for (^x)@ via Seq receiver normalization"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_view_succeeds() {
    // ^(x@) encoded as Final(View(Var("x")))
    // should rewrite to View(Final(Var("x"))) = (^x)@
    // which resolves to "final_x_view" via the View arm's Final handling
    let mut encoder = AYEncoder::new();

    let expr = final_expr(view(var("x")));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of view should succeed via rewrite to View(Final(..))");
    assert!(
        encoder.vars_for_test().contains_key("final_x_view"),
        "Should create final_x_view variable for ^(x@) = (^x)@"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_method_call_with_args_succeeds() {
    // ^(x.get(i)) encoded as Final(MethodCall{receiver: Var("x"), method: "get", args: [Var("i")]})
    // should rewrite to (^x).get(^i) — VARIABLE arguments keep the legacy
    // full distribution (#124 exempts only GROUND-CONSTANT arguments).
    //
    // Seq method normalize wraps receiver in View: View(Final(Var("x"))) => final_x_view
    // The arg ^i goes through encode_pure for Int arg: Final(Var("i")) => i_final
    // Requires prescan of the rewritten form for is_seq_receiver dispatch (#756).
    let mut encoder = AYEncoder::new();

    let expr = final_expr(method_call(var("x"), "get", vec![var("i")]));

    // Prescan the rewritten form: (^x).get(^i) so is_seq_receiver finds final_x_view as Seq
    let rewritten = method_call(final_expr(var("x")), "get", vec![final_expr(var("i"))]);
    encoder.register_sort_hints(std::slice::from_ref(&rewritten));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of method call with args should succeed");
    assert!(
        encoder.vars_for_test().contains_key("final_x_view"),
        "Should create final_x_view for (^x)@ via Seq receiver normalization"
    );
    assert!(
        encoder.vars_for_test().contains_key("i_final"),
        "Should create i_final for ^i argument"
    );
}

#[test]
#[timeout(30000)]
fn test_final_tuple_get_with_axioms_verifies() {
    // Semantic test: when result = tuple2(x, y), then tuple_get_0(result) == x.
    // This tests that tuple axioms work so that the Final rewrite is meaningful.
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name,
    };

    use crate::verify::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // body: result = __trust_wp_tuple2(x, y)
    let body = logic_fn_call(&tuple_logic_fn_name(2), vec![var("x"), var("y")]);

    // ensures: __trust_wp_tuple_get_0(result) == x
    let ensures = eq(
        logic_fn_call(&tuple_field_logic_fn_name(0), vec![var("result")]),
        var("x"),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "tuple_get_0(tuple2(x, y)) == x should verify with axioms: {result:?}"
    );
}
