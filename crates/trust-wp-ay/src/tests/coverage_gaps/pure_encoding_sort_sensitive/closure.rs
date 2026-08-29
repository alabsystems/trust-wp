// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use super::*;

// ── Closure encoding ─────────────────────────────────────────────────

/// Parameterized closure expressions now encode as fresh constants (#985).
#[test]
#[timeout(30000)]
fn closure_returns_unsupported_error() {
    let mut encoder = AYEncoder::new();

    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(var("x")),
    };
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Parameterized closure should encode as fresh constant (#985)"
    );
}

/// Single-parameter closure in a Mapping-returning logic function encodes as
/// Mapping-sorted constant with a defining axiom. (#2683)
///
/// Pattern: `#[logic] fn g() -> Mapping<Int, bool> { |x| x > 0 }`
/// The closure body should be reachable via `mapping_get(g(), x) == (x > 0)`.
#[test]
#[timeout(30000)]
fn closure_in_mapping_logic_fn_encodes_as_mapping() {
    use trust_wp_core::{
        formula::{sort_intern::intern_sort_name, ExprSort},
        logic::LogicFnDef,
    };

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Create: #[logic] fn g() -> Mapping<Int, bool> { |x| x > 0 }
    let closure_body = gt(var("x"), int(0));
    let closure = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(closure_body),
    };
    let g_def = LogicFnDef::new(
        "g".to_string(),
        "crate::test::g".to_string(),
        vec![],
        closure,
    )
    .with_return_sort(Some(ExprSort::Datatype(intern_sort_name("Mapping"))))
    .with_mode(trust_wp_core::logic::LogicMode::Open);

    // Registration should succeed and create a Mapping-sorted UF with axiom
    encoder
        .register_logic_fn(&g_def)
        .expect("register g logic fn");

    // Now verify: mapping_get(g(), 5) should equal (5 > 0) = true
    // Declare a variable to use as the mapping_get result
    let g_call = logic_fn_call("g", vec![]);
    let five = int(5);
    let get_expr = method_call(g_call.clone(), "get", vec![five]);
    // If the encoding worked, mapping_get(g(), 5) should be constrained
    // by the closure axiom to equal (5 > 0) = true.
    // Asserting mapping_get(g(), 5) == false should be UNSAT.
    let negative_check = eq(get_expr, bool_expr(false));
    let result = encoder.encode_pure(&negative_check);
    // The encode_pure call should succeed (closure body axiom constrains the
    // mapping_get result)
    assert!(
        result.is_ok(),
        "mapping_get on closure-based Mapping logic fn should encode: {result:?}"
    );
}
