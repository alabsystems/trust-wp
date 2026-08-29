// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(30000)]
fn test_unknown_method_returns_error() {
    // x.some_custom_method() should return EncodingError (#1820).
    // Previously fell through to an Int UF, which was unsound.
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("x"), "some_custom_method", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "Unknown method should produce EncodingError, got: {result:?}"
    );
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("some_custom_method"),
        "error should name the method, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_registered_logic_fn_routed_via_method_syntax() {
    // When a logic function is registered (e.g., "sub_pre"), calling it
    // as a method (receiver.sub_pre(args)) should route through the logic
    // function encoder rather than creating a raw UF.
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register logic function "sub_pre" with 2 Int params -> Bool
    let logic_fn = LogicFnDef::new(
        "sub_pre".to_string(),
        "sub_pre".to_string(),
        vec!["a".to_string(), "b".to_string()],
        gt(var("a"), var("b")),
    )
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("registration should succeed");

    // Call as method syntax: x.sub_pre(y)
    // This should rewrite to sub_pre(x, y) and use the registered function
    let expr = method_call(var("x"), "sub_pre", vec![var("y")]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("Method-syntax logic function call should succeed");
    // The logic function's SMT name should be present (with "logic_" prefix)
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("sub_pre");
    assert!(
        encoder.decls().has_logic_func(&smt_name),
        "Should use registered logic function '{smt_name}'; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_registered_logic_fn_typeparam_receiver_method_syntax_avoids_sort_fallback() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{LogicFnDef, LogicMode},
    };

    use crate::encoder::unsoundness;

    let mut encoder = AYEncoder::new_with_quantifiers();
    let self_sort = intern_sort_name("Self");
    let logic_fn = LogicFnDef::new(
        "logic_default".to_string(),
        "test::T::logic_default".to_string(),
        vec!["receiver".to_string()],
        eq(var("receiver"), var("receiver")),
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::TypeParam(self_sort))]);

    let before = unsoundness::snapshot();
    encoder
        .register_logic_fn(&logic_fn)
        .expect("registration should resolve TypeParam receiver sorts");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("logic_default");
    let func_decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .expect("logic_default should be declared");
    let domain = func_decl.domain();
    assert_eq!(
        domain.len(),
        1,
        "logic_default should have exactly one receiver parameter"
    );
    assert_eq!(
        domain[0],
        Sort::Int,
        "TypeParam receiver sorts should resolve to Int at declaration time"
    );

    let call = method_call(int(42), "logic_default", vec![]);
    let call_term = encoder
        .encode_pure(&call)
        .expect("method-syntax call should encode without sort fallback");
    let not_call = encoder.solver.not(call_term);
    encoder.assert_term(not_call);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "logic_default(42) should reduce to 42 == 42"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        !delta.contains_key(&unsoundness::UnsoundnessCategory::SortFallbackToInt),
        "method-syntax receiver specialization should avoid SortFallbackToInt: {delta:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_registered_intersection_logic_fn_not_shadowed_by_fset_dispatch() {
    // Regression guard for #1124 follow-up: if a logic function named
    // "intersection" is registered, method syntax must route to logic-fn
    // encoding instead of hardcoded FSet dispatch.
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "intersection".to_string(),
        "intersection".to_string(),
        vec!["a".to_string(), "b".to_string()],
        gt(var("a"), var("b")),
    )
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("registration should succeed");

    let expr = method_call(var("x"), "intersection", vec![var("y")]);
    let _term = encoder
        .encode_pure(&expr)
        .expect("registered intersection should route to logic-fn path");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("intersection");
    assert!(
        encoder.decls().has_logic_func(&smt_name),
        "Expected registered logic-fn decl '{smt_name}'; found {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_spec_func("fset_intersection"),
        "Logic-fn route should not declare fset_intersection UF"
    );
}

#[test]
#[timeout(30000)]
fn test_registered_difference_logic_fn_not_shadowed_by_fset_dispatch() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "difference".to_string(),
        "difference".to_string(),
        vec!["a".to_string(), "b".to_string()],
        gt(var("a"), var("b")),
    )
    .with_mode(LogicMode::Open);
    encoder
        .register_logic_fn(&logic_fn)
        .expect("registration should succeed");

    let expr = method_call(var("x"), "difference", vec![var("y")]);
    let _term = encoder
        .encode_pure(&expr)
        .expect("registered difference should route to logic-fn path");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("difference");
    assert!(
        encoder.decls().has_logic_func(&smt_name),
        "Expected registered logic-fn decl '{smt_name}'; found {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_spec_func("fset_difference"),
        "Logic-fn route should not declare fset_difference UF"
    );
}

#[test]
#[timeout(30000)]
fn test_registered_peek_logic_fn_not_shadowed_by_fset_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_open_logic_fn(&mut encoder, "peek", &["a"]);

    let expr = method_call(var("x"), "peek", vec![]);
    let _term = encoder
        .encode_pure(&expr)
        .expect("registered peek should route to logic-fn path");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("peek");
    assert!(
        encoder.decls().has_logic_func(&smt_name),
        "Expected registered logic-fn decl '{smt_name}'; found {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_spec_func("fset_peek"),
        "Logic-fn route should not declare fset_peek UF"
    );
}

#[test]
#[timeout(30000)]
fn test_registered_remove_logic_fn_not_shadowed_by_fset_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_open_logic_fn(&mut encoder, "remove", &["a", "b"]);

    let expr = method_call(var("x"), "remove", vec![var("y")]);
    let _term = encoder
        .encode_pure(&expr)
        .expect("registered remove should route to logic-fn path");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("remove");
    assert!(
        encoder.decls().has_logic_func(&smt_name),
        "Expected registered logic-fn decl '{smt_name}'; found {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_spec_func("fset_remove"),
        "Logic-fn route should not declare fset_remove UF"
    );
}

#[test]
#[timeout(30000)]
fn test_registered_is_empty_logic_fn_not_shadowed_by_fset_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_open_logic_fn(&mut encoder, "is_empty", &["a"]);

    let expr = method_call(var("x"), "is_empty", vec![]);
    let _term = encoder
        .encode_pure(&expr)
        .expect("registered is_empty should route to logic-fn path");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("is_empty");
    assert!(
        encoder.decls().has_logic_func(&smt_name),
        "Expected registered logic-fn decl '{smt_name}'; found {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_spec_func("fset_is_empty"),
        "Logic-fn route should not declare fset_is_empty UF"
    );
}

#[test]
#[timeout(30000)]
fn test_registered_contains_logic_fn_not_shadowed_by_fset_dispatch() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    register_open_logic_fn(&mut encoder, "contains", &["a", "b"]);

    let expr = method_call(var("x"), "contains", vec![var("y")]);
    let _term = encoder
        .encode_pure(&expr)
        .expect("registered contains should route to logic-fn path");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("contains");
    assert!(
        encoder.decls().has_logic_func(&smt_name),
        "Expected registered logic-fn decl '{smt_name}'; found {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
    assert!(
        !encoder.decls().has_spec_func("fset_contains"),
        "Logic-fn route should not declare fset_contains UF"
    );
}

#[test]
#[timeout(30000)]
fn test_unknown_method_with_args_returns_error() {
    // x.custom(y, z) should return EncodingError (#1820).
    // Previously fell through to an Int UF.
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("x"), "custom", vec![var("y"), var("z")]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "Unknown method with args should produce EncodingError, got: {result:?}"
    );
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("custom"),
        "error should name the method, got: {msg}"
    );
}
