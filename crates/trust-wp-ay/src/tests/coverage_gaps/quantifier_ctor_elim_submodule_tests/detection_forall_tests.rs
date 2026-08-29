// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// `detect_constructor_eq` on a Forall body with Implies guard detects the
/// constructor equality in the LHS of the implication.
#[test]
#[timeout(30000)]
fn test_detect_forall_implies_guard_detects_constructor_eq() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    // forall<v> (x == Some(v)) ==> v > 0
    let guard = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));
    let body = implies(guard, gt(var("v"), int(0)));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Forall, &body, &["v"]);
    assert!(
        info.is_some(),
        "Forall with Implies guard should detect constructor equality"
    );
    let info = info.unwrap();
    assert_eq!(info.ctor_name, "OptionInt::Some");
    assert_eq!(info.var_field_map, vec![("v", 0)]);
    assert!(info.inner_ctor.is_none());
}

/// `detect_constructor_eq` on a Forall body WITHOUT Implies returns None (#1781).
#[test]
#[timeout(30000)]
fn test_detect_forall_non_implies_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    // forall<v> x == Some(v)  (bare Eq, not wrapped in Implies)
    let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Forall, &body, &["v"]);
    assert!(
        info.is_none(),
        "Forall without Implies body must return None (#1781)"
    );
}

/// `detect_constructor_eq` on a Forall body with And (not Implies) returns None.
#[test]
#[timeout(30000)]
fn test_detect_forall_and_body_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    // forall<v> (x == Some(v)) && (v > 0)
    let body = and(
        eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")])),
        gt(var("v"), int(0)),
    );

    let info = detect_constructor_eq(&encoder, QuantifierKind::Forall, &body, &["v"]);
    assert!(
        info.is_none(),
        "Forall with And body must return None (#1781)"
    );
}

/// Forall with Implies and reversed equality: `forall<v> Some(v) == x ==> P(v)`.
#[test]
#[timeout(30000)]
fn test_detect_forall_implies_reversed_equality() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    // forall<v> (Some(v) == x) ==> v > 0
    let guard = eq(logic_fn_call("OptionInt::Some", vec![var("v")]), var("x"));
    let body = implies(guard, gt(var("v"), int(0)));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Forall, &body, &["v"]);
    assert!(
        info.is_some(),
        "reversed equality in Implies guard should be detected"
    );
    let info = info.unwrap();
    assert_eq!(info.ctor_name, "OptionInt::Some");
}
