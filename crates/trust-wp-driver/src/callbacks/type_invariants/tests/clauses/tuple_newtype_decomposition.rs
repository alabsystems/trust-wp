// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    super::common::{
        collect_newtype_param_set, collect_newtype_param_set_with_invariant_flag,
        collect_type_invariant_clauses,
    },
    *,
};

// --- Tuple field decomposition tests (#946) ---

#[test]
fn build_newtype_param_set_includes_datatype_backed_single_field_structs() {
    // Single-field structs are always simplified because MIR-level aggregate
    // collapse (`Self(n)` → `n`) produces scalar results. Without newtype
    // simplification, `Var("self.0")` from closure-capture-style field
    // projection stays disconnected from `self`. (#2669)
    let source = r#"
#[allow(dead_code)]
pub struct PositiveU32(u32);

pub fn stronger(x: PositiveU32) -> PositiveU32 {
let _ = x;
x
}
"#;

    let newtype_params = collect_newtype_param_set(source, "stronger", &["x"]);
    assert!(
        newtype_params.contains("x"),
        "single-field struct params must be in newtype_params for field simplification, got {newtype_params:?}"
    );
    assert!(
        newtype_params.contains("result"),
        "single-field struct results must be in newtype_params for field simplification, got {newtype_params:?}"
    );
}

#[test]
fn build_newtype_param_set_includes_datatype_backed_invariant_newtypes() {
    // Same as above: single-field structs with type invariants must be
    // simplified to scalars to match MIR-level aggregate collapse. (#2669)
    let source = r#"
#[allow(dead_code)]
pub struct PositiveU32(u32);

pub fn stronger(x: PositiveU32) -> PositiveU32 {
let _ = x;
x
}
"#;

    let newtype_params =
        collect_newtype_param_set_with_invariant_flag(source, "stronger", &["x"], true);
    assert!(
        newtype_params.contains("x"),
        "invariant newtype params must be in newtype_params for field simplification, got {newtype_params:?}"
    );
    assert!(
        newtype_params.contains("result"),
        "invariant newtype results must be in newtype_params for field simplification, got {newtype_params:?}"
    );
}

/// Tuple parameter `x: (Sum10, i32)` should generate a precondition for
/// the invariant-bearing first field, but no postcondition (no &mut).
#[test]
fn tuple_param_generates_field_precondition() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn with_tuple(x: (Sum10, i32)) {
let _ = x;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(source, "with_tuple", &["x"]);
    assert_eq!(
        reqs.len(),
        1,
        "tuple (Sum10, i32) should produce 1 precondition, got {reqs:?}"
    );
    assert!(
        enss.is_empty(),
        "tuple without &mut fields should produce no postconditions, got {enss:?}"
    );
    match &reqs[0] {
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            assert!(
                method.contains("Sum10"),
                "expected method to reference Sum10, got {method}"
            );
            match receiver.as_ref() {
                PureExpr::LogicFnCall { name, args } => {
                    assert!(
                        name.contains("tuple_get_0"),
                        "expected tuple_get_0, got {name}"
                    );
                    assert_eq!(args.len(), 1);
                    assert!(
                        matches!(&args[0], PureExpr::Var(n, _) if n == "x"),
                        "expected Var(x), got {:?}",
                        args[0]
                    );
                }
                other => panic!("expected LogicFnCall, got {other:?}"),
            }
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

/// Tuple parameter `x: (Sum10, &mut Sum10)` should generate preconditions
/// for both fields plus a postcondition for the &mut field's final value.
#[test]
fn tuple_param_mut_ref_field_generates_postcondition() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn with_mut_tuple(x: (Sum10, &mut Sum10)) {
let _ = x;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(source, "with_mut_tuple", &["x"]);
    assert_eq!(
        reqs.len(),
        2,
        "tuple (Sum10, &mut Sum10) should produce 2 preconditions, got {reqs:?}"
    );
    assert_eq!(
        enss.len(),
        1,
        "tuple with one &mut field should produce 1 postcondition, got {enss:?}"
    );
    match &enss[0] {
        PureExpr::MethodCall { receiver, .. } => match receiver.as_ref() {
            PureExpr::Final(inner) => match inner.as_ref() {
                PureExpr::LogicFnCall { name, .. } => {
                    assert!(
                        name.contains("tuple_get_1"),
                        "expected tuple_get_1 in final value, got {name}"
                    );
                }
                other => panic!("expected LogicFnCall inside Final, got {other:?}"),
            },
            other => panic!("expected Final, got {other:?}"),
        },
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

/// Tuple parameter `x: &(Sum10, i32)` should dereference x before tuple_get.
#[test]
fn tuple_shared_ref_param_dereferences_before_field_access() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn with_ref_tuple(x: &(Sum10, i32)) {
let _ = x;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(source, "with_ref_tuple", &["x"]);
    assert_eq!(reqs.len(), 1, "expected one precondition, got {reqs:?}");
    assert!(
        enss.is_empty(),
        "shared ref tuple should produce no postconditions, got {enss:?}"
    );
    match &reqs[0] {
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            assert!(
                method.contains("Sum10"),
                "expected method to reference Sum10, got {method}"
            );
            match receiver.as_ref() {
                PureExpr::LogicFnCall { name, args } => {
                    assert!(
                        name.contains("tuple_get_0"),
                        "expected tuple_get_0, got {name}"
                    );
                    assert_eq!(args.len(), 1);
                    assert!(
                        matches!(
                            &args[0],
                            PureExpr::Deref(inner)
                                if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "x")
                        ),
                        "expected tuple_get_0(*x), got {:?}",
                        args[0]
                    );
                }
                other => panic!("expected LogicFnCall, got {other:?}"),
            }
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

/// Tuple parameter `x: (&Sum10, i32)` should dereference the reference
/// field before applying the invariant method.
#[test]
fn tuple_shared_ref_field_dereferences_before_invariant() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn with_ref_field(x: (&Sum10, i32)) {
let _ = x;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(source, "with_ref_field", &["x"]);
    assert_eq!(reqs.len(), 1, "expected one precondition, got {reqs:?}");
    assert!(
        enss.is_empty(),
        "shared ref field should produce no postconditions, got {enss:?}"
    );
    match &reqs[0] {
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            assert!(
                method.contains("Sum10"),
                "expected method to reference Sum10, got {method}"
            );
            match receiver.as_ref() {
                PureExpr::Deref(inner) => match inner.as_ref() {
                    PureExpr::LogicFnCall { name, args } => {
                        assert!(
                            name.contains("tuple_get_0"),
                            "expected tuple_get_0, got {name}"
                        );
                        assert_eq!(args.len(), 1);
                        assert!(
                            matches!(&args[0], PureExpr::Var(n, _) if n == "x"),
                            "expected tuple_get_0(x), got {:?}",
                            args[0]
                        );
                    }
                    other => panic!("expected LogicFnCall inside Deref, got {other:?}"),
                },
                other => panic!("expected Deref receiver, got {other:?}"),
            }
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

/// Tuple of only primitives `(i32, bool)` should produce no clauses.
#[test]
fn tuple_all_primitive_fields_produces_no_clauses() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn with_prim_tuple(_x: (i32, bool), _y: Sum10) {
let _ = _x;
let _ = _y;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(source, "with_prim_tuple", &["_x", "_y"]);
    assert_eq!(
        reqs.len(),
        1,
        "only direct Sum10 param should produce a precondition, got {reqs:?}"
    );
    assert!(
        enss.is_empty(),
        "no &mut params should produce no postconditions, got {enss:?}"
    );
}
