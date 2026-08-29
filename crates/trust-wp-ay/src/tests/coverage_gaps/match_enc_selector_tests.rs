// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for match_enc ADT constructor/selector functions with
//! zero prior test coverage:
//! - `AYEncoder::datatype_from_adt_decl`
//! - `AYEncoder::nullary_constructor_datatype`
//! - `AYEncoder::constructor_payload_selector` (static)
//! - `AYEncoder::constructor_multi_field_selectors` (static)

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use ntest::timeout;
use trust_wp_core::{
    formula::ExprSort,
    logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
};

use crate::encoder::AYEncoder;

// ── Helpers ─────────────────────────────────────────────────────────

fn option_int_adt() -> AdtDecl {
    AdtDecl::new(
        "std::option::Option<i32>".to_string(),
        "OptionInt".to_string(),
        AdtKind::Enum,
        vec![
            AdtConstructorDecl::new(
                "Some".to_string(),
                "Some".to_string(),
                vec![AdtFieldDecl::new("0".to_string(), ExprSort::Int)],
            ),
            AdtConstructorDecl::new("None".to_string(), "None".to_string(), vec![]),
        ],
    )
}

fn point_struct_adt() -> AdtDecl {
    AdtDecl::new(
        "my_mod::Point".to_string(),
        "Point".to_string(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "Point".to_string(),
            "Point".to_string(),
            vec![
                AdtFieldDecl::new("x".to_string(), ExprSort::Int),
                AdtFieldDecl::new("y".to_string(), ExprSort::Int),
            ],
        )],
    )
}

fn wrapper_struct_adt() -> AdtDecl {
    AdtDecl::new(
        "my_mod::Wrapper".to_string(),
        "Wrapper".to_string(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "Wrapper".to_string(),
            "Wrapper".to_string(),
            vec![AdtFieldDecl::new("inner".to_string(), ExprSort::Int)],
        )],
    )
}

fn traffic_light_enum_adt() -> AdtDecl {
    AdtDecl::new(
        "my_mod::Light".to_string(),
        "Light".to_string(),
        AdtKind::Enum,
        vec![
            AdtConstructorDecl::new("Red".to_string(), "Red".to_string(), vec![]),
            AdtConstructorDecl::new("Yellow".to_string(), "Yellow".to_string(), vec![]),
            AdtConstructorDecl::new("Green".to_string(), "Green".to_string(), vec![]),
        ],
    )
}

fn option_int_ay_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "optionint_some_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    }
}

fn point_ay_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "Point".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Point".to_string(),
            fields: vec![
                DatatypeField {
                    name: "point_x".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "point_y".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    }
}

// ── datatype_from_adt_decl ──────────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_datatype_from_adt_decl_enum_option_int() {
    let mut encoder = AYEncoder::new();
    let decl = option_int_adt();
    let dt = encoder.datatype_from_adt_decl(&decl);

    assert_eq!(dt.name, "OptionInt");
    assert_eq!(dt.constructors.len(), 2);

    let some_ctor = &dt.constructors[0];
    assert_eq!(some_ctor.name, "Some");
    assert_eq!(some_ctor.fields.len(), 1);
    // Enum field selector: lowered_adt_lowered_ctor_field
    assert_eq!(some_ctor.fields[0].name, "optionint_some_0");
    assert_eq!(some_ctor.fields[0].sort, Sort::Int);

    let none_ctor = &dt.constructors[1];
    assert_eq!(none_ctor.name, "None");
    assert!(none_ctor.fields.is_empty());
}

#[test]
#[timeout(30000)]
fn test_datatype_from_adt_decl_struct_point() {
    let mut encoder = AYEncoder::new();
    let decl = point_struct_adt();
    let dt = encoder.datatype_from_adt_decl(&decl);

    assert_eq!(dt.name, "Point");
    assert_eq!(dt.constructors.len(), 1);

    let ctor = &dt.constructors[0];
    assert_eq!(ctor.name, "Point");
    assert_eq!(ctor.fields.len(), 2);
    // Struct field selector: lowered_adt_field
    assert_eq!(ctor.fields[0].name, "point_x");
    assert_eq!(ctor.fields[1].name, "point_y");
}

#[test]
#[timeout(30000)]
fn test_datatype_from_adt_decl_single_field_struct() {
    let mut encoder = AYEncoder::new();
    let decl = wrapper_struct_adt();
    let dt = encoder.datatype_from_adt_decl(&decl);

    assert_eq!(dt.name, "Wrapper");
    assert_eq!(dt.constructors.len(), 1);
    assert_eq!(dt.constructors[0].fields.len(), 1);
    assert_eq!(dt.constructors[0].fields[0].name, "wrapper_inner");
}

#[test]
#[timeout(30000)]
fn test_datatype_from_adt_decl_all_nullary_enum() {
    let mut encoder = AYEncoder::new();
    let decl = traffic_light_enum_adt();
    let dt = encoder.datatype_from_adt_decl(&decl);

    assert_eq!(dt.name, "Light");
    assert_eq!(dt.constructors.len(), 3);
    for ctor in &dt.constructors {
        assert!(ctor.fields.is_empty(), "all constructors should be nullary");
    }
    assert_eq!(dt.constructors[0].name, "Red");
    assert_eq!(dt.constructors[1].name, "Yellow");
    assert_eq!(dt.constructors[2].name, "Green");
}

#[test]
#[timeout(30000)]
fn test_datatype_from_adt_decl_unnamed_fields_use_index() {
    let mut encoder = AYEncoder::new();
    let decl = AdtDecl::new(
        "my_mod::Pair".to_string(),
        "Pair".to_string(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "Pair".to_string(),
            "Pair".to_string(),
            vec![
                AdtFieldDecl::new(String::new(), ExprSort::Int),
                AdtFieldDecl::new(String::new(), ExprSort::Bool),
            ],
        )],
    );
    let dt = encoder.datatype_from_adt_decl(&decl);

    assert_eq!(dt.constructors[0].fields[0].name, "pair_0");
    assert_eq!(dt.constructors[0].fields[1].name, "pair_1");
}

// ── nullary_constructor_datatype ────────────────────────────────────

#[test]
#[timeout(30000)]
fn test_nullary_constructor_datatype_returns_some_for_nullary() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_ay_datatype();
    encoder.ensure_datatype_declared(&dt);

    let result = encoder.nullary_constructor_datatype("None");
    assert!(result.is_some(), "None is nullary, should return Some");
    assert_eq!(result.unwrap().name, "OptionInt");
}

#[test]
#[timeout(30000)]
fn test_nullary_constructor_datatype_returns_none_for_non_nullary() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_ay_datatype();
    encoder.ensure_datatype_declared(&dt);

    let result = encoder.nullary_constructor_datatype("Some");
    assert!(
        result.is_none(),
        "Some has one field, should not be considered nullary"
    );
}

#[test]
#[timeout(30000)]
fn test_nullary_constructor_datatype_unknown_ctor_returns_none() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_ay_datatype();
    encoder.ensure_datatype_declared(&dt);

    let result = encoder.nullary_constructor_datatype("Unknown");
    assert!(result.is_none(), "unknown constructor should return None");
}

#[test]
#[timeout(30000)]
fn test_nullary_constructor_datatype_all_nullary_enum() {
    let mut encoder = AYEncoder::new();
    let light_dt = DatatypeSort {
        name: "Light".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Red".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Yellow".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Green".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&light_dt);

    assert!(encoder.nullary_constructor_datatype("Red").is_some());
    assert!(encoder.nullary_constructor_datatype("Yellow").is_some());
    assert!(encoder.nullary_constructor_datatype("Green").is_some());
}

// ── constructor_payload_selector (static) ───────────────────────────

#[test]
#[timeout(30000)]
fn test_constructor_payload_selector_single_field() {
    let dt = option_int_ay_datatype();
    let result = AYEncoder::constructor_payload_selector(&dt, "Some");
    assert!(result.is_some());
    let (name, sort) = result.unwrap();
    assert_eq!(name, "optionint_some_0");
    assert_eq!(*sort, Sort::Int);
}

#[test]
#[timeout(30000)]
fn test_constructor_payload_selector_nullary_returns_none() {
    let dt = option_int_ay_datatype();
    let result = AYEncoder::constructor_payload_selector(&dt, "None");
    assert!(
        result.is_none(),
        "nullary constructor has no payload selector"
    );
}

#[test]
#[timeout(30000)]
fn test_constructor_payload_selector_multi_field_returns_none() {
    let dt = point_ay_datatype();
    let result = AYEncoder::constructor_payload_selector(&dt, "Point");
    assert!(
        result.is_none(),
        "multi-field constructors are not single-payload"
    );
}

#[test]
#[timeout(30000)]
fn test_constructor_payload_selector_unknown_ctor() {
    let dt = option_int_ay_datatype();
    let result = AYEncoder::constructor_payload_selector(&dt, "Unknown");
    assert!(result.is_none(), "unknown constructor should return None");
}

#[test]
#[timeout(30000)]
fn test_constructor_payload_selector_qualified_name() {
    let dt = option_int_ay_datatype();
    let result = AYEncoder::constructor_payload_selector(&dt, "std::option::Option::Some");
    assert!(
        result.is_some(),
        "qualified constructor name should be stripped to short form"
    );
    let (name, _) = result.unwrap();
    assert_eq!(name, "optionint_some_0");
}

// ── constructor_multi_field_selectors (static) ──────────────────────

#[test]
#[timeout(30000)]
fn test_multi_field_selectors_returns_fields_for_multi_field_ctor() {
    let dt = point_ay_datatype();
    let result = AYEncoder::constructor_multi_field_selectors(&dt, "Point");
    assert!(result.is_some());
    let fields = result.unwrap();
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].name, "point_x");
    assert_eq!(fields[1].name, "point_y");
}

#[test]
#[timeout(30000)]
fn test_multi_field_selectors_returns_none_for_single_field() {
    let dt = option_int_ay_datatype();
    let result = AYEncoder::constructor_multi_field_selectors(&dt, "Some");
    assert!(
        result.is_none(),
        "single-field constructor handled by constructor_payload_selector"
    );
}

#[test]
#[timeout(30000)]
fn test_multi_field_selectors_returns_none_for_nullary() {
    let dt = option_int_ay_datatype();
    let result = AYEncoder::constructor_multi_field_selectors(&dt, "None");
    assert!(result.is_none(), "nullary constructor has no fields");
}

#[test]
#[timeout(30000)]
fn test_multi_field_selectors_unknown_ctor() {
    let dt = point_ay_datatype();
    let result = AYEncoder::constructor_multi_field_selectors(&dt, "Unknown");
    assert!(result.is_none(), "unknown constructor should return None");
}

#[test]
#[timeout(30000)]
fn test_multi_field_selectors_qualified_name() {
    let dt = point_ay_datatype();
    let result = AYEncoder::constructor_multi_field_selectors(&dt, "my_mod::Point");
    assert!(
        result.is_some(),
        "qualified name should be stripped to short form"
    );
    assert_eq!(result.unwrap().len(), 2);
}
