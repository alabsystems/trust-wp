// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use ntest::timeout;
// =============================================================================
// Tests for driver-provided AdtDecls predeclaration (Pass 0 of predeclare_datatype_vars)
// =============================================================================

/// Verify that adt_decls from the driver are registered as native DatatypeSorts
/// before match-arm heuristic scanning (Pass 0). (#1982 Slice 3)
#[test]
#[timeout(30000)]
fn adt_decls_predeclares_user_struct_as_native_datatype() {
    use trust_wp_core::{
        formula::ExprSort,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let mut encoder = crate::encoder::AYEncoder::new_all();

    let mut adt_decls = std::collections::HashMap::new();
    adt_decls.insert(
        "Point".to_string(),
        AdtDecl::new(
            "my_crate::Point".to_string(),
            "Point".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Point".to_string(),
                "mk_Point".to_string(),
                vec![
                    AdtFieldDecl::new("x".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("y".to_string(), ExprSort::Int),
                ],
            )],
        ),
    );

    super::datatype_predecl::predeclare_datatype_vars(
        &mut encoder,
        &[],
        &[],
        &[],
        None,
        Some(&adt_decls),
    );

    assert!(
        encoder.decls().has_datatype("Point"),
        "Point should be registered as a native DatatypeSort from adt_decls (#1982)"
    );
}

/// Verify that driver-provided enum ADT declarations produce the correct
/// DatatypeSort structure with multiple constructors. (#1982 Slice 3)
#[test]
#[timeout(30000)]
fn adt_decls_predeclares_user_enum_with_multiple_constructors() {
    use trust_wp_core::{
        formula::ExprSort,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let mut encoder = crate::encoder::AYEncoder::new_all();

    let mut adt_decls = std::collections::HashMap::new();
    adt_decls.insert(
        "Shape".to_string(),
        AdtDecl::new(
            "my_crate::Shape".to_string(),
            "Shape".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "Circle".to_string(),
                    "mk_Circle".to_string(),
                    vec![AdtFieldDecl::new("radius".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "Rect".to_string(),
                    "mk_Rect".to_string(),
                    vec![
                        AdtFieldDecl::new("width".to_string(), ExprSort::Int),
                        AdtFieldDecl::new("height".to_string(), ExprSort::Int),
                    ],
                ),
            ],
        ),
    );

    super::datatype_predecl::predeclare_datatype_vars(
        &mut encoder,
        &[],
        &[],
        &[],
        None,
        Some(&adt_decls),
    );

    assert!(
        encoder.decls().has_datatype("Shape"),
        "Shape enum should be registered as a native DatatypeSort from adt_decls (#1982)"
    );
}

/// Verify that adt_decl_to_datatype_sort correctly maps ExprSort::Bool fields
/// to Sort::Bool (not the default Sort::Int fallback). (#1982 Slice 3)
#[test]
#[timeout(30000)]
fn adt_decl_to_datatype_sort_maps_field_sorts_correctly() {
    use trust_wp_core::{
        formula::ExprSort,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let decl = AdtDecl::new(
        "my_crate::Predicate".to_string(),
        "Predicate".to_string(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "Predicate".to_string(),
            "mk_Predicate".to_string(),
            vec![
                AdtFieldDecl::new("value".to_string(), ExprSort::Int),
                AdtFieldDecl::new("active".to_string(), ExprSort::Bool),
            ],
        )],
    );

    let dt = super::datatype_predecl::adt_decl_to_datatype_sort(&decl);

    assert_eq!(dt.name, "Predicate");
    assert_eq!(dt.constructors.len(), 1);
    assert_eq!(dt.constructors[0].name, "mk_Predicate");
    assert_eq!(dt.constructors[0].fields.len(), 2);
    assert_eq!(dt.constructors[0].fields[0].name, "value");
    assert_eq!(dt.constructors[0].fields[0].sort, ay_dpll::api::Sort::Int);
    assert_eq!(dt.constructors[0].fields[1].name, "active");
    assert_eq!(dt.constructors[0].fields[1].sort, ay_dpll::api::Sort::Bool);
}
