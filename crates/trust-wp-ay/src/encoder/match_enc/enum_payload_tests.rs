// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for registered enum payload projection axioms.

use std::collections::HashMap;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use ntest::timeout;
use trust_wp_core::{
    formula::ExprSort,
    logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
};

use super::super::AYEncoder;

fn list_decl() -> AdtDecl {
    AdtDecl::new(
        "test::List".to_string(),
        "List".to_string(),
        AdtKind::Enum,
        vec![
            AdtConstructorDecl::new(
                "Cons".to_string(),
                "Cons".to_string(),
                vec![
                    AdtFieldDecl::new("0".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("1".to_string(), ExprSort::Int),
                ],
            ),
            AdtConstructorDecl::new("Nil".to_string(), "Nil".to_string(), vec![]),
        ],
    )
}

#[test]
#[timeout(30000)]
fn nested_option_field_is_declared_before_outer_enum() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let adt_decls = HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "test::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new(
                        "0".to_string(),
                        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("OptionInt")),
                    )],
                ),
                AdtConstructorDecl::new(
                    "Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("0".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);

    encoder.register_adt_decls(&adt_decls);

    assert!(
        encoder.get_datatype_decl("OptionInt").is_some(),
        "the native nested Option datatype must precede the outer declaration"
    );
    let outer = encoder
        .get_datatype_decl("OwnResult")
        .expect("outer datatype should be registered");
    assert!(
        matches!(
            outer.constructors[0].fields[0].sort,
            Sort::Datatype(ref datatype) if datatype.name == "OptionInt"
        ),
        "the outer datatype field must reuse the native Option sort"
    );
}

#[test]
#[timeout(30000)]
fn registered_enum_payload_projection_list_shape_does_not_panic() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_adt_decls(&HashMap::from([("List".to_string(), list_decl())]));

    let datatype = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&datatype);

    let receiver_sort = Sort::Datatype(datatype);
    let projection = encoder.registered_enum_payload_projection(&receiver_sort, 0);
    assert!(
        projection.is_some(),
        "field-0 payload projection should be available for List::Cons"
    );
}

#[test]
#[timeout(30000)]
fn ground_registered_enum_payload_reconstruction_single_carrier_does_not_panic() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let adt_decls = HashMap::from([(
        "OwnResult".to_string(),
        AdtDecl::new(
            "test::OwnResult".to_string(),
            "OwnResult".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "Ok".to_string(),
                    "Ok".to_string(),
                    vec![AdtFieldDecl::new("0".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "Err".to_string(),
                    "Err".to_string(),
                    vec![AdtFieldDecl::new("0".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )]);
    encoder.register_adt_decls(&adt_decls);

    let datatype = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "0".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&datatype);

    let receiver_sort = Sort::Datatype(datatype);
    let recv = encoder
        .get_or_declare_var("recv", receiver_sort.clone())
        .expect("declare recv");
    let projection_decl = encoder.get_or_declare_method_func(
        "enum_payload_get_0_1_test",
        std::slice::from_ref(&receiver_sort),
        Sort::Int,
    );
    let projection_term = encoder.solver.apply(&projection_decl, &[recv]);

    encoder.assert_ground_registered_enum_payload_reconstruction(
        &receiver_sort,
        recv,
        0,
        projection_term,
    );
}
