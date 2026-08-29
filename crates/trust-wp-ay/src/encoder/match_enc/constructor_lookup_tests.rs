// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use trust_wp_core::{
    formula::PureExpr,
    logic::{AdtConstructorDecl, AdtDecl, AdtKind},
};

use super::{super::AYEncoder, synthesized_enum_alias_name};
use crate::encoder::sort_context::{register_adt_family_alias, same_structural_family};

fn synthesized_list_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "Adt_Cons_Nil".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "adt_cons_nil_cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "adt_cons_nil_cons_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    }
}

fn registered_list_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "List".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "list_cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "list_cons_1".to_string(),
                        sort: Sort::Uninterpreted("List".to_string()),
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    }
}

fn synthesized_widget_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "Adt_Alpha_Beta".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Alpha".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Beta".to_string(),
                fields: vec![],
            },
        ],
    }
}

fn registered_widget_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "WidgetState".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Alpha".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Beta".to_string(),
                fields: vec![],
            },
        ],
    }
}

#[test]
fn synthesized_enum_alias_uses_short_constructor_names() {
    let decl = AdtDecl::new(
        "creusot_test::List".to_string(),
        "List".to_string(),
        AdtKind::Enum,
        vec![
            AdtConstructorDecl::new("Cons".to_string(), "List::Cons".to_string(), vec![]),
            AdtConstructorDecl::new("Nil".to_string(), "List::Nil".to_string(), vec![]),
        ],
    );

    assert_eq!(
        synthesized_enum_alias_name(&decl).as_deref(),
        Some("Adt_Cons_Nil"),
        "qualified constructor names must register the same alias used by match encoding"
    );
}

#[test]
fn qualified_constructor_lookup_prefers_alias_over_exact_metadata() {
    let mut encoder = AYEncoder::new();
    let synthesized = synthesized_list_datatype();
    let registered = registered_list_datatype();

    encoder.register_datatype(registered.name.clone(), registered);
    register_adt_family_alias("Adt_Cons_Nil", "List");
    encoder.ensure_datatype_declared(&synthesized);

    let cons_dt = encoder
        .constructor_datatype("List::Cons")
        .expect("qualified constructor should resolve through synthesized alias");
    assert_eq!(cons_dt.name, "Adt_Cons_Nil");

    let head = encoder.solver.int_const(1);
    let tail = encoder.solver.int_const(0);
    let cons = encoder
        .safe_datatype_constructor(
            "alias preference regression",
            &cons_dt,
            "Cons",
            &[head, tail],
        )
        .expect("alias-selected constructor must match ay's declared datatype");
    assert_eq!(
        encoder.solver.get_sort(cons),
        Sort::Datatype(synthesized).as_term_sort()
    );
}

#[test]
fn qualified_constructor_lookup_accepts_synthesized_family_alias() {
    let mut encoder = AYEncoder::new();
    let synthesized = synthesized_list_datatype();
    let registered = registered_list_datatype();

    register_adt_family_alias("Adt_Cons_Nil", "List");
    encoder.ensure_datatype_declared(&synthesized);
    encoder.register_datatype(registered.name.clone(), registered);

    let cons_dt = encoder
        .constructor_datatype("List::Cons")
        .expect("qualified constructor should resolve through synthesized alias");
    assert_eq!(cons_dt.name, "Adt_Cons_Nil");

    let nil_dt = encoder
        .constructor_datatype("List::Nil")
        .expect("nullary constructor should resolve through synthesized alias");
    let nil = encoder
        .safe_datatype_constructor("alias lookup regression", &nil_dt, "Nil", &[])
        .expect("alias-selected datatype must be constructible");
    assert_eq!(
        encoder.solver.get_sort(nil),
        Sort::Datatype(synthesized).as_term_sort()
    );
}

#[test]
fn qualified_constructor_call_falls_back_when_alias_target_is_not_constructible() {
    let mut encoder = AYEncoder::new();
    let registered = registered_list_datatype();
    let synthesized = synthesized_list_datatype();

    encoder.ensure_datatype_declared(&registered);
    register_adt_family_alias("Adt_Cons_Nil", "List");
    encoder.ensure_datatype_declared(&synthesized);

    let expr = PureExpr::LogicFnCall {
        name: "List::Cons".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(0)],
    };
    let term = encoder
        .encode_pure(&expr)
        .expect("constructor alias conflict should fall back instead of panicking");

    let _ = encoder.solver.get_sort(term);
}

#[test]
fn unqualified_constructor_lookup_prefers_synthesized_family_alias() {
    let mut encoder = AYEncoder::new();
    let synthesized = synthesized_list_datatype();
    let registered = registered_list_datatype();

    register_adt_family_alias("Adt_Cons_Nil", "List");
    encoder.ensure_datatype_declared(&synthesized);
    encoder.register_datatype(registered.name.clone(), registered);

    let cons_dt = encoder
        .constructor_datatype("Cons")
        .expect("unqualified constructor should resolve through synthesized alias");
    assert_eq!(cons_dt.name, "Adt_Cons_Nil");

    let head = encoder.solver.int_const(1);
    let tail = encoder.solver.int_const(0);
    let cons = encoder
        .safe_datatype_constructor(
            "unqualified alias lookup regression",
            &cons_dt,
            "Cons",
            &[head, tail],
        )
        .expect("alias-selected unqualified constructor must match ay's declared datatype");
    assert_eq!(
        encoder.solver.get_sort(cons),
        Sort::Datatype(synthesized).as_term_sort()
    );
}

#[test]
fn constructor_call_falls_back_when_native_family_is_already_locked() {
    let mut encoder = AYEncoder::new();
    let synthesized = synthesized_list_datatype();
    let registered = registered_list_datatype();

    encoder.ensure_datatype_declared(&registered);
    register_adt_family_alias("Adt_Cons_Nil", "List");
    encoder.register_datatype(synthesized.name.clone(), synthesized);

    let cons = PureExpr::LogicFnCall {
        name: "Cons".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(0)],
    };
    encoder
        .encode_pure(&cons)
        .expect("native constructor mismatch should fall back to UF encoding");
}

#[test]
fn datatype_registration_infers_synthesized_family_alias() {
    let mut encoder = AYEncoder::new();
    let synthesized = synthesized_widget_datatype();
    let registered = registered_widget_datatype();

    encoder.register_datatype(registered.name.clone(), registered);
    encoder.register_datatype(synthesized.name.clone(), synthesized.clone());

    let alpha_dt = encoder
        .constructor_datatype("Alpha")
        .expect("unqualified constructor should resolve through inferred alias");
    assert_eq!(alpha_dt.name, "Adt_Alpha_Beta");

    assert_eq!(
        same_structural_family(
            &Sort::Uninterpreted("WidgetState".to_string()),
            &Sort::Uninterpreted("Adt_Alpha_Beta".to_string())
        ),
        Some("WidgetState".to_string())
    );
}

#[test]
fn qualified_constructor_lookup_keeps_exact_match_without_alias() {
    let mut encoder = AYEncoder::new();
    let datatype = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_ok_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_err_0".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };

    encoder.ensure_datatype_declared(&datatype);

    let found = encoder
        .constructor_datatype("OwnResult::Ok")
        .expect("qualified user constructor should still resolve exactly");
    assert_eq!(found.name, "OwnResult");
}
