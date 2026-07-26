// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `LogicFnDef`, `TypeInvariantDef`, `AdtDecl`,
//! `AdtConstructorDecl`, `AdtFieldDecl`, `AdtKind`, and `FieldRangeKind`.
//!
//! These types carry metadata from the driver into the encoder. Bugs here
//! can cause silent mis-encoding of logic functions, type invariants, or
//! ADT field range axioms.

use trust_wp_core::{
    formula::{ExprSort, PureExpr},
    logic::{
        AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind, FieldRangeKind, LogicFnDef, LogicMode,
        TypeInvariantDef,
    },
};

// ── LogicFnDef: builder chain ───────────────────────────────────────

#[test]
fn logic_fn_def_new_defaults() {
    let def = LogicFnDef::new(
        "max".into(),
        "crate::max".into(),
        vec!["a".into(), "b".into()],
        PureExpr::Var("a".into(), None),
    );
    assert_eq!(def.name(), "max");
    assert_eq!(def.full_path(), "crate::max");
    assert_eq!(def.params(), &["a", "b"]);
    assert!(def.param_sorts().is_empty());
    assert_eq!(def.return_sort(), None);
    assert!(def.requires().is_empty());
    assert!(def.ensures().is_empty());
    assert!(!def.is_recursive());
    assert!(!def.is_opaque());
    assert_eq!(def.mode(), LogicMode::Default);
}

#[test]
fn logic_fn_def_new_with_requires() {
    let req = PureExpr::BinOp(
        std::sync::Arc::new(PureExpr::Var("a".into(), None)),
        trust_wp_core::formula::BinOp::Gt,
        std::sync::Arc::new(PureExpr::Int(0)),
    );
    let def = LogicFnDef::new_with_requires(
        "f".into(),
        "mod::f".into(),
        vec!["a".into()],
        vec![req.clone()],
        PureExpr::Var("a".into(), None),
    );
    assert_eq!(def.requires().len(), 1);
    assert_eq!(def.requires()[0], req);
}

#[test]
fn logic_fn_def_with_param_sorts() {
    let def = LogicFnDef::new(
        "pred".into(),
        "pred".into(),
        vec!["x".into(), "y".into()],
        PureExpr::Bool(true),
    )
    .with_param_sorts(vec![Some(ExprSort::Bool), Some(ExprSort::Seq)]);
    assert_eq!(
        def.param_sorts(),
        &[Some(ExprSort::Bool), Some(ExprSort::Seq)]
    );
}

#[test]
fn logic_fn_def_with_return_sort() {
    let def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Bool(false))
        .with_return_sort(Some(ExprSort::Bool));
    assert_eq!(def.return_sort(), Some(ExprSort::Bool));
}

#[test]
fn logic_fn_def_with_opaque() {
    let def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0)).with_opaque(true);
    assert!(def.is_opaque());
}

#[test]
fn logic_fn_def_with_mode() {
    let def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0))
        .with_mode(LogicMode::Prophetic);
    assert_eq!(def.mode(), LogicMode::Prophetic);
}

#[test]
fn logic_fn_def_builder_chain() {
    let def = LogicFnDef::new(
        "check".into(),
        "mod::check".into(),
        vec!["xs".into()],
        PureExpr::Bool(true),
    )
    .with_param_sorts(vec![Some(ExprSort::Seq)])
    .with_return_sort(Some(ExprSort::Bool))
    .with_opaque(true)
    .with_mode(LogicMode::Open);

    assert_eq!(def.name(), "check");
    assert_eq!(def.param_sorts(), &[Some(ExprSort::Seq)]);
    assert_eq!(def.return_sort(), Some(ExprSort::Bool));
    assert!(def.is_opaque());
    assert_eq!(def.mode(), LogicMode::Open);
}

// ── LogicFnDef: mutable setters ─────────────────────────────────────

#[test]
fn logic_fn_def_set_body() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    def.set_body(PureExpr::Int(42));
    assert_eq!(*def.body(), PureExpr::Int(42));
}

#[test]
fn logic_fn_def_set_requires() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    def.set_requires(vec![PureExpr::Bool(true)]);
    assert_eq!(def.requires().len(), 1);
    assert_eq!(def.requires()[0], PureExpr::Bool(true));
}

#[test]
fn logic_fn_def_extend_requires() {
    let mut def = LogicFnDef::new_with_requires(
        "f".into(),
        "f".into(),
        vec![],
        vec![PureExpr::Bool(true)],
        PureExpr::Int(0),
    );
    def.extend_requires([PureExpr::Bool(false)]);
    assert_eq!(def.requires().len(), 2);
    assert_eq!(def.requires()[1], PureExpr::Bool(false));
}

#[test]
fn logic_fn_def_set_ensures() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    def.set_ensures(vec![PureExpr::Bool(true)]);
    assert_eq!(def.ensures().len(), 1);
}

#[test]
fn logic_fn_def_set_mode() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    def.set_mode(LogicMode::OpenSelf);
    assert_eq!(def.mode(), LogicMode::OpenSelf);
}

#[test]
fn logic_fn_def_set_is_recursive() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    assert!(!def.is_recursive());
    def.set_is_recursive(true);
    assert!(def.is_recursive());
}

#[test]
fn logic_fn_def_set_is_opaque() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    assert!(!def.is_opaque());
    def.set_is_opaque(true);
    assert!(def.is_opaque());
}

#[test]
fn logic_fn_def_set_param_sorts() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec!["x".into()], PureExpr::Int(0));
    assert!(def.param_sorts().is_empty());
    def.set_param_sorts(vec![Some(ExprSort::Int)]);
    assert_eq!(def.param_sorts(), &[Some(ExprSort::Int)]);
}

#[test]
fn logic_fn_def_set_return_sort() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    assert_eq!(def.return_sort(), None);
    def.set_return_sort(Some(ExprSort::Seq));
    assert_eq!(def.return_sort(), Some(ExprSort::Seq));
}

// ── LogicFnDef: take methods ────────────────────────────────────────

#[test]
fn logic_fn_def_take_requires_empties_vec() {
    let mut def = LogicFnDef::new_with_requires(
        "f".into(),
        "f".into(),
        vec![],
        vec![PureExpr::Bool(true), PureExpr::Bool(false)],
        PureExpr::Int(0),
    );
    let taken = def.take_requires();
    assert_eq!(taken.len(), 2);
    assert!(
        def.requires().is_empty(),
        "take_requires must leave empty vec"
    );
}

#[test]
fn logic_fn_def_take_ensures_empties_vec() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    def.set_ensures(vec![PureExpr::Bool(true)]);
    let taken = def.take_ensures();
    assert_eq!(taken.len(), 1);
    assert!(
        def.ensures().is_empty(),
        "take_ensures must leave empty vec"
    );
}

#[test]
fn logic_fn_def_take_body_replaces_with_default() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(42));
    let taken = def.take_body();
    assert_eq!(taken, PureExpr::Int(42));
    assert_eq!(
        *def.body(),
        PureExpr::Bool(false),
        "take_body must replace with Bool(false)"
    );
}

// ── LogicFnDef: mutable access ──────────────────────────────────────

#[test]
fn logic_fn_def_body_mut() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    *def.body_mut() = PureExpr::Int(99);
    assert_eq!(*def.body(), PureExpr::Int(99));
}

#[test]
fn logic_fn_def_params_mut() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec!["x".into()], PureExpr::Int(0));
    def.params_mut().push("y".into());
    assert_eq!(def.params(), &["x", "y"]);
}

#[test]
fn logic_fn_def_requires_mut() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    def.requires_mut().push(PureExpr::Bool(true));
    assert_eq!(def.requires().len(), 1);
}

#[test]
fn logic_fn_def_ensures_mut() {
    let mut def = LogicFnDef::new("f".into(), "f".into(), vec![], PureExpr::Int(0));
    def.ensures_mut().push(PureExpr::Bool(true));
    assert_eq!(def.ensures().len(), 1);
}

// ── TypeInvariantDef ────────────────────────────────────────────────

#[test]
fn type_invariant_def_new_defaults() {
    let inv = TypeInvariantDef::new("Counter".into(), "self".into(), PureExpr::Bool(true));
    assert_eq!(inv.type_name(), "Counter");
    assert_eq!(inv.self_param(), "self");
    assert_eq!(*inv.body(), PureExpr::Bool(true));
    assert_eq!(inv.param_sort(), None);
    assert!(!inv.is_newtype());
    assert_eq!(inv.element_invariant_method(), None);
}

#[test]
fn type_invariant_def_with_param_sort() {
    let inv = TypeInvariantDef::new("T".into(), "self".into(), PureExpr::Bool(true))
        .with_param_sort(Some(ExprSort::Int));
    assert_eq!(inv.param_sort(), Some(&ExprSort::Int));
}

#[test]
fn type_invariant_def_with_newtype() {
    let inv = TypeInvariantDef::new("NonZero".into(), "self".into(), PureExpr::Bool(true))
        .with_newtype(true);
    assert!(inv.is_newtype());
}

#[test]
fn type_invariant_def_with_element_invariant_method() {
    let inv = TypeInvariantDef::new("Vec".into(), "self".into(), PureExpr::Bool(true))
        .with_element_invariant_method(Some("__trust_wp_invariant_Elem".into()));
    assert_eq!(
        inv.element_invariant_method(),
        Some("__trust_wp_invariant_Elem")
    );
}

#[test]
fn type_invariant_def_builder_chain() {
    let body = PureExpr::BinOp(
        std::sync::Arc::new(PureExpr::Var("self".into(), None)),
        trust_wp_core::formula::BinOp::Gt,
        std::sync::Arc::new(PureExpr::Int(0)),
    );
    let inv = TypeInvariantDef::new("Positive".into(), "self".into(), body.clone())
        .with_param_sort(Some(ExprSort::Int))
        .with_newtype(false)
        .with_element_invariant_method(None);
    assert_eq!(inv.type_name(), "Positive");
    assert_eq!(*inv.body(), body);
    assert_eq!(inv.param_sort(), Some(&ExprSort::Int));
    assert!(!inv.is_newtype());
    assert_eq!(inv.element_invariant_method(), None);
}

#[test]
fn type_invariant_def_set_body() {
    let mut inv = TypeInvariantDef::new("T".into(), "self".into(), PureExpr::Bool(true));
    inv.set_body(PureExpr::Bool(false));
    assert_eq!(*inv.body(), PureExpr::Bool(false));
}

// ── FieldRangeKind ──────────────────────────────────────────────────

#[test]
fn field_range_kind_unsigned() {
    let kind = FieldRangeKind::Unsigned(32);
    assert_eq!(kind, FieldRangeKind::Unsigned(32));
    assert_ne!(kind, FieldRangeKind::Unsigned(64));
    assert_ne!(kind, FieldRangeKind::Signed(32));
}

#[test]
fn field_range_kind_signed() {
    let kind = FieldRangeKind::Signed(16);
    assert_eq!(kind, FieldRangeKind::Signed(16));
    assert_ne!(kind, FieldRangeKind::Signed(32));
    assert_ne!(kind, FieldRangeKind::Unsigned(16));
}

#[test]
fn field_range_kind_debug() {
    let dbg_unsigned = format!("{:?}", FieldRangeKind::Unsigned(8));
    assert!(dbg_unsigned.contains("Unsigned"), "Debug: {dbg_unsigned}");
    assert!(dbg_unsigned.contains('8'), "Debug: {dbg_unsigned}");

    let dbg_signed = format!("{:?}", FieldRangeKind::Signed(64));
    assert!(dbg_signed.contains("Signed"), "Debug: {dbg_signed}");
    assert!(dbg_signed.contains("64"), "Debug: {dbg_signed}");
}

#[test]
fn field_range_kind_copy() {
    let a = FieldRangeKind::Unsigned(32);
    let b = a;
    assert_eq!(a, b);
}

#[test]
#[allow(clippy::clone_on_copy)]
fn field_range_kind_clone() {
    let a = FieldRangeKind::Signed(16);
    let b = a.clone();
    assert_eq!(a, b);
}

// ── AdtKind ─────────────────────────────────────────────────────────

#[test]
fn adt_kind_variants_distinct() {
    assert_ne!(AdtKind::Struct, AdtKind::Enum);
    assert_eq!(AdtKind::Struct, AdtKind::Struct);
    assert_eq!(AdtKind::Enum, AdtKind::Enum);
}

#[test]
fn adt_kind_debug() {
    assert_eq!(format!("{:?}", AdtKind::Struct), "Struct");
    assert_eq!(format!("{:?}", AdtKind::Enum), "Enum");
}

#[test]
fn adt_kind_copy() {
    let a = AdtKind::Enum;
    let b = a;
    assert_eq!(a, b);
}

// ── AdtFieldDecl ────────────────────────────────────────────────────

#[test]
fn adt_field_decl_new() {
    let field = AdtFieldDecl::new("count".into(), ExprSort::Int);
    assert_eq!(field.name, "count");
    assert_eq!(field.sort, ExprSort::Int);
}

#[test]
fn adt_field_decl_equality() {
    let a = AdtFieldDecl::new("x".into(), ExprSort::Bool);
    let b = AdtFieldDecl::new("x".into(), ExprSort::Bool);
    assert_eq!(a, b);
}

#[test]
fn adt_field_decl_inequality_name() {
    let a = AdtFieldDecl::new("x".into(), ExprSort::Int);
    let b = AdtFieldDecl::new("y".into(), ExprSort::Int);
    assert_ne!(a, b);
}

#[test]
fn adt_field_decl_inequality_sort() {
    let a = AdtFieldDecl::new("x".into(), ExprSort::Int);
    let b = AdtFieldDecl::new("x".into(), ExprSort::Bool);
    assert_ne!(a, b);
}

#[test]
fn adt_field_decl_clone() {
    let a = AdtFieldDecl::new("x".into(), ExprSort::Seq);
    let b = a.clone();
    assert_eq!(a, b);
}

// ── AdtConstructorDecl ──────────────────────────────────────────────

#[test]
fn adt_constructor_decl_new() {
    let ctor = AdtConstructorDecl::new(
        "Some".into(),
        "Option_Some".into(),
        vec![AdtFieldDecl::new("0".into(), ExprSort::Int)],
    );
    assert_eq!(ctor.rust_name, "Some");
    assert_eq!(ctor.smt_name, "Option_Some");
    assert_eq!(ctor.fields.len(), 1);
    assert_eq!(ctor.fields[0].name, "0");
}

#[test]
fn adt_constructor_decl_empty_fields() {
    let ctor = AdtConstructorDecl::new("None".into(), "Option_None".into(), vec![]);
    assert!(ctor.fields.is_empty());
}

#[test]
fn adt_constructor_decl_equality() {
    let a = AdtConstructorDecl::new("C".into(), "smt_C".into(), vec![]);
    let b = AdtConstructorDecl::new("C".into(), "smt_C".into(), vec![]);
    assert_eq!(a, b);
}

#[test]
fn adt_constructor_decl_inequality_smt_name() {
    let a = AdtConstructorDecl::new("C".into(), "smt_C_v1".into(), vec![]);
    let b = AdtConstructorDecl::new("C".into(), "smt_C_v2".into(), vec![]);
    assert_ne!(a, b);
}

#[test]
fn adt_constructor_decl_clone() {
    let a = AdtConstructorDecl::new(
        "Pair".into(),
        "Pair_mk".into(),
        vec![
            AdtFieldDecl::new("fst".into(), ExprSort::Int),
            AdtFieldDecl::new("snd".into(), ExprSort::Bool),
        ],
    );
    let b = a.clone();
    assert_eq!(a, b);
}

// ── AdtDecl ─────────────────────────────────────────────────────────

#[test]
fn adt_decl_new_struct() {
    let decl = AdtDecl::new(
        "my_crate::Point".into(),
        "Point".into(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "Point".into(),
            "Point_mk".into(),
            vec![
                AdtFieldDecl::new("x".into(), ExprSort::Int),
                AdtFieldDecl::new("y".into(), ExprSort::Int),
            ],
        )],
    );
    assert_eq!(decl.rust_path, "my_crate::Point");
    assert_eq!(decl.adt_name, "Point");
    assert_eq!(decl.kind, AdtKind::Struct);
    assert_eq!(decl.constructors.len(), 1);
    assert_eq!(decl.constructors[0].fields.len(), 2);
}

#[test]
fn adt_decl_new_enum() {
    let decl = AdtDecl::new(
        "std::option::Option".into(),
        "Option".into(),
        AdtKind::Enum,
        vec![
            AdtConstructorDecl::new("None".into(), "Option_None".into(), vec![]),
            AdtConstructorDecl::new(
                "Some".into(),
                "Option_Some".into(),
                vec![AdtFieldDecl::new("0".into(), ExprSort::Int)],
            ),
        ],
    );
    assert_eq!(decl.kind, AdtKind::Enum);
    assert_eq!(decl.constructors.len(), 2);
    assert_eq!(decl.constructors[0].rust_name, "None");
    assert_eq!(decl.constructors[1].rust_name, "Some");
}

#[test]
fn adt_decl_equality() {
    let make = || {
        AdtDecl::new(
            "p".into(),
            "T".into(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new("T".into(), "T_mk".into(), vec![])],
        )
    };
    assert_eq!(make(), make());
}

#[test]
fn adt_decl_inequality_kind() {
    let a = AdtDecl::new("p".into(), "T".into(), AdtKind::Struct, vec![]);
    let b = AdtDecl::new("p".into(), "T".into(), AdtKind::Enum, vec![]);
    assert_ne!(a, b);
}

#[test]
fn adt_decl_clone() {
    let decl = AdtDecl::new(
        "p".into(),
        "T".into(),
        AdtKind::Enum,
        vec![
            AdtConstructorDecl::new("A".into(), "T_A".into(), vec![]),
            AdtConstructorDecl::new(
                "B".into(),
                "T_B".into(),
                vec![AdtFieldDecl::new("val".into(), ExprSort::Int)],
            ),
        ],
    );
    let cloned = decl.clone();
    assert_eq!(decl, cloned);
}

// ── type_invariant_def! macro ───────────────────────────────────────

#[test]
fn type_invariant_def_macro_field_order_1() {
    let inv = trust_wp_core::type_invariant_def!(
        type_name: "Counter".to_string(),
        self_param: "self".to_string(),
        param_sort: Some(ExprSort::Int),
        body: PureExpr::Bool(true),
        is_newtype: false,
        element_invariant_method: None,
    );
    assert_eq!(inv.type_name(), "Counter");
    assert_eq!(inv.param_sort(), Some(&ExprSort::Int));
    assert!(!inv.is_newtype());
}

#[test]
fn type_invariant_def_macro_field_order_2() {
    let inv = trust_wp_core::type_invariant_def!(
        type_name: "Vec".to_string(),
        self_param: "self".to_string(),
        body: PureExpr::Bool(true),
        param_sort: Some(ExprSort::Seq),
        is_newtype: false,
        element_invariant_method: Some("__trust_wp_invariant_Elem".to_string()),
    );
    assert_eq!(inv.type_name(), "Vec");
    assert_eq!(inv.param_sort(), Some(&ExprSort::Seq));
    assert_eq!(
        inv.element_invariant_method(),
        Some("__trust_wp_invariant_Elem")
    );
}
