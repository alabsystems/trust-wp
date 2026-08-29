// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::{formula::PureExpr, logic::LogicFnDef};
// =============================================================================
// Tests for predeclare_collected_vars (AC5: non-Int sort coverage) (#1965)
// =============================================================================

/// Verify that predeclare_collected_vars pre-declares Seq-annotated variables
/// with Sort::Seq(Int) instead of the default Int. This is the core
/// AC5 acceptance criterion for the deferred-declaration design. (#2080)
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_declares_seq_annotation() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = crate::encoder::AYEncoder::new();
    let requires = vec![PureExpr::Var("v".into(), Some(ExprSort::Seq))];
    let ensures = vec![];

    super::predeclare_collected_vars(&mut encoder, &requires, &ensures, &[], None, None, None)
        .expect("predeclare should succeed");

    assert_eq!(
        encoder.var_sort("v"),
        Some(&ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int)),
        "Seq-annotated var should be pre-declared as Sort::Seq(Int) (#1965, #2080)"
    );
}

/// Bootstrap must predeclare the matching mut companion when the goal already
/// carries a mut-ref carrier shape.
#[test]
#[timeout(30000)]
fn bootstrap_predeclares_closure_postcondition_mut_companion_for_mutref_carrier() {
    use trust_wp_core::{
        formula::{intern_sort_name, BinOp, ExprSort},
        logic::LogicMode,
    };

    let logic_fn = LogicFnDef::new(
        "closure_postcondition_3_i_u_i".to_string(),
        "test::closure_postcondition_3_i_u_i".to_string(),
        vec!["self".to_string(), "x".to_string(), "result".to_string()],
        PureExpr::Bool(true),
    )
    .with_mode(LogicMode::Open);

    let x_ann = ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), Some(x_ann.clone()))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::LogicFnCall {
        name: "closure_postcondition_3_i_u_i".to_string(),
        args: vec![],
    }];

    let setup_result = super::setup_verification_encoder(&super::VerificationSetup {
        requires: &requires,
        ensures: &ensures,
        result_expr: None,
        context_exprs: &[],
        ghost_context: None,
        logic_fns: Some(&[logic_fn]),
        mode_overrides: None,
        type_invariants: None,
        track: crate::TrackLevel::Auto,
        timeout: Some(std::time::Duration::from_secs(5)),
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("setup should succeed");

    assert!(
        setup_result.encoder.has_closure_postcondition_mut_symbols(),
        "bootstrap should predeclare the matching mut companion before goal encoding"
    );
}

/// Generic `MutRef<TypeParam>` annotations must keep the mut-ref carrier so
/// closure-spec calls on generic `&mut T` parameters share the same UF domain.
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_preserves_generic_mutref_annotation() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = crate::encoder::AYEncoder::new_with_quantifiers();
    let ann = ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
    let requires = vec![PureExpr::Var("v".into(), Some(ann.clone()))];

    super::predeclare_collected_vars(&mut encoder, &requires, &[], &[], None, None, None)
        .expect("predeclare should succeed");

    let expected_sort = encoder.sort_from_expr_sort(ann);
    assert_eq!(
        encoder.var_sort("v"),
        Some(&expected_sort),
        "generic mut-ref annotations should predeclare on the mut-ref carrier sort"
    );
}

/// Verify that bootstrap predeclaration resolves a registered user ADT
/// annotation to the native DatatypeSort instead of freezing the variable as
/// Uninterpreted("Type"). This keeps the first declaration aligned with the
/// Pass 0 ADT registry. (#1982 Slice 3)
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_declares_registered_datatype_annotation() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    let mut encoder = crate::encoder::AYEncoder::new_all();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "Point".to_string(),
        AdtDecl::new(
            "crate::Point".to_string(),
            "Point".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Point".to_string(),
                "Point".to_string(),
                vec![AdtFieldDecl::new("x".to_string(), ExprSort::Int)],
            )],
        ),
    )]));

    let requires = vec![PureExpr::Var(
        "p".into(),
        Some(ExprSort::Datatype(intern_sort_name("crate::Point"))),
    )];

    super::predeclare_collected_vars(&mut encoder, &requires, &[], &[], None, None, None)
        .expect("predeclare should succeed");

    let declared_sort = encoder
        .var_sort("p")
        .cloned()
        .expect("datatype-annotated var should be predeclared");
    assert!(
        matches!(declared_sort, ay_dpll::api::Sort::Datatype(ref dt) if dt.name == "Point"),
        "registered ADT annotation should predeclare as native DatatypeSort: {declared_sort:?}"
    );
}

/// Canonical model types must stay on the Seq encoding carrier even when the
/// same bare name is also registered as a native datatype. Otherwise bootstrap
/// can freeze `result` as `Datatype(Seq)` and later Seq operations request the
/// Seq encoding sort, reproducing the `ghost/seq_iter.rs` conflict from #2116.
/// In mixed datatype mode the carrier is intentionally `Uninterpreted("Seq")`
/// to avoid ay-dpll's unsupported native-Seq/datatype fragment. (#2080, #2699)
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_keeps_registered_seq_model_type_on_encoding_sort() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = crate::encoder::AYEncoder::new_all();
    encoder.ensure_datatype_declared(&DatatypeSort {
        name: "Seq".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Seq".to_string(),
            fields: vec![DatatypeField {
                name: "seq_elements".to_string(),
                sort: Sort::seq(Sort::Int),
            }],
        }],
    });

    let requires = vec![PureExpr::Var(
        "result".into(),
        Some(ExprSort::Datatype(intern_sort_name("creusot_std::Seq"))),
    )];

    super::predeclare_collected_vars(&mut encoder, &requires, &[], &[], None, None, None)
        .expect("predeclare should succeed");

    let result_sort = encoder.var_sort("result");
    assert!(
        matches!(result_sort, Some(Sort::Seq(_)))
            || matches!(result_sort, Some(Sort::Uninterpreted(name)) if name == "Seq"),
        "registered Seq model types must still predeclare on the Seq encoding carrier, got {:?}",
        result_sort
    );
}

/// Same regression boundary as the Seq case above, but for FMap-backed model
/// types. This keeps bootstrap aligned with the FMap encoding pipeline even
/// when a same-named native datatype has already been registered. (#2116)
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_keeps_registered_fmap_model_type_on_encoding_sort() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = crate::encoder::AYEncoder::new_all();
    encoder.ensure_datatype_declared(&DatatypeSort {
        name: "FMap".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "FMap".to_string(),
            fields: vec![DatatypeField {
                name: "fmap_entries".to_string(),
                sort: Sort::Uninterpreted("FMap".to_string()),
            }],
        }],
    });

    let requires = vec![PureExpr::Var(
        "m".into(),
        Some(ExprSort::Datatype(intern_sort_name("creusot_std::FMap"))),
    )];

    super::predeclare_collected_vars(&mut encoder, &requires, &[], &[], None, None, None)
        .expect("predeclare should succeed");

    assert_eq!(
        encoder.var_sort("m"),
        Some(&Sort::Uninterpreted("FMap".to_string())),
        "registered FMap model types must still predeclare on the canonical FMap encoding sort"
    );
}

/// Verify that Bool-context variables (e.g., condition of Ite) are pre-declared
/// as Bool instead of defaulting to Int.
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_declares_bool_context() {
    let mut encoder = crate::encoder::AYEncoder::new();
    // `if b { x } else { y }` — b is in bool context
    let requires = vec![PureExpr::Ite(
        Arc::new(PureExpr::Var("b".into(), None)),
        Arc::new(PureExpr::Var("x".into(), None)),
        Arc::new(PureExpr::Var("y".into(), None)),
    )];
    let ensures = vec![];

    super::predeclare_collected_vars(&mut encoder, &requires, &ensures, &[], None, None, None)
        .expect("predeclare should succeed");

    assert_eq!(
        encoder.var_sort("b"),
        Some(&ay_dpll::api::Sort::Bool),
        "Ite-condition var should be pre-declared as Bool (#1965)"
    );
    // x and y should not be declared (they default to Int)
    assert_eq!(
        encoder.var_sort("x"),
        None,
        "non-Bool var should not be pre-declared (Int is the default)"
    );
}

/// Verify that variables with Seq-only method calls (e.g., v.push_back(x)) are
/// pre-declared as Seq, demonstrating the method-call evidence path.
/// Note: `len` alone is ambiguous; `push_back` is a Seq-only method.
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_declares_seq_from_method_call() {
    let mut encoder = crate::encoder::AYEncoder::new();
    // v.push_back(x) — push_back is a Seq-only method
    let ensures = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".into(), None)),
        method: "push_back".into(),
        args: vec![PureExpr::Var("x".into(), None)],
    }];

    super::predeclare_collected_vars(&mut encoder, &[], &ensures, &[], None, None, None)
        .expect("predeclare should succeed");

    assert_eq!(
        encoder.var_sort("v"),
        Some(&ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int)),
        "var with push_back() method call should be pre-declared as Seq (#1965)"
    );
}

/// Verify that already-declared variables are not re-declared by predeclare.
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_skips_already_declared() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = crate::encoder::AYEncoder::new();
    // Pre-declare v as Bool (simulating earlier pipeline stage)
    encoder
        .get_or_declare_var("v", ay_dpll::api::Sort::Bool)
        .expect("manual predecl");

    // Now run predeclare_collected_vars with Seq annotation
    let requires = vec![PureExpr::Var("v".into(), Some(ExprSort::Seq))];
    super::predeclare_collected_vars(&mut encoder, &requires, &[], &[], None, None, None)
        .expect("predeclare should succeed");

    // Should still be Bool (first declaration wins)
    assert_eq!(
        encoder.var_sort("v"),
        Some(&ay_dpll::api::Sort::Bool),
        "already-declared var should keep its original sort (#1965)"
    );
}

/// Verify that predeclare scans logic function bodies for sort evidence.
/// A variable used with push_back inside a logic fn body should be pre-declared
/// as Seq even when the caller's requires/ensures don't mention it. (#1965)
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_scans_logic_fn_bodies() {
    use trust_wp_core::logic::LogicFnDef;

    let mut encoder = crate::encoder::AYEncoder::new();
    let logic_fns = vec![LogicFnDef::new(
        "helper".into(),
        "mod::helper".into(),
        vec!["s".into()],
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".into(), None)),
            method: "push_back".into(),
            args: vec![PureExpr::Int(1)],
        },
    )
    .with_param_sorts(vec![None])];

    super::predeclare_collected_vars(&mut encoder, &[], &[], &[], None, Some(&logic_fns), None)
        .expect("predeclare should succeed");

    assert_eq!(
        encoder.var_sort("s"),
        Some(&ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int)),
        "var with push_back in logic fn body should be pre-declared as Seq (#1965)"
    );
}

/// Verify that predeclare scans type invariant bodies for sort evidence. (#1965)
#[test]
#[timeout(30000)]
fn predeclare_collected_vars_scans_type_invariant_bodies() {
    let mut encoder = crate::encoder::AYEncoder::new();
    let invs = vec![trust_wp_core::type_invariant_def! {
        type_name: "MyVec".into(),
        self_param: "self".into(),
        param_sort: None,
        body: PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self".into(), None)),
            method: "push_back".into(),
            args: vec![PureExpr::Int(0)],
        },
        is_newtype: false,
        element_invariant_method: None,
    }];

    super::predeclare_collected_vars(&mut encoder, &[], &[], &[], None, None, Some(&invs))
        .expect("predeclare should succeed");

    assert_eq!(
        encoder.var_sort("self"),
        Some(&ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int)),
        "self var with push_back in type invariant body should be pre-declared as Seq (#1965)"
    );
}
