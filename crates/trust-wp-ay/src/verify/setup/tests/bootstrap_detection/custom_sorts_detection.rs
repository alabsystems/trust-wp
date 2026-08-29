// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::{
    formula::{ExprSort, PureExpr},
    logic::type_invariant_method_name,
};

use super::*;
/// Regression test for #994/#1944: match constructor patterns should set the
/// `needs_custom_sorts` flag, which routes to Logic::All.
#[test]
#[timeout(30000)]
fn match_constructor_triggers_custom_sorts_detection() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let match_ensures = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: PureExpr::Var("v".to_string(), None),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Int(0),
            },
        ],
    };

    let (use_quantifiers, _needs_array_theory, needs_custom_sorts) =
        detect_logic_requirements(&[], &[match_ensures], &[], None, None, None);
    assert!(
        needs_custom_sorts,
        "match with Constructor pattern should set needs_custom_sorts (#1944)"
    );
    assert!(
        use_quantifiers,
        "match with Constructor pattern should set use_quantifiers"
    );
}

/// Regression test for #994/#1944: datatype spec methods (is_some, unwrap, etc.)
/// should also set the `needs_custom_sorts` flag.
#[test]
#[timeout(30000)]
fn datatype_spec_method_triggers_custom_sorts_detection() {
    let is_some_ensures = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("opt".to_string(), None)),
        method: "is_some".to_string(),
        args: vec![],
    };

    let (_use_quantifiers, _needs_array_theory, needs_custom_sorts) =
        detect_logic_requirements(&[], &[is_some_ensures], &[], None, None, None);
    assert!(
        needs_custom_sorts,
        "is_some spec method should set needs_custom_sorts (#1944)"
    );
}

/// Whole-borrow `MutRef` carriers use uninterpreted sorts/UFs that the normal
/// quantified/array encoder already supports. Escalating every mut-borrow goal
/// to `Logic::All` regresses broad mut-borrow verification to `Unknown`. (#2141)
#[test]
#[timeout(30000)]
fn mut_ref_annotation_does_not_trigger_custom_sorts_detection() {
    let mut_ref_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var(
            "result".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )),
        trust_wp_core::formula::BinOp::Eq,
        Arc::new(PureExpr::Var(
            "input".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )),
    );

    let (use_quantifiers, _needs_array_theory, needs_custom_sorts) =
        detect_logic_requirements(&[], &[mut_ref_ensures], &[], None, None, None);
    assert!(
        use_quantifiers,
        "MutRef carriers should leave pure QF_LIA so whole-borrow UFs can be declared (#2141, #2517)"
    );
    assert!(
        !needs_custom_sorts,
        "MutRef carriers should not force Logic::All setup (#2141)"
    );
}

#[test]
#[timeout(30000)]
fn mut_ref_annotation_bootstraps_uf_capable_logic() {
    use ay_dpll::api::Logic;

    let mut_ref_ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var(
            "result".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )),
        trust_wp_core::formula::BinOp::Eq,
        Arc::new(PureExpr::Var(
            "input".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )),
    );
    let expr_slices = [ExprSlice::formula(std::slice::from_ref(&mut_ref_ensures))];

    let encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: None,
        result_expr: None,
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        track: trust_wp_core::TrackLevel::default(),
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("MutRef equality should bootstrap");

    assert_eq!(
        encoder.logic(),
        Logic::Uflia,
        "MutRef carrier equality should bootstrap a UF-capable logic without escalating to Logic::All (#2141, #2517)"
    );
}

/// Regression for #2593: bootstrap must not reuse the whole-borrow `MutRef`
/// carrier when a precondition first touches `View(Deref(Var("ma")))`.
#[test]
#[timeout(30000)]
fn setup_projects_mutref_current_view_from_predeclared_base_carrier() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::BinOp;

    let mr_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let requires = [PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("ma".to_string(), Some(mr_int)),
        ))))),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let context_exprs: [&PureExpr; 0] = [];

    let setup_result = setup_verification_encoder(&VerificationSetup {
        requires: &requires,
        ensures: &[],
        context_exprs: &context_exprs,
        result_expr: None,
        ghost_context: None,
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        track: trust_wp_core::TrackLevel::default(),
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("bootstrap should encode View(Deref(MutRef(Int))) requires");
    let encoder = setup_result.encoder;

    assert_eq!(
        encoder.var_sort("ma"),
        Some(&Sort::Uninterpreted("__trust_wp_mutref::int".to_string())),
        "the source parameter should stay on the whole-borrow carrier sort"
    );
    assert_eq!(
        encoder.var_sort("ma_current"),
        Some(&Sort::Int),
        "the dereferenced current alias must project to the referent sort"
    );
    assert_eq!(
        encoder.var_sort("ma_current_view"),
        Some(&Sort::Int),
        "the current-view alias must not inherit the whole-borrow carrier (#2593)"
    );
}

/// Regression test for #994: filtered logic functions can require custom
/// sorts even when the goal expression itself does not mention constructors.
#[test]
#[timeout(30000)]
fn logic_fn_body_match_constructor_triggers_logic_all_bootstrap() {
    use ay_dpll::api::Logic;

    let logic_fn = make_logic_fn_with_adt_param("sum", "self");
    let goal = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("l".to_string(), None)),
        method: "sum".to_string(),
        args: vec![],
    };
    let expr_slices = [ExprSlice::formula(std::slice::from_ref(&goal))];

    let encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: None,
        result_expr: None,
        logic_fns: Some(LogicFnInput::FilterForGoal(std::slice::from_ref(&logic_fn))),
        mode_overrides: None,
        type_invariants: None,
        track: trust_wp_core::TrackLevel::default(),
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("logic fn with constructor match should bootstrap");

    assert_eq!(
        encoder.logic(),
        Logic::All,
        "logic fn bodies with constructor matches must route bootstrap to Logic::All (#994)"
    );
}

/// Regression test for #994: filtered type invariants can require custom
/// sorts via datatype spec methods even when the goal is only the invariant UF.
#[test]
#[timeout(30000)]
fn type_invariant_body_datatype_spec_method_triggers_logic_all_bootstrap() {
    use ay_dpll::api::Logic;

    let invariant = make_invariant_with_body(
        "OptWrapper",
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
            method: "is_some".to_string(),
            args: vec![],
        },
    );
    let goal = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: type_invariant_method_name("OptWrapper"),
        args: vec![],
    };
    let expr_slices = [ExprSlice::formula(std::slice::from_ref(&goal))];

    let encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: None,
        result_expr: None,
        logic_fns: None,
        mode_overrides: None,
        type_invariants: Some(TypeInvariantInput::FilterForGoal(std::slice::from_ref(
            &invariant,
        ))),
        track: trust_wp_core::TrackLevel::default(),
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("type invariant with datatype method should bootstrap");

    assert_eq!(
        encoder.logic(),
        Logic::All,
        "type invariant bodies with datatype methods must route bootstrap to Logic::All (#994)"
    );
}

/// Negative test: plain arithmetic should NOT set needs_custom_sorts.
#[test]
#[timeout(30000)]
fn plain_arithmetic_does_not_trigger_custom_sorts() {
    let arith_ensure = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    let (_use_quantifiers, _needs_array_theory, needs_custom_sorts) =
        detect_logic_requirements(&[], &[arith_ensure], &[], None, None, None);
    assert!(
        !needs_custom_sorts,
        "plain arithmetic should not set needs_custom_sorts"
    );
}

/// Regression test for #1944: when `adt_decls` contains user-defined structs,
/// `detect_logic_requirements` must set `needs_custom_sorts`, and the bootstrap
/// must select `Logic::All` so ay's datatype theory is available.
#[test]
#[timeout(30000)]
fn adt_decls_with_custom_struct_triggers_logic_all_bootstrap() {
    use ay_dpll::api::Logic;
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

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

    // Static detection: adt_decls alone should set needs_custom_sorts.
    let (_use_quantifiers, _needs_array_theory, needs_custom_sorts) =
        detect_logic_requirements(&[], &[], &[], None, None, Some(&adt_decls));
    assert!(
        needs_custom_sorts,
        "non-empty adt_decls should set needs_custom_sorts (#1944)"
    );

    // End-to-end: bootstrap with adt_decls should select Logic::All.
    let simple_ensure = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        trust_wp_core::formula::BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let expr_slices = [ExprSlice::formula(std::slice::from_ref(&simple_ensure))];

    let encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: None,
        result_expr: None,
        logic_fns: None,
        mode_overrides: None,
        type_invariants: None,
        track: trust_wp_core::TrackLevel::default(),
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: Some(&adt_decls),
        adt_field_ranges: None,
    })
    .expect("bootstrap with adt_decls should succeed");

    assert_eq!(
        encoder.logic(),
        Logic::All,
        "bootstrap with custom adt_decls must select Logic::All (#1944)"
    );
    assert!(
        encoder.has_custom_datatypes(),
        "encoder should report has_custom_datatypes after adt_decls registration (#1944)"
    );
}

/// Verify that `has_custom_datatypes` returns `false` for an encoder with
/// only the built-in OptionInt/ResultIntInt datatypes.
#[test]
#[timeout(30000)]
fn has_custom_datatypes_false_for_builtins_only() {
    let mut encoder = crate::encoder::AYEncoder::new_all();

    assert!(
        !encoder.has_custom_datatypes(),
        "fresh encoder should not report custom datatypes"
    );

    // Declaring OptionInt (built-in) should not flip the flag.
    encoder.ensure_datatype_declared(&ay_dpll::api::DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor::new(
                "Some".to_string(),
                vec![ay_dpll::api::DatatypeField::new(
                    "val".to_string(),
                    ay_dpll::api::Sort::Int,
                )],
            ),
            ay_dpll::api::DatatypeConstructor::new("None".to_string(), vec![]),
        ],
    });
    assert!(
        !encoder.has_custom_datatypes(),
        "OptionInt is a built-in — should not count as custom (#1944)"
    );

    // Declaring a user-defined datatype should flip the flag.
    encoder.ensure_datatype_declared(&ay_dpll::api::DatatypeSort {
        name: "Point".to_string(),
        constructors: vec![ay_dpll::api::DatatypeConstructor::new(
            "mk_Point".to_string(),
            vec![
                ay_dpll::api::DatatypeField::new("x".to_string(), ay_dpll::api::Sort::Int),
                ay_dpll::api::DatatypeField::new("y".to_string(), ay_dpll::api::Sort::Int),
            ],
        )],
    });
    assert!(
        encoder.has_custom_datatypes(),
        "user-defined Point should count as custom datatype (#1944)"
    );
}
