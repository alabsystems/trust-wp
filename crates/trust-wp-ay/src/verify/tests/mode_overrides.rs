// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use crate::{
    tests::helpers::{add, bool_expr, eq, gt, int, var},
    PureExpr,
};

// --- mode_overrides length validation (#1786) ---

#[test]
#[timeout(30000)]
fn mut_borrow_mode_overrides_mismatch_drops_overrides_silently() {
    use std::collections::HashMap;

    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let requires = vec![gt(var("x"), int(0))];
    let ensures = vec![gt(var("result"), int(0))];
    let final_values = HashMap::from([("x".to_string(), int(1))]);

    let logic_fn = LogicFnDef::new("f".to_string(), "crate::f".to_string(), vec![], int(0));
    let logic_fns = vec![logic_fn];
    // 2 overrides for 1 logic fn — overrides are silently dropped (#2316, #2700)
    let mode_overrides = vec![LogicMode::Open, LogicMode::Default];

    let result = crate::verify::mut_borrow::verify_mut_borrow_function_with_modes(
        crate::MutBorrowRequest::new(&requires, &ensures, &final_values)
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides)),
    );
    // Should NOT error — overrides are dropped, verification proceeds
    assert!(
        result.is_ok(),
        "mode_overrides mismatch should be silently dropped, not error: {result:?}"
    );
}

struct SharedRequestFixture {
    requires: Vec<PureExpr>,
    ensures: Vec<PureExpr>,
    ghost_context: Vec<PureExpr>,
    return_expr: PureExpr,
    logic_fns: Vec<trust_wp_core::logic::LogicFnDef>,
    mode_overrides: Vec<trust_wp_core::logic::LogicMode>,
    type_invariants: Vec<trust_wp_core::logic::TypeInvariantDef>,
    timeout: std::time::Duration,
    type_constants: std::collections::HashMap<String, PureExpr>,
    closure_captures: Vec<crate::ClosureCaptureInfo>,
    adt_field_ranges: trust_wp_core::logic::AdtFieldRanges,
    adt_decls: trust_wp_core::logic::AdtDecls,
    unsoundness_snapshot: crate::encoder::unsoundness::Snapshot,
}

impl SharedRequestFixture {
    fn sample_logic_fn() -> trust_wp_core::logic::LogicFnDef {
        trust_wp_core::logic::LogicFnDef::new(
            "helper".to_string(),
            "crate::helper".to_string(),
            vec!["x".to_string()],
            add(var("x"), int(1)),
        )
        .with_mode(trust_wp_core::logic::LogicMode::Open)
    }

    fn sample_type_invariant() -> trust_wp_core::logic::TypeInvariantDef {
        trust_wp_core::type_invariant_def! {
            type_name: "Counter".to_string(),
            self_param: "self".to_string(),
            param_sort: None,
            body: gt(var("self"), int(0)),
            is_newtype: false,
            element_invariant_method: None,
        }
    }

    fn sample_closure_capture() -> crate::ClosureCaptureInfo {
        crate::closure_capture_info! {
            def_id: "crate::closure".to_string(),
            captures: vec![crate::CaptureField::new(
                "x",
                crate::ExprSort::Int,
                crate::CaptureKind::ByMutRef,
            )],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: Some(vec!["arg".to_string()]),
            ensures_exprs: None,
        }
    }

    fn sample_adt_field_ranges() -> trust_wp_core::logic::AdtFieldRanges {
        std::collections::HashMap::from([(
            "Counter".to_string(),
            vec![(
                "Counter".to_string(),
                vec![(0, trust_wp_core::logic::FieldRangeKind::Unsigned(32))],
            )],
        )])
    }

    fn sample_adt_decls() -> trust_wp_core::logic::AdtDecls {
        use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

        std::collections::HashMap::from([(
            "Counter".to_string(),
            AdtDecl::new(
                "crate::Counter".to_string(),
                "Counter".to_string(),
                AdtKind::Struct,
                vec![AdtConstructorDecl::new(
                    "Counter".to_string(),
                    "Counter".to_string(),
                    vec![AdtFieldDecl::new("value".to_string(), crate::ExprSort::Int)],
                )],
            ),
        )])
    }

    fn sample_unsoundness_snapshot() -> crate::encoder::unsoundness::Snapshot {
        std::collections::HashMap::from([(
            crate::encoder::unsoundness::UnsoundnessCategory::SortFallbackToInt,
            1,
        )])
    }

    fn sample() -> Self {
        use std::{collections::HashMap, time::Duration};

        let requires = vec![gt(var("x"), int(0))];
        let ensures = vec![eq(var("result"), add(var("x"), int(1)))];
        let ghost_context = vec![eq(var("ghost_flag"), bool_expr(true))];
        let return_expr = add(var("x"), int(1));
        let logic_fns = vec![Self::sample_logic_fn()];
        let mode_overrides = vec![trust_wp_core::logic::LogicMode::OpenSelf];
        let type_invariants = vec![Self::sample_type_invariant()];
        let timeout = Duration::from_secs(7);
        let type_constants = HashMap::from([("T::MAX".to_string(), PureExpr::Int(99))]);
        let closure_captures = vec![Self::sample_closure_capture()];
        let adt_field_ranges = Self::sample_adt_field_ranges();
        let adt_decls = Self::sample_adt_decls();
        let unsoundness_snapshot = Self::sample_unsoundness_snapshot();

        Self {
            requires,
            ensures,
            ghost_context,
            return_expr,
            logic_fns,
            mode_overrides,
            type_invariants,
            timeout,
            type_constants,
            closure_captures,
            adt_field_ranges,
            adt_decls,
            unsoundness_snapshot,
        }
    }
}

fn assert_shared_request_base(
    base: &crate::verify::types::VerificationBase<'_>,
    fixture: &SharedRequestFixture,
) {
    assert_eq!(base.requires, fixture.requires.as_slice());
    assert_eq!(base.ensures, fixture.ensures.as_slice());
    assert_eq!(base.ghost_context, Some(fixture.ghost_context.as_slice()));
    assert_eq!(base.return_expr, Some(&fixture.return_expr));
    assert_eq!(base.mode_overrides, Some(fixture.mode_overrides.as_slice()));
    assert_eq!(base.track, Some(crate::TrackLevel::Ptr));
    assert_eq!(base.timeout, Some(fixture.timeout));
    assert_eq!(base.type_constants, Some(&fixture.type_constants));
    assert!(base.total_int_arithmetic);
    assert_eq!(
        base.adt_field_ranges.as_ref(),
        Some(&fixture.adt_field_ranges)
    );
    assert_eq!(base.adt_decls.as_ref(), Some(&fixture.adt_decls));
    assert_eq!(
        base.unsoundness_snapshot.as_ref(),
        Some(&fixture.unsoundness_snapshot)
    );

    let logic_fns = base.logic_fns.expect("logic_fns should be stored in base");
    assert_eq!(logic_fns.len(), fixture.logic_fns.len());
    assert_eq!(logic_fns[0].name(), fixture.logic_fns[0].name());
    assert_eq!(logic_fns[0].full_path(), fixture.logic_fns[0].full_path());
    assert_eq!(logic_fns[0].body(), fixture.logic_fns[0].body());
    assert_eq!(logic_fns[0].mode(), fixture.logic_fns[0].mode());

    let type_invariants = base
        .type_invariants
        .expect("type_invariants should be stored in base");
    assert_eq!(type_invariants.len(), fixture.type_invariants.len());
    assert_eq!(
        type_invariants[0].type_name(),
        fixture.type_invariants[0].type_name()
    );
    assert_eq!(
        type_invariants[0].self_param(),
        fixture.type_invariants[0].self_param()
    );
    assert_eq!(type_invariants[0].body(), fixture.type_invariants[0].body());

    let closure_captures = base
        .closure_captures
        .expect("closure_captures should be stored in base");
    assert_eq!(closure_captures.len(), fixture.closure_captures.len());
    assert_eq!(
        closure_captures[0].def_id(),
        fixture.closure_captures[0].def_id()
    );
    assert_eq!(
        closure_captures[0].param_name(),
        fixture.closure_captures[0].param_name()
    );
    assert_eq!(
        closure_captures[0].captures(),
        fixture.closure_captures[0].captures()
    );
}

#[test]
#[timeout(30000)]
fn verification_request_shared_builders_write_through_to_base() {
    let fixture = SharedRequestFixture::sample();

    let request = crate::VerificationRequest::new(&fixture.requires, &fixture.ensures)
        .ghost_context(Some(&fixture.ghost_context))
        .return_expr(Some(&fixture.return_expr))
        .logic_fns(Some(&fixture.logic_fns))
        .mode_overrides(Some(&fixture.mode_overrides))
        .type_invariants(Some(&fixture.type_invariants))
        .track(Some(crate::TrackLevel::Ptr))
        .timeout(Some(fixture.timeout))
        .type_constants(Some(&fixture.type_constants))
        .closure_captures(Some(&fixture.closure_captures))
        .total_int_arithmetic(true)
        .adt_field_ranges(Some(fixture.adt_field_ranges.clone()))
        .adt_decls(Some(fixture.adt_decls.clone()))
        .unsoundness_snapshot(Some(fixture.unsoundness_snapshot.clone()));

    assert_shared_request_base(&request.base, &fixture);
}

#[test]
#[timeout(30000)]
fn mut_borrow_request_shared_builders_write_through_to_base() {
    let fixture = SharedRequestFixture::sample();
    let final_values = std::collections::HashMap::from([("x".to_string(), var("x_final"))]);

    let request = crate::MutBorrowRequest::new(&fixture.requires, &fixture.ensures, &final_values)
        .ghost_context(Some(&fixture.ghost_context))
        .return_expr(Some(&fixture.return_expr))
        .logic_fns(Some(&fixture.logic_fns))
        .mode_overrides(Some(&fixture.mode_overrides))
        .type_invariants(Some(&fixture.type_invariants))
        .track(Some(crate::TrackLevel::Ptr))
        .timeout(Some(fixture.timeout))
        .type_constants(Some(&fixture.type_constants))
        .closure_captures(Some(&fixture.closure_captures))
        .total_int_arithmetic(true)
        .adt_field_ranges(Some(fixture.adt_field_ranges.clone()))
        .adt_decls(Some(fixture.adt_decls.clone()))
        .unsoundness_snapshot(Some(fixture.unsoundness_snapshot.clone()));

    assert_shared_request_base(&request.base, &fixture);
    assert_eq!(request.final_values, &final_values);
    assert!(request.resolve_assumptions.is_none());
    assert!(request.prophecy_writebacks.is_none());
    assert!(request.borrow_finality.is_none());
    assert!(request.mutation_continued_params.is_none());
}
