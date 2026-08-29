// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};
// =============================================================================
// Tests for filter_logic_functions_for_goal
// =============================================================================

/// `filter_logic_functions_for_goal` with `None` logic_fns returns (None, None).
#[test]
#[timeout(30000)]
fn filter_logic_functions_for_goal_none_input_returns_none() {
    let (fns, modes) = super::filter_logic_functions_for_goal(None, None, &[], &[], &[]).unwrap();
    assert!(fns.is_none(), "no logic fns input -> None output");
    assert!(modes.is_none(), "no mode overrides input -> None output");
}

/// `filter_logic_functions_for_goal` returns only logic functions referenced
/// in the goal expressions.
#[test]
#[timeout(30000)]
fn filter_logic_functions_for_goal_filters_unreferenced() {
    use trust_wp_core::logic::LogicFnDef;

    let referenced = LogicFnDef::new(
        "used_fn".into(),
        "mod::used_fn".into(),
        vec![],
        PureExpr::Int(0),
    );
    let unreferenced = LogicFnDef::new(
        "unused_fn".into(),
        "mod::unused_fn".into(),
        vec![],
        PureExpr::Int(1),
    );
    let fns = [referenced.clone(), unreferenced];

    let ensures = [PureExpr::LogicFnCall {
        name: "used_fn".into(),
        args: vec![],
    }];

    let (filtered, _modes) =
        super::filter_logic_functions_for_goal(Some(&fns), None, &[], &ensures, &[]).unwrap();

    let filtered = filtered.unwrap();
    assert_eq!(filtered.len(), 1, "only referenced logic fn should remain");
    assert_eq!(filtered[0].name(), "used_fn");
}

/// `filter_logic_functions_for_goal` silently drops mode_overrides when lengths
/// don't match (#2316, #2700). The overrides are computed from the full
/// logic_fn_defs set, but logic_fns may be a filtered subset. Rather than
/// returning an encoding error, the overrides are dropped and filtered_modes
/// returns None.
#[test]
#[timeout(30000)]
fn filter_logic_functions_for_goal_mismatched_modes_drops_overrides() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let fns = [
        LogicFnDef::new("a".into(), "mod::a".into(), vec![], PureExpr::Int(0)),
        LogicFnDef::new("b".into(), "mod::b".into(), vec![], PureExpr::Int(1)),
    ];
    let modes = [LogicMode::Open]; // length 1 != 2

    let result = super::filter_logic_functions_for_goal(Some(&fns), Some(&modes), &[], &[], &[]);
    // Should NOT error — overrides are dropped
    let (filtered_fns, filtered_modes) = result.expect("should not error on mismatched lengths");
    // filtered_fns should still be returned (possibly empty since no names referenced)
    assert!(filtered_fns.is_some(), "logic fns should be Some");
    // filtered_modes should be None because overrides were dropped
    assert!(
        filtered_modes.is_none(),
        "modes should be None after drop, got: {filtered_modes:?}"
    );
}

/// `filter_logic_functions_for_goal` preserves mode overrides aligned with
/// the filtered indices.
#[test]
#[timeout(30000)]
fn filter_logic_functions_for_goal_preserves_aligned_modes() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let fn_a = LogicFnDef::new("a".into(), "mod::a".into(), vec![], PureExpr::Int(0));
    let fn_b = LogicFnDef::new("b".into(), "mod::b".into(), vec![], PureExpr::Int(1));
    let fns = [fn_a, fn_b];
    let modes = [LogicMode::Open, LogicMode::Default];

    let ensures = [PureExpr::LogicFnCall {
        name: "b".into(),
        args: vec![],
    }];

    let (filtered, filtered_modes) =
        super::filter_logic_functions_for_goal(Some(&fns), Some(&modes), &[], &ensures, &[])
            .unwrap();

    let filtered = filtered.unwrap();
    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].name(), "b");

    let filtered_modes = filtered_modes.unwrap();
    assert_eq!(filtered_modes.len(), 1);
    assert_eq!(
        filtered_modes[0],
        LogicMode::Default,
        "mode should be aligned with filtered fn index"
    );
}

/// Same-module visibility overrides must be reflected both in the aligned
/// override slice and in the filtered definitions seen by downstream setup.
#[test]
#[timeout(30000)]
fn filter_logic_functions_for_goal_applies_effective_mode_to_filtered_defs() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let helper = LogicFnDef::new(
        "max_logic".into(),
        "simple_examples::max_logic".into(),
        vec!["a".into(), "b".into()],
        PureExpr::Ite(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("a".into(), None)),
                trust_wp_core::formula::BinOp::Ge,
                Arc::new(PureExpr::Var("b".into(), None)),
            )),
            Arc::new(PureExpr::Var("a".into(), None)),
            Arc::new(PureExpr::Var("b".into(), None)),
        ),
    )
    .with_mode(LogicMode::Default);
    let unrelated = LogicFnDef::new(
        "unused".into(),
        "simple_examples::unused".into(),
        vec![],
        PureExpr::Int(0),
    );
    let fns = [helper, unrelated];
    let modes = [LogicMode::Open, LogicMode::Default];
    let ensures = [PureExpr::LogicFnCall {
        name: "max_logic".into(),
        args: vec![
            PureExpr::Var("a".into(), Some(ExprSort::Int)),
            PureExpr::Var("b".into(), Some(ExprSort::Int)),
        ],
    }];

    let (filtered, filtered_modes) =
        super::filter_logic_functions_for_goal(Some(&fns), Some(&modes), &[], &ensures, &[])
            .unwrap();

    let filtered = filtered.expect("filtered logic fns");
    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].name(), "max_logic");
    assert_eq!(
        filtered[0].mode(),
        LogicMode::Open,
        "filtered definition should carry the same-module effective mode"
    );
    assert_eq!(
        filtered_modes.expect("filtered modes"),
        vec![LogicMode::Open]
    );
}

#[test]
#[timeout(30000)]
fn filter_logic_functions_for_goal_retains_default_seq_view_for_view_operator() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let view_fn = LogicFnDef::new(
        "view".into(),
        "crate::PersistentArray::view".into(),
        vec!["self".into()],
        PureExpr::LogicFnCall {
            name: "model".into(),
            args: vec![PureExpr::Var("self".into(), None)],
        },
    )
    .with_return_sort(Some(ExprSort::Seq));
    let unrelated = LogicFnDef::new(
        "unused".into(),
        "crate::unused".into(),
        vec![],
        PureExpr::Int(0),
    );
    let fns = [view_fn, unrelated];
    let modes = [LogicMode::Default, LogicMode::Open];
    let ensures = [PureExpr::View(Arc::new(PureExpr::Var(
        "result".into(),
        None,
    )))];

    let (filtered, filtered_modes) =
        super::filter_logic_functions_for_goal(Some(&fns), Some(&modes), &[], &ensures, &[])
            .unwrap();

    let filtered = filtered.expect("filtered logic fns");
    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].name(), "view");
    assert_eq!(
        filtered_modes.expect("filtered modes"),
        vec![LogicMode::Default]
    );
}

#[test]
#[timeout(30000)]
fn filter_logic_functions_for_goal_retains_opaque_view_return_sort_for_view_operator() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let view_fn = LogicFnDef::new(
        "view".into(),
        "crate::<T as View>::view".into(),
        vec!["self".into()],
        PureExpr::Var("self".into(), None),
    )
    .with_opaque(true)
    .with_return_sort(Some(ExprSort::Datatype(intern_sort_name("Mapping"))));
    let unrelated = LogicFnDef::new(
        "unused".into(),
        "crate::unused".into(),
        vec![],
        PureExpr::Int(0),
    );
    let fns = [view_fn, unrelated];
    let modes = [LogicMode::Default, LogicMode::Open];
    let ensures = [PureExpr::View(Arc::new(PureExpr::Var(
        "result".into(),
        None,
    )))];

    let (filtered, filtered_modes) =
        super::filter_logic_functions_for_goal(Some(&fns), Some(&modes), &[], &ensures, &[])
            .unwrap();

    let filtered = filtered.expect("filtered logic fns");
    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].name(), "view");
    assert_eq!(
        filtered_modes.expect("filtered modes"),
        vec![LogicMode::Default]
    );
}

#[test]
#[timeout(30000)]
fn filter_logic_functions_for_goal_scans_selected_type_invariant_bodies() {
    use trust_wp_core::logic::{type_invariant_method_name, LogicFnDef};

    let good_bucket = LogicFnDef::new(
        "good_bucket".into(),
        "crate::MyHashMap::good_bucket".into(),
        vec!["self".into(), "l".into(), "h".into()],
        PureExpr::Bool(true),
    );
    let no_double_binding = LogicFnDef::new(
        "no_double_binding".into(),
        "crate::List::no_double_binding".into(),
        vec!["self".into()],
        PureExpr::Bool(true),
    );
    let unrelated = LogicFnDef::new(
        "unrelated".into(),
        "crate::unrelated".into(),
        vec![],
        PureExpr::Bool(true),
    );
    let logic_fns = [good_bucket, no_double_binding, unrelated];

    let invariant = super::make_invariant_with_body(
        "MyHashMap",
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("self".into(), None)),
                method: "good_bucket".into(),
                args: vec![PureExpr::Var("l".into(), None), PureExpr::Int(0)],
            }),
            trust_wp_core::formula::BinOp::And,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("l".into(), None)),
                method: "no_double_binding".into(),
                args: vec![],
            }),
        ),
    );
    let goal = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("map".into(), None)),
        method: type_invariant_method_name("MyHashMap"),
        args: vec![],
    };
    let selected_invariants = super::filter_type_invariants_for_goal(
        Some(std::slice::from_ref(&invariant)),
        std::slice::from_ref(&goal),
        &[],
        &[],
    )
    .expect("type invariant filter should return a selection");
    let logic_formula_exprs = super::formula_exprs_with_type_invariant_bodies(
        std::slice::from_ref(&goal),
        Some(&selected_invariants),
    );

    let (filtered, _) = super::filter_logic_functions_for_goal(
        Some(&logic_fns),
        None,
        &logic_formula_exprs,
        &[],
        &[],
    )
    .expect("logic filtering should succeed");
    let names = filtered
        .expect("filtered logic functions")
        .into_iter()
        .map(|logic_fn| logic_fn.name().to_string())
        .collect::<std::collections::HashSet<_>>();

    assert!(names.contains("good_bucket"));
    assert!(names.contains("no_double_binding"));
    assert!(!names.contains("unrelated"));
}
