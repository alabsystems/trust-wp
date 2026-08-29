// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

use super::*;
#[test]
#[timeout(30000)]
fn build_logic_fn_param_dt_map_finds_adt_param() {
    let logic_fn = make_logic_fn_with_adt_param("sum", "self");
    let map = super::build_logic_fn_param_dt_map(&[logic_fn], &[]);

    assert!(map.contains_key("sum"), "should find 'sum' entry");
    let entries = &map["sum"];
    assert_eq!(entries.len(), 1, "should have one Datatype param");
    assert_eq!(entries[0].0, 0, "param index 0 (self) should be Datatype");
    let dt = &entries[0].1;
    assert_eq!(dt.constructors.len(), 2, "Cons and Nil");
}

#[test]
#[timeout(30000)]
fn collect_call_site_dt_vars_maps_method_receiver() {
    let logic_fn = make_logic_fn_with_adt_param("sum", "self");
    let param_dt_map = super::build_logic_fn_param_dt_map(&[logic_fn], &[]);

    // Simulate: `l.sum()` → MethodCall { receiver: Var("l"), method: "sum", args: [] }
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("l".to_string(), None)),
        method: "sum".to_string(),
        args: vec![],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_call_site_dt_vars(&expr, &param_dt_map, &mut dt_vars);

    assert!(
        dt_vars.contains_key("l"),
        "call-site var 'l' should be mapped to Datatype sort"
    );
    assert_eq!(dt_vars["l"].constructors.len(), 2);
}

#[test]
#[timeout(30000)]
fn collect_call_site_dt_vars_maps_deref_receiver() {
    let logic_fn = make_logic_fn_with_adt_param("sum", "self");
    let param_dt_map = super::build_logic_fn_param_dt_map(&[logic_fn], &[]);

    // Simulate: `(*self).sum()` → MethodCall { receiver: Deref(Var("self")), method: "sum" }
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self".to_string(),
            None,
        )))),
        method: "sum".to_string(),
        args: vec![],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_call_site_dt_vars(&expr, &param_dt_map, &mut dt_vars);

    assert!(
        dt_vars.contains_key("self_current"),
        "Deref(Var('self')) should map to 'self_current'"
    );
}

#[test]
#[timeout(30000)]
fn collect_call_site_dt_vars_in_binop() {
    let logic_fn = make_logic_fn_with_adt_param("sum", "self");
    let param_dt_map = super::build_logic_fn_param_dt_map(&[logic_fn], &[]);

    // Simulate: `l.sum() + k@ <= 1_000_000`
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("l".to_string(), None)),
                method: "sum".to_string(),
                args: vec![],
            }),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "k".to_string(),
                None,
            )))),
        )),
        trust_wp_core::formula::BinOp::Le,
        Arc::new(PureExpr::Int(1_000_000)),
    );

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_call_site_dt_vars(&expr, &param_dt_map, &mut dt_vars);

    assert!(
        dt_vars.contains_key("l"),
        "nested MethodCall receiver 'l' should be found in BinOp tree"
    );
    assert!(
        !dt_vars.contains_key("k"),
        "'k' is not a Datatype-sorted param"
    );
}

#[test]
#[timeout(30000)]
fn resolve_call_site_var_name_handles_all_forms() {
    assert_eq!(
        super::resolve_call_site_var_name(&PureExpr::Var("l".to_string(), None)),
        Some("l".to_string())
    );
    assert_eq!(
        super::resolve_call_site_var_name(&PureExpr::Deref(Arc::new(PureExpr::Var(
            "self".to_string(),
            None
        )))),
        Some("self_current".to_string())
    );
    assert_eq!(
        super::resolve_call_site_var_name(&PureExpr::Final(Arc::new(PureExpr::Var(
            "self".to_string(),
            None
        )))),
        Some("self_final".to_string())
    );
    assert_eq!(
        super::resolve_call_site_var_name(&PureExpr::Int(42)),
        None,
        "non-variable expressions should return None"
    );
}

#[test]
#[timeout(30000)]
fn collect_call_site_dt_vars_rejects_incompatible_final_annotation() {
    let logic_fn = make_logic_fn_with_adt_param("get", "self");
    let param_dt_map = super::build_logic_fn_param_dt_map(&[logic_fn], &[]);

    // Models the hashmap_list.rs pollution shape: an unqualified `get` with a
    // List-sorted formal must not predeclare `^self` as List when MIR already
    // says the argument is `&mut MyHashMap`.
    let expr = PureExpr::LogicFnCall {
        name: "get".to_string(),
        args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
            "self".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                intern_sort_name("MyHashMap"),
            )))),
        )))],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_call_site_dt_vars(&expr, &param_dt_map, &mut dt_vars);

    assert!(
        !dt_vars.contains_key("self_final"),
        "incompatible final receiver annotation must not be predeclared as List"
    );
}

#[test]
#[timeout(30000)]
fn collect_call_site_dt_vars_accepts_compatible_final_annotation() {
    let logic_fn = make_logic_fn_with_adt_param("get", "self");
    let param_dt_map = super::build_logic_fn_param_dt_map(&[logic_fn], &[]);
    let list_dt_name = &param_dt_map["get"][0].1.name;

    let expr = PureExpr::LogicFnCall {
        name: "get".to_string(),
        args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
            "l".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                intern_sort_name(list_dt_name),
            )))),
        )))],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_call_site_dt_vars(&expr, &param_dt_map, &mut dt_vars);

    assert!(
        dt_vars.contains_key("l_final"),
        "matching final receiver annotation should still propagate datatype evidence"
    );
}

#[test]
#[timeout(30000)]
fn collect_call_site_dt_vars_skips_ambiguous_short_method_receiver() {
    let list_dt = ay_dpll::api::DatatypeSort {
        name: "List".to_string(),
        constructors: vec![],
    };
    let map_dt = ay_dpll::api::DatatypeSort {
        name: "MyHashMap".to_string(),
        constructors: vec![],
    };
    let param_dt_map = std::collections::HashMap::from([(
        "get".to_string(),
        vec![(0, list_dt.clone()), (0, map_dt.clone())],
    )]);

    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self".to_string(),
            None,
        )))),
        method: "get".to_string(),
        args: vec![],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_call_site_dt_vars(&expr, &param_dt_map, &mut dt_vars);

    assert!(
        !dt_vars.contains_key("self_current"),
        "unannotated receiver must not be predeclared from ambiguous short-name get candidates"
    );
}

#[test]
#[timeout(30000)]
fn collect_call_site_dt_vars_uses_annotation_to_disambiguate_short_method_receiver() {
    let list_dt = ay_dpll::api::DatatypeSort {
        name: "List".to_string(),
        constructors: vec![],
    };
    let map_dt = ay_dpll::api::DatatypeSort {
        name: "MyHashMap".to_string(),
        constructors: vec![],
    };
    let param_dt_map = std::collections::HashMap::from([(
        "get".to_string(),
        vec![(0, list_dt.clone()), (0, map_dt.clone())],
    )]);

    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                intern_sort_name("MyHashMap"),
            )))),
        )))),
        method: "get".to_string(),
        args: vec![],
    };

    let mut dt_vars = std::collections::HashMap::new();
    super::collect_call_site_dt_vars(&expr, &param_dt_map, &mut dt_vars);

    assert_eq!(
        dt_vars.get("self_current").map(|dt| dt.name.as_str()),
        Some("MyHashMap"),
        "receiver annotation should choose the matching datatype candidate"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_collects_usage_sorts_and_formula_fn_hints() {
    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();
    let formula = PureExpr::LogicFnCall {
        name: "is_valid".to_string(),
        args: vec![],
    };
    let value = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))),
        method: "len".to_string(),
        args: vec![],
    };

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        std::slice::from_ref(&formula),
        &[&value],
        None,
        None,
        None,
        None,
        None,
    );

    assert_eq!(
        plan.source_sort("v"),
        Some(&ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int)),
        "Seq-only method evidence should become a planned source declaration"
    );
    assert_eq!(
        plan.sort_hint("v_view"),
        Some(&trust_wp_core::formula::ExprSort::Seq),
        "view-derived receiver hints should remain in the planned bootstrap boundary"
    );
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("is_valid");
    assert_eq!(
        plan.sort_hint(&smt_name),
        Some(&trust_wp_core::formula::ExprSort::Bool),
        "formula-position logic fn calls should register Bool return hints in the plan"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_does_not_leak_logic_fn_local_self_datatype() {
    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();
    let logic_fn = make_logic_fn_with_adt_param("get", "self");

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        &[],
        &[],
        None,
        None,
        Some(std::slice::from_ref(&logic_fn)),
        None,
        None,
    );

    assert!(
        plan.source_sort("self").is_none(),
        "logic-function-local self must not predeclare the verified function's self"
    );
    assert!(
        plan.source_sort("self_current").is_none(),
        "logic-function-local match scrutinees must not leak as self_current"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_strengthens_result_constructor_datatype() {
    use trust_wp_core::formula::intern_sort_name;

    use crate::tests::helpers::{eq, int, logic_fn_call};

    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();
    let formula = eq(
        PureExpr::Var(
            "result".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("std::option::Option"))),
        ),
        logic_fn_call("Some", vec![int(1)]),
    );

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        std::slice::from_ref(&formula),
        &[],
        None,
        Some(std::slice::from_ref(&formula)),
        None,
        None,
        None,
    );

    assert!(
        matches!(plan.source_sort("result"), Some(ay_dpll::api::Sort::Datatype(dt)) if dt.name == "OptionInt"),
        "constructor equality should predeclare result as OptionInt instead of weak Option"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_prefers_body_option_payload_over_none_postcondition() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::intern_sort_name;

    use crate::tests::helpers::{eq, logic_fn_call, var};

    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();
    let formula = eq(
        PureExpr::Var(
            "result".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("std::option::Option"))),
        ),
        logic_fn_call("None", vec![]),
    );
    let return_expr = logic_fn_call(
        "Some",
        vec![logic_fn_call("OwnResult::Err", vec![var("e")])],
    );

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        std::slice::from_ref(&formula),
        &[&return_expr],
        Some(&return_expr),
        Some(std::slice::from_ref(&formula)),
        None,
        None,
        None,
    );

    let Some(Sort::Datatype(dt)) = plan.source_sort("result") else {
        panic!("None postcondition plus Some(user-constructor) body should predeclare a datatype");
    };
    assert_ne!(
        dt.name, "OptionInt",
        "body constructor payload evidence should prevent weak OptionInt predeclaration"
    );
    let some_ctor = dt
        .constructors
        .iter()
        .find(|ctor| ctor.name.ends_with("__Some") || ctor.name == "Some")
        .expect("payload option datatype should include a Some constructor");
    assert_eq!(
        some_ctor.fields.first().map(|field| &field.sort),
        Some(&Sort::Uninterpreted("OwnResult".to_string())),
        "Some payload should use the user constructor carrier sort"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_strengthens_return_call_alias_for_result_match() {
    use trust_wp_core::formula::Pattern;

    use crate::tests::helpers::{bool_expr, match_expr, var};

    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();
    let formula = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                bool_expr(true),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                bool_expr(true),
            ),
        ],
    );
    let return_expr = var("call_3");

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        std::slice::from_ref(&formula),
        &[&return_expr],
        Some(&return_expr),
        Some(std::slice::from_ref(&formula)),
        None,
        None,
        None,
    );

    assert!(
        matches!(plan.source_sort("result"), Some(ay_dpll::api::Sort::Datatype(dt)) if dt.name == "OptionInt"),
        "result should be predeclared as OptionInt for match postconditions"
    );
    assert!(
        matches!(plan.source_sort("call_3"), Some(ay_dpll::api::Sort::Datatype(dt)) if dt.name == "OptionInt"),
        "synthetic return call alias should share result's OptionInt sort"
    );
    assert!(
        plan.source_sort("ordinary").is_none(),
        "non-return variables should not be introduced by this strengthening"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_predeclares_self_for_closure_captures() {
    use trust_wp_core::formula::intern_sort_name;

    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();
    let capture_info = crate::closure_capture_info! {
        def_id: "test::closure#0".to_string(),
        captures: vec![crate::CaptureField::new(
            "x",
            crate::ExprSort::Datatype(intern_sort_name("NonZero")),
            crate::CaptureKind::ByValue,
        )],
        param_name: Some("self".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    };
    let expected_sort = ay_dpll::api::Sort::Uninterpreted(format!(
        "ClosureEnv_{}",
        crate::encoder::closure_sorts::closure_symbol_suffix(capture_info.def_id())
    ));

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        &[],
        &[],
        None,
        None,
        None,
        None,
        Some(std::slice::from_ref(&capture_info)),
    );

    assert_eq!(
        plan.source_sort("self"),
        Some(&expected_sort),
        "closure bootstrap should predeclare the receiver name with the closure-env sort"
    );
}

#[test]
#[timeout(30000)]
fn bootstrap_encoder_predeclares_result_constructor_datatype() {
    use trust_wp_core::formula::intern_sort_name;

    use crate::tests::helpers::{eq, int, logic_fn_call};

    let formula = eq(
        PureExpr::Var(
            "result".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("std::option::Option"))),
        ),
        logic_fn_call("Some", vec![int(1)]),
    );
    let expr_slices = [ExprSlice::formula(std::slice::from_ref(&formula))];

    let encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: Some(std::slice::from_ref(&formula)),
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
    .expect("bootstrap should predeclare result with the stronger OptionInt datatype");

    assert!(
        matches!(encoder.var_sort("result"), Some(ay_dpll::api::Sort::Datatype(dt)) if dt.name == "OptionInt"),
        "bootstrap should bind result directly to OptionInt to avoid later phantom upgrades"
    );
}

#[test]
#[timeout(30000)]
fn bootstrap_encoder_does_not_strengthen_requires_only_result_constructor() {
    use crate::tests::helpers::{eq, int, logic_fn_call};

    let requires = eq(
        PureExpr::Var("result".to_string(), None),
        logic_fn_call("Some", vec![int(1)]),
    );
    let expr_slices = [ExprSlice::formula(std::slice::from_ref(&requires))];

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
    .expect("non-postcondition result equality should not force constructor datatype");

    // Constructor equality evidence (`result == Some(1)`) assigns the
    // reserved OptionInt family instead of leaving the variable untyped.
    // AY 0.4 requires that reserved family to use its canonical native
    // datatype from the first declaration; this is representation
    // normalization, not an added postcondition assumption.
    let sort = encoder
        .var_sort("result")
        .expect("constructor equality evidence should assign result a sort");
    assert!(
        matches!(&sort, ay_dpll::api::Sort::Datatype(dt) if dt.name == "OptionInt"),
        "requires-only constructor evidence should use native OptionInt: {sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn bootstrap_encoder_applies_sort_plan_for_declared_logic_fn_domain() {
    use trust_wp_core::{
        formula::ExprSort,
        logic::{LogicFnDef, LogicMode},
    };

    let logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["s".to_string()],
        PureExpr::Int(0),
    )
    .with_param_sorts(vec![Some(ExprSort::Seq)])
    .with_mode(LogicMode::Open);

    let call = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![PureExpr::View(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))],
    };
    let expr_slices = [ExprSlice::value(std::slice::from_ref(&call))];

    let encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: None,
        result_expr: None,
        logic_fns: Some(LogicFnInput::Prefiltered(std::slice::from_ref(&logic_fn))),
        mode_overrides: None,
        type_invariants: None,
        track: trust_wp_core::TrackLevel::default(),
        timeout: None,
        type_constants: None,
        closure_captures: None,
        adt_decls: None,
        adt_field_ranges: None,
    })
    .expect("bootstrap should apply the planned Seq declaration");

    // Assert the INVARIANT, not one spelling of it. What this test is about —
    // per its own message — is that logic-fn domain propagation predeclares
    // the derived view name via SortPlan at all, rather than leaving it Int.
    // Which Seq carrier that sort is spelled with is the encoder's choice and
    // differs by track.
    //
    // Hard-coding `Sort::seq(Sort::Int)` here also pinned the exact thing whose
    // violation caused the Seq-split bug: a predeclared variable sort that
    // disagrees with the carrier the projectors are declared over. Comparing
    // against the encoder's own carrier tests that agreement, so this is a
    // stronger demand than the literal was, not a weaker one — and it is the
    // reason the literal and `hard_timeout_and_retry`'s
    // `Sort::Uninterpreted("Seq")` could not both hold.
    assert_eq!(
        encoder.var_sort("v_view"),
        Some(&encoder.seq_carrier().sort()),
        "logic-fn domain propagation should predeclare the input-derived view \
         name via SortPlan, at the encoder's own Seq carrier"
    );
    assert_ne!(
        encoder.var_sort("v_view"),
        Some(&ay_dpll::api::Sort::Int),
        "the predeclared view name must not fall back to Int"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_applies_method_call_logic_fn_domain() {
    use ay_dpll::api::Sort;
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{LogicFnDef, LogicMode},
    };

    let logic_fn = LogicFnDef::new(
        "invariant".to_string(),
        "AssocStruct::invariant".to_string(),
        vec!["self".to_string()],
        PureExpr::Bool(true),
    )
    .with_param_sorts(vec![Some(ExprSort::Datatype(intern_sort_name(
        "AssocStruct",
    )))])
    .with_mode(LogicMode::Open);
    let formula = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("assoc".to_string(), None)),
        method: "invariant".to_string(),
        args: vec![],
    };
    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        std::slice::from_ref(&formula),
        &[],
        None,
        None,
        Some(std::slice::from_ref(&logic_fn)),
        None,
        None,
    );

    assert_eq!(
        plan.source_sort("assoc"),
        Some(&Sort::Uninterpreted("AssocStruct".to_string())),
        "method-call receiver should get the called logic function's declared domain sort"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_ignores_unrelated_logic_param_names() {
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{LogicFnDef, LogicMode},
    };

    let map_sort = ExprSort::Datatype(intern_sort_name("MyHashMap"));
    let unrelated = LogicFnDef::new(
        "resolve".to_string(),
        "MyHashMap::resolve".to_string(),
        vec!["self".to_string(), "result".to_string()],
        PureExpr::Bool(true),
    )
    .with_param_sorts(vec![Some(map_sort.clone()), Some(map_sort)])
    .with_mode(LogicMode::Open);
    let value = PureExpr::Var("ordinary".to_string(), None);
    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        &[],
        &[&value],
        None,
        None,
        Some(std::slice::from_ref(&unrelated)),
        None,
        None,
    );

    assert!(
        plan.source_sort("self").is_none() && plan.source_sort("result").is_none(),
        "visible logic functions must not globally seed common parameter names"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_seeds_active_logic_fn_param_names() {
    use ay_dpll::api::Sort;
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{LogicFnDef, LogicMode},
    };

    let ensures = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("assoc".to_string(), None)),
        method: "invariant".to_string(),
        args: vec![],
    };
    let mut logic_fn = LogicFnDef::new(
        "invariant".to_string(),
        "Struct::invariant".to_string(),
        vec!["self".to_string(), "assoc".to_string()],
        PureExpr::Bool(true),
    )
    .with_param_sorts(vec![
        Some(ExprSort::Datatype(intern_sort_name("Struct"))),
        Some(ExprSort::Datatype(intern_sort_name("AssocStruct"))),
    ])
    .with_mode(LogicMode::Open);
    logic_fn.set_ensures(vec![ensures.clone()]);
    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        std::slice::from_ref(&ensures),
        &[],
        None,
        Some(std::slice::from_ref(&ensures)),
        Some(std::slice::from_ref(&logic_fn)),
        None,
        None,
    );

    assert_eq!(
        plan.source_sort("assoc"),
        Some(&Sort::Uninterpreted("AssocStruct".to_string())),
        "a logic function's own postcondition should see its parameter sort"
    );
}

#[test]
#[timeout(30000)]
fn build_bootstrap_sort_plan_does_not_pollute_seq_receiver_from_overloaded_method() {
    use ay_dpll::api::Sort;
    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort},
        logic::{LogicFnDef, LogicMode},
    };

    let memory_sort = ExprSort::Datatype(intern_sort_name("Memory"));
    let memory_index = LogicFnDef::new(
        "index_logic".to_string(),
        "Memory::index_logic".to_string(),
        vec!["self".to_string(), "i".to_string()],
        PureExpr::Int(0),
    )
    .with_param_sorts(vec![Some(memory_sort.clone()), Some(ExprSort::Int)])
    .with_mode(LogicMode::Open);
    let list_seg = LogicFnDef::new(
        "list_seg".to_string(),
        "Memory::list_seg".to_string(),
        vec![
            "self".to_string(),
            "first".to_string(),
            "s".to_string(),
            "last".to_string(),
            "l".to_string(),
            "h".to_string(),
        ],
        PureExpr::Bool(true),
    )
    .with_param_sorts(vec![
        Some(memory_sort),
        Some(ExprSort::Int),
        Some(ExprSort::Seq),
        Some(ExprSort::Int),
        Some(ExprSort::Int),
        Some(ExprSort::Int),
    ])
    .with_mode(LogicMode::Open);

    let ambiguous_index = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("s2".to_string(), None)),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    let seq_domain_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
        method: "list_seg".to_string(),
        args: vec![
            PureExpr::Var("first".to_string(), None),
            PureExpr::Var("s2".to_string(), None),
            PureExpr::Var("last".to_string(), None),
            PureExpr::Int(0),
            PureExpr::Int(1),
        ],
    };
    let encoder = crate::encoder::AYEncoder::new_with_quantifiers();
    let logic_fns = vec![memory_index, list_seg];

    let plan = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        &[],
        &[&ambiguous_index, &seq_domain_call],
        None,
        None,
        Some(&logic_fns),
        None,
        None,
    );

    assert_eq!(
        plan.source_sort("s2"),
        Some(&Sort::seq(Sort::Int)),
        "ambiguous index_logic overloads must not overwrite list_seg's Seq domain evidence"
    );

    let plan_with_seq_evidence_first = super::bootstrap::build_bootstrap_sort_plan(
        &encoder,
        &[],
        &[&seq_domain_call, &ambiguous_index],
        None,
        None,
        Some(&logic_fns),
        None,
        None,
    );

    assert_eq!(
        plan_with_seq_evidence_first.source_sort("s2"),
        Some(&Sort::seq(Sort::Int)),
        "incompatible single-candidate index_logic evidence must not replace existing Seq evidence"
    );
}

#[test]
#[timeout(30000)]
fn bootstrap_encoder_preserves_view_alias_hints_from_plan() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))),
        method: "len".to_string(),
        args: vec![],
    };
    let expr_slices = [ExprSlice::value(std::slice::from_ref(&expr))];

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
    .expect("bootstrap should preserve planned view alias hints");

    let receiver = match &expr {
        PureExpr::MethodCall { receiver, .. } => receiver.as_ref(),
        _ => unreachable!("test expression is a method call"),
    };
    assert!(
        encoder.is_seq_receiver(receiver, None),
        "bootstrap should route view-derived Seq evidence through the planned hint boundary"
    );
}
