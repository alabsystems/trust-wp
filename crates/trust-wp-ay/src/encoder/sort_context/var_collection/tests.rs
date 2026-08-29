// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use super::*;

#[test]
#[timeout(30000)]
fn test_var_with_no_context_defaults_to_int() {
    let exprs = vec![PureExpr::Var("x".into(), None)];
    let usage = collect_variable_usage(&exprs);
    assert_eq!(usage.len(), 1);
    let sort = determine_sort(usage.get("x").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::Int);
}

#[test]
#[timeout(30000)]
fn test_var_with_seq_annotation() {
    let exprs = vec![PureExpr::Var("v".into(), Some(ExprSort::Seq))];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("v").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_var_with_bool_annotation() {
    let exprs = vec![PureExpr::Var("b".into(), Some(ExprSort::Bool))];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("b").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_var_in_bool_context_via_and() {
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("flag".into(), None)),
        BinOp::And,
        Arc::new(PureExpr::Bool(true)),
    )];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("flag").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_view_marks_has_view() {
    // View alone is ambiguous (could be scalar i32@ or collection Vec@).
    // has_view is recorded but does NOT determine Seq by itself.
    let exprs = vec![PureExpr::View(Arc::new(PureExpr::Var("s".into(), None)))];
    let usage = collect_variable_usage(&exprs);
    assert!(usage.get("s").unwrap().has_view);
    // Without additional evidence, defaults to Int.
    let sort = determine_sort(usage.get("s").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::Int);
}

#[test]
#[timeout(30000)]
fn test_view_with_seq_method_resolves_to_seq() {
    // View + len method together indicate a Seq-sorted variable.
    let exprs = vec![
        PureExpr::View(Arc::new(PureExpr::Var("v".into(), None))),
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("v".into(), None)),
            method: "len".into(),
            args: vec![],
        },
    ];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("v").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_method_call_records_method() {
    let exprs = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".into(), None)),
        method: "push_back".into(),
        args: vec![PureExpr::Int(42)],
    }];
    let usage = collect_variable_usage(&exprs);
    assert!(usage
        .get("v")
        .unwrap()
        .method_calls
        .contains(&"push_back".to_string()));
    let sort = determine_sort(usage.get("v").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_tuple_constructor_equality_resolves_tuple_sort_independent_of_formula_order() {
    let tuple2 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2);
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let exprs = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: tuple_get_0,
                args: vec![PureExpr::Var("p".into(), None)],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(4)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("p".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: tuple2,
                args: vec![PureExpr::Int(2), PureExpr::Int(3)],
            }),
        ),
    ];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("p").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("Tuple2".to_string())
    );
}

#[test]
#[timeout(30000)]
fn test_tuple_field_projection_marks_view_tuple_sort() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);
    let exprs = vec![
        PureExpr::LogicFnCall {
            name: tuple_get_0,
            args: vec![PureExpr::View(Arc::new(PureExpr::Var("frag".into(), None)))],
        },
        PureExpr::LogicFnCall {
            name: tuple_get_1,
            args: vec![PureExpr::View(Arc::new(PureExpr::Var("frag".into(), None)))],
        },
    ];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("frag_view").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("Tuple2".to_string()),
        "tuple field projections on frag@ should predeclare frag_view as Tuple2"
    );
}

#[test]
#[timeout(30000)]
fn test_tuple_field_projection_beats_view_annotation() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);
    let authority_id = trust_wp_core::formula::intern_sort_name("Authority");
    let exprs = vec![
        PureExpr::Var("frag_view".into(), Some(ExprSort::Datatype(authority_id))),
        PureExpr::LogicFnCall {
            name: tuple_get_0,
            args: vec![PureExpr::View(Arc::new(PureExpr::Var("frag".into(), None)))],
        },
        PureExpr::LogicFnCall {
            name: tuple_get_1,
            args: vec![PureExpr::View(Arc::new(PureExpr::Var("frag".into(), None)))],
        },
    ];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("frag_view").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("Tuple2".to_string()),
        "tuple projection evidence should outrank non-Int view annotations for frag_view"
    );
}

#[test]
#[timeout(30000)]
fn test_tuple_constructor_equality_on_view_marks_view_tuple_sort() {
    let tuple2 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2);
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "result".into(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: tuple2,
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        }),
    )];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("result_view").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("Tuple2".to_string()),
        "tuple constructor equality on result@ should predeclare result_view as Tuple2"
    );
}

#[test]
#[timeout(30000)]
fn test_conflicting_tuple_constructor_branches_do_not_force_arity() {
    let tuple2 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2);
    let tuple3 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(3);
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("p".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Ite(
            Arc::new(PureExpr::Var("flag".into(), None)),
            Arc::new(PureExpr::LogicFnCall {
                name: tuple2,
                args: vec![PureExpr::Int(2), PureExpr::Int(3)],
            }),
            Arc::new(PureExpr::LogicFnCall {
                name: tuple3,
                args: vec![PureExpr::Int(2), PureExpr::Int(3), PureExpr::Int(4)],
            }),
        )),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("p").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::Int);
}

#[test]
#[timeout(30000)]
fn test_quantifier_sort_evidence() {
    let exprs = vec![PureExpr::Forall {
        var: "i".into(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![],
    }];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("i").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_deref_marks_borrow_context() {
    let exprs = vec![PureExpr::Deref(Arc::new(PureExpr::Var("r".into(), None)))];
    let usage = collect_variable_usage(&exprs);
    assert!(usage.get("r").unwrap().has_borrow_context);
}

#[test]
#[timeout(30000)]
fn test_annotation_beats_bool_context() {
    // Variable has Int annotation but appears in bool context.
    // Annotation takes priority (Int is the default, so bool wins).
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
        BinOp::And,
        Arc::new(PureExpr::Bool(true)),
    )];
    let usage = collect_variable_usage(&exprs);
    // Int annotation + bool context -> bool context wins (Int is default).
    let sort = determine_sort(usage.get("x").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::Bool);
}

#[test]
#[timeout(30000)]
fn test_seq_annotation_beats_bool_context() {
    // Variable has Seq annotation and appears in bool context.
    // Seq annotation wins (stronger evidence).
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("v".into(), Some(ExprSort::Seq))),
        BinOp::And,
        Arc::new(PureExpr::Bool(true)),
    )];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("v").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_merge_combines_evidence() {
    let mut u1 = VarUsage {
        has_view: true,
        ..VarUsage::default()
    };
    let u2 = VarUsage {
        method_calls: vec!["len".into()],
        in_bool_context: true,
        ..VarUsage::default()
    };
    u1.merge(u2);
    assert!(u1.has_view);
    assert!(u1.in_bool_context);
    assert_eq!(u1.method_calls.len(), 1);
}

#[test]
#[timeout(30000)]
fn test_vec_datatype_annotation_resolves_to_seq() {
    // Datatype("std::vec::Vec") -> Seq, not Uninterpreted("std::vec::Vec"). (#2124)
    let id = trust_wp_core::formula::intern_sort_name("std::vec::Vec");
    let exprs = vec![PureExpr::Var("a".into(), Some(ExprSort::Datatype(id)))];
    let sort = determine_sort(collect_variable_usage(&exprs).get("a").unwrap());
    assert_eq!(sort, ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int));
}

#[test]
#[timeout(30000)]
fn test_var_with_type_param_annotation_resolves_to_int() {
    // TypeParam annotation from MIR resolves to Int (universal sort) for
    // monomorphic verification. (#2551: previously Uninterpreted, causing
    // sort mismatches and SortFallbackToInt demotions.)
    let id = trust_wp_core::formula::intern_sort_name("T");
    let exprs = vec![PureExpr::Var("x".into(), Some(ExprSort::TypeParam(id)))];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("x").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Int,
        "TypeParam(T) should resolve to Int"
    );
}

#[test]
#[timeout(30000)]
fn test_quantifier_with_type_param_sort() {
    // Quantifier-bound TypeParam sort resolves to Int (universal sort). (#2551)
    let id = trust_wp_core::formula::intern_sort_name("K");
    let exprs = vec![PureExpr::Forall {
        var: "k".into(),
        var_sort: Some(ExprSort::TypeParam(id)),
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![],
    }];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("k").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Int,
        "Quantifier TypeParam(K) should resolve to Int"
    );
}

#[test]
#[timeout(30000)]
fn test_type_param_in_bool_context_resolves_to_bool() {
    // TypeParam->Int falls through determine_sort's Priority 1 (non-Int
    // annotation check), allowing Bool context from And to win at Priority 3.
    // This is correct: in `x && true`, the variable is genuinely Bool. (#2551)
    let id = trust_wp_core::formula::intern_sort_name("T");
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), Some(ExprSort::TypeParam(id)))),
        BinOp::And,
        Arc::new(PureExpr::Bool(true)),
    )];
    let usage = collect_variable_usage(&exprs);
    let sort = determine_sort(usage.get("x").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Bool,
        "TypeParam in And context should resolve to Bool, got {sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_multiple_exprs_union() {
    let exprs = vec![
        PureExpr::View(Arc::new(PureExpr::Var("s".into(), None))),
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".into(), None)),
            method: "push_back".into(),
            args: vec![PureExpr::Int(1)],
        },
    ];
    let usage = collect_variable_usage(&exprs);
    let u = usage.get("s").unwrap();
    assert!(u.has_view);
    assert!(u.method_calls.contains(&"push_back".to_string()));
}

#[test]
#[timeout(30000)]
fn test_match_arm_bindings_do_not_leak_into_global_usage() {
    let exprs = vec![PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("pair".into(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "OwnResult::Ok".into(),
                        inner: Some(Box::new(Pattern::Binding("s".into()))),
                    },
                    Pattern::Constructor {
                        name: "OwnResult::Ok".into(),
                        inner: Some(Box::new(Pattern::Binding("r".into()))),
                    },
                ]),
                body: PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("T::clone".into(), None)),
                    method: "postcondition".into(),
                    args: vec![
                        PureExpr::Var("s".into(), None),
                        PureExpr::Var("r".into(), None),
                    ],
                },
            },
            MatchArm {
                pattern: Pattern::Tuple(vec![
                    Pattern::Constructor {
                        name: "OwnResult::Err".into(),
                        inner: Some(Box::new(Pattern::Binding("s".into()))),
                    },
                    Pattern::Constructor {
                        name: "OwnResult::Err".into(),
                        inner: Some(Box::new(Pattern::Binding("r".into()))),
                    },
                ]),
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("s".into(), None)),
                    BinOp::Eq,
                    Arc::new(PureExpr::Var("r".into(), None)),
                ),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Bool(false),
            },
        ],
    }];

    let usage = collect_variable_usage_as_formula(&exprs);

    assert!(
        !usage.contains_key("s"),
        "match-arm local binder `s` should not leak into global usage: {usage:?}"
    );
    assert!(
        !usage.contains_key("r"),
        "match-arm local binder `r` should not leak into global usage: {usage:?}"
    );
    assert!(
        usage.contains_key("pair"),
        "scrutinee should still contribute global usage"
    );
}

// ── Constructor equality evidence tests (#2700) ──────────────────────

#[test]
#[timeout(30000)]
fn test_constructor_equality_option_some_resolves_option_sort() {
    // `call_3 == Some(1)` should give `call_3` an Option sort.
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("call_3".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "Some".into(),
            args: vec![PureExpr::Int(1)],
        }),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("call_3").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("OptionInt".to_string()),
        "call_3 == Some(1) should resolve to OptionInt sort"
    );
}

#[test]
#[timeout(30000)]
fn test_constructor_equality_option_none_resolves_option_sort() {
    // `none == None()` should give `none` an Option sort.
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("none".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "None".into(),
            args: vec![],
        }),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("none").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("OptionInt".to_string()),
        "none == None() should resolve to OptionInt sort"
    );
}

#[test]
#[timeout(30000)]
fn test_constructor_equality_result_err_resolves_result_sort() {
    // `call_3 == Err(true)` should give `call_3` a Result sort.
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("call_3".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "Err".into(),
            args: vec![PureExpr::Bool(true)],
        }),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("call_3").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("ResultIntInt".to_string()),
        "call_3 == Err(true) should resolve to ResultIntInt sort"
    );
}

#[test]
#[timeout(30000)]
fn test_constructor_equality_result_ok_resolves_result_sort() {
    // `call_7 == Ok(1)` should give `call_7` a Result sort.
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("call_7".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "Ok".into(),
            args: vec![PureExpr::Int(1)],
        }),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("call_7").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("ResultIntInt".to_string()),
        "call_7 == Ok(1) should resolve to ResultIntInt sort"
    );
}

#[test]
#[timeout(30000)]
fn test_constructor_equality_reversed_order() {
    // `Err(true) == call_3` — constructor on left, variable on right.
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::LogicFnCall {
            name: "Err".into(),
            args: vec![PureExpr::Bool(true)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Var("call_3".into(), None)),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("call_3").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("ResultIntInt".to_string()),
        "Err(true) == call_3 should still resolve to ResultIntInt"
    );
}

#[test]
#[timeout(30000)]
fn test_constructor_equality_through_view_wrapper() {
    // `Deref(call_3) == Err(true)` — variable wrapped in Deref.
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "call_3".into(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "Err".into(),
            args: vec![PureExpr::Bool(true)],
        }),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("call_3").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::Uninterpreted("ResultIntInt".to_string()),
        "Deref(call_3) == Err(true) should still resolve to ResultIntInt"
    );
}

#[test]
#[timeout(30000)]
fn test_annotation_beats_constructor_evidence() {
    // Explicit Seq annotation from MIR should win over constructor evidence.
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Seq))),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "Some".into(),
            args: vec![PureExpr::Int(1)],
        }),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    let sort = determine_sort(usage.get("x").unwrap());
    assert_eq!(
        sort,
        ay_dpll::api::Sort::seq(ay_dpll::api::Sort::Int),
        "Seq annotation should beat constructor equality evidence"
    );
}

// ── Int-literal-equality anti-Bool evidence (arc_and_rc sort-plan flake) ──

#[test]
#[timeout(30000)]
fn int_literal_eq_evidence_collected_through_view() {
    // `rc3@ == 2` marks BOTH the base var and the view-derived name.
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var("rc3".into(), None)))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(2)),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    assert!(
        usage.get("rc3").unwrap().int_literal_eq,
        "base var must carry int-literal-eq evidence"
    );
    assert!(
        usage.get("rc3_view").unwrap().int_literal_eq,
        "view-derived name must carry int-literal-eq evidence"
    );
}

#[test]
#[timeout(30000)]
fn int_literal_eq_evidence_collected_for_ne_and_reversed_operands() {
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Int(7)),
        BinOp::Ne,
        Arc::new(PureExpr::Var("x".into(), None)),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    assert!(
        usage.get("x").unwrap().int_literal_eq,
        "Ne with reversed operands must also collect the evidence"
    );
}

#[test]
#[timeout(30000)]
fn in_range_int_literals_are_not_anti_bool_evidence() {
    for literal in [0, 1] {
        let exprs = vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(literal)),
        )];
        let usage = collect_variable_usage_as_formula(&exprs);
        assert!(
            !usage.get("x").unwrap().int_literal_eq,
            "x == {literal} is Bool-encodable via ay's 0/1 bridge — no veto"
        );
    }
}

#[test]
#[timeout(30000)]
fn negated_int_literal_is_anti_bool_evidence() {
    let exprs = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::UnOp(
            trust_wp_core::formula::UnOp::Neg,
            Arc::new(PureExpr::Int(3)),
        )),
    )];
    let usage = collect_variable_usage_as_formula(&exprs);
    assert!(
        usage.get("x").unwrap().int_literal_eq,
        "x == -3 is out of the Bool 0/1 range — must veto"
    );
}

#[test]
#[timeout(30000)]
fn determine_sort_int_literal_eq_vetoes_bool_context() {
    let bool_only = VarUsage {
        in_bool_context: true,
        ..VarUsage::default()
    };
    assert_eq!(
        determine_sort(&bool_only),
        ay_dpll::api::Sort::Bool,
        "bool context alone still infers Bool (pre-fix behavior pinned)"
    );

    let vetoed = VarUsage {
        in_bool_context: true,
        int_literal_eq: true,
        ..VarUsage::default()
    };
    assert_eq!(
        determine_sort(&vetoed),
        ay_dpll::api::Sort::Int,
        "int-literal-eq evidence must veto the bool-context Bool inference"
    );
}
