// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::{
    contract_parser::parse_contract_body,
    formula::{intern_sort_name, BinOp, ExprSort, PureExpr, UnOp},
};

use super::{
    proof_assert_snapshot_facts::collect_scalar_wrapper_aliases,
    proof_assert_verify::{
        collect_deref_snapshot_aliases, derive_snapshot_deref_alias_substitutions,
        filter_len_only_irrelevant_facts, inline_bool_mapping_closure_calls,
        instantiate_mapping_closure_ground, instantiate_mapping_closure_ground_from_expr,
        preserve_transparent_adapter_views, retain_relevant_mapping_closure_foralls,
        rewrite_iterator_spec_proof_assert_clauses, substitute_assertion_final_carriers,
        substitute_assertion_names, substitute_precise_final_update_carriers,
        substitute_snapshot_facts,
    },
};
use crate::mir_analysis::effects::MappingClosureInfo;

fn iter_mut_var(name: &str) -> PureExpr {
    PureExpr::Var(
        name.to_string(),
        Some(ExprSort::Datatype(intern_sort_name(
            "std::collections::hash_map::IterMut",
        ))),
    )
}

fn seq_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
}

fn contains_iterator_spec_method(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            matches!(method.as_str(), "produces" | "completed")
                || contains_iterator_spec_method(receiver)
                || args.iter().any(contains_iterator_spec_method)
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            contains_iterator_spec_method(lhs) || contains_iterator_spec_method(rhs)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_iterator_spec_method(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_iterator_spec_method(cond)
                || contains_iterator_spec_method(then_expr)
                || contains_iterator_spec_method(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            contains_iterator_spec_method(body)
                || triggers.iter().flatten().any(contains_iterator_spec_method)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(contains_iterator_spec_method),
        PureExpr::Match { scrutinee, arms } => {
            contains_iterator_spec_method(scrutinee)
                || arms
                    .iter()
                    .any(|arm| contains_iterator_spec_method(&arm.body))
        }
        PureExpr::Let { value, body, .. }
        | PureExpr::LetAssume {
            assumption: value,
            body,
        }
        | PureExpr::LetObligation {
            obligation: value,
            body,
        } => contains_iterator_spec_method(value) || contains_iterator_spec_method(body),
        PureExpr::Closure { body, .. } => contains_iterator_spec_method(body),
        _ => false,
    }
}

#[test]
fn proof_assert_prepare_rewrites_iterator_specs_in_preconditions_and_ensures() {
    let mut preconditions = vec![PureExpr::MethodCall {
        receiver: Arc::new(iter_mut_var("it0")),
        method: "completed".to_string(),
        args: vec![],
    }];
    let mut ensures = vec![PureExpr::MethodCall {
        receiver: Arc::new(iter_mut_var("it0")),
        method: "produces".to_string(),
        args: vec![
            seq_var("visited"),
            PureExpr::Deref(Arc::new(iter_mut_var("it1"))),
        ],
    }];

    rewrite_iterator_spec_proof_assert_clauses(&mut preconditions, &mut ensures);

    assert!(
        preconditions
            .iter()
            .chain(ensures.iter())
            .all(|expr| !contains_iterator_spec_method(expr)),
        "proof_assert preparation should eliminate produces/completed calls before SMT"
    );
}

#[test]
fn proof_assert_prepare_rewrites_parsed_hash_map_quantifier_iterator_specs() {
    let mut preconditions = Vec::new();
    let mut ensures = vec![parse_contract_body(
        "exists<prod: Seq<(K, V)>, it1: &mut hash_map::IntoIter<K, V>> \
             it1.completed() && it0.produces(prod, *it1)",
    )
    .unwrap()];

    rewrite_iterator_spec_proof_assert_clauses(&mut preconditions, &mut ensures);

    assert!(
        ensures.iter().all(|expr| !contains_iterator_spec_method(expr)),
        "parsed HashMap iterator proof_assert should eliminate produces/completed calls, got {ensures:?}"
    );
}

/// When the closure body contains a parameter variable with a non-Int sort
/// (e.g., `Datatype(42)` from `creusot_std::Int`), `to_forall_axiom` must
/// normalize it to `ExprSort::Int` so the forall body matches the
/// `mapping_get` key sort. (#2245)
#[test]
fn mapping_closure_to_forall_axiom_normalizes_datatype_sort_to_int() {
    let datatype_sort = ExprSort::Datatype(42);
    let info = MappingClosureInfo {
        result_var: PureExpr::Var("_call_7".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), Some(datatype_sort))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        param_names: vec!["x".into()],
    };
    let axiom = info.to_forall_axiom().expect("should produce axiom");
    match &axiom {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        } => {
            assert_eq!(var, "x");
            assert_eq!(*var_sort, Some(ExprSort::Int));
            // The body RHS should have the param normalized to Int, not Datatype(42)
            match body.as_ref() {
                PureExpr::BinOp(_, BinOp::Eq, rhs) => match rhs.as_ref() {
                    PureExpr::BinOp(lhs_inner, BinOp::Add, _) => match lhs_inner.as_ref() {
                        PureExpr::Var(name, sort) => {
                            assert_eq!(name, "x");
                            assert_eq!(
                                *sort,
                                Some(ExprSort::Int),
                                "normalize_var_sort_to_int should rewrite Datatype(42) to Int"
                            );
                        }
                        other => panic!("expected Var, got {other:?}"),
                    },
                    other => panic!("expected BinOp Add, got {other:?}"),
                },
                other => panic!("expected BinOp Eq, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// Verify that `to_forall_axiom` with an already-Int sort parameter still works.
/// Regression guard: `normalize_var_sort_to_int` must be idempotent on Int sorts.
#[test]
fn mapping_closure_to_forall_axiom_int_sort_unchanged() {
    let info = MappingClosureInfo {
        result_var: PureExpr::Var("_call_9".into(), None),
        body_expr: PureExpr::Var("k".into(), Some(ExprSort::Int)),
        param_names: vec!["k".into()],
    };
    let axiom = info.to_forall_axiom().expect("should produce axiom");
    match &axiom {
        PureExpr::Forall { body, .. } => match body.as_ref() {
            PureExpr::BinOp(_, BinOp::Eq, rhs) => match rhs.as_ref() {
                PureExpr::Var(name, sort) => {
                    assert_eq!(name, "k");
                    assert_eq!(*sort, Some(ExprSort::Int));
                }
                other => panic!("expected Var, got {other:?}"),
            },
            other => panic!("expected BinOp Eq, got {other:?}"),
        },
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// When no closure body params exist, `to_forall_axiom` returns None.
#[test]
fn mapping_closure_to_forall_axiom_empty_params_returns_none() {
    let info = MappingClosureInfo {
        result_var: PureExpr::Var("_call_5".into(), None),
        body_expr: PureExpr::Int(42),
        param_names: vec![],
    };
    assert!(info.to_forall_axiom().is_none());
}

#[test]
fn retain_relevant_mapping_closure_foralls_drops_sequence_length_only_axioms() {
    let mapping = MappingClosureInfo {
        result_var: PureExpr::Var("pred0".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("k".into(), Some(ExprSort::Int))),
                BinOp::Mod,
                Arc::new(PureExpr::Int(2)),
            )),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
        param_names: vec!["k".into()],
    };
    let axiom = mapping.to_forall_axiom().expect("mapping closure axiom");
    let sequence = PureExpr::LogicFnCall {
        name: "seq".to_string(),
        args: vec![PureExpr::Var("pred0".into(), None)],
    };
    let assertion = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(sequence.clone()),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );
    let retained_fact = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(sequence),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );
    let mut facts = vec![axiom.clone(), retained_fact.clone()];

    let filtered =
        retain_relevant_mapping_closure_foralls(&mut facts, &[mapping], &assertion, &[], &[]);

    assert_eq!(filtered, 1);
    assert_eq!(facts, vec![retained_fact]);
    assert!(!facts.contains(&axiom));
}

#[test]
fn retain_relevant_mapping_closure_foralls_keeps_lookup_axioms() {
    let mapping = MappingClosureInfo {
        result_var: PureExpr::Var("pred0".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::Var("k".into(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
        param_names: vec!["k".into()],
    };
    let axiom = mapping.to_forall_axiom().expect("mapping closure axiom");
    let assertion = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("pred0".into(), None)),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    let mut facts = vec![axiom.clone()];

    let filtered =
        retain_relevant_mapping_closure_foralls(&mut facts, &[mapping], &assertion, &[], &[]);

    assert_eq!(filtered, 0);
    assert_eq!(facts, vec![axiom]);
}

#[test]
fn filter_len_only_irrelevant_facts_keeps_length_cone() {
    let call_11_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_11".into(), None)),
        method: "len".to_string(),
        args: vec![],
    };
    let call_9_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_9".into(), None)),
        method: "len".to_string(),
        args: vec![],
    };
    let assertion = PureExpr::BinOp(
        Arc::new(call_11_len.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(2)),
    );
    let keep_call_9_len = PureExpr::BinOp(
        Arc::new(call_9_len.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );
    let keep_call_11_len = PureExpr::BinOp(
        Arc::new(call_11_len.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(call_9_len),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    let drop_seq_element = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("call_11".into(), None)),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(1)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Var("call_7".into(), None)),
    );
    let drop_alias = PureExpr::BinOp(
        Arc::new(PureExpr::Var("preds".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("call_11".into(), None)),
    );
    let mut facts = vec![
        drop_alias,
        keep_call_9_len.clone(),
        drop_seq_element,
        keep_call_11_len.clone(),
    ];

    let filtered = filter_len_only_irrelevant_facts(&assertion, &mut facts);

    assert_eq!(filtered, 2);
    assert_eq!(facts, vec![keep_call_9_len, keep_call_11_len]);
}

#[test]
fn filter_len_only_irrelevant_facts_keeps_scalar_side_facts() {
    let assertion = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("items".into(), None)),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Var("n".into(), Some(ExprSort::Int))),
    );
    let scalar_fact = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".into(), Some(ExprSort::Int))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(2)),
    );
    let element_fact = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("items".into(), None)),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    );
    let mut facts = vec![scalar_fact.clone(), element_fact];

    let filtered = filter_len_only_irrelevant_facts(&assertion, &mut facts);

    assert_eq!(filtered, 1);
    assert_eq!(facts, vec![scalar_fact]);
}

#[test]
fn instantiate_mapping_closure_ground_returns_empty_without_mappings() {
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_3".into(), None)),
        method: "get".to_string(),
        args: vec![PureExpr::Int(41)],
    }];

    let instances = instantiate_mapping_closure_ground(&assumptions, &[]);

    assert!(instances.is_empty());
}

#[test]
fn instantiate_mapping_closure_ground_substitutes_get_argument_into_body() {
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_3".into(), None)),
        method: "get".to_string(),
        args: vec![PureExpr::Int(41)],
    }];
    let mappings = vec![MappingClosureInfo {
        result_var: PureExpr::Var("call_3".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(41)),
        ),
        param_names: vec!["x".into()],
    }];

    let instances = instantiate_mapping_closure_ground(&assumptions, &mappings);

    assert_eq!(
        instances,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Int(41)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(41)),
        )]
    );
}

#[test]
fn instantiate_mapping_closure_ground_supports_index_logic_assumptions() {
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_7".into(), None)),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(5)],
    }];
    let mappings = vec![MappingClosureInfo {
        result_var: PureExpr::Var("call_7".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::Var("k".into(), Some(ExprSort::Int))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        param_names: vec!["k".into()],
    }];

    let instances = instantiate_mapping_closure_ground(&assumptions, &mappings);

    assert_eq!(
        instances,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Int(5)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )]
    );
}

#[test]
fn instantiate_mapping_closure_ground_normalizes_wrapper_arg_sort_to_int() {
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_9".into(), None)),
        method: "get".to_string(),
        args: vec![PureExpr::Var(
            "call_27".into(),
            Some(ExprSort::Datatype(intern_sort_name(
                "trust_wp_std::ghost::Snapshot",
            ))),
        )],
    }];
    let mappings = vec![MappingClosureInfo {
        result_var: PureExpr::Var("call_9".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        param_names: vec!["x".into()],
    }];

    let instances = instantiate_mapping_closure_ground(&assumptions, &mappings);

    assert_eq!(
        instances,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("call_27".into(), Some(ExprSort::Int))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )]
    );
}

#[test]
fn instantiate_mapping_closure_ground_chains_generated_instances_once() {
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_9".into(), None)),
        method: "get".to_string(),
        args: vec![PureExpr::Int(2)],
    }];
    let mappings = vec![
        MappingClosureInfo {
            result_var: PureExpr::Var("call_9".into(), None),
            body_expr: PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("call_8".into(), None)),
                method: "get".to_string(),
                args: vec![PureExpr::Var("x".into(), Some(ExprSort::Int))],
            },
            param_names: vec!["x".into()],
        },
        MappingClosureInfo {
            result_var: PureExpr::Var("call_8".into(), None),
            body_expr: PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".into(), Some(ExprSort::Int))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
            param_names: vec!["y".into()],
        },
    ];

    let instances = instantiate_mapping_closure_ground(&assumptions, &mappings);

    assert_eq!(
        instances,
        vec![
            PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("call_8".into(), None)),
                method: "get".to_string(),
                args: vec![PureExpr::Int(2)],
            },
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("call_8".into(), None)),
                    method: "get".to_string(),
                    args: vec![PureExpr::Int(2)],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(2)),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                )),
            ),
        ]
    );
}

#[test]
fn instantiate_mapping_closure_ground_ignores_unmatched_receivers() {
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_3".into(), None)),
        method: "get".to_string(),
        args: vec![PureExpr::Int(9)],
    }];
    let mappings = vec![MappingClosureInfo {
        result_var: PureExpr::Var("call_4".into(), None),
        body_expr: PureExpr::Var("x".into(), Some(ExprSort::Int)),
        param_names: vec!["x".into()],
    }];

    let instances = instantiate_mapping_closure_ground(&assumptions, &mappings);

    assert!(instances.is_empty());
}

#[test]
fn instantiate_mapping_closure_ground_skips_mappings_without_parameters() {
    let assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_3".into(), None)),
        method: "get".to_string(),
        args: vec![PureExpr::Int(9)],
    }];
    let mappings = vec![MappingClosureInfo {
        result_var: PureExpr::Var("call_3".into(), None),
        body_expr: PureExpr::Bool(true),
        param_names: vec![],
    }];

    let instances = instantiate_mapping_closure_ground(&assumptions, &mappings);

    assert!(instances.is_empty());
}

#[test]
fn instantiate_mapping_closure_ground_from_expr_finds_direct_method_calls() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_8".into(), None)),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(2)],
    };
    let mappings = vec![MappingClosureInfo {
        result_var: PureExpr::Var("call_8".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
        param_names: vec!["x".into()],
    }];

    let instances = instantiate_mapping_closure_ground_from_expr(&expr, &mappings);

    assert_eq!(
        instances,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("call_8".into(), None)),
                method: "get".to_string(),
                args: vec![PureExpr::Int(2)],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(2)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        )]
    );
}

#[test]
fn instantiate_mapping_closure_ground_from_expr_recurses_through_ite() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("call_9".into(), None)),
            method: "get".to_string(),
            args: vec![PureExpr::Int(7)],
        }),
        Arc::new(PureExpr::Bool(false)),
    );
    let mappings = vec![MappingClosureInfo {
        result_var: PureExpr::Var("call_9".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::Var("k".into(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(7)),
        ),
        param_names: vec!["k".into()],
    }];

    let instances = instantiate_mapping_closure_ground_from_expr(&expr, &mappings);

    assert_eq!(
        instances,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Int(7)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(7)),
        )]
    );
}

#[test]
fn instantiate_mapping_closure_ground_from_expr_grounds_bool_predicates_under_not() {
    let expr = PureExpr::UnOp(
        UnOp::Not,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("call_pred".into(), None)),
            method: "index_logic".to_string(),
            args: vec![PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".into(), Some(ExprSort::Int))),
                BinOp::Sub,
                Arc::new(PureExpr::Int(1)),
            )],
        }),
    );
    let mappings = vec![MappingClosureInfo {
        result_var: PureExpr::Var("call_pred".into(), None),
        body_expr: PureExpr::BinOp(
            Arc::new(PureExpr::Var("k".into(), Some(ExprSort::Int))),
            BinOp::Lt,
            Arc::new(PureExpr::Int(0)),
        ),
        param_names: vec!["k".into()],
    }];

    let instances = instantiate_mapping_closure_ground_from_expr(&expr, &mappings);

    assert_eq!(
        instances,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".into(), Some(ExprSort::Int))),
                BinOp::Sub,
                Arc::new(PureExpr::Int(1)),
            )),
            BinOp::Lt,
            Arc::new(PureExpr::Int(0)),
        )]
    );
}

#[test]
fn instantiate_mapping_closure_ground_from_expr_chains_generated_instances_once() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_9".into(), None)),
        method: "get".to_string(),
        args: vec![PureExpr::Int(2)],
    };
    let mappings = vec![
        MappingClosureInfo {
            result_var: PureExpr::Var("call_9".into(), None),
            body_expr: PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("call_8".into(), None)),
                method: "get".to_string(),
                args: vec![PureExpr::Var("x".into(), Some(ExprSort::Int))],
            },
            param_names: vec!["x".into()],
        },
        MappingClosureInfo {
            result_var: PureExpr::Var("call_8".into(), None),
            body_expr: PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".into(), Some(ExprSort::Int))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
            param_names: vec!["y".into()],
        },
    ];

    let instances = instantiate_mapping_closure_ground_from_expr(&expr, &mappings);

    assert_eq!(
        instances,
        vec![
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("call_9".into(), None)),
                    method: "get".to_string(),
                    args: vec![PureExpr::Int(2)],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("call_8".into(), None)),
                    method: "get".to_string(),
                    args: vec![PureExpr::Int(2)],
                }),
            ),
            PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("call_8".into(), None)),
                    method: "get".to_string(),
                    args: vec![PureExpr::Int(2)],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Int(2)),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                )),
            ),
        ]
    );
}

#[test]
fn substitute_snapshot_facts_applies_local_aliases_before_grounding() {
    let facts = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("_call_31".into(), None)),
        method: "get".to_string(),
        args: vec![PureExpr::Var("call_30".into(), Some(ExprSort::Int))],
    }];
    let mut substitutions = HashMap::new();
    substitutions.insert("call_30".to_string(), PureExpr::Var("call_27".into(), None));
    substitutions.insert("call_31".to_string(), PureExpr::Var("call_20".into(), None));
    substitutions.insert(
        "_call_31".to_string(),
        PureExpr::Var("call_20".into(), None),
    );

    let substituted = substitute_snapshot_facts(&facts, &substitutions);

    assert_eq!(
        substituted,
        vec![PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("call_20".into(), None)),
            method: "get".to_string(),
            args: vec![PureExpr::Var("call_27".into(), None)],
        }]
    );
}

#[test]
fn substitute_snapshot_facts_preserves_bare_final_carrier_binding() {
    let facts = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(seq_var("call_4")))),
        BinOp::Eq,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(seq_var("call_4")),
            method: "push_back".to_string(),
            args: vec![PureExpr::Int(30)],
        }),
    )];
    let substitutions = HashMap::from([(
        "call_4".to_string(),
        PureExpr::LogicFnCall {
            name: "seq_empty".to_string(),
            args: vec![],
        },
    )]);

    let substituted = substitute_snapshot_facts(&facts, &substitutions);

    assert_eq!(
        substituted,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(seq_var("call_4")))),
            BinOp::Eq,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(seq_var("call_4")),
                method: "push_back".to_string(),
                args: vec![PureExpr::Int(30)],
            }),
        )],
        "fact-boundary Final(call_N) carriers must stay symbolic instead of collapsing through seq_empty()"
    );
}

#[test]
fn preserve_transparent_adapter_views_keeps_copied_adapter_bridged_in_prepared_vc() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "Copied".to_string(),
            args: vec![PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "xs".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "ys".to_string(),
                    None,
                )))],
            }],
        }),
    );

    let preserved = preserve_transparent_adapter_views(expr);

    assert_eq!(
        preserved,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::View(Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "xs".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "ys".to_string(),
                    None,
                )))],
            }))),
        ),
        "prepared VC should keep copied adapters bridged to the inner iterator/view term"
    );
}

#[test]
fn substitute_assertion_names_preserves_final_carrier_indirection_2616() {
    let assertion = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(seq_var("v")),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(30)),
    );
    let substitutions = HashMap::from([
        (
            "v".to_string(),
            PureExpr::Final(Arc::new(seq_var("call_4"))),
        ),
        (
            "call_4".to_string(),
            PureExpr::LogicFnCall {
                name: "seq_empty".to_string(),
                args: vec![],
            },
        ),
    ]);
    let filter = HashSet::from(["v".to_string()]);

    let substituted = substitute_assertion_names(&assertion, &substitutions, &filter);

    assert_eq!(
        substituted,
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Final(Arc::new(seq_var("call_4")))),
                method: "index_logic".to_string(),
                args: vec![PureExpr::Int(0)],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(30)),
        ),
        "proof_assert assertion substitution should expand the source name without collapsing the symbolic final carrier through call_4 == seq_empty()"
    );
}

#[test]
fn substitute_assertion_final_carriers_prefers_ghost_post_state_binding_2616() {
    let assertion = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Final(Arc::new(seq_var("call_4")))),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0)],
        }),
        BinOp::Eq,
        Arc::new(PureExpr::Int(30)),
    );
    let facts = vec![
        PureExpr::BinOp(
            Arc::new(seq_var("v")),
            BinOp::Eq,
            Arc::new(PureExpr::Final(Arc::new(seq_var("call_4")))),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(seq_var("call_4")))),
            BinOp::Eq,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(seq_var("call_4")),
                method: "push_back".to_string(),
                args: vec![PureExpr::Int(30)],
            }),
        ),
    ];

    let substituted = substitute_assertion_final_carriers(&assertion, &facts);

    assert_eq!(
        substituted,
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(seq_var("call_4")),
                    method: "push_back".to_string(),
                    args: vec![PureExpr::Int(30)],
                }),
                method: "index_logic".to_string(),
                args: vec![PureExpr::Int(0)],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(30)),
        ),
        "assertion final-carrier rewriting should inline the ghost-helper post-state fact instead of the weaker v == ^call_4 alias"
    );
}

#[test]
fn collect_scalar_wrapper_aliases_prefers_scalar_side_of_snapshot_equality() {
    let facts = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("call_27".into(), Some(ExprSort::Int))),
        BinOp::Eq,
        Arc::new(PureExpr::Var(
            "call_30".into(),
            Some(ExprSort::Datatype(intern_sort_name(
                "trust_wp_std::ghost::Snapshot",
            ))),
        )),
    )];

    let aliases = collect_scalar_wrapper_aliases(&facts);

    assert_eq!(
        aliases.get("call_30"),
        Some(&PureExpr::Var("call_27".into(), Some(ExprSort::Int)))
    );
}

#[test]
fn substitute_precise_final_update_carriers_avoids_quantifier_capture() {
    let assertion = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Final(Arc::new(seq_var("x")))),
                method: "index_logic".to_string(),
                args: vec![PureExpr::Var("i".to_string(), Some(ExprSort::Int))],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        )),
        triggers: vec![],
    };
    let facts = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(seq_var("x")))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )];

    let rewritten = substitute_precise_final_update_carriers(&assertion, &facts);

    assert_eq!(
        rewritten, assertion,
        "final-carrier rewriting must not capture aliases under quantifier binders"
    );
}

#[test]
fn derive_snapshot_deref_alias_substitutions_recovers_source_deref_binding() {
    let mut substitutions = HashMap::from([(
        "x".to_string(),
        PureExpr::Var(
            "call_30".into(),
            Some(ExprSort::Datatype(intern_sort_name(
                "trust_wp_std::ghost::Snapshot",
            ))),
        ),
    )]);
    let wrapper_aliases = HashMap::from([(
        "call_30".to_string(),
        PureExpr::Var("call_27".into(), Some(ExprSort::Int)),
    )]);

    derive_snapshot_deref_alias_substitutions(&mut substitutions, &wrapper_aliases);

    assert_eq!(
        substitutions.get("*x"),
        Some(&PureExpr::Var("call_27".into(), Some(ExprSort::Int)))
    );
    assert_eq!(
        substitutions.get("*call_30"),
        Some(&PureExpr::Var("call_27".into(), Some(ExprSort::Int)))
    );
}

#[test]
fn collect_deref_snapshot_aliases_follows_wrapper_seen_under_deref() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "call_30".into(),
            Some(ExprSort::Datatype(intern_sort_name(
                "trust_wp_std::ghost::Snapshot",
            ))),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );
    let facts = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("call_27".into(), Some(ExprSort::Int))),
        BinOp::Eq,
        Arc::new(PureExpr::Var(
            "call_30".into(),
            Some(ExprSort::Datatype(intern_sort_name(
                "trust_wp_std::ghost::Snapshot",
            ))),
        )),
    )];

    let aliases = collect_deref_snapshot_aliases(&expr, &facts);

    assert_eq!(
        aliases.get("call_30"),
        Some(&PureExpr::Var("call_27".into(), Some(ExprSort::Int)))
    );
}

#[test]
fn inline_bool_mapping_closure_calls_rewrites_predicate_index_logic() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("call_20".into(), None)),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(3)],
    };
    let mappings = vec![
        MappingClosureInfo {
            result_var: PureExpr::Var("call_20".into(), None),
            body_expr: PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("call_14".into(), None)),
                    method: "get".to_string(),
                    args: vec![PureExpr::Var("k".into(), Some(ExprSort::Int))],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::Int(0)),
            ),
            param_names: vec!["k".into()],
        },
        MappingClosureInfo {
            result_var: PureExpr::Var("call_14".into(), None),
            body_expr: PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
            param_names: vec!["x".into()],
        },
    ];

    let rewritten = inline_bool_mapping_closure_calls(&expr, &mappings);

    assert_eq!(
        rewritten,
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("call_14".into(), None)),
                method: "get".to_string(),
                args: vec![PureExpr::Int(3)],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )
    );
}

/// D-241: a re-bound parameter's own name inside a recorded value is renamed
/// to its entry symbol occurrence by occurrence, keeping each occurrence's
/// sort; a binder of the same spelling and another name are left alone.
#[test]
fn entry_value_rename_keeps_each_sort_and_every_binder() {
    use super::proof_assert_snapshot::{param_entry_value_name, rename_to_entry_values};

    let datatype = Some(ExprSort::Datatype(intern_sort_name("P")));
    let var = |name: &str, sort: Option<ExprSort>| PureExpr::Var(name.to_string(), sort);
    let eq =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs));
    let field_of = |base: PureExpr| PureExpr::LogicFnCall {
        name: "__trust_wp_tuple_get_0".to_string(),
        args: vec![base],
    };
    let bound = |name: &str| PureExpr::Forall {
        var: name.to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(eq(
            var(name, Some(ExprSort::Int)),
            var("y", Some(ExprSort::Int)),
        )),
        triggers: Vec::new(),
    };
    let fact = PureExpr::BinOp(
        Arc::new(eq(
            PureExpr::BinOp(
                Arc::new(var("x", Some(ExprSort::Int))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
            field_of(var("x", datatype.clone())),
        )),
        BinOp::And,
        Arc::new(bound("x")),
    );
    let entry = param_entry_value_name("x");
    let renamed = rename_to_entry_values(&fact, &HashSet::from(["x".to_string()]));
    let expected = PureExpr::BinOp(
        Arc::new(eq(
            PureExpr::BinOp(
                Arc::new(var(&entry, Some(ExprSort::Int))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
            field_of(var(&entry, datatype)),
        )),
        BinOp::And,
        Arc::new(bound("x")),
    );
    assert_eq!(renamed, expected);
    let renamed_y = rename_to_entry_values(&fact, &HashSet::from(["y".to_string()]));
    assert!(
        renamed_y.free_vars().contains(&param_entry_value_name("y"))
            && !renamed_y.free_vars().contains("y")
            && renamed_y.free_vars().contains("x"),
        "a free `y` is renamed inside the binder too, and `x` is left alone: {renamed_y}"
    );
}
