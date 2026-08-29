// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use super::*;

#[test]
fn substitution_assumptions_include_simple_and_deref_bindings_only() {
    let mut substitutions = NameSubstitutions::default();
    substitutions.insert("x".to_string(), PureExpr::Int(5));
    substitutions.insert("*p".to_string(), PureExpr::Int(10));
    substitutions.insert("^*p".to_string(), PureExpr::Int(11));
    substitutions.insert("self.0".to_string(), PureExpr::Int(42));
    substitutions.insert("mod::x".to_string(), PureExpr::Int(7));

    let assumptions = substitution_assumptions(&substitutions);

    assert!(
        assumptions.contains(&PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(5)),
        )),
        "simple identifier substitution should become equality assumption"
    );
    assert!(
        assumptions.contains(&PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "p".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(10)),
        )),
        "deref substitution should become equality assumption"
    );
    assert!(
        assumptions.contains(&PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(
                PureExpr::Var("p".to_string(), None),
            ))))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(11)),
        )),
        "final deref substitution should become equality assumption"
    );
    // `self.0` is now accepted as a closure capture env field key so
    // synthesized substitutions for `Box<&mut T>` ByValue captures inside
    // `move ||` closures flow through proof_assert verification. (#5 09)
    assert!(
        assumptions.contains(&PureExpr::BinOp(
            Arc::new(PureExpr::Var("self.0".to_string(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        )),
        "self.N closure-env keys should produce equality assumptions"
    );
    assert_eq!(
        assumptions.len(),
        4,
        "non-dotted-ident keys (e.g. `mod::x`) should still be skipped"
    );
}

#[test]
fn substitution_assumptions_use_authoritative_name_sort_for_ghost_helpers() {
    let ghost_call = PureExpr::LogicFnCall {
        name: "is_empty_ghost".to_string(),
        args: vec![PureExpr::Var("v".to_string(), Some(ExprSort::Seq))],
    };
    let substitutions = NameSubstitutions::new(
        HashMap::from([("is_empty".to_string(), ghost_call.clone())]),
        HashMap::from([("is_empty".to_string(), Some(ExprSort::Bool))]),
    );

    let assumptions = substitution_assumptions(&substitutions);

    assert_eq!(
        assumptions,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("is_empty".to_string(), Some(ExprSort::Bool),)),
            BinOp::Eq,
            Arc::new(ghost_call),
        )],
        "driver-carried name_sorts should annotate the LHS even when RHS helper names are unknown"
    );
}

#[test]
fn substitution_assumptions_bridge_final_deref_bindings_into_view_domain() {
    let duration_sort = ExprSort::Datatype(intern_sort_name("std::time::Duration"));
    let substitutions = NameSubstitutions::new(
        HashMap::from([("^*d".to_string(), PureExpr::Int(11))]),
        HashMap::from([("d".to_string(), Some(duration_sort.clone()))]),
    );

    let assumptions = substitution_assumptions(&substitutions);

    assert_eq!(
        assumptions,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                PureExpr::Deref(Arc::new(PureExpr::Var(
                    "d".to_string(),
                    Some(duration_sort),
                ))),
            ))))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(11)),
        )],
        "final-deref substitutions for non-scalar types must compare in view space"
    );
}

#[test]
fn substitution_assumptions_final_var_caret_prefix() {
    // "^x" → parse_substitution_lhs produces Final(Var("x"))
    // Base sort is None when there's no "x" entry in substitutions
    // and name_sorts is empty.
    let mut substitutions = NameSubstitutions::default();
    substitutions.insert("^x".to_string(), PureExpr::Int(42));

    let assumptions = substitution_assumptions(&substitutions);

    assert_eq!(
        assumptions,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        )],
        "^x should parse as Final(Var(x)) — sort is None without base entry"
    );
}

#[test]
fn substitution_assumptions_double_final_caret_prefix() {
    // "^^x" → parse_substitution_lhs produces Final(Final(Var("x")))
    let mut substitutions = NameSubstitutions::default();
    substitutions.insert("^^x".to_string(), PureExpr::Int(7));

    let assumptions = substitution_assumptions(&substitutions);

    assert_eq!(
        assumptions,
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
                PureExpr::Var("x".to_string(), None),
            ))))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(7)),
        )],
        "^^x should parse as Final(Final(Var(x))) — sort is None without base entry"
    );
}

#[test]
fn substitution_assumptions_skip_non_ident_keys() {
    // Keys like "self.0" and "mod::path" are not simple identifiers
    let mut substitutions = NameSubstitutions::default();
    substitutions.insert("self.field".to_string(), PureExpr::Int(1));
    substitutions.insert("mod::inner".to_string(), PureExpr::Int(2));
    substitutions.insert(String::new(), PureExpr::Int(3));

    let assumptions = substitution_assumptions(&substitutions);

    assert!(
        assumptions.is_empty(),
        "non-ident keys should produce no assumptions"
    );
}
