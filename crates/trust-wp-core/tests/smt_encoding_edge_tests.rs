// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::{
    formula::{BinOp, Formula, PureExpr},
    smt::{expr_to_smt, formula_to_smt, SmtGenerator},
};

#[test]
fn expr_to_smt_old_view_of_deref_uses_old_current_view_name() {
    let expr = PureExpr::Old(Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(
        Arc::new(PureExpr::Var("v".to_string(), None)),
    )))));

    assert_eq!(expr_to_smt(&expr), "old_v_current_view");
}

#[test]
fn expr_to_smt_old_method_call_prefixes_receiver_and_arguments() {
    let expr = PureExpr::Old(Arc::new(PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("xs".to_string(), None)),
        method: "custom".to_string(),
        args: vec![PureExpr::Var("i".to_string(), None)],
    }));

    assert_eq!(expr_to_smt(&expr), "(custom old_xs old_i)");
}

#[test]
fn formula_to_smt_forall_with_trigger_patterns() {
    let formula = Formula::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(Formula::Pure(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ))),
        triggers: vec![vec![
            Formula::Pure(PureExpr::LogicFnCall {
                name: "f".to_string(),
                args: vec![PureExpr::Var("i".to_string(), None)],
            }),
            Formula::Pure(PureExpr::LogicFnCall {
                name: "g".to_string(),
                args: vec![PureExpr::Var("i".to_string(), None)],
            }),
        ]],
    };

    assert_eq!(
        formula_to_smt(&formula),
        "(forall ((i Int)) (! (> i 0) :pattern ((logic_f i) (logic_g i))))"
    );
}

#[test]
fn generator_declares_old_current_view_for_old_view_of_deref() {
    let expr = PureExpr::Old(Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(
        Arc::new(PureExpr::Var("v".to_string(), None)),
    )))));

    let mut generator = SmtGenerator::new();
    generator.declare_vars_in_expr(&expr);

    assert!(generator
        .output()
        .contains("(declare-const old_v_current_view Seq)"));
}

#[test]
fn generator_formula_declares_free_trigger_vars_but_not_bound_names() {
    let formula = Formula::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(Formula::True),
        triggers: vec![vec![Formula::Pure(PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![
                PureExpr::Var("i".to_string(), None),
                PureExpr::Var("y".to_string(), None),
            ],
        })]],
    };

    let mut generator = SmtGenerator::new();
    generator.declare_vars_in_formula(&formula);
    let output = generator.output();

    assert!(output.contains("(declare-const y Int)"));
    assert!(!output.contains("(declare-const i Int)"));
}
