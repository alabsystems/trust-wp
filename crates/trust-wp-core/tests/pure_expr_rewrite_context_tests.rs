// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{ExprSort, MatchArm, Pattern, PureExpr, PureExprChildRole};

fn role_suffix(role: PureExprChildRole) -> &'static str {
    match role {
        PureExprChildRole::Root => "root",
        PureExprChildRole::MethodReceiver => "method_receiver",
        PureExprChildRole::MethodArg => "method_arg",
        PureExprChildRole::LogicFnArg => "logic_fn_arg",
        PureExprChildRole::QuantifierBody => "quantifier_body",
        PureExprChildRole::QuantifierTrigger => "quantifier_trigger",
        PureExprChildRole::MatchScrutinee => "match_scrutinee",
        PureExprChildRole::MatchArmBody => "match_arm_body",
        PureExprChildRole::LetValue => "let_value",
        PureExprChildRole::LetBody => "let_body",
        PureExprChildRole::LetAssumeAssumption => "let_assume_assumption",
        PureExprChildRole::LetAssumeBody => "let_assume_body",
        PureExprChildRole::LetObligationObligation => "let_obligation_obligation",
        PureExprChildRole::LetObligationBody => "let_obligation_body",
        PureExprChildRole::FinalInner => "final_inner",
        PureExprChildRole::OldInner => "old_inner",
        PureExprChildRole::DerefInner => "deref_inner",
        PureExprChildRole::ViewInner => "view_inner",
        PureExprChildRole::UnaryOperand => "unary_operand",
        PureExprChildRole::BinaryLeft => "binary_left",
        PureExprChildRole::BinaryRight => "binary_right",
        PureExprChildRole::IteCondition => "ite_condition",
        PureExprChildRole::IteThen => "ite_then",
        PureExprChildRole::IteElse => "ite_else",
        PureExprChildRole::ClosureBody => "closure_body",
        _ => panic!("unexpected PureExprChildRole variant in test: {role:?}"),
    }
}

fn annotate_var_roles(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up_with_context(
        PureExprChildRole::Root,
        |_, role, _| role,
        |node, role| match node {
            PureExpr::Var(name, sort) => {
                PureExpr::Var(format!("{name}_{}", role_suffix(*role)), sort)
            }
            other => other,
        },
    )
}

#[test]
fn rewrite_bottom_up_with_context_rewrites_quantifier_triggers_and_body() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Var("body".to_string(), None)),
        triggers: vec![vec![PureExpr::Var("trigger".to_string(), None)]],
    };

    let rewritten = annotate_var_roles(&expr);

    assert_eq!(
        rewritten,
        PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Var("body_quantifier_body".to_string(), None)),
            triggers: vec![vec![PureExpr::Var(
                "trigger_quantifier_trigger".to_string(),
                None
            )]],
        }
    );
}

#[test]
fn rewrite_bottom_up_with_context_tags_method_receiver_and_args() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("recv".to_string(), None)),
        method: "f".to_string(),
        args: vec![PureExpr::Var("arg".to_string(), None)],
    };

    let rewritten = annotate_var_roles(&expr);

    assert_eq!(
        rewritten,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("recv_method_receiver".to_string(), None)),
            method: "f".to_string(),
            args: vec![PureExpr::Var("arg_method_arg".to_string(), None)],
        }
    );
}

#[test]
fn rewrite_bottom_up_with_context_tags_final_inner_children() {
    let expr = PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)));

    let rewritten = annotate_var_roles(&expr);

    assert_eq!(
        rewritten,
        PureExpr::Final(Arc::new(PureExpr::Var("x_final_inner".to_string(), None)))
    );
}

#[test]
fn rewrite_bottom_up_with_context_rewrites_match_bodies_without_touching_patterns() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("scrutinee".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("bound".to_string()),
            body: PureExpr::Var("body".to_string(), None),
        }],
    };

    let rewritten = annotate_var_roles(&expr);

    assert_eq!(
        rewritten,
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("scrutinee_match_scrutinee".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Binding("bound".to_string()),
                body: PureExpr::Var("body_match_arm_body".to_string(), None),
            }],
        }
    );
}
