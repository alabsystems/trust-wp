// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    super::NameSubstitutions,
    branch_merge::{build_bool_ite_merged_substitutions, build_ite_merged_substitutions},
};

#[test]
fn ite_merge_uses_typed_pre_branch_binding_when_default_branch_is_missing() {
    let discr_expr = PureExpr::Var("tag".to_string(), Some(ExprSort::Int));
    let mut then_subs = HashMap::new();
    then_subs.insert(
        "seq".to_string(),
        PureExpr::Var("seq_then".to_string(), Some(ExprSort::Seq)),
    );
    let guard = PureExpr::BinOp(
        Arc::new(discr_expr.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    );
    let branch_subs = vec![(
        Some(guard),
        NameSubstitutions::new(
            then_subs,
            HashMap::from([("seq".to_string(), Some(ExprSort::Seq))]),
        ),
    )];
    let fallback_exprs = HashMap::from([(
        "seq".to_string(),
        PureExpr::Var("seq".to_string(), Some(ExprSort::Seq)),
    )]);

    let merged = build_ite_merged_substitutions(&branch_subs, &fallback_exprs);

    assert_eq!(
        merged.get("seq"),
        Some(&PureExpr::Ite(
            Arc::new(PureExpr::BinOp(
                Arc::new(discr_expr),
                BinOp::Eq,
                Arc::new(PureExpr::Int(1)),
            )),
            Arc::new(PureExpr::Var("seq_then".to_string(), Some(ExprSort::Seq))),
            Arc::new(PureExpr::Var("seq".to_string(), Some(ExprSort::Seq))),
        )),
        "missing default branch should fall back to the typed pre-branch value"
    );
}

#[test]
fn bool_merge_uses_symbolic_deref_fallback_instead_of_star_var_name() {
    let condition = PureExpr::Var("cond".to_string(), Some(ExprSort::Bool));
    let then_map = NameSubstitutions::new(
        HashMap::from([("*p".to_string(), PureExpr::Int(1))]),
        HashMap::from([(
            "p".to_string(),
            Some(ExprSort::Ref(Box::new(ExprSort::Int))),
        )]),
    );
    let else_map = NameSubstitutions::new(
        HashMap::new(),
        HashMap::from([(
            "p".to_string(),
            Some(ExprSort::Ref(Box::new(ExprSort::Int))),
        )]),
    );
    let fallback_exprs = HashMap::from([(
        "p".to_string(),
        PureExpr::Var(
            "p".to_string(),
            Some(ExprSort::Ref(Box::new(ExprSort::Int))),
        ),
    )]);

    let merged =
        build_bool_ite_merged_substitutions(&condition, &then_map, &else_map, &fallback_exprs);

    assert_eq!(
        merged.get("*p"),
        Some(&PureExpr::Ite(
            Arc::new(PureExpr::Var("cond".to_string(), Some(ExprSort::Bool))),
            Arc::new(PureExpr::Int(1)),
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "p".to_string(),
                Some(ExprSort::Ref(Box::new(ExprSort::Int))),
            )))),
        )),
        "missing deref branch should fall back to a symbolic deref, not Var(\"*p\")"
    );
}
