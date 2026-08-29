// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{ssa_rename_call_assumptions, transform_contract};
use crate::callbacks::parsing::{LoopFields, MutBorrowFields, ParsedContract};

fn make_parsed_contract() -> ParsedContract {
    ParsedContract {
        requires: Vec::new(),
        ensures: Vec::new(),
        result_expr: None,
        result_expr_spanned: None,
        arg_names: Vec::new(),
        call_assumptions: Vec::new(),
        pre_loop_call_assumptions: Vec::new(),
        call_obligations: Vec::new(),
        pre_loop_call_obligations: Vec::new(),
        post_loop_call_obligations: Vec::new(),
        loop_fields: LoopFields {
            invariants: Vec::new(),
            per_loop_invariants: Vec::new(),
            per_loop_variants: Vec::new(),
            all_loop_spans: Vec::new(),
            variants: Vec::new(),
            loop_analysis: None,
            loop_obligation_groups: Vec::new(),
        },
        mut_borrow: MutBorrowFields {
            mut_borrow_body: None,
            mut_ref_param_names: HashSet::new(),
            projected_final_pins: Vec::new(),
        },
        reborrow_prophecy: None,
    }
}

#[test]
fn transform_contract_keeps_base_requires_separate_from_appended_clauses() {
    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Bool(true)];
    parsed.call_assumptions = vec![PureExpr::Bool(false)];
    parsed.mut_borrow.mut_ref_param_names = HashSet::from(["x".to_string()]);

    let tc = transform_contract(&parsed);

    assert_eq!(tc.base_requires, vec![PureExpr::Bool(true)]);
    assert_eq!(tc.base_requires_count, tc.base_requires.len());
    assert!(
        tc.effective_requires.starts_with(&tc.base_requires),
        "effective requires should preserve the user-clause prefix"
    );
    assert!(
        tc.effective_requires.contains(&PureExpr::Bool(false)),
        "call assumptions should still merge into effective requires"
    );
    assert_eq!(
        parsed.requires,
        vec![PureExpr::Bool(true)],
        "parsed.requires must be unchanged after pure transform (#2265)"
    );
}

#[test]
fn transform_contract_keeps_base_ensures_and_call_obligations_separate() {
    let mut parsed = make_parsed_contract();
    parsed.ensures = vec![PureExpr::Bool(true)];
    parsed.call_obligations = vec![PureExpr::Int(1), PureExpr::Int(2)];

    let tc = transform_contract(&parsed);

    assert_eq!(tc.base_ensures, vec![PureExpr::Bool(true)]);
    assert_eq!(tc.base_ensures_count, tc.base_ensures.len());
    assert_eq!(
        tc.call_obligation_ensures,
        vec![PureExpr::Int(1), PureExpr::Int(2)]
    );
    assert_eq!(
        tc.effective_ensures,
        vec![PureExpr::Bool(true), PureExpr::Int(1), PureExpr::Int(2)]
    );
    assert_eq!(
        parsed.call_obligations,
        vec![PureExpr::Int(1), PureExpr::Int(2)],
        "parsed call obligations should remain available for downstream diagnostics"
    );
    assert_eq!(
        parsed.ensures,
        vec![PureExpr::Bool(true)],
        "parsed.ensures must be unchanged after pure transform (#2265)"
    );
}

/// Regression guard for #2265: `transform_contract` is now pure — `parsed.requires`
/// and `parsed.ensures` must remain unchanged after the transform. This was the
/// root cause of #2264 (recursive variant verification read drained raw clauses).
#[test]
fn transform_contract_preserves_parsed_requires_and_ensures_2265() {
    let mut parsed = make_parsed_contract();
    parsed.requires = vec![PureExpr::Var("x".to_string(), None), PureExpr::Bool(true)];
    parsed.ensures = vec![PureExpr::Var("result".to_string(), None)];

    let tc = transform_contract(&parsed);

    // After pure transform, parsed.requires and parsed.ensures are unchanged
    assert_eq!(
        parsed.requires,
        vec![PureExpr::Var("x".to_string(), None), PureExpr::Bool(true)],
        "parsed.requires must be unchanged after pure transform (#2265)"
    );
    assert_eq!(
        parsed.ensures,
        vec![PureExpr::Var("result".to_string(), None)],
        "parsed.ensures must be unchanged after pure transform (#2265)"
    );

    // The original user clauses are also preserved in tc.base_requires / tc.base_ensures
    assert_eq!(
        tc.base_requires,
        vec![PureExpr::Var("x".to_string(), None), PureExpr::Bool(true)],
        "tc.base_requires preserves original user preconditions"
    );
    assert_eq!(
        tc.base_ensures,
        vec![PureExpr::Var("result".to_string(), None)],
        "tc.base_ensures preserves original user postconditions"
    );
}

#[test]
fn ssa_rename_call_assumptions_rewrites_quantifier_triggers() {
    let mut assumptions = vec![PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                PureExpr::Final(Arc::new(PureExpr::Var(
                    "v".to_string(),
                    Some(ExprSort::Seq),
                ))),
            ))))),
            BinOp::Eq,
            Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
        )),
        triggers: vec![vec![PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
            PureExpr::Var("v".to_string(), Some(ExprSort::Seq)),
        ))))]],
    }];

    assert!(ssa_rename_call_assumptions(&mut assumptions));
    assert_eq!(
        assumptions,
        vec![PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                    PureExpr::Var("v".to_string(), Some(ExprSort::Seq)),
                ))))),
                BinOp::Eq,
                Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            )),
            triggers: vec![vec![PureExpr::View(Arc::new(PureExpr::Var(
                "v_ssa_1".to_string(),
                Some(ExprSort::Seq),
            )))]],
        }]
    );
}
