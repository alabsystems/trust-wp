// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{BinOp, PureExpr};

use super::contract_transform::make_parsed_contract;
use crate::callbacks::verification::clause_enrichment::{
    apply_const_item_substitutions, apply_const_item_substitutions_to_loop_invariants,
    discharge_ensures_already_required,
};

fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

#[test]
fn const_substitution_rewrites_flat_and_per_loop_invariants() {
    let mut parsed = make_parsed_contract();
    parsed.loop_fields.invariants = vec![eq(var("head"), var("NULL"))];
    parsed.loop_fields.per_loop_invariants = vec![(10, 20, vec![eq(var("tail"), var("NULL"))])];

    let substitutions = HashMap::from([("NULL".to_string(), PureExpr::Int(0))]);
    apply_const_item_substitutions_to_loop_invariants(&mut parsed, &substitutions);

    assert_eq!(
        parsed.loop_fields.invariants,
        vec![eq(var("head"), PureExpr::Int(0))],
        "flat loop invariants should use the literal const value"
    );
    assert_eq!(
        parsed.loop_fields.per_loop_invariants[0].2,
        vec![eq(var("tail"), PureExpr::Int(0))],
        "per-loop invariants should use the literal const value"
    );
}

#[test]
fn const_substitution_keeps_existing_requires_and_ensures_path() {
    let mut parsed = make_parsed_contract();
    parsed.loop_fields.invariants = vec![eq(var("head"), var("NULL"))];
    let mut requires = vec![eq(var("arg"), var("NULL"))];
    let mut ensures = vec![eq(var("result"), var("NULL"))];

    let substitutions = HashMap::from([("NULL".to_string(), PureExpr::Int(0))]);
    apply_const_item_substitutions(&mut parsed, &mut requires, &mut ensures, &substitutions);

    assert_eq!(requires, vec![eq(var("arg"), PureExpr::Int(0))]);
    assert_eq!(ensures, vec![eq(var("result"), PureExpr::Int(0))]);
    assert_eq!(
        parsed.loop_fields.invariants,
        vec![eq(var("head"), PureExpr::Int(0))]
    );
}

#[test]
fn discharge_ensures_already_required_does_not_drop_real_obligations() {
    let same_clause = eq(var("state"), PureExpr::Int(1));
    let requires = vec![same_clause.clone()];
    let mut ensures = vec![same_clause];

    discharge_ensures_already_required(&requires, &mut ensures);

    assert_eq!(
        ensures, requires,
        "a pre-state requirement is not a proof of the matching post-state obligation"
    );
}
