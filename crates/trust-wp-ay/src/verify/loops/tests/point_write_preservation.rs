// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use super::*;

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn seq_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
}

fn int_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Int))
}

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn bin(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
}

fn index_logic(receiver: PureExpr, index: PureExpr) -> PureExpr {
    method_call(receiver, "index_logic", vec![index])
}

fn set(receiver: PureExpr, index: PureExpr, value: PureExpr) -> PureExpr {
    method_call(receiver, "set", vec![index, value])
}

#[test]
#[timeout(30000)]
fn point_write_preserves_universal_index_invariant() {
    let mem = seq_var("mem");
    let i = int_var("i");
    let universal_nonnegative = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(bin(
            PureExpr::Int(0),
            BinOp::Le,
            index_logic(mem.clone(), i),
        )),
        triggers: vec![],
    };
    let written_value_nonnegative = bin(PureExpr::Int(0), BinOp::Le, var("new_value"));
    let invariants = vec![universal_nonnegative, written_value_nonnegative];

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "mem".to_string(),
        set(mem, var("write_index"), var("new_value")),
    );

    let result = verify_preservation(
        &invariants,
        Some(&PureExpr::Bool(true)),
        &["mem"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("point-write preservation should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "point-write facts should preserve the universal index invariant, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn point_write_rejects_negative_written_value() {
    let mem = seq_var("mem");
    let i = int_var("i");
    let universal_nonnegative = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(bin(
            PureExpr::Int(0),
            BinOp::Le,
            index_logic(mem.clone(), i),
        )),
        triggers: vec![],
    };
    let invariants = vec![universal_nonnegative];

    let mut body_effect = HashMap::new();
    body_effect.insert(
        "mem".to_string(),
        set(mem, var("write_index"), PureExpr::Int(-1)),
    );

    let result = verify_preservation(
        &invariants,
        Some(&PureExpr::Bool(true)),
        &["mem"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("point-write preservation should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "negative point-write value should fail preservation, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_shape_does_not_bypass_preservation() {
    let l = var("l");
    let key = var("key");
    let value = var("value");
    let get_matches_value = bin(method_call(l.clone(), "get", vec![key]), BinOp::Eq, value);
    let no_double_binding = method_call(l.clone(), "no_double_binding", vec![]);
    let invariant = bin(get_matches_value, BinOp::Implies, no_double_binding);
    let invariants = vec![invariant];

    let mut body_effect = HashMap::new();
    body_effect.insert("l".to_string(), var("next_l"));

    let result = verify_preservation(
        &invariants,
        Some(&PureExpr::Bool(true)),
        &["l"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("hashmap/list-shaped preservation should encode");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "hashmap/list method-name shape without semantics should fail, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn hashmap_list_shape_does_not_bypass_full_loop_verification() {
    let self_value = var("self");
    let key = var("key");
    let l = var("l");
    let invariant = bin(method_call(self_value, "get", vec![key]), BinOp::Eq, l);
    let invariants = vec![invariant];
    let ensures = vec![PureExpr::Bool(false)];

    let body_effect = HashMap::new();
    let deref_body_effect = HashMap::new();
    let double_deref_body_effect = HashMap::new();
    let pre_loop_assignments = HashMap::new();
    let modified_vars = Vec::new();
    let ctx = LoopVerificationContext::new(
        &[],
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &deref_body_effect, &double_deref_body_effect),
        &pre_loop_assignments,
    );

    let result = verify_loop_invariant(&ctx).expect("hashmap/list-shaped loop should encode");

    assert!(
        !matches!(result.postcondition, VerificationResult::Verified(_)),
        "false postcondition must not verify just because invariants match hashmap/list names; got {result:?}"
    );
}
