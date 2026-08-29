// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;
use trust_wp_ay::{
    verify_function_with_modes, UnsoundnessCategory, VerificationRequest, VerificationResult,
};
use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr},
    logic::LogicFnDef,
};

fn int(value: i64) -> PureExpr {
    PureExpr::Int(value)
}

fn bool_expr(value: bool) -> PureExpr {
    PureExpr::Bool(value)
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

fn logic_fn_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    }
}

#[test]
#[timeout(10000)]
fn test_opaque_logic_fn_declared_bool_return_encodes_at_call_site() {
    let logic_fn = LogicFnDef::new(
        "is_valid".to_string(),
        "test::is_valid".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_return_sort(Some(ExprSort::Bool));
    let requires: Vec<PureExpr> = vec![];
    let ensures = vec![eq(logic_fn_call("is_valid", vec![int(0)]), bool_expr(true))];
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&logic_fn))),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "Bool-returning opaque logic fn calls should encode as Bool instead of erroring: {result:?}"
    );
}

#[test]
fn test_logic_fn_sort_fallback_is_demoting_after_return_sort_fix() {
    assert!(
        UnsoundnessCategory::SortFallbackToIntFromLogicFn.is_demoting(),
        "truly unknown logic fn return sorts remain demoting after #2320"
    );
}
