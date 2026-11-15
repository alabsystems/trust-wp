// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The gate refuses unplaced named-field metadata wherever a request carries it.

use std::sync::Arc;

use trust_wp_core::{
    formula::{MatchArm, Pattern, PureExpr},
    logic::LogicFnDef,
};

use super::{CheckPlacement, VerificationRequest};

fn reordered_pattern_body() -> PureExpr {
    PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("s".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "S{a,b}".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("aa".to_string()),
                    Pattern::Wildcard,
                ]))),
            },
            body: PureExpr::Var("aa".to_string(), None),
        }],
    }
}

fn placed_body() -> PureExpr {
    PureExpr::Var("s".to_string(), None)
}

#[test]
fn a_placed_request_passes_the_gate() {
    let requires = vec![PureExpr::Bool(true)];
    let ensures = vec![placed_body()];
    let request = VerificationRequest::new(&requires, &ensures);
    assert!(request.into_placed().is_ok(), "a placed request must pass");
}

#[test]
fn unplaced_metadata_in_a_clause_is_refused() {
    let requires = vec![reordered_pattern_body()];
    let ensures = vec![PureExpr::Bool(true)];
    let request = VerificationRequest::new(&requires, &ensures);
    let Err(err) = request.into_placed() else {
        panic!("the gate must refuse unplaced metadata");
    };
    assert!(
        err.to_string().contains("S{a,b}"),
        "the refusal must name the constructor: {err}"
    );
}

/// This is the s82 v4 defect in one test: the metadata is not in the contract,
/// it is in a LOGIC FUNCTION BODY the contract calls. Every earlier fix lived
/// on the contract-rewriting path and never saw this expression.
#[test]
fn unplaced_metadata_in_a_logic_fn_body_is_refused() {
    let requires: Vec<PureExpr> = Vec::new();
    let ensures = vec![PureExpr::Bool(true)];
    let logic_fns = vec![LogicFnDef::new(
        "pick".to_string(),
        "crate::pick".to_string(),
        vec!["s".to_string()],
        reordered_pattern_body(),
    )];
    let request = VerificationRequest::new(&requires, &ensures).logic_fns(Some(&logic_fns));
    let Err(err) = request.into_placed() else {
        panic!("a logic-fn body is a producer too");
    };
    assert!(err.to_string().contains("S{a,b}"), "{err}");
}

/// A closure's inlined body reaches the obligation through `closure_inline`,
/// never through a clause, so the clause scans alone would let it in.
#[test]
fn unplaced_metadata_in_an_inlined_closure_body_is_refused() {
    use super::ClosureCaptureInfo;
    let requires: Vec<PureExpr> = Vec::new();
    let ensures = vec![PureExpr::Bool(true)];
    let captures = vec![
        ClosureCaptureInfo::new("crate::f::{closure#0}".to_string(), Vec::new())
            .with_body_expr(Some(reordered_pattern_body())),
    ];
    let request = VerificationRequest::new(&requires, &ensures).closure_captures(Some(&captures));
    let Err(err) = request.into_placed() else {
        panic!("a closure body is a producer too");
    };
    assert!(err.to_string().contains("S{a,b}"), "{err}");
}

#[test]
fn unplaced_metadata_in_a_closure_ensures_is_refused() {
    use super::ClosureCaptureInfo;
    let requires: Vec<PureExpr> = Vec::new();
    let ensures = vec![PureExpr::Bool(true)];
    let captures = vec![
        ClosureCaptureInfo::new("crate::f::{closure#0}".to_string(), Vec::new())
            .with_ensures_exprs(Some(vec![reordered_pattern_body()])),
    ];
    let request = VerificationRequest::new(&requires, &ensures).closure_captures(Some(&captures));
    assert!(
        request.into_placed().is_err(),
        "a closure ensures is a producer too"
    );
}

/// A logic function withdrawn for reading a final value (its body names
/// `WITHDRAWN_FINAL_READER`, D-108): a goal that may name it, by any
/// spelling, or carries the marker an inliner expanded, is refused; a goal
/// that names neither passes, and the definitions themselves are not goals.
#[test]
fn a_goal_naming_a_withdrawn_final_reader_is_refused() {
    use trust_wp_core::logic::final_reads::WITHDRAWN_FINAL_READER;
    let var = |name: &str| PureExpr::Var(name.to_string(), None);
    let logic_fns = vec![LogicFnDef::new(
        "unchanged".to_string(),
        "crate::unchanged".to_string(),
        vec!["q".to_string()],
        PureExpr::LogicFnCall {
            name: WITHDRAWN_FINAL_READER.to_string(),
            args: vec![var("q")],
        },
    )];
    let requires: Vec<PureExpr> = Vec::new();
    let refused = [
        PureExpr::LogicFnCall {
            name: "unchanged".to_string(),
            args: vec![var("p")],
        },
        PureExpr::MethodCall {
            receiver: Arc::new(var("p")),
            method: "unchanged".to_string(),
            args: vec![],
        },
        PureExpr::LogicFnCall {
            name: "Self::unchanged".to_string(),
            args: vec![var("p")],
        },
        PureExpr::LogicFnCall {
            name: WITHDRAWN_FINAL_READER.to_string(),
            args: vec![var("p")],
        },
    ];
    for goal in refused {
        let ensures = vec![goal.clone()];
        let request = VerificationRequest::new(&requires, &ensures).logic_fns(Some(&logic_fns));
        let Err(err) = request.into_placed() else {
            panic!("a goal naming a withdrawn final reader must be refused: {goal:?}");
        };
        assert!(err.to_string().contains("reads a final value"), "{err}");
    }
    let ensures = vec![PureExpr::LogicFnCall {
        name: "changed".to_string(),
        args: vec![var("p")],
    }];
    let request = VerificationRequest::new(&requires, &ensures).logic_fns(Some(&logic_fns));
    assert!(
        request.into_placed().is_ok(),
        "the withdrawn definition itself is not a goal"
    );
}

/// A definition that reads a final value and that nothing withdrew (the
/// library facade takes its definitions from its caller) is read by the door
/// as a withdrawn one: its `&mut` parameter is one value in the encoder, so
/// `^q == *q` would hold of every `q` (D-109).
#[test]
fn a_goal_naming_an_unwithdrawn_final_reader_is_refused() {
    let var = |name: &str| PureExpr::Var(name.to_string(), None);
    let logic_fns = vec![LogicFnDef::new(
        "unchanged".to_string(),
        "crate::unchanged".to_string(),
        vec!["q".to_string()],
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(var("q")))),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::Deref(Arc::new(var("q")))),
        ),
    )];
    let requires: Vec<PureExpr> = Vec::new();
    let ensures = vec![PureExpr::LogicFnCall {
        name: "unchanged".to_string(),
        args: vec![var("p")],
    }];
    let request = VerificationRequest::new(&requires, &ensures).logic_fns(Some(&logic_fns));
    let Err(err) = request.into_placed() else {
        panic!("a goal naming a final-reading definition must be refused");
    };
    assert!(err.to_string().contains("reads a final value"), "{err}");
}
