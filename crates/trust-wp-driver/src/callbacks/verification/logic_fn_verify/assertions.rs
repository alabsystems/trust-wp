// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `proof_assert!`s in a logic function's body are goals of that function.
//!
//! Creusot translates a `proof_assert!` in a pearlite body to
//! `TermKind::Assert`, and the logic VC generator conjoins its condition into
//! the `vc_` goal it emits for every logic function with a contract (requires,
//! ensures or variant): `requires ==> wp(body)` with `Assert { cond }` read as
//! `cond && k(())`. A logic function with no contract gets no goal at all.
//!
//! The logic-postcondition lane proves `ensures` from the body's VALUE, which
//! an assertion does not change, so it never met them
//! (logic_fn_body_assertion_never_examined.rs). This module states them as one
//! goal over the body's own scoping: the `let` bindings in scope where the
//! assertion sits and the branch conditions of the `if`/`match` arms it is in.
//! An assertion anywhere else — inside a quantifier, a closure, a call argument
//! or a `let` initializer — is REFUSED, never dropped.

use trust_wp_core::formula::{MatchArm, PureExpr, PureExprDepthLimitedTraversalExt as _};

/// The body walk's depth budget, the encoder's own (`MAX_ENCODING_DEPTH`).
const DEPTH_LIMIT: usize = 200;

/// What a logic function body owes for its own assertions.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum AssertionGoal {
    /// The body holds no `proof_assert!`.
    None,
    /// The condition every assertion puts on the body's parameters.
    Goal(PureExpr),
    /// An assertion sits where this walk cannot place it; the reason names it.
    Refused(&'static str),
}

/// The arguments of `proof_assert!(..)` as the contract parser spells it.
fn proof_assert_args(expr: &PureExpr) -> Option<&[PureExpr]> {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if name == "proof_assert" || name.ends_with("::proof_assert") =>
        {
            Some(args)
        }
        _ => None,
    }
}

/// Whether any node of `expr` is a `proof_assert!`. Past the depth budget the
/// answer is yes: an assertion the walk cannot see is one it cannot place.
fn contains_proof_assert(expr: &PureExpr) -> bool {
    expr.any_recursive_with_depth_limit(DEPTH_LIMIT, true, |node| proof_assert_args(node).is_some())
}

/// The goal a logic function body owes for its own assertions.
pub(super) fn assertion_goal(body: &PureExpr) -> AssertionGoal {
    if !contains_proof_assert(body) {
        return AssertionGoal::None;
    }
    match goal_of(body, 0) {
        Ok(Some(goal)) => AssertionGoal::Goal(goal),
        Ok(None) => AssertionGoal::Refused("a proof_assert! the body walk could not place"),
        Err(reason) => AssertionGoal::Refused(reason),
    }
}

fn and(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(
        std::sync::Arc::new(left),
        trust_wp_core::formula::BinOp::And,
        std::sync::Arc::new(right),
    )
}

/// The goal of the assertions in `expr`, `None` when it holds none.
///
/// Only the positions a statement sequence produces are walked: the body
/// itself, a `let` continuation (`proof_assert!(c); rest` is parsed as
/// `let $stmtN = proof_assert(c) in rest`), and the arms of an `if` or a
/// `match`. Everything the goal keeps from the body — a binding's value, a
/// branch condition, a scrutinee — must itself be assertion-free, so the goal
/// never carries a `proof_assert` term for the encoder to guess at.
fn goal_of(expr: &PureExpr, depth: usize) -> Result<Option<PureExpr>, &'static str> {
    if depth > DEPTH_LIMIT {
        return Err("a proof_assert! nested deeper than the body walk reaches");
    }
    if !contains_proof_assert(expr) {
        return Ok(None);
    }
    if let Some(args) = proof_assert_args(expr) {
        let [cond] = args else {
            return Err("a proof_assert! whose body did not parse as one condition");
        };
        if contains_proof_assert(cond) {
            return Err("a proof_assert! inside another proof_assert!");
        }
        return Ok(Some(cond.clone()));
    }
    let next = depth + 1;
    match expr {
        PureExpr::Let { var, value, body } => {
            let body_goal = goal_of(body, next)?;
            if proof_assert_args(value).is_some() {
                // `var` is the assertion's unit value; nothing reads it.
                let value_goal = goal_of(value, next)?;
                return Ok(match (value_goal, body_goal) {
                    (Some(first), Some(rest)) => Some(and(first, rest)),
                    (first, rest) => first.or(rest),
                });
            }
            if contains_proof_assert(value) {
                return Err("a proof_assert! inside a let initializer");
            }
            Ok(body_goal.map(|goal| PureExpr::Let {
                var: var.clone(),
                value: value.clone(),
                body: std::sync::Arc::new(goal),
            }))
        }
        PureExpr::Ite(cond, then_branch, else_branch) => {
            if contains_proof_assert(cond) {
                return Err("a proof_assert! inside an if condition");
            }
            let then_goal = goal_of(then_branch, next)?;
            let else_goal = goal_of(else_branch, next)?;
            if then_goal.is_none() && else_goal.is_none() {
                return Ok(None);
            }
            Ok(Some(PureExpr::Ite(
                cond.clone(),
                std::sync::Arc::new(then_goal.unwrap_or(PureExpr::Bool(true))),
                std::sync::Arc::new(else_goal.unwrap_or(PureExpr::Bool(true))),
            )))
        }
        PureExpr::Match { scrutinee, arms } => {
            if contains_proof_assert(scrutinee) {
                return Err("a proof_assert! inside a match scrutinee");
            }
            let mut any = false;
            let mut goal_arms = Vec::with_capacity(arms.len());
            for arm in arms {
                let arm_goal = goal_of(&arm.body, next)?;
                any |= arm_goal.is_some();
                goal_arms.push(MatchArm {
                    pattern: arm.pattern.clone(),
                    body: arm_goal.unwrap_or(PureExpr::Bool(true)),
                });
            }
            Ok(any.then(|| PureExpr::Match {
                scrutinee: scrutinee.clone(),
                arms: goal_arms,
            }))
        }
        _ => Err("a proof_assert! inside an expression (a quantifier, closure, call or operator)"),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::BinOp;

    use super::*;

    fn pa(cond: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: "proof_assert".to_string(),
            args: vec![cond],
        }
    }

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn stmt(value: PureExpr, body: PureExpr) -> PureExpr {
        PureExpr::Let {
            var: "$stmt0".to_string(),
            value: Arc::new(value),
            body: Arc::new(body),
        }
    }

    #[test]
    fn a_body_without_assertions_owes_nothing() {
        assert_eq!(assertion_goal(&PureExpr::Int(1)), AssertionGoal::None);
    }

    #[test]
    fn a_leading_assertion_is_the_goal() {
        let body = stmt(pa(PureExpr::Bool(false)), PureExpr::Int(1));
        assert_eq!(
            assertion_goal(&body),
            AssertionGoal::Goal(PureExpr::Bool(false))
        );
    }

    #[test]
    fn an_assertion_keeps_the_let_bindings_in_scope() {
        let body = PureExpr::Let {
            var: "y".to_string(),
            value: Arc::new(var("x")),
            body: Arc::new(stmt(pa(var("y")), var("y"))),
        };
        assert_eq!(
            assertion_goal(&body),
            AssertionGoal::Goal(PureExpr::Let {
                var: "y".to_string(),
                value: Arc::new(var("x")),
                body: Arc::new(var("y")),
            })
        );
    }

    #[test]
    fn an_assertion_in_one_branch_is_owed_under_that_branch_only() {
        let body = PureExpr::Ite(
            Arc::new(var("c")),
            Arc::new(stmt(pa(var("p")), PureExpr::Int(1))),
            Arc::new(PureExpr::Int(2)),
        );
        assert_eq!(
            assertion_goal(&body),
            AssertionGoal::Goal(PureExpr::Ite(
                Arc::new(var("c")),
                Arc::new(var("p")),
                Arc::new(PureExpr::Bool(true)),
            ))
        );
    }

    #[test]
    fn two_assertions_are_both_owed() {
        let body = stmt(pa(var("p")), stmt(pa(var("q")), PureExpr::Int(1)));
        assert_eq!(
            assertion_goal(&body),
            AssertionGoal::Goal(PureExpr::BinOp(
                Arc::new(var("p")),
                BinOp::And,
                Arc::new(var("q")),
            ))
        );
    }

    #[test]
    fn an_assertion_the_walk_cannot_place_is_refused_not_dropped() {
        let body = PureExpr::BinOp(
            Arc::new(stmt(pa(var("p")), PureExpr::Int(1))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        assert!(matches!(assertion_goal(&body), AssertionGoal::Refused(_)));
        let in_initializer = PureExpr::Let {
            var: "y".to_string(),
            value: Arc::new(stmt(pa(var("p")), PureExpr::Int(1))),
            body: Arc::new(var("y")),
        };
        assert!(matches!(
            assertion_goal(&in_initializer),
            AssertionGoal::Refused(_)
        ));
    }
}
