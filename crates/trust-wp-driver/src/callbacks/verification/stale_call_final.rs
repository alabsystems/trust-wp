// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Removal of a call's prophecy credit for a `&mut` parameter whose referent
//! something other than that call can still decide.
//!
//! A call's ensures is instantiated at the call site with the callee's `^p`
//! collapsed onto the caller's `Final(<root param>)`, producing premises like
//! `x_final == 1` for `set(&mut *x)` with `#[ensures(^r == 1)]`. That equality
//! is the reference semantics only while the borrow handed to the call is the
//! last thing that decides `*x` before `x`'s own borrow is resolved: the
//! reborrow expires at the return, the callee's final flows back into `*x`,
//! and `^x` is fixed from `*x` at resolution — which is AFTER the body's last
//! write. Creusot never binds `^x` at a call for exactly this reason.
//!
//! When the body writes `*x` after such a call, `^x` is decided by that write
//! and the call's premise names a value the program does not hand back, so
//! every postcondition about `^x` can be discharged with the callee's value.
//! That was an exit-0 false accept — see the `*_call_then_direct_write_final_stale`
//! cases. The same holds when the borrow ESCAPES and nothing here writes it at
//! all: `^x` is then whatever the caller leaves, and the premise promises a
//! value the caller is free to overwrite.
//!
//! The write's own value is NOT recovered here: the mut-borrow lane havocked
//! the referent at the call, so the write's rvalue may read an unknown value.
//! Dropping the premise loses the credit in both directions (the true
//! postcondition is not provable either); premises only get weaker, which is
//! the direction a fix in this family must fail in.

use trust_wp_core::formula::{BinOp, PureExpr};

use super::super::parsing::ParsedContract;

/// Drop every call-assumption conjunct that constrains `Final^k(<param>)`, or
/// a projection out of it, for a parameter whose credit is dead.
pub(super) fn drop_stale_call_final_assumptions(parsed: &mut ParsedContract) {
    if parsed.mut_borrow.stale_call_final_params.is_empty() {
        return;
    }
    let stale = parsed.mut_borrow.stale_call_final_params.clone();

    let dropped = retain_live_conjuncts(&mut parsed.call_assumptions, &stale)
        + retain_live_conjuncts(&mut parsed.pre_loop_call_assumptions, &stale);

    tracing::trace!(
        params = ?stale,
        dropped,
        "stale call-final credit: dropped call assumptions pinning a parameter \
         prophecy the call no longer decides"
    );
}

/// Rewrite each assumption to the conjunction of its conjuncts that do not
/// mention a stale prophecy, dropping it outright when nothing survives.
/// Returns how many conjuncts were removed.
fn retain_live_conjuncts(
    assumptions: &mut Vec<PureExpr>,
    stale: &std::collections::HashSet<String>,
) -> usize {
    let mut dropped = 0;
    let mut kept = Vec::with_capacity(assumptions.len());
    for assumption in assumptions.drain(..) {
        let mut conjuncts = Vec::new();
        split_conjuncts(&assumption, &mut conjuncts);
        let live: Vec<PureExpr> = conjuncts
            .into_iter()
            .filter(|conjunct| {
                let stale_here = mentions_stale_prophecy(conjunct, stale);
                if stale_here {
                    dropped += 1;
                }
                !stale_here
            })
            .collect();
        if let Some(rebuilt) = live.into_iter().reduce(|lhs, rhs| {
            PureExpr::BinOp(
                std::sync::Arc::new(lhs),
                BinOp::And,
                std::sync::Arc::new(rhs),
            )
        }) {
            kept.push(rebuilt);
        }
    }
    *assumptions = kept;
    dropped
}

/// Flatten a top-level `&&` chain. Only `And` is split: a conjunct under an
/// `Or`, an implication or an `Ite` is load-bearing for the branch it guards,
/// so such an assumption is judged (and dropped) whole.
fn split_conjuncts(expr: &PureExpr, out: &mut Vec<PureExpr>) {
    if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
        split_conjuncts(lhs, out);
        split_conjuncts(rhs, out);
    } else {
        out.push(expr.clone());
    }
}

/// Whether `expr` constrains a stale parameter's prophecy at any depth.
///
/// Anything UNDER a `Final` counts, not just a bare variable: a field of the
/// final value arrives as `Final(tuple_get_0(Var(p)))`, and receiver-state
/// threading stacks `Final`s. A clause that only READS the referent
/// (`Deref(Var(p))`) is untouched — the entry value is not what the call
/// credited, and no later write changes it.
fn mentions_stale_prophecy(expr: &PureExpr, stale: &std::collections::HashSet<String>) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Final(inner) if mentions_var(inner, stale)))
}

/// Whether `expr` names one of `names`, or a PROJECTION out of one.
///
/// The disqualified set is keyed on the parameter, because MIR borrow
/// provenance is; a `&mut` held one field deep reaches the formulas as its own
/// carrier, `w.0`, and the credit the call pinned is spelled on that carrier
/// alone. Matching the parameter name only would leave the grant and the
/// obligation naming different things, which is the whole defect. A Rust
/// identifier cannot contain `.`, so a dotted name is always a projection of
/// the parameter it is prefixed by and never a different parameter. The
/// keying is per-PARAMETER either way: a carrier disqualifies its siblings
/// too, which only ever drops a further premise.
fn mentions_var(expr: &PureExpr, names: &std::collections::HashSet<String>) -> bool {
    expr.any_recursive(|node| match node {
        PureExpr::Var(name, _) => names.iter().any(|stale| {
            name == stale
                || name
                    .strip_prefix(stale.as_str())
                    .is_some_and(|rest| rest.starts_with('.'))
        }),
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, sync::Arc};

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn fin(expr: PureExpr) -> PureExpr {
        PureExpr::Final(Arc::new(expr))
    }

    fn deref(expr: PureExpr) -> PureExpr {
        PureExpr::Deref(Arc::new(expr))
    }

    fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
    }

    fn and(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))
    }

    fn stale(names: &[&str]) -> HashSet<String> {
        names.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn drops_the_pin_on_a_rewritten_parameter() {
        let s = stale(&["x"]);
        let mut assumptions = vec![eq(fin(var("x")), PureExpr::Int(1))];
        assert_eq!(retain_live_conjuncts(&mut assumptions, &s), 1);
        assert!(assumptions.is_empty());
    }

    #[test]
    fn keeps_the_conjuncts_that_do_not_pin_it() {
        // Only the prophecy conjunct is invalidated by a later write; the
        // result fact from the same call still holds.
        let s = stale(&["x"]);
        let result_fact = eq(var("result"), PureExpr::Int(5));
        let mut assumptions = vec![and(
            eq(fin(var("x")), PureExpr::Int(1)),
            result_fact.clone(),
        )];
        assert_eq!(retain_live_conjuncts(&mut assumptions, &s), 1);
        assert_eq!(assumptions, vec![result_fact]);
    }

    #[test]
    fn keeps_a_read_of_the_referent() {
        // `*x` is the entry value, which no later write changes.
        let s = stale(&["x"]);
        let read = eq(deref(var("x")), PureExpr::Int(0));
        let mut assumptions = vec![read.clone()];
        assert_eq!(retain_live_conjuncts(&mut assumptions, &s), 0);
        assert_eq!(assumptions, vec![read]);
    }

    #[test]
    fn drops_a_receiver_state_threaded_chain() {
        // `Final(Final(x))` is the same prophecy after receiver-state threading.
        let s = stale(&["x"]);
        let mut assumptions = vec![eq(fin(fin(var("x"))), deref(var("y")))];
        assert_eq!(retain_live_conjuncts(&mut assumptions, &s), 1);
        assert!(assumptions.is_empty());
    }

    #[test]
    fn drops_a_field_of_the_final_value() {
        // `(^s).a` arrives as `Final(tuple_get_0(s))`, not a bare variable.
        let s = stale(&["s"]);
        let field = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![var("s")],
        };
        let mut assumptions = vec![eq(fin(field), PureExpr::Int(1))];
        assert_eq!(retain_live_conjuncts(&mut assumptions, &s), 1);
        assert!(assumptions.is_empty());
    }

    #[test]
    fn drops_the_pin_on_a_mut_ref_held_one_field_deep() {
        // A `&mut` inside a by-value struct parameter reaches the formulas as
        // its own carrier; the parameter is what MIR provenance can key on.
        let s = stale(&["w"]);
        let mut assumptions = vec![eq(fin(var("w.0")), PureExpr::Int(1))];
        assert_eq!(retain_live_conjuncts(&mut assumptions, &s), 1);
        assert!(assumptions.is_empty());
    }

    #[test]
    fn a_longer_name_is_not_a_projection() {
        // `w2` is a different parameter, not a field of `w`.
        let s = stale(&["w"]);
        let other = eq(fin(var("w2")), PureExpr::Int(1));
        let mut assumptions = vec![other.clone()];
        assert_eq!(retain_live_conjuncts(&mut assumptions, &s), 0);
        assert_eq!(assumptions, vec![other]);
    }

    #[test]
    fn leaves_other_parameters_alone() {
        let s = stale(&["x"]);
        let other = eq(fin(var("y")), PureExpr::Int(1));
        let mut assumptions = vec![other.clone()];
        assert_eq!(retain_live_conjuncts(&mut assumptions, &s), 0);
        assert_eq!(assumptions, vec![other]);
    }
}
