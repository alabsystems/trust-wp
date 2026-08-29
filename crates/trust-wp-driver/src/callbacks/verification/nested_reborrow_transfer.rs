// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Nested-reborrow transfer premise repair (rusthorn `inc_max_3` class).
//!
//! When the mut-borrow analysis recognized nested-reborrow transfer calls
//! (`swap(&mut ma, &mut mb)` over `&mut T`-typed parameter slots, see
//! `mir_analysis::mut_borrow::nested_transfer`), it emits exact, branch-merged
//! RustHorn expiry resolutions (`Final(<slot content>) == <slot exit value>`)
//! in `MutBorrowBody::nested_slot_resolutions`.
//!
//! The generic call-assumption extraction, however, has ALSO instantiated the
//! transfer callee's ensures with the two reference levels collapsed:
//! `^mma` (the callee's prophecy for the *slot*) is substituted as
//! `Final(Var("ma"))` — the prophecy of the slot's ENTRY borrow — producing
//! unguarded facts like `ma_final == mb_current` (and, after SSA renaming,
//! `Final^k` chains) that mis-pin the entry borrows' prophecies across all
//! branches. This pass:
//!
//! 1. removes exactly those collapsed transfer instantiations from
//!    `call_assumptions`/`pre_loop_call_assumptions` (every `&&`-conjunct of
//!    a removed assumption is `Final^k(p) == Deref(Final^j(q))`-shaped over
//!    the transfer params), and
//! 2. appends the exact expiry resolutions in their place.
//!
//! Soundness: the removed facts are premises — removing premises only weakens
//! the verification condition. The added resolutions are exact RustHorn
//! semantics: on every path, each parameter slot at function exit holds a
//! known entry borrow (the recognized transfer calls apply a spec-given
//! permutation and nothing else rebinds the slots — otherwise the analysis
//! poisons and this pass does not run), and a `&mut` parameter's borrow
//! expires at function exit in whichever slot it ended up, resolving its
//! prophecy to that slot's exit pointee value. The premises are Ite-guarded
//! by the same branch conditions as the contents/values they equate, so no
//! cross-branch fact is asserted unguarded.

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

use super::super::parsing::ParsedContract;

/// Replace collapsed transfer-call instantiations with exact expiry
/// resolutions. Poisoned tracking deliberately emits no resolutions, but must
/// still remove the known-invalid collapsed premises; retaining them in that
/// case would turn a conservative coverage loss into false proof credit.
pub(super) fn apply_nested_transfer_resolutions(parsed: &mut ParsedContract) {
    let Some(mut_borrow) = parsed.mut_borrow.mut_borrow_body.as_ref() else {
        return;
    };
    if mut_borrow.nested_transfer_params.is_empty() {
        return;
    }
    let resolutions = mut_borrow.nested_slot_resolutions.clone();
    let params = mut_borrow.nested_transfer_params.clone();

    replace_collapsed_transfer_assumptions(
        &mut parsed.call_assumptions,
        &mut parsed.pre_loop_call_assumptions,
        &resolutions,
        &params,
    );

    // Strip level-collapsed BODY write facts over the transfer params from the
    // extracted return expression (see `strip_collapsed_body_facts`). These are
    // the branch-scoped `LetAssume` facts the block extractor synthesized for
    // writes like `*ma += 2` using the collapsed naming (`Deref(ma)` for the
    // post-write state, `Deref(Final^k(ma))` for the pre-write state). On
    // paths where no transfer-call substitution fired, both sides collapse to
    // the SAME symbol, yielding a per-path premise `*ma == *ma + 2` — a
    // contradiction that asserts the negation of a REACHABLE path condition
    // and lets postconditions that are false on that path verify vacuously
    // (adjudicated 2026-07-22: e2-class should_fail programs false-verified).
    // The exact expiry resolutions appended above already carry the write
    // semantics for every path, so dropping these body premises only removes
    // invalid or redundant facts (fail-closed: premises only get weaker).
    if let Some(result_expr) = parsed.result_expr.as_mut() {
        *result_expr = strip_collapsed_body_facts(result_expr, &params);
    }
    if let Some(spanned) = parsed.result_expr_spanned.as_mut() {
        spanned.expr = strip_collapsed_body_facts(&spanned.expr, &params);
    }

    tracing::trace!(
        resolutions = resolutions.len(),
        params = ?params,
        "nested-reborrow transfer: replaced collapsed call instantiations \
         with expiry resolutions"
    );
}

fn replace_collapsed_transfer_assumptions(
    call_assumptions: &mut Vec<PureExpr>,
    pre_loop_call_assumptions: &mut Vec<PureExpr>,
    resolutions: &[PureExpr],
    params: &std::collections::HashSet<String>,
) {
    let is_collapsed = |expr: &PureExpr| is_collapsed_transfer_instantiation(expr, params);
    call_assumptions.retain(|assumption| !is_collapsed(assumption));
    pre_loop_call_assumptions.retain(|assumption| !is_collapsed(assumption));

    call_assumptions.extend(resolutions.iter().cloned());
    pre_loop_call_assumptions.extend(resolutions.iter().cloned());
}

/// Whether an expression mentions any transfer param variable.
fn expr_mentions_param(expr: &PureExpr, params: &std::collections::HashSet<String>) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Var(name, _) if params.contains(name)))
}

/// Strip body-extraction `LetAssume` facts that mention a nested-transfer
/// param from a return expression.
///
/// The block extractor models a transfer call by substituting the slot var
/// with `Final(slot)` in the continuation, and then synthesizes write facts
/// for `*slot += k` as `Deref(slot) == Deref(Final^j(slot)) + k` — using the
/// bare `Deref(slot)` symbol for the post-write state. That symbol ALSO
/// denotes the slot's ENTRY value everywhere else in the VC, so on any path
/// where the substitution chain is empty the fact degenerates to the
/// contradiction `*slot == *slot + k`, which (as a branch-guarded premise)
/// asserts the negation of a reachable path condition. All such body facts
/// over transfer params are invalid-or-redundant: the exact expiry
/// resolutions emitted by the mut-borrow analysis carry the per-path write
/// semantics. Dropping an assumption only weakens the premise set (sound);
/// obligations (`LetObligation`) are never dropped.
fn strip_collapsed_body_facts(
    expr: &PureExpr,
    params: &std::collections::HashSet<String>,
) -> PureExpr {
    match expr {
        PureExpr::LetAssume { assumption, body } => {
            let stripped_body = strip_collapsed_body_facts(body, params);
            if expr_mentions_param(assumption, params) {
                stripped_body
            } else {
                PureExpr::LetAssume {
                    assumption: Arc::clone(assumption),
                    body: Arc::new(stripped_body),
                }
            }
        }
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::clone(obligation),
            body: Arc::new(strip_collapsed_body_facts(body, params)),
        },
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::clone(cond),
            Arc::new(strip_collapsed_body_facts(then_expr, params)),
            Arc::new(strip_collapsed_body_facts(else_expr, params)),
        ),
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::clone(value),
            body: Arc::new(strip_collapsed_body_facts(body, params)),
        },
        other => other.clone(),
    }
}

/// Whether `expr` is a (conjunction of) level-collapsed transfer
/// instantiation equations over the transfer params:
/// every `&&`-conjunct is `Final^k(Var(p)) == Deref(Final^j(Var(q)))`
/// (either orientation), `k >= 1`, `j >= 0`, both in `params`.
/// Fixed-point equations are included: they are still level-collapsed call
/// premises, and a mixed permutation must not retain its invalid cross-slot
/// conjunct merely because one slot stayed fixed. Removing an unrelated
/// same-shape identity premise can only weaken verification (fail closed).
fn is_collapsed_transfer_instantiation(
    expr: &PureExpr,
    params: &std::collections::HashSet<String>,
) -> bool {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            is_collapsed_transfer_instantiation(lhs, params)
                && is_collapsed_transfer_instantiation(rhs, params)
        }
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
            matches_transfer_sides(lhs, rhs, params) || matches_transfer_sides(rhs, lhs, params)
        }
        _ => false,
    }
}

fn matches_transfer_sides(
    final_side: &PureExpr,
    deref_side: &PureExpr,
    params: &std::collections::HashSet<String>,
) -> bool {
    let Some(target) = final_chain_var(final_side) else {
        return false;
    };
    let Some(source) = deref_of_final_chain_var(deref_side) else {
        return false;
    };
    params.contains(target) && params.contains(source)
}

/// `Final^k(Var(name))` with `k >= 1` → `name`.
fn final_chain_var(expr: &PureExpr) -> Option<&str> {
    let PureExpr::Final(inner) = expr else {
        return None;
    };
    let mut current = inner.as_ref();
    loop {
        match current {
            PureExpr::Final(inner) => current = inner.as_ref(),
            PureExpr::Var(name, _) => return Some(name),
            _ => return None,
        }
    }
}

/// `Deref(Final^j(Var(name)))` with `j >= 0` → `name`.
fn deref_of_final_chain_var(expr: &PureExpr) -> Option<&str> {
    let PureExpr::Deref(inner) = expr else {
        return None;
    };
    let mut current = inner.as_ref();
    loop {
        match current {
            PureExpr::Final(inner) => current = inner.as_ref(),
            PureExpr::Var(name, _) => return Some(name),
            _ => return None,
        }
    }
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

    fn params(names: &[&str]) -> HashSet<String> {
        names.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn matches_flat_swap_instantiation() {
        let p = params(&["ma", "mb"]);
        let expr = and(
            eq(fin(var("ma")), deref(var("mb"))),
            eq(fin(var("mb")), deref(var("ma"))),
        );
        assert!(is_collapsed_transfer_instantiation(&expr, &p));
    }

    #[test]
    fn matches_depth_collapsed_instantiation() {
        let p = params(&["ma", "mb"]);
        // Final(Final(ma)) == Deref(Final(mb)) — receiver-state-threaded copy.
        let expr = and(
            eq(fin(fin(var("ma"))), deref(fin(var("mb")))),
            eq(fin(fin(fin(var("mb")))), deref(fin(var("ma")))),
        );
        assert!(is_collapsed_transfer_instantiation(&expr, &p));
    }

    #[test]
    fn filters_identity_equations_from_transfer_instantiations() {
        // A fixed-point arm is still a level-collapsed call premise. It must be
        // removed alongside moved arms in a mixed permutation; the exact exit
        // resolution is re-added separately when tracking remains sound.
        let p = params(&["ma", "mb"]);
        let expr = eq(fin(var("ma")), deref(var("ma")));
        assert!(is_collapsed_transfer_instantiation(&expr, &p));
    }

    #[test]
    fn rejects_non_transfer_params() {
        let p = params(&["ma", "mb"]);
        let expr = eq(fin(var("ma")), deref(var("other")));
        assert!(!is_collapsed_transfer_instantiation(&expr, &p));
    }

    #[test]
    fn rejects_mixed_conjunctions() {
        // A conjunction with one non-transfer conjunct must be kept whole.
        let p = params(&["ma", "mb"]);
        let expr = and(
            eq(fin(var("ma")), deref(var("mb"))),
            eq(var("x"), PureExpr::Int(0)),
        );
        assert!(!is_collapsed_transfer_instantiation(&expr, &p));
    }

    #[test]
    fn rejects_value_level_facts() {
        let p = params(&["ma", "mb"]);
        let expr = eq(
            PureExpr::View(Arc::new(fin(var("ma")))),
            PureExpr::View(Arc::new(deref(var("mb")))),
        );
        assert!(!is_collapsed_transfer_instantiation(&expr, &p));
    }

    fn let_assume(assumption: PureExpr, body: PureExpr) -> PureExpr {
        PureExpr::LetAssume {
            assumption: Arc::new(assumption),
            body: Arc::new(body),
        }
    }

    fn ite(cond: PureExpr, then_expr: PureExpr, else_expr: PureExpr) -> PureExpr {
        PureExpr::Ite(Arc::new(cond), Arc::new(then_expr), Arc::new(else_expr))
    }

    fn unit() -> PureExpr {
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".to_string(),
            args: vec![],
        }
    }

    fn add2(e: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(e), BinOp::Add, Arc::new(PureExpr::Int(2)))
    }

    // Regression: adjudication 2026-07-22 (dn33-39 class). The block extractor
    // synthesizes per-path write facts for `*ma += 2` with collapsed naming;
    // on the no-substitution path the fact is `*ma == *ma + 2` — a
    // contradiction that, as a branch-guarded premise, asserts the negation
    // of a REACHABLE path condition and false-verified e2-class should_fail
    // programs. The strip must drop every body `LetAssume` fact mentioning a
    // transfer param (contradictory or not — all use the collapsed model)
    // while preserving Ite structure and unrelated facts.
    #[test]
    fn strips_collapsed_write_facts_over_transfer_params() {
        let p = params(&["ma", "mb", "mc"]);
        // Ite(*ma < *mb,
        //     LetAssume { *ma == *^ma + 2, () },   <- collapsed but non-degenerate
        //     LetAssume { *ma == *ma + 2, () })    <- degenerate contradiction
        let cond = PureExpr::BinOp(
            Arc::new(deref(var("ma"))),
            BinOp::Lt,
            Arc::new(deref(var("mb"))),
        );
        let then_fact = eq(deref(var("ma")), add2(deref(fin(var("ma")))));
        let else_fact = eq(deref(var("ma")), add2(deref(var("ma"))));
        let body = ite(
            cond.clone(),
            let_assume(then_fact, unit()),
            let_assume(else_fact, unit()),
        );

        let stripped = strip_collapsed_body_facts(&body, &p);

        assert_eq!(stripped, ite(cond, unit(), unit()));
    }

    #[test]
    fn keeps_unrelated_body_facts_and_obligations() {
        let p = params(&["ma", "mb"]);
        // An assert-derived fact over an unrelated var must survive; an
        // obligation over a transfer param must NEVER be dropped (it is
        // proved, not assumed — dropping it would be fail-open).
        let unrelated_fact = eq(var("x"), PureExpr::Int(5));
        let obligation = eq(deref(var("ma")), PureExpr::Int(0));
        let body = let_assume(
            unrelated_fact.clone(),
            PureExpr::LetObligation {
                obligation: Arc::new(obligation.clone()),
                body: Arc::new(unit()),
            },
        );

        let stripped = strip_collapsed_body_facts(&body, &p);

        assert_eq!(
            stripped,
            let_assume(
                unrelated_fact,
                PureExpr::LetObligation {
                    obligation: Arc::new(obligation),
                    body: Arc::new(unit()),
                },
            )
        );
    }

    #[test]
    fn poisoned_tracking_still_removes_collapsed_premises() {
        let p = params(&["ma", "mb"]);
        let collapsed = and(
            eq(fin(var("ma")), deref(var("mb"))),
            eq(fin(var("mb")), deref(var("ma"))),
        );
        let unrelated = eq(var("x"), PureExpr::Int(0));
        let mut call_assumptions = vec![collapsed.clone(), unrelated.clone()];
        let mut pre_loop_call_assumptions = vec![collapsed, unrelated.clone()];

        replace_collapsed_transfer_assumptions(
            &mut call_assumptions,
            &mut pre_loop_call_assumptions,
            &[],
            &p,
        );

        assert_eq!(call_assumptions, vec![unrelated.clone()]);
        assert_eq!(pre_loop_call_assumptions, vec![unrelated]);
    }
}
