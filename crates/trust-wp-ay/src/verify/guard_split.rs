// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Guarded-premise split: completeness for `pre ==> post` call premises.
//!
//! The driver scopes every call's postcondition premise under that call's own
//! preconditions (`pre ==> post`, the weakest-precondition shape
//! `wp(call) = pre && (post ==> Q)`), and the preconditions are goals of the
//! same query. A solver can fail to fire such a premise (a quantified `pre`
//! in antecedent position, or an implication step its proof checker only
//! trusts), although the unguarded query it replaces was proved.
//!
//! When the single query is not verified, this module retries it as a
//! sequence of queries over the SAME premises `P` and goals `G`. Every
//! top-level premise `g ==> q` is a candidate; candidates whose guard matches
//! goals of the query (modulo variable sort annotations) are tried first:
//!
//! 1. `P_k ⊢ g_k` for the premise's OWN guard conjuncts `g_k` not yet
//!    established (a premise is only selected when its guard matches goals
//!    modulo variable sort annotations, but the exact guard is what is proved);
//! 2. `P_{k+1}` = `P_k` with every premise `g ==> q` whose guard conjuncts are
//!    all established replaced (in place) by `q`, the unguarded shape every
//!    downstream premise consumer (eager closure-law instantiation, alias
//!    filters) was written for;
//! 3. finally `P_n ⊢ G`.
//!
//! SOUND: if `P_k ⊨ g` and `(g ==> q) ∈ P_k` then `P_k ⊨ q`, and `q ⊨ g ==> q`,
//! so `P_{k+1}` is equivalent to `P_k`, and by induction to `P`; `P_n ⊨ G`
//! gives `P ⊨ G`.
//! This holds for any premise of the form `g ==> q` and any order of queries.
//! Only a VERIFIED sub-query with accepted solver evidence establishes a guard;
//! a guard whose sub-query is not verified stays guarded (its premise is left
//! unchanged). If the final query is not verified, the ORIGINAL outcome is
//! returned unchanged, so failure reporting is identical to the unsplit query.

use trust_wp_core::formula::{BinOp, PureExpr};

use super::types::{VerificationOutcome, VerificationResult};
use crate::EncodingError;

/// Upper bound on solver queries one split may issue (batch, per-guard and
/// final queries together).
const MAX_GUARD_SPLIT_QUERIES: usize = 6;

fn push_conjuncts(expr: &PureExpr, out: &mut Vec<PureExpr>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            push_conjuncts(lhs, out);
            push_conjuncts(rhs, out);
        }
        PureExpr::Bool(true) => {}
        other => {
            if !out.contains(other) {
                out.push(other.clone());
            }
        }
    }
}

/// `expr` with every variable sort annotation removed. Used ONLY to decide
/// which premises are worth splitting on (a guard and the matching goal can
/// differ in a `Ref` annotation of the same variable); what a sub-query proves
/// is always the premise's own guard, never the erased or goal form.
fn erase_var_sorts(expr: &PureExpr) -> PureExpr {
    expr.clone().rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, Some(_)) => PureExpr::Var(name, None),
        other => other,
    })
}

/// A premise `g ==> q` (at `index` in the premise list). `guard` holds the
/// premise's OWN conjuncts; `matches_goals` records whether they all match
/// (modulo variable sort annotations) goal conjuncts of the same query.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct GuardedPremise {
    pub(crate) index: usize,
    pub(crate) guard: Vec<PureExpr>,
    pub(crate) matches_goals: bool,
    /// The guard's layers, outermost first (`g1 ==> (g2 ==> q)` has layers
    /// `[g1, g2]`): each is established by its own sub-query, so a refused
    /// inner layer never refuses an outer layer another premise shares.
    pub(crate) layers: Vec<Vec<PureExpr>>,
}

/// Every top-level implication premise, goal-matching guards first (stable
/// order within each group).
pub(crate) fn guarded_premises(requires: &[PureExpr], ensures: &[PureExpr]) -> Vec<GuardedPremise> {
    let mut goal_conjuncts = Vec::new();
    for goal in ensures {
        push_conjuncts(goal, &mut goal_conjuncts);
    }
    let goal_conjuncts: Vec<PureExpr> = goal_conjuncts.iter().map(erase_var_sorts).collect();
    let mut premises: Vec<GuardedPremise> = requires
        .iter()
        .enumerate()
        .filter_map(|(index, premise)| {
            let PureExpr::BinOp(guard, BinOp::Implies, post) = premise else {
                return None;
            };
            let mut conjuncts = Vec::new();
            push_conjuncts(guard, &mut conjuncts);
            if conjuncts.is_empty() {
                return None;
            }
            let layer_matches = |layer: &[PureExpr]| {
                layer
                    .iter()
                    .all(|c| goal_conjuncts.contains(&erase_var_sorts(c)))
            };
            let matches_goals = layer_matches(&conjuncts);
            let mut layers = vec![conjuncts.clone()];
            // A nested guard `g1 ==> (g2 ==> q)` (a call postcondition scoped
            // under its own preconditions, then under earlier obligations):
            // while each inner layer also matches goals, its conjuncts belong
            // to the guard, so establishing them discharges the whole chain.
            if matches_goals {
                let mut inner = post.as_ref();
                while let PureExpr::BinOp(inner_guard, BinOp::Implies, inner_post) = inner {
                    let mut layer = Vec::new();
                    push_conjuncts(inner_guard, &mut layer);
                    if !layer_matches(&layer) {
                        break;
                    }
                    for c in &layer {
                        if !conjuncts.contains(c) {
                            conjuncts.push(c.clone());
                        }
                    }
                    layers.push(layer);
                    inner = inner_post.as_ref();
                }
            }
            Some(GuardedPremise {
                index,
                guard: conjuncts,
                matches_goals,
                layers,
            })
        })
        .collect();
    premises.sort_by_key(|premise| !premise.matches_goals);
    premises
}

/// A sub-query establishes its goals only when verified with accepted
/// solver evidence (the same bar a consumer applies to a verified outcome).
pub(crate) fn outcome_establishes(outcome: &VerificationOutcome) -> bool {
    matches!(outcome.result, VerificationResult::Verified(_))
        && outcome
            .provenance
            .as_ref()
            .and_then(|provenance| provenance.solve_evidence.as_ref())
            .is_some_and(|evidence| evidence.accepted_for_consumer)
}

/// Replace, in place, every guarded premise whose guard is fully
/// established by its post `q`.
///
/// The peel loop is driven by the SHAPE of `current[index]`, not by the
/// `layers` [`guarded_premises`] recorded: once the recorded layers are gone
/// it keeps going while the remaining post is itself an implication whose
/// antecedent conjuncts are all established, so it can peel into a user
/// postcondition's own implication. That is still sound — a conjunct reaches
/// `established` only as the verified goal of a query over a premise set
/// equivalent to `requires`, so `requires |= g`, so replacing `g ==> q` by
/// `q` is equivalence-preserving whatever produced the `g` — but it is more
/// than "peel every guard layer", and the extra peels are not bounded by
/// `premise.layers`.
fn discharge_established(
    current: &mut [PureExpr],
    guarded: &[GuardedPremise],
    established: &[PureExpr],
) {
    for premise in guarded {
        if !premise.guard.iter().all(|c| established.contains(c)) {
            continue;
        }
        // Peel every guard layer whose conjuncts are all established.
        while let PureExpr::BinOp(guard, BinOp::Implies, post) = &current[premise.index] {
            let mut layer = Vec::new();
            push_conjuncts(guard, &mut layer);
            if !layer.iter().all(|c| established.contains(c)) {
                break;
            }
            current[premise.index] = post.as_ref().clone();
        }
    }
}

/// Retry a non-verified query as the guarded-premise split described in the
/// module docs. `run` issues one unsplit query over (premises, goals).
pub(crate) fn retry_with_guard_split<F>(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    original: VerificationOutcome,
    mut run: F,
) -> VerificationOutcome
where
    F: FnMut(&[PureExpr], &[PureExpr]) -> Result<VerificationOutcome, EncodingError>,
{
    if matches!(original.result, VerificationResult::Verified(_)) {
        return original;
    }
    if original
        .result
        .unknown_reason_str()
        .is_some_and(|reason| reason.to_ascii_lowercase().contains("timeout"))
    {
        return original;
    }
    let guarded = guarded_premises(requires, ensures);
    if guarded.is_empty() {
        return original;
    }
    let mut batch_guards: Vec<PureExpr> = Vec::new();
    for premise in guarded.iter().filter(|premise| premise.matches_goals) {
        for conjunct in &premise.guard {
            if !batch_guards.contains(conjunct) {
                batch_guards.push(conjunct.clone());
            }
        }
    }
    let mut current = requires.to_vec();
    let mut established: Vec<PureExpr> = Vec::new();
    let mut refused: Vec<PureExpr> = Vec::new();
    let mut queries = 0usize;

    if !batch_guards.is_empty() {
        queries += 1;
        let batch_ok = run(&current, &batch_guards)
            .map(|outcome| outcome_establishes(&outcome))
            .unwrap_or(false);
        if batch_ok {
            established = batch_guards;
            discharge_established(&mut current, &guarded, &established);
        }
    }
    'premises: for premise in &guarded {
        for layer in &premise.layers {
            let missing: Vec<PureExpr> = layer
                .iter()
                .filter(|c| !established.contains(c))
                .cloned()
                .collect();
            if missing.is_empty() {
                continue;
            }
            if missing.iter().any(|c| refused.contains(c)) {
                continue 'premises;
            }
            // Leave room for the final query.
            if queries + 2 > MAX_GUARD_SPLIT_QUERIES {
                break 'premises;
            }
            queries += 1;
            let ok = run(&current, &missing)
                .map(|outcome| outcome_establishes(&outcome))
                .unwrap_or(false);
            if ok {
                established.extend(missing);
                discharge_established(&mut current, &guarded, &established);
            } else {
                refused.extend(missing);
                continue 'premises;
            }
        }
    }
    if established.is_empty() {
        return original;
    }
    match run(&current, ensures) {
        Ok(outcome) if outcome_establishes(&outcome) => {
            tracing::debug!(
                queries = queries + 1,
                guards = established.len(),
                "guarded-premise split verified the query"
            );
            outcome
        }
        _ => original,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn implies(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs))
    }

    fn and(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))
    }

    #[test]
    fn goal_matching_guards_are_ordered_before_other_implications() {
        let requires = vec![
            implies(and(var("g1"), var("g2")), var("q")),
            implies(var("h"), var("r")),
            var("p"),
        ];
        let ensures = vec![var("g1"), and(var("g2"), var("goal"))];
        let guarded = guarded_premises(&requires, &ensures);
        assert_eq!(
            guarded,
            vec![
                GuardedPremise {
                    index: 0,
                    guard: vec![var("g1"), var("g2")],
                    matches_goals: true,
                    layers: vec![vec![var("g1"), var("g2")]],
                },
                GuardedPremise {
                    index: 1,
                    guard: vec![var("h")],
                    matches_goals: false,
                    layers: vec![vec![var("h")]],
                },
            ]
        );
    }

    #[test]
    fn guard_matches_goal_modulo_sort_annotation_but_keeps_its_own_form() {
        use trust_wp_core::formula::ExprSort;
        let typed = PureExpr::Var("w".to_string(), Some(ExprSort::Int));
        let requires = vec![implies(typed.clone(), var("q"))];
        let ensures = vec![var("w")];
        let guarded = guarded_premises(&requires, &ensures);
        assert_eq!(
            guarded,
            vec![GuardedPremise {
                index: 0,
                guard: vec![typed.clone()],
                matches_goals: true,
                layers: vec![vec![typed]],
            }]
        );
    }

    #[test]
    fn refused_guard_stays_guarded_and_original_outcome_is_returned() {
        let requires = vec![implies(var("g"), var("q"))];
        let ensures = vec![var("goal")];
        let original = VerificationOutcome::without_provenance(VerificationResult::Failed(
            super::super::types::Counterexample::empty(),
        ));
        let mut seen_final_premises = Vec::new();
        let outcome = retry_with_guard_split(&requires, &ensures, original, |premises, goals| {
            if goals == ensures.as_slice() {
                seen_final_premises.push(premises.to_vec());
            }
            Ok(VerificationOutcome::without_provenance(
                VerificationResult::Unknown(super::super::types::UnknownReason::SolverMessage(
                    "refused".to_string(),
                )),
            ))
        });
        assert!(matches!(outcome.result, VerificationResult::Failed(_)));
        assert!(
            seen_final_premises.is_empty(),
            "no guard was established, so no final query is issued"
        );
    }

    #[test]
    fn discharge_rewrites_only_fully_established_guards_in_place() {
        let requires = vec![
            implies(and(var("g1"), var("g2")), var("q")),
            implies(var("g1"), var("r")),
        ];
        let ensures = vec![var("g1"), var("g2")];
        let guarded = guarded_premises(&requires, &ensures);
        let mut current = requires.clone();
        discharge_established(&mut current, &guarded, &[var("g1")]);
        assert_eq!(current[0], requires[0]);
        assert_eq!(current[1], var("r"));
    }

    #[test]
    fn nested_goal_matching_layers_are_kept_apart_and_peeled_one_at_a_time() {
        // `pre1 ==> (pre2 ==> q2)`: a later call's post under an earlier
        // obligation and its own precondition; `pre1 ==> q1`: the earlier post.
        let requires = vec![
            implies(var("pre1"), implies(var("pre2"), var("q2"))),
            implies(var("pre1"), var("q1")),
            // A user postcondition's own implication is not a goal layer.
            implies(var("pre1"), implies(var("user"), var("q3"))),
        ];
        let ensures = vec![var("pre1"), var("pre2"), var("goal")];
        let guarded = guarded_premises(&requires, &ensures);
        assert_eq!(
            guarded[0].layers,
            vec![vec![var("pre1")], vec![var("pre2")]]
        );
        assert_eq!(guarded[0].guard, vec![var("pre1"), var("pre2")]);
        assert_eq!(guarded[2].layers, vec![vec![var("pre1")]]);

        let mut current = requires.clone();
        discharge_established(&mut current, &guarded, &[var("pre1")]);
        // Only fully established guards are peeled; the user implication stays.
        assert_eq!(current[0], requires[0]);
        assert_eq!(current[1], var("q1"));
        assert_eq!(current[2], implies(var("user"), var("q3")));
        discharge_established(&mut current, &guarded, &[var("pre1"), var("pre2")]);
        assert_eq!(current[0], var("q2"));
    }
}
