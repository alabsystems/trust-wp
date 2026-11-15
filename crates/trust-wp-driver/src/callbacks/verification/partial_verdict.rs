// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verdict ceilings for a body extraction that gave up
//! ([`demote_incomplete_extraction`]) and for clause-free function bodies.
//!
//! A function with no `requires`/`ensures`/`invariant`/`variant` of its own
//! (and no inherited trait contract) is a verification target only for its
//! body obligations: machine-integer arithmetic and index bounds goals, call
//! preconditions. A `verified` verdict for it would claim that no execution
//! panics, but assert kinds no lane charges, diverging calls (`panic!`/`assert!` arms,
//! `unreachable!`, `abort`) behind no switch edge the verdict proved dead,
//! calls to callees whose body is checked by no lane (std/extern specs, fn
//! pointers) and `Drop` glue are not discharged by any lane (see
//! `panic_site_coverage`). While
//! such a site is reachable the verdict is capped at `unknown (partial: panic
//! paths unchecked (...))`: a counterexample still reports FAILED, but a
//! proof of the arithmetic obligations alone is never credited as a
//! function-level proof.

use std::collections::HashMap;

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
use trust_wp_ay::{EncodingError, UnknownReason, VerificationOutcome, VerificationResult};
use trust_wp_core::formula::PureExpr;
use trust_wp_driver::StdSpec;

use super::skip_decision::ContractClausePresence;
use crate::{
    callbacks::{discovery::trusted::has_trusted_marker, try_get_body_with_context},
    contracts::FunctionContract,
    mir_analysis::{unchecked_panic_sites, EnteredBody, ProvedDeadEdges},
};

/// Stable prefix of the capped verdict's reason.
pub(super) const PARTIAL_PANIC_PATHS_REASON: &str = "partial: panic paths unchecked";

/// The verdict this body may report, or `None` when it may report none.
///
/// `None` is reserved for a body that is a verification target ONLY because it
/// hands captures to a closure and somebody must pay for the grant, AND whose
/// obligations all discharged. Such a body writes no clause, so `verified`
/// would be the claim this module refuses for every clause-free body, while
/// the cap's `unknown (partial)` would report a defect where there is none.
/// Every other verdict — a refuted capture obligation, an undischarged one, an
/// encoding error — is returned and reported, which is what keeps the grant
/// paid for.
///
/// `proved_dead_edges` are read from the SAME extraction whose obligations
/// produced `result`: an edge counts as dead only because this verdict proved
/// it so on every path to its switch (D-142), and only when
/// [`dead_edges_the_proof_owns`] passed them for the premises that proof used
/// (D-143).
///
/// No closure reaches the `None` arm: `discover_closure_capture_invariant_owners`
/// admits fns only. `unchecked_panic_sites` credits a call into a closure with
/// a user spec only when the closure's own body is clean (D-104), and then on
/// the premise that the closure's lane discharges what that body does own —
/// its arithmetic and its callees' preconditions; a closure whose verdict were
/// withheld here would break that premise without a trace.
pub(super) fn cap_clause_free_verdict(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    clause_presence: &ContractClausePresence,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    proved_dead_edges: Option<&ProvedDeadEdges>,
    result: Result<VerificationOutcome, EncodingError>,
) -> Option<Result<VerificationOutcome, EncodingError>> {
    let mut outcome = match result {
        Ok(outcome) => outcome,
        Err(error) => return Some(Err(error)),
    };
    if contract.capture_owner_only && matches!(outcome.result, VerificationResult::Verified(_)) {
        return None;
    }
    if clause_presence.has_clauses()
        || contract.trait_origin.is_some()
        || !matches!(outcome.result, VerificationResult::Verified(_))
    {
        return Some(Ok(outcome));
    }
    let none_dead = ProvedDeadEdges::default();
    let sites = match try_get_body_with_context(tcx, contract.local_def_id) {
        Some(body_with_facts) => unchecked_panic_sites(
            tcx,
            &body_with_facts.body,
            user_specs,
            trait_specs,
            &|entered| entered_body(tcx, entered),
            proved_dead_edges.unwrap_or(&none_dead),
        ),
        None => vec!["no MIR body".to_string()],
    };
    if sites.is_empty() {
        return Some(Ok(outcome));
    }
    outcome.result = VerificationResult::Unknown(UnknownReason::Demoted(format!(
        "{PARTIAL_PANIC_PATHS_REASON} ({})",
        sites.join(", ")
    )));
    Some(Ok(outcome))
}

/// `proved_dead_edges`, when the proof that charged them had only entry facts
/// to stand on; otherwise none (D-143).
///
/// A charge `!guard` is a goal proved from `premises`. The primary walk records
/// a callee's postcondition, an assertion fact or an expiry fact as a premise
/// of EVERY goal, guarded by the obligations recorded before it but not by the
/// switch arm it was found in, and a panic arm's charge is pushed after its
/// sibling arm was walked: `assert!(x < 100); below(x);` proves the charge from
/// `below`'s `x < 100`, a fact of the path that passed the check
/// (clause_free_panic_arm_goal_by_later_callee_post.rs). A result-position
/// `LetAssume` in a goal is hoisted into the premises the same way. So an edge
/// is honored only while every premise is `true`, an `inv`, or one of
/// `requires` — the function's own preconditions with the parameter type
/// ranges the driver adds to them — which hold at entry on every path, and no
/// goal carries a `LetAssume`. The test is by source, not by shape: `below`'s
/// `x@ < 100` is spelled like a range.
pub(super) fn dead_edges_the_proof_owns<'a>(
    proved_dead_edges: &'a ProvedDeadEdges,
    requires: &[PureExpr],
    premises: &[PureExpr],
    goals: &[PureExpr],
    result_expr: Option<&PureExpr>,
) -> Option<&'a ProvedDeadEdges> {
    let entry_fact = |premise: &PureExpr| match premise {
        PureExpr::Bool(true) => true,
        PureExpr::LogicFnCall { name, args } if name == "inv" && args.len() == 1 => true,
        _ => requires.contains(premise),
    };
    let hoists = |expr: &PureExpr| expr.any_recursive(|e| matches!(e, PureExpr::LetAssume { .. }));
    let offender = premises
        .iter()
        .find(|premise| !entry_fact(premise))
        .or_else(|| goals.iter().find(|goal| hoists(goal)))
        .or_else(|| result_expr.filter(|result| hoists(result)));
    if let Some(offender) = offender {
        if !proved_dead_edges.is_empty() && std::env::var_os("TRUST_WP_AUTHORITY_TRACE").is_some() {
            let shown: String = format!("{offender:?}").chars().take(240).collect();
            eprintln!("[TWP_AUTH] proved switch edges dropped: not an entry fact: {shown}");
        }
        return None;
    }
    Some(proved_dead_edges)
}

/// Fail closed when body extraction gave up before every obligation site was
/// walked (`gap`, see `ParsedContract::extraction_fail_closed_reason`): the
/// proof may be missing obligations, so it is not a verification.
pub(super) fn demote_incomplete_extraction(
    gap: Option<&str>,
    result: Result<VerificationOutcome, EncodingError>,
) -> Result<VerificationOutcome, EncodingError> {
    result.map(|mut outcome| {
        if let Some(gap) = gap {
            if matches!(outcome.result, VerificationResult::Verified(_)) {
                outcome.result = VerificationResult::Unknown(UnknownReason::Demoted(format!(
                    "demoted: body extraction incomplete ({gap}); obligations past the gap were not walked"
                )));
            }
        }
        outcome
    })
}

/// What the panic account may read of a local item a credited call enters.
///
/// `#[trusted]` is decided by `has_trusted_marker`, the predicate discovery
/// uses to skip the item's body, so the account treats as an assumption
/// exactly the items no lane verifies.
fn entered_body<'tcx>(tcx: TyCtxt<'tcx>, entered: LocalDefId) -> Option<EnteredBody<'tcx>> {
    let def_id = entered.to_def_id();
    if has_trusted_marker(tcx, def_id, tcx.get_all_attrs(def_id)) {
        return Some(EnteredBody::Trusted);
    }
    try_get_body_with_context(tcx, entered).map(EnteredBody::Mir)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, PureExpr};

    use super::{dead_edges_the_proof_owns, ProvedDeadEdges};

    fn view_x_cmp(op: BinOp, bound: i64) -> PureExpr {
        let x = PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)));
        PureExpr::BinOp(Arc::new(x), op, Arc::new(PureExpr::Int(bound.into())))
    }

    #[test]
    fn a_callee_postcondition_premise_disowns_the_edges() {
        let edges = ProvedDeadEdges::default();
        let range = view_x_cmp(BinOp::Ge, 0);
        let post = view_x_cmp(BinOp::Lt, 100);
        let premises = [range.clone(), post];
        assert!(dead_edges_the_proof_owns(&edges, &[range], &premises, &[], None).is_none());
    }

    #[test]
    fn requires_true_and_inv_premises_keep_the_edges() {
        let edges = ProvedDeadEdges::default();
        let range = view_x_cmp(BinOp::Ge, 0);
        let inv = PureExpr::LogicFnCall {
            name: "inv".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        };
        let premises = [range.clone(), PureExpr::Bool(true), inv];
        assert!(dead_edges_the_proof_owns(&edges, &[range], &premises, &[], None).is_some());
    }

    #[test]
    fn a_let_assume_in_a_goal_disowns_the_edges() {
        let edges = ProvedDeadEdges::default();
        let goal = PureExpr::LetAssume {
            assumption: Arc::new(view_x_cmp(BinOp::Lt, 100)),
            body: Arc::new(PureExpr::Bool(true)),
        };
        assert!(dead_edges_the_proof_owns(&edges, &[], &[], &[goal], None).is_none());
    }
}
