// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Joining a host's credit to the callables it hands to code trust-wp does not
//! verify (D-118).
//!
//! `o.map(|j| w[j])` runs the closure inside `Option::map`, whose builtin spec
//! states the result and no precondition. The closure's bounds check is owed
//! by the closure's own verification under `requires true`
//! (`fn_owes_abort_or_callee_precondition`), and the host that handed it over
//! is credited only if that verification came out clean — the same scan
//! (`crate_callable_escapes`) names the closure a target and names what the
//! host rests on. A callable whose precondition nothing states for every
//! argument (a `#[requires]` closure, a type parameter, `dyn Fn`, a fn pointer),
//! or that writes host memory through a `&mut` no call lane advances, leaves
//! the host with no credit at all.
//!
//! Acceptance-narrowing only: it turns credits into errors and never the other
//! way round.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::logic::TypeInvariantDef;

use super::trait_credit_join::{take_back, LateWithdrawal, TraitCreditJoin};
use crate::callbacks::{
    discovery::{
        closures_defined_by_body, crate_callable_escapes, CallableEscape, EscapedCallable,
    },
    reporting::{ProofAssertCounters, VerificationCounters},
    verification_context::VerificationRunConfig,
};

/// Withdraw every credit whose host handed a callable to code trust-wp does
/// not verify and that callable's obligations were not discharged, joined to
/// the trait join to a fixpoint; report a refusal for a host no lane examined
/// that handed over a callable whose precondition nothing states.
///
/// The two joins feed one ledger ([`TraitCreditJoin::withdrawn`]) and run
/// until neither withdraws anything new:
/// - the trait join runs first: a closure whose clean verdict it took back is
///   not clean for the host that rests on it;
/// - a host this join withdraws that implements a contracted trait method
///   (or is its default body) did not discharge that contract, and the trait
///   join must see it before any caller handed the contract settles
///   (trait_impl_escape_withdrawal_leaves_trait_callers_credited.rs).
///
/// A closure's verdict is read from the trait join's own ledger of the
/// contract loop, the one snapshot both joins take per item.
///
/// The escapes are read with the run's definition set (`config`), the one
/// discovery made its targets from.
pub(super) fn demote(
    tcx: TyCtxt<'_>,
    config: &VerificationRunConfig<'_>,
    trait_join: &mut TraitCreditJoin,
    counters: &mut VerificationCounters,
    pa_counters: &mut ProofAssertCounters,
) {
    let (trait_specs, type_invariant_defs) = (config.trait_specs, config.type_invariant_defs);
    let escapes = crate_callable_escapes(tcx, type_invariant_defs);
    let defined = closures_defined_by_body(tcx);
    loop {
        trait_join.demote(tcx, counters, pa_counters);
        if escapes.is_empty() {
            return;
        }
        let withdrawn_here = withdraw_hand_offs(
            tcx,
            type_invariant_defs,
            trait_join,
            &escapes,
            &defined,
            counters,
            pa_counters,
        );
        let mut trait_contract_left = false;
        for def_id in withdrawn_here {
            trait_contract_left |=
                trait_join.withdrawn_later(tcx, trait_specs, def_id, LateWithdrawal::HandOff);
        }
        // Termination: each round that continues left a trait contract
        // standing for an item never withdrawn before, and the credited items
        // are finite.
        if !trait_contract_left {
            break;
        }
    }
    report_unexamined_hosts(tcx, trait_join, &escapes, counters);
}

/// One pass of the escaped-callable join over the credits still standing.
/// Returns the items it withdrew; the caller enters them in the ledger.
fn withdraw_hand_offs(
    tcx: TyCtxt<'_>,
    type_invariant_defs: &[TypeInvariantDef],
    trait_join: &TraitCreditJoin,
    escapes: &HashMap<LocalDefId, Vec<CallableEscape>>,
    defined: &HashMap<LocalDefId, Vec<LocalDefId>>,
    counters: &mut VerificationCounters,
    pa_counters: &mut ProofAssertCounters,
) -> Vec<DefId> {
    let already_withdrawn = trait_join.withdrawn();
    let mut walk = ShortfallWalk {
        tcx,
        type_invariant_defs,
        escapes,
        defined,
        outcomes: trait_join.clean_outcomes(),
        withdrawn: already_withdrawn,
        memo: HashMap::new(),
        visiting: HashSet::new(),
    };
    let mut withdrawn_here = Vec::new();
    for item in trait_join.credited() {
        if already_withdrawn.contains(&item.def_id) {
            continue;
        }
        let Some(host) = item.def_id.as_local() else {
            continue;
        };
        let Some(reason) = walk.host_shortfall(host) else {
            continue;
        };
        eprintln!(
            "trust-wp: {} error: verdict withdrawn - {reason}",
            item.def_path
        );
        eprintln!(
            "  a callable run by code trust-wp does not verify answers for its obligations by its own verification, and the caller that handed it over rests on that verification and on seeing what the callable writes"
        );
        take_back(item, counters, pa_counters);
        withdrawn_here.push(item.def_id);
    }
    withdrawn_here
}

/// A host no lane examined has no credit to withdraw, and nothing else
/// reports what it handed over. A requires-free closure it handed over
/// reports itself (it is a target); the rest must be named here.
fn report_unexamined_hosts(
    tcx: TyCtxt<'_>,
    trait_join: &TraitCreditJoin,
    escapes: &HashMap<LocalDefId, Vec<CallableEscape>>,
    counters: &mut VerificationCounters,
) {
    let credited_ids: HashSet<DefId> = trait_join
        .credited()
        .iter()
        .map(|item| item.def_id)
        .collect();
    let mut unexamined: Vec<(LocalDefId, &CallableEscape)> = escapes
        .iter()
        .filter(|(host, _)| {
            let def_id = host.to_def_id();
            !credited_ids.contains(&def_id) && !trait_join.clean_outcomes().contains_key(&def_id)
        })
        .flat_map(|(host, list)| {
            list.iter()
                .filter(|escape| {
                    matches!(
                        escape.callable,
                        EscapedCallable::Unresolved(_) | EscapedCallable::UnseenWrite(_)
                    )
                })
                .take(1)
                .map(move |escape| (*host, escape))
        })
        .collect();
    unexamined.sort_by_key(|(host, _)| host.local_def_index.as_u32());
    for (host, escape) in unexamined {
        eprintln!(
            "trust-wp: {} error: refused - {}",
            tcx.def_path_str(host.to_def_id()),
            describe_escape(tcx, escape, None)
        );
        counters.errors += 1;
    }
}

fn describe_escape(tcx: TyCtxt<'_>, escape: &CallableEscape, why: Option<&str>) -> String {
    match &escape.callable {
        EscapedCallable::Unresolved(what) => format!(
            "hands {what} to {}, which calls it under no precondition this run can state",
            escape.callee
        ),
        EscapedCallable::UnseenWrite(what) => format!(
            "hands {what} to {}, which runs it where no lane sees the write, so the host's proof reads that memory at its value before the call",
            escape.callee
        ),
        EscapedCallable::Closure(closure) => format!(
            "hands the closure {} to {}, which calls it under no precondition, and that closure {}",
            tcx.def_path_str(closure.to_def_id()),
            escape.callee,
            why.unwrap_or("was not verified")
        ),
    }
}

/// Whether a body's hand-offs are all discharged, memoised over the closure
/// nesting (a closure may hand another closure over in turn).
struct ShortfallWalk<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    /// The set discovery read, so a closure it made a target is one this walk
    /// expects a verdict from.
    type_invariant_defs: &'a [TypeInvariantDef],
    escapes: &'a HashMap<LocalDefId, Vec<CallableEscape>>,
    /// The closures each body defines, one level deep.
    defined: &'a HashMap<LocalDefId, Vec<LocalDefId>>,
    outcomes: &'a HashMap<DefId, bool>,
    withdrawn: &'a HashSet<DefId>,
    memo: HashMap<LocalDefId, Option<String>>,
    visiting: HashSet<LocalDefId>,
}

impl ShortfallWalk<'_, '_> {
    /// The first hand-off of `host` that is not discharged, described.
    fn host_shortfall(&mut self, host: LocalDefId) -> Option<String> {
        if let Some(known) = self.memo.get(&host) {
            return known.clone();
        }
        if !self.visiting.insert(host) {
            // Closure types cannot nest into themselves; a cycle here is a
            // shape this walk does not understand, and it credits nothing.
            return Some("hands over a callable whose verification depends on itself".to_string());
        }
        let mut found = None;
        for escape in self.escapes.get(&host).into_iter().flatten() {
            let why = match &escape.callable {
                EscapedCallable::Unresolved(_) | EscapedCallable::UnseenWrite(_) => Some(None),
                EscapedCallable::Closure(closure) => self.closure_shortfall(*closure).map(Some),
            };
            if let Some(why) = why {
                found = Some(describe_escape(self.tcx, escape, why.as_deref()));
                break;
            }
        }
        // A closure the host DEFINES runs on the host's behalf wherever it is
        // not handed to unverified code itself: called directly, or through a
        // verified generic hop, its precondition is its body's WP (D-54), and
        // that WP reads a combinator it calls as owing nothing. So the host
        // rests on that closure's own hand-offs as on its own.
        let defined = self.defined.get(&host).cloned().unwrap_or_default();
        for closure in defined {
            if found.is_some() {
                break;
            }
            if let Some(inner) = self.host_shortfall(closure) {
                found = Some(format!(
                    "defines the closure {}, which in turn {inner}",
                    self.tcx.def_path_str(closure.to_def_id())
                ));
            }
        }
        self.visiting.remove(&host);
        self.memo.insert(host, found.clone());
        found
    }

    /// Why an escaped closure's obligations are not discharged, if they are
    /// not: its own verdict, then what it hands over in turn.
    fn closure_shortfall(&mut self, closure: LocalDefId) -> Option<String> {
        let def_id = closure.to_def_id();
        match self.outcomes.get(&def_id) {
            Some(true) if !self.withdrawn.contains(&def_id) => {}
            Some(_) => return Some("was not verified".to_string()),
            None => {
                if crate::callbacks::discovery::fn_owes_abort_or_callee_precondition(
                    self.tcx,
                    closure,
                    self.type_invariant_defs,
                ) {
                    return Some("was never verified in this run".to_string());
                }
            }
        }
        self.host_shortfall(closure)
            .map(|inner| format!("in turn {inner}"))
    }
}
