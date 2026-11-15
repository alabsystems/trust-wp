// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Joining the trait-contract grant to the obligation that pays for it.
//!
//! See `crate::trait_credit` for why the two were separate. This module owns
//! the run-level bookkeeping: which items took a grant, which impls left a
//! contract standing, and the demotion that withdraws the first when the
//! second happened.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_driver::StdSpec;

use super::{
    credit_graph::build_credit_graph,
    skip_decision::{check_contract_skip, SkipDecision},
};
use crate::{
    callbacks::reporting::{ProofAssertCounters, VerificationCounters},
    contracts::FunctionContract,
    trait_credit::{self, CreditGraph, CreditedItem, UndischargedTraitContracts},
};

/// The counters an item's verification is measured against.
pub(super) struct CounterSnapshot {
    verified: usize,
    verified_native_only: usize,
    verified_with_axiom_deps: usize,
    pa_verified: usize,
    pa_failed: usize,
    pa_errors: usize,
    failed: usize,
    errors: usize,
    panics: usize,
    assumed: usize,
    refutations_withheld: usize,
    vacuous: usize,
    evidence_gaps: usize,
}

impl CounterSnapshot {
    pub(super) fn take(counters: &VerificationCounters, pa_counters: &ProofAssertCounters) -> Self {
        Self {
            verified: counters.verified,
            verified_native_only: counters.verified_native_only,
            verified_with_axiom_deps: counters.verified_with_axiom_deps,
            pa_verified: pa_counters.verified,
            pa_failed: pa_counters.failed,
            pa_errors: pa_counters.errors,
            failed: counters.failed,
            errors: counters.errors,
            panics: counters.panics,
            assumed: counters.assumed,
            refutations_withheld: counters.refutations_withheld,
            vacuous: counters.vacuous,
            evidence_gaps: counters.evidence_gaps,
        }
    }

    /// Whether the item verified since the snapshot came out CREDITED and
    /// clean: a `verified` (or `verified*`) verdict and no failure, refusal,
    /// withheld refutation, vacuity, assumption or evidence gap beside it,
    /// its own `proof_assert!`s included.
    pub(super) fn clean_credit_since(
        &self,
        counters: &VerificationCounters,
        pa_counters: &ProofAssertCounters,
    ) -> bool {
        let credited = counters.verified > self.verified
            || counters.verified_with_axiom_deps > self.verified_with_axiom_deps;
        credited
            && counters.failed == self.failed
            && counters.errors == self.errors
            && counters.panics == self.panics
            && counters.assumed == self.assumed
            && counters.refutations_withheld == self.refutations_withheld
            && counters.vacuous == self.vacuous
            && counters.evidence_gaps == self.evidence_gaps
            && pa_counters.failed == self.pa_failed
            && pa_counters.errors == self.pa_errors
    }

    /// Whether any function-contract verdict was reached since the snapshot.
    fn any_verdict_since(&self, counters: &VerificationCounters) -> bool {
        counters.verified > self.verified
            || counters.verified_with_axiom_deps > self.verified_with_axiom_deps
            || counters.failed > self.failed
            || counters.errors > self.errors
            || counters.panics > self.panics
            || counters.assumed > self.assumed
            || counters.vacuous > self.vacuous
            || counters.evidence_gaps > self.evidence_gaps
    }
}

/// Why an implementation of a contracted trait method did not discharge it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shortfall {
    Panicked,
    Failed,
    RefutationWithheld,
    Unproved,
    Assumed,
    /// Proved, but the proof's strict certification was not checked. Whether
    /// it is checked depends on machine load, and a grant is a proof claim.
    EvidenceGap,
    NoVerdict,
    NotVerified,
    Refused,
    /// A logic function implementing a program trait method: its body is
    /// erased to `unreachable!()` in the code that runs.
    LogicBodyForProgramMethod,
    /// A logic function whose body does not establish its trait logic
    /// method's postcondition (`logic_impl_discharge`).
    LogicBodyUndischarged,
    /// Credited, then withdrawn by the escaped-callable join
    /// ([`super::escape_credit_join`]): it hands a callable to code trust-wp
    /// does not verify, and that callable's obligations were not discharged.
    HandOffUndischarged,
    /// Credited, then withdrawn by a late verdict on its own `proof_assert!`.
    OwnAssertionUnproved,
    /// Credited, then withdrawn because it rests on a contract nothing
    /// discharged (the trait or the callee join).
    Withdrawn,
}

impl Shortfall {
    /// The blame text after the implementation's path.
    fn describe(self, default_body: bool) -> &'static str {
        match (self, default_body) {
            (Self::Panicked, false) => "panicked during body verification",
            (Self::Failed, false) => "did not satisfy the contract it inherited",
            (Self::RefutationWithheld, false) => {
                "left the contract it inherited unproved (refutation withheld)"
            }
            (Self::Unproved, false) => "did not prove the contract it inherited",
            (Self::Assumed, false) => "had the contract it inherited assumed, not proved",
            (Self::EvidenceGap, false) => {
                "proved the contract it inherited without certified proof evidence"
            }
            (Self::NoVerdict, false) => "reached no verdict on the contract it inherited",
            (Self::NotVerified, false) => "was never verified in this run",
            (Self::Refused, false) => "was refused, not verified",
            (Self::LogicBodyForProgramMethod, _) => {
                "is a logic function, which cannot implement a program trait method"
            }
            (Self::LogicBodyUndischarged, _) => {
                "is a logic function whose body does not establish the postcondition it owes"
            }
            (Self::HandOffUndischarged, false) => {
                "hands a callable to code trust-wp does not verify, and that callable's \
                 obligations were not discharged"
            }
            (Self::OwnAssertionUnproved, false) => "left a proof_assert of its own unproved",
            (Self::Panicked, true) => "default body panicked during verification",
            (Self::Failed, true) => "default body did not satisfy the contract it declares",
            (Self::RefutationWithheld, true) => {
                "default body left the contract it declares unproved (refutation withheld)"
            }
            (Self::Unproved, true) => "default body did not prove the contract it declares",
            (Self::Assumed, true) => {
                "default body had the contract it declares assumed, not proved"
            }
            (Self::EvidenceGap, true) => {
                "default body proved the contract it declares without certified proof evidence"
            }
            (Self::NoVerdict, true) => {
                "default body reached no verdict on the contract it declares"
            }
            (Self::NotVerified, true) => "default body was never verified in this run",
            (Self::Refused, true) => "default body was refused, not verified",
            (Self::HandOffUndischarged, true) => {
                "default body hands a callable to code trust-wp does not verify, and that \
                 callable's obligations were not discharged"
            }
            (Self::OwnAssertionUnproved, true) => {
                "default body left a proof_assert of its own unproved"
            }
            (Self::Withdrawn, false) => "had its credit withdrawn",
            (Self::Withdrawn, true) => "default body had its credit withdrawn",
        }
    }

    /// The blame text after a local item's path, for the postconditions the
    /// item declares itself and hands its callers (D-127).
    fn describe_own(self) -> &'static str {
        match self {
            Self::Panicked => "panicked during body verification",
            Self::Failed => "did not satisfy its own contract",
            Self::RefutationWithheld => "left its own contract unproved (refutation withheld)",
            Self::Unproved => "did not prove its own contract",
            Self::Assumed => "had its own contract assumed, not proved",
            Self::EvidenceGap => "proved its own contract without certified proof evidence",
            Self::NoVerdict => "reached no verdict on its own contract",
            Self::NotVerified => "was never verified in this run",
            Self::Refused => "was refused, not verified",
            Self::LogicBodyForProgramMethod | Self::LogicBodyUndischarged => {
                "is a logic function whose contract a program caller cannot rest on"
            }
            Self::HandOffUndischarged => {
                "hands a callable to code trust-wp does not verify, and that callable's \
                 obligations were not discharged"
            }
            Self::OwnAssertionUnproved => "left a proof_assert of its own unproved",
            Self::Withdrawn => "had its credit withdrawn",
        }
    }
}

/// Run-level trait-contract credit ledger.
#[derive(Default)]
pub(super) struct TraitCreditJoin {
    credited: Vec<CreditedItem>,
    undischarged: UndischargedTraitContracts,
    /// Items the contract loop reached ([`Self::reach`]). An implementation
    /// not in here was never examined.
    examined: HashSet<DefId>,
    /// Every item the contract loop closed: `true` when it came out credited
    /// and clean ([`CounterSnapshot::clean_credit_since`]). The escaped-callable
    /// join reads a closure's verdict here (D-118).
    clean_outcomes: HashMap<DefId, bool>,
    /// Every credited item whose credit a pass after the contract loop took
    /// back: this join, the escaped-callable join, a late verdict on the
    /// item's own assertions. ONE ledger for every withdrawal source, so no
    /// credit is taken back twice and every withdrawn implementation counts as
    /// not discharging the trait contract it owes before any caller of that
    /// contract settles.
    withdrawn: HashSet<DefId>,
    /// The credit graph, built on the first demotion that needs it: the
    /// withdrawal fixpoint may demote several times over one crate.
    graph: Option<CreditGraph>,
    /// Local items that hand their callers postconditions of their own: a
    /// caller's verification conditions assume them at every call (D-127).
    own_contracts: HashSet<DefId>,
    /// Those of [`Self::own_contracts`] their own verification did not
    /// discharge, keyed by the item itself: every credit naming one, through
    /// any chain of calls, rests on nothing.
    own_undischarged: UndischargedTraitContracts,
}

impl TraitCreditJoin {
    /// Start a fresh grant record for one item.
    pub(super) fn begin_item(&self) {
        trait_credit::reset_grants();
    }

    /// Every verification target in `contracts` that declares postconditions
    /// hands them to each of its callers: the credit join below holds them to
    /// its verdict, including one the contract loop never reaches (D-127).
    pub(super) fn register_own_contracts(
        &mut self,
        tcx: TyCtxt<'_>,
        contracts: &[FunctionContract],
        logic_fn_paths: &HashSet<String>,
        logic_fn_has_ensures: &HashSet<String>,
    ) {
        for contract in contracts {
            let target = matches!(
                check_contract_skip(tcx, contract, logic_fn_paths, logic_fn_has_ensures),
                SkipDecision::Verify | SkipDecision::CoroutineBody
            );
            if target && !contract.ensures.is_empty() {
                self.own_contracts.insert(contract.def_id);
            }
        }
    }

    fn record_own_undischarged(&mut self, tcx: TyCtxt<'_>, def_id: DefId, shortfall: Shortfall) {
        if self.own_contracts.contains(&def_id)
            && !self
                .own_undischarged
                .get(def_id)
                .is_some_and(|list| !list.is_empty())
        {
            self.own_undischarged.record(
                def_id,
                def_id,
                tcx.def_path_str(def_id),
                shortfall.describe_own(),
            );
        }
    }

    /// Close one item: bank the credit it was given with the grants it took,
    /// and record it as a non-discharging impl if it owed a trait contract and
    /// did not come out proved.
    ///
    /// Every credited item is banked, grant or no grant: whether a credit
    /// rests on a withdrawn one is decided at the end of the run, when the
    /// whole ledger is known.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn end_item(
        &mut self,
        tcx: TyCtxt<'_>,
        trait_specs: &HashMap<DefId, StdSpec>,
        def_id: DefId,
        def_path: &str,
        before: &CounterSnapshot,
        counters: &VerificationCounters,
        pa_counters: &ProofAssertCounters,
    ) {
        let grants = trait_credit::take_grants();
        self.clean_outcomes
            .insert(def_id, before.clean_credit_since(counters, pa_counters));
        let fn_credits = counters.verified.saturating_sub(before.verified);
        let native_only_credits = counters
            .verified_native_only
            .saturating_sub(before.verified_native_only);
        let axiom_dep_credits = counters
            .verified_with_axiom_deps
            .saturating_sub(before.verified_with_axiom_deps);
        let pa_credits = pa_counters.verified.saturating_sub(before.pa_verified);
        if fn_credits > 0 || axiom_dep_credits > 0 || pa_credits > 0 {
            self.credited.push(CreditedItem {
                def_id,
                def_path: def_path.to_string(),
                grants,
                fn_credits,
                native_only_credits,
                axiom_dep_credits,
                pa_credits,
            });
        }
        if self.own_contracts.contains(&def_id) {
            if let Some(shortfall) = shortfall_since(before, counters, true) {
                self.record_own_undischarged(tcx, def_id, shortfall);
            }
        }
        let Some((trait_method, default_body)) = owed_trait_contract(tcx, trait_specs, def_id)
        else {
            return;
        };
        let owes_postconditions = trait_specs
            .get(&trait_method)
            .is_some_and(|spec| !spec.ensures.is_empty());
        let Some(shortfall) = shortfall_since(before, counters, owes_postconditions) else {
            return;
        };
        self.record_undischarged(tcx, trait_method, def_id, default_body, shortfall);
    }

    /// Close an item the contract loop classified as a logic function. It is
    /// never verified as a program body, so when it implements a contracted
    /// trait method this is where its discharge is decided: a logic function
    /// discharges no PROGRAM trait method's contract (the code that runs is
    /// its erased body), and a trait LOGIC method's contract is left standing
    /// by an impl `logic_impl_discharge` checked and could not prove, whose
    /// declaration's axiom that check has already withdrawn.
    pub(super) fn end_logic_item(
        &mut self,
        tcx: TyCtxt<'_>,
        trait_specs: &HashMap<DefId, StdSpec>,
        def_id: DefId,
        undischarged_logic_impls: &HashSet<DefId>,
    ) {
        let Some((trait_method, default_body)) = owed_trait_contract(tcx, trait_specs, def_id)
        else {
            return;
        };
        let trait_method_is_logic = crate::logic::has_logic_marker(tcx.get_all_attrs(trait_method));
        let shortfall = if !trait_method_is_logic {
            Shortfall::LogicBodyForProgramMethod
        } else if undischarged_logic_impls.contains(&def_id) {
            Shortfall::LogicBodyUndischarged
        } else {
            return;
        };
        self.record_undischarged(tcx, trait_method, def_id, default_body, shortfall);
    }

    /// The contract loop reached `def_id`: it is verified next (and closed by
    /// [`Self::end_item`]), skipped for a benign reason whose obligation is
    /// stated elsewhere (trusted, logic function, bodyless declaration), or
    /// refused ([`Self::refused`]).
    pub(super) fn reach(&mut self, def_id: DefId) {
        self.examined.insert(def_id);
    }

    /// The contract loop REFUSED `def_id` (a coroutine body): it proved
    /// nothing, so a trait contract it owes is undischarged, and a caller
    /// handed that contract loses the credit. Reached is not examined: an
    /// `async fn` implementing a sync trait declaration was otherwise the one
    /// implementation that owed a contract and left it standing without a
    /// shortfall (sync_trait_decl_async_impl_ensures_granted_to_caller.rs).
    pub(super) fn refused(
        &mut self,
        tcx: TyCtxt<'_>,
        trait_specs: &HashMap<DefId, StdSpec>,
        def_id: DefId,
    ) {
        self.record_own_undischarged(tcx, def_id, Shortfall::Refused);
        if let Some((trait_method, default_body)) = owed_trait_contract(tcx, trait_specs, def_id) {
            self.record_undischarged(tcx, trait_method, def_id, default_body, Shortfall::Refused);
        }
    }

    /// Record every implementation of a contracted trait method the contract
    /// loop never reached: stopped short (the adaptive fail-fast stop, the
    /// crate wall-clock budget) or never handed it at all. A caller's grant
    /// rests on that body, and an unexamined body discharged nothing.
    pub(super) fn record_unexamined(
        &mut self,
        tcx: TyCtxt<'_>,
        trait_specs: &HashMap<DefId, StdSpec>,
    ) {
        let mut unexamined: Vec<(DefId, DefId, bool)> = tcx
            .hir_body_owners()
            .map(|local| local.to_def_id())
            .filter(|def_id| !self.examined.contains(def_id))
            .filter_map(|def_id| {
                owed_trait_contract(tcx, trait_specs, def_id)
                    .map(|(trait_method, default_body)| (def_id, trait_method, default_body))
            })
            .collect();
        unexamined.sort_by_key(|(def_id, _, _)| (def_id.krate.as_u32(), def_id.index.as_u32()));
        let mut own: Vec<DefId> = self
            .own_contracts
            .iter()
            .filter(|def_id| !self.clean_outcomes.contains_key(def_id))
            .copied()
            .collect();
        own.sort_by_key(|def_id| (def_id.krate.as_u32(), def_id.index.as_u32()));
        for def_id in own {
            self.record_own_undischarged(tcx, def_id, Shortfall::NotVerified);
        }
        for (def_id, trait_method, default_body) in unexamined {
            self.record_undischarged(
                tcx,
                trait_method,
                def_id,
                default_body,
                Shortfall::NotVerified,
            );
        }
    }

    /// A pass after the contract loop took back `def_id`'s credit for `why`.
    ///
    /// The caller has already subtracted the credit and reported it. What
    /// this adds is the other half of the join: an implementation whose credit
    /// is gone did not discharge the trait contract it owes, so every caller
    /// handed that contract rests on nothing. Returns whether a trait contract
    /// was newly left undischarged, i.e. whether the trait join must run again.
    pub(super) fn withdrawn_later(
        &mut self,
        tcx: TyCtxt<'_>,
        trait_specs: &HashMap<DefId, StdSpec>,
        def_id: DefId,
        why: LateWithdrawal,
    ) -> bool {
        if !self.withdrawn.insert(def_id) {
            return false;
        }
        let shortfall = match why {
            LateWithdrawal::HandOff => Shortfall::HandOffUndischarged,
            LateWithdrawal::OwnAssertion => Shortfall::OwnAssertionUnproved,
        };
        let own_left = self.own_contracts.contains(&def_id);
        self.record_own_undischarged(tcx, def_id, shortfall);
        let Some((trait_method, default_body)) = owed_trait_contract(tcx, trait_specs, def_id)
        else {
            return own_left;
        };
        self.record_undischarged(tcx, trait_method, def_id, default_body, shortfall);
        true
    }

    /// Every item a later pass withdrew so far.
    pub(super) fn withdrawn(&self) -> &HashSet<DefId> {
        &self.withdrawn
    }

    fn record_undischarged(
        &mut self,
        tcx: TyCtxt<'_>,
        trait_method: DefId,
        implementation: DefId,
        default_body: bool,
        shortfall: Shortfall,
    ) {
        self.undischarged.record(
            trait_method,
            implementation,
            tcx.def_path_str(implementation),
            shortfall.describe(default_body),
        );
    }

    pub(super) fn credited(&self) -> &[CreditedItem] {
        &self.credited
    }

    pub(super) fn clean_outcomes(&self) -> &HashMap<DefId, bool> {
        &self.clean_outcomes
    }

    pub(super) fn credited_mut(&mut self) -> &mut Vec<CreditedItem> {
        &mut self.credited
    }

    pub(super) fn undischarged_mut(&mut self) -> &mut UndischargedTraitContracts {
        &mut self.undischarged
    }

    /// Withdraw every verdict that rests, through any chain of calls, on a
    /// trait contract no impl discharged.
    ///
    /// THE RULE: a caller may not assume a trait method's contract unless that
    /// contract is discharged for the impls that can run. trust-wp already
    /// states both obligations — the impl body's (inherited contract) and the
    /// impl contract's (refinement goal) — but a generic call site takes its
    /// grant from the TRAIT method, so grant and obligation sat in different
    /// verdicts. This joins them, and `trait_credit::withdrawals` carries the
    /// join along the call graph: a caller of `gen_read::<W>` rests on
    /// `gen_read`'s contract, which rests on the undischarged `Rd::rd`, and
    /// the one walk that withdraws `gen_read` withdraws that caller too.
    ///
    /// Every `verified` line was printed when its item finished, so each
    /// withdrawal prints its own line naming the item, and a reader of the
    /// output (the adversarial gate's `verified_functions` included) must
    /// subtract it.
    ///
    /// Acceptance-narrowing only: it turns credits into errors and never the
    /// other way round.
    ///
    /// Items already in the withdrawal ledger are skipped, and every item
    /// withdrawn here joins it, so a later join does not take the same credit
    /// back twice. Returns whether anything was withdrawn.
    pub(super) fn demote(
        &mut self,
        tcx: TyCtxt<'_>,
        counters: &mut VerificationCounters,
        pa_counters: &mut ProofAssertCounters,
    ) -> bool {
        let mut any = false;
        // A withdrawn item that declares postconditions of its own leaves
        // them undischarged, which may poison callers neither join reached
        // yet: run both to a fixpoint. Each round that continues records an
        // own contract not recorded before, so the loop ends.
        loop {
            let mut newly = self.demote_trait_grants(tcx, counters, pa_counters);
            newly.extend(self.demote_callee_contracts(tcx, counters, pa_counters));
            any |= !newly.is_empty();
            let mut left = false;
            for def_id in newly {
                let before = self.own_undischarged.get(def_id).map_or(0, <[_]>::len);
                self.record_own_undischarged(tcx, def_id, Shortfall::Withdrawn);
                left |= self.own_undischarged.get(def_id).map_or(0, <[_]>::len) > before;
            }
            if !left {
                return any;
            }
        }
    }

    /// One pass of the trait join: withdraw every credit resting on a trait
    /// contract no impl discharged. Returns the items it withdrew.
    fn demote_trait_grants(
        &mut self,
        tcx: TyCtxt<'_>,
        counters: &mut VerificationCounters,
        pa_counters: &mut ProofAssertCounters,
    ) -> Vec<DefId> {
        if self.undischarged.is_empty() || self.credited.is_empty() {
            return Vec::new();
        }
        let graph = self.graph.get_or_insert_with(|| build_credit_graph(tcx));
        let path_of = |def_id: DefId| tcx.def_path_str(def_id);
        let mut newly = Vec::new();
        for withdrawal in trait_credit::withdrawals(&self.credited, graph, &self.undischarged) {
            let item = withdrawal.item;
            if !self.withdrawn.insert(item.def_id) {
                continue;
            }
            newly.push(item.def_id);
            eprintln!(
                "trust-wp: {} error: verdict withdrawn - {}",
                item.def_path,
                trait_credit::render_withdrawal(&withdrawal, &self.undischarged, path_of)
            );
            eprintln!("  a caller may not assume a trait contract its impl never discharged");
            take_back(item, counters, pa_counters);
        }
        newly
    }

    /// One pass of the callee join (D-127): withdraw every credit resting,
    /// through any chain of calls, on a local item's own postconditions that
    /// item's verification did not discharge. A call assumes its callee's
    /// postconditions; the callee's own lane owes them. A callee refuted in
    /// its own lane (`lend` under `^x == *x`, returning `x`) handed its
    /// caller a false fact, and the caller was credited over it. Returns the
    /// items it withdrew.
    fn demote_callee_contracts(
        &mut self,
        tcx: TyCtxt<'_>,
        counters: &mut VerificationCounters,
        pa_counters: &mut ProofAssertCounters,
    ) -> Vec<DefId> {
        if self.own_undischarged.is_empty() || self.credited.is_empty() {
            return Vec::new();
        }
        let graph = self.graph.get_or_insert_with(|| build_credit_graph(tcx));
        let path_of = |def_id: DefId| tcx.def_path_str(def_id);
        let mut newly = Vec::new();
        for withdrawal in trait_credit::withdrawals(&self.credited, graph, &self.own_undischarged) {
            let item = withdrawal.item;
            if !self.withdrawn.insert(item.def_id) {
                continue;
            }
            newly.push(item.def_id);
            eprintln!(
                "trust-wp: {} error: verdict withdrawn - {}",
                item.def_path,
                trait_credit::render_callee_withdrawal(
                    &withdrawal,
                    &self.own_undischarged,
                    path_of
                )
            );
            eprintln!(
                "  a caller may not assume a callee's contract the callee's own verification did \
                 not discharge"
            );
            take_back(item, counters, pa_counters);
        }
        newly
    }
}

/// Why a pass after the contract loop took an item's credit back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LateWithdrawal {
    /// The escaped-callable join ([`super::escape_credit_join`]).
    HandOff,
    /// A verdict on the item's own `proof_assert!` reached after it settled.
    OwnAssertion,
}

/// Subtract a withdrawn item's credits, each from the counter that counted it,
/// and count them as errors.
pub(super) fn take_back(
    item: &CreditedItem,
    counters: &mut VerificationCounters,
    pa_counters: &mut ProofAssertCounters,
) {
    counters.verified = counters.verified.saturating_sub(item.fn_credits);
    counters.verified_native_only = counters
        .verified_native_only
        .saturating_sub(item.native_only_credits);
    counters.verified_with_axiom_deps = counters
        .verified_with_axiom_deps
        .saturating_sub(item.axiom_dep_credits);
    counters.errors += item.fn_credits + item.axiom_dep_credits;
    pa_counters.verified = pa_counters.verified.saturating_sub(item.pa_credits);
    pa_counters.errors += item.pa_credits;
}

/// Why an implementation examined between `before` and `counters` did not
/// discharge the trait contract it owes, or `None` when it did.
///
/// Positive evidence only: a verdict that is not a certified proof is a
/// shortfall, and so is silence where the contract has postconditions a
/// caller is handed.
fn shortfall_since(
    before: &CounterSnapshot,
    counters: &VerificationCounters,
    owes_postconditions: bool,
) -> Option<Shortfall> {
    Some(if counters.panics > before.panics {
        Shortfall::Panicked
    } else if counters.failed > before.failed {
        Shortfall::Failed
    } else if counters.refutations_withheld > before.refutations_withheld {
        Shortfall::RefutationWithheld
    } else if counters.errors > before.errors || counters.vacuous > before.vacuous {
        // A vacuous verdict is no proof (trait_impl_vacuous_body_grant_kept.rs).
        Shortfall::Unproved
    } else if counters.evidence_gaps > before.evidence_gaps {
        // A discharge whose certification was not checked is not one a
        // caller may lean on: whether the check runs depends on machine load,
        // and the grant would flip with it.
        Shortfall::EvidenceGap
    } else if counters.assumed > before.assumed {
        Shortfall::Assumed
    } else if !before.any_verdict_since(counters) && owes_postconditions {
        // A caller is handed these postconditions; silence paid for none.
        Shortfall::NoVerdict
    } else {
        return None;
    })
}

/// The contracted trait method whose trait-level contract the body of
/// `def_id` owes, and whether that body is the trait's own default body.
///
/// An impl item owes its trait method's contract. A contracted trait method's
/// default body owes the contract it declares: it is the body that runs for
/// every impl that does not override it, including impls in crates this run
/// never sees, and no other run verifies it.
pub(super) fn owed_trait_contract(
    tcx: TyCtxt<'_>,
    trait_specs: &HashMap<DefId, StdSpec>,
    def_id: DefId,
) -> Option<(DefId, bool)> {
    let assoc = tcx.opt_associated_item(def_id)?;
    if let Some(trait_method) = assoc.trait_item_def_id() {
        return trait_specs
            .contains_key(&trait_method)
            .then_some((trait_method, false));
    }
    // `defaultness` is only asked of a trait's own item: on an inherent impl
    // item it ICEs.
    (matches!(assoc.container, rustc_middle::ty::AssocContainer::Trait)
        && trait_specs.contains_key(&def_id)
        && tcx.defaultness(def_id).has_value())
    .then_some((def_id, true))
}

#[cfg(test)]
mod tests {
    use super::{shortfall_since, CounterSnapshot, Shortfall};
    use crate::callbacks::reporting::{ProofAssertCounters, VerificationCounters};

    fn after(change: impl FnOnce(&mut VerificationCounters)) -> Option<Shortfall> {
        let before = VerificationCounters::default();
        let snapshot = CounterSnapshot::take(&before, &ProofAssertCounters::default());
        let mut counters = VerificationCounters::default();
        change(&mut counters);
        shortfall_since(&snapshot, &counters, true)
    }

    #[test]
    fn a_certified_proof_discharges() {
        assert_eq!(after(|c| c.verified += 1), None);
    }

    #[test]
    fn a_proof_without_certified_evidence_discharges_nothing() {
        assert_eq!(
            after(|c| c.evidence_gaps += 1),
            Some(Shortfall::EvidenceGap)
        );
    }

    #[test]
    fn a_refutation_outranks_an_evidence_gap() {
        assert_eq!(
            after(|c| {
                c.evidence_gaps += 1;
                c.failed += 1;
            }),
            Some(Shortfall::Failed)
        );
    }

    #[test]
    fn silence_discharges_no_postcondition() {
        assert_eq!(after(|_| {}), Some(Shortfall::NoVerdict));
    }
}
