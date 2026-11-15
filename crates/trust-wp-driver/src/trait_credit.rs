// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trait-contract credit: who was handed a trait method's contract, and who
//! owed it.
//!
//! A generic call `t.rd()` under `T: Rd` resolves to the TRAIT method's
//! `DefId`, so the caller is handed the trait-level contract — a fact about
//! whichever impl actually runs. That fact is only true if the impl discharged
//! it. trust-wp does state that obligation (an impl without its own clauses
//! inherits the trait's and is verified against them; an impl with its own
//! clauses owes the refinement goal), but until now nothing connected the two:
//! an impl could come out `unknown`, `FAILED`, or with its refinement REFUSED,
//! and every caller kept the credit it took from that same contract.
//!
//! This module is the connection. It records, per verification item, which
//! contracted trait methods that item's verification conditions took a grant
//! from; the verification loop records which impls failed to discharge; and
//! the demotion pass at the end of the run withdraws every credit that rests
//! on an undischarged contract.
//!
//! Direction of travel: this only ever REMOVES accept paths. A trait method
//! with no undischarged implementation poisons nothing, and an item that took
//! no trait grant is never touched.
//!
//! An IMPLEMENTATION of a contracted trait method is every body this crate
//! owns that can run for it: each local impl item, and the trait's own default
//! body. A call the resolver pins to one local impl item rests on that impl
//! alone; every other call to a trait method rests on all of them.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Operand},
    ty::{GenericArgs, TyCtxt},
};
use trust_wp_driver::StdSpec;

thread_local! {
    /// Contracted trait methods whose spec has been handed to the item
    /// currently being verified.
    static GRANTS: RefCell<HashSet<DefId>> = RefCell::new(HashSet::new());
}

/// Start a fresh grant record for one verification item.
pub(crate) fn reset_grants() {
    GRANTS.with(|grants| grants.borrow_mut().clear());
}

/// Take (and clear) the grants recorded since the last [`reset_grants`].
pub(crate) fn take_grants() -> HashSet<DefId> {
    GRANTS.with(|grants| std::mem::take(&mut *grants.borrow_mut()))
}

/// Record that the item under verification was handed a trait-level contract
/// whose obligation `owed_by` pays: the one impl item the call runs, or the
/// trait method itself when the call may run any implementation.
fn note_grant(owed_by: DefId) {
    GRANTS.with(|grants| {
        grants.borrow_mut().insert(owed_by);
    });
}

/// The local impl item that runs when `trait_method` is called with `args`
/// from the body of `caller`, when resolution selects exactly one.
///
/// `None` whenever that is not known: a receiver still generic, a `dyn` call,
/// the trait's own default body, a foreign item, an argument list that does
/// not normalize. `None` sends the caller to the trait method, which reaches
/// every implementation, so this can only ever narrow a withdrawal to the
/// code that actually runs.
///
/// The ONE resolver behind both readings of a call: the grant ledger
/// ([`GrantSite`]) and the credit graph's walk over the same MIR name what it
/// returns, in the typing environment of the body that makes the call.
pub(crate) fn impl_item_that_runs<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_method: DefId,
    args: GenericArgs<'tcx>,
    caller: DefId,
) -> Option<DefId> {
    use rustc_middle::ty::{Instance, InstanceKind, TypeVisitableExt, TypingEnv};
    if tcx.trait_of_assoc(trait_method).is_none() || tcx.impl_of_assoc(trait_method).is_some() {
        return None;
    }
    if args.has_escaping_bound_vars() {
        return None;
    }
    let typing_env = TypingEnv::post_analysis(tcx, caller);
    // Resolution normalizes and may reach trait selection on shapes the
    // verifier never otherwise asks about; a panic there is an unknown callee,
    // not a crash.
    let instance = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let args = tcx
            .try_normalize_erasing_regions(
                typing_env,
                rustc_middle::ty::set_aliases_to_non_rigid(tcx, args),
            )
            .ok()?;
        Instance::try_resolve(tcx, typing_env, trait_method, args)
            .ok()
            .flatten()
    }))
    .ok()
    .flatten()?;
    let InstanceKind::Item(item) = instance.def else {
        return None;
    };
    (item != trait_method && item.is_local() && tcx.impl_of_assoc(item).is_some()).then_some(item)
}

/// The call a spec lookup is made for: its callee operand in the body that
/// makes it.
#[derive(Clone, Copy)]
pub(crate) struct GrantSite<'a, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) body: &'a Body<'tcx>,
    pub(crate) func: &'a Operand<'tcx>,
}

impl GrantSite<'_, '_> {
    /// [`impl_item_that_runs`] for this call, when its operand is the direct
    /// `FnDef` of `trait_method`. A callee reached any other way (a fn-pointer
    /// local the lookup backtracked through) names the trait method.
    fn impl_item_that_runs(&self, trait_method: DefId) -> Option<DefId> {
        let Operand::Constant(constant) = self.func else {
            return None;
        };
        let rustc_middle::ty::TyKind::FnDef(callee, args) = constant.const_.ty().kind() else {
            return None;
        };
        if *callee != trait_method {
            return None;
        }
        impl_item_that_runs(
            self.tcx,
            trait_method,
            args.skip_binder(),
            self.body.source.def_id(),
        )
    }
}

/// The direct by-`DefId` spec lookup every call-site resolution chain starts
/// with, with the trait-grant record attached.
///
/// `user_specs` still wins over `trait_specs` — a trait method with a default
/// body appears in both, and the item-level contract is the one the body was
/// verified against. The grant is recorded whenever the callee IS a contracted
/// trait method either way: for a default method the code that runs at a
/// generic call site is whichever impl the caller instantiates, not the
/// default body, so the caller is still leaning on the trait-level contract.
pub(crate) fn lookup_user_or_trait_spec<'a>(
    user_specs: &'a HashMap<DefId, StdSpec>,
    trait_specs: &'a HashMap<DefId, StdSpec>,
    def_id: DefId,
    site: GrantSite<'_, '_>,
) -> Option<&'a StdSpec> {
    lookup_noting_grant(user_specs, trait_specs, def_id, || {
        site.impl_item_that_runs(def_id)
    })
}

/// [`lookup_user_or_trait_spec`] with the call's resolution supplied.
fn lookup_noting_grant<'a>(
    user_specs: &'a HashMap<DefId, StdSpec>,
    trait_specs: &'a HashMap<DefId, StdSpec>,
    def_id: DefId,
    impl_item_that_runs: impl FnOnce() -> Option<DefId>,
) -> Option<&'a StdSpec> {
    let trait_spec = trait_specs.get(&def_id);
    if trait_spec.is_some() {
        note_grant(impl_item_that_runs().unwrap_or(def_id));
    }
    user_specs.get(&def_id).or(trait_spec)
}

/// Why one implementation of a contracted trait method did not discharge it.
#[derive(Debug, Clone)]
pub(crate) struct UndischargedImpl {
    /// The body that owed the contract: an impl item, or the trait method
    /// itself for its default body.
    pub(crate) implementation: DefId,
    /// How the implementation is named in a blame line.
    pub(crate) impl_path: String,
    /// Which obligation was left standing.
    pub(crate) reason: &'static str,
}

/// Per-trait-method record of implementations that left the contract standing.
#[derive(Debug, Default)]
pub(crate) struct UndischargedTraitContracts {
    by_trait_method: HashMap<DefId, Vec<UndischargedImpl>>,
}

impl UndischargedTraitContracts {
    pub(crate) fn record(
        &mut self,
        trait_method: DefId,
        implementation: DefId,
        impl_path: String,
        reason: &'static str,
    ) {
        self.by_trait_method
            .entry(trait_method)
            .or_default()
            .push(UndischargedImpl {
                implementation,
                impl_path,
                reason,
            });
    }

    /// The trait methods `implementation` left undischarged, with why.
    fn left_by(&self, implementation: DefId) -> Vec<(DefId, &UndischargedImpl)> {
        let mut out: Vec<(DefId, &UndischargedImpl)> = self
            .by_trait_method
            .iter()
            .flat_map(|(trait_method, list)| list.iter().map(move |u| (*trait_method, u)))
            .filter(|(_, u)| u.implementation == implementation)
            .collect();
        out.sort_by_key(|(trait_method, _)| def_id_key(*trait_method));
        out
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.by_trait_method.is_empty()
    }

    pub(crate) fn get(&self, trait_method: DefId) -> Option<&[UndischargedImpl]> {
        self.by_trait_method.get(&trait_method).map(Vec::as_slice)
    }
}

/// An item that was credited a verdict.
///
/// Every credited item is recorded, not only those that took a trait grant
/// directly: a credit one ordinary call away from a withdrawn one rests on it
/// just as much, and the withdrawal walk can only reach an item it was told
/// about.
#[derive(Debug)]
pub(crate) struct CreditedItem {
    pub(crate) def_id: DefId,
    pub(crate) def_path: String,
    /// What pays for each trait-level contract this item's verification
    /// conditions were handed (the call-site ledger): the impl item the call
    /// was pinned to, or the trait method when it may run any implementation.
    pub(crate) grants: HashSet<DefId>,
    /// Function-contract verdicts credited to this item as `verified`.
    pub(crate) fn_credits: usize,
    /// Of `fn_credits`, those on proof authority only ay can re-check.
    pub(crate) native_only_credits: usize,
    /// Function-contract verdicts credited to this item as `verified*`. A
    /// separate counter from `fn_credits`, so a withdrawal takes back each
    /// from the counter that counted it.
    pub(crate) axiom_dep_credits: usize,
    /// `proof_assert!` verdicts credited to this item.
    pub(crate) pa_credits: usize,
}

/// What the withdrawal walk knows about one local body.
#[derive(Debug, Default, Clone)]
pub(crate) struct CreditNode {
    /// Every function item, closure and destructor the body names, or `None`
    /// when its MIR could not be read. An unread body is treated as reaching
    /// every undischarged contract: the walk cannot show it does not.
    pub(crate) mentions: Option<Vec<DefId>>,
    /// The trait method this body implements. A body that reaches an
    /// undischarged contract leaves the trait method it implements
    /// undischarged too, whether or not that trait method is contracted: a
    /// caller that names the trait method may be handed this body's contract.
    pub(crate) implements: Option<DefId>,
}

/// The local call graph the withdrawal walk runs over, keyed by body owner.
/// A `DefId` with no entry is a leaf: a foreign item, or a local item with no
/// body (a bodyless trait method, a constructor).
pub(crate) type CreditGraph = HashMap<DefId, CreditNode>;

/// The next hop from a node toward what poisoned it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Hop {
    /// A trait method some implementation left undischarged, or that
    /// implementation itself.
    Undischarged,
    /// A body the walk could not read.
    Unread,
    /// Through a node this one names (or was handed the contract of).
    Via(DefId),
}

/// Where a withdrawal's chain ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ChainEnd {
    Undischarged(DefId),
    Unread(DefId),
}

/// One withdrawn credit and the chain it rests on.
#[derive(Debug)]
pub(crate) struct Withdrawal<'a> {
    pub(crate) item: &'a CreditedItem,
    /// The nodes between the item and the chain's end, nearest first; empty
    /// when the item names the end directly.
    pub(crate) through: Vec<DefId>,
    pub(crate) end: ChainEnd,
}

fn def_id_key(def_id: DefId) -> (u32, u32) {
    (def_id.krate.as_u32(), def_id.index.as_u32())
}

/// Every credit that rests, through any chain of calls, on a trait contract
/// some impl left undischarged.
///
/// THE ONE RULE, for a credit one call away and ten calls away alike: an item
/// is withdrawn when anything it names reaches an undischarged trait method
/// through the graph. A body reaches what it names; a trait method reaches
/// what any of its impls reaches; an implementation that did not discharge
/// the contract is poisoned itself. The item's own ledger grants count as
/// names, so the direct case (`gen_read` handed `Rd::rd`) and the transitive
/// case (`go` naming `gen_read`) are decided by the same walk.
///
/// The walk is over names, not over which contracts a verification condition
/// actually consumed, so it may withdraw a credit that did not need the
/// poisoned contract. That is the only direction it may err in. With no
/// undischarged contract it withdraws nothing.
pub(crate) fn withdrawals<'a>(
    credited: &'a [CreditedItem],
    graph: &CreditGraph,
    undischarged: &UndischargedTraitContracts,
) -> Vec<Withdrawal<'a>> {
    if undischarged.is_empty() {
        return Vec::new();
    }
    let mut preds: HashMap<DefId, Vec<DefId>> = HashMap::new();
    for (owner, node) in graph {
        for named in node.mentions.iter().flatten() {
            preds.entry(*named).or_default().push(*owner);
        }
        if let Some(trait_method) = node.implements {
            preds.entry(*owner).or_default().push(trait_method);
        }
    }
    for item in credited {
        for grant in &item.grants {
            preds.entry(*grant).or_default().push(item.def_id);
        }
    }
    for list in preds.values_mut() {
        list.sort_by_key(|d| def_id_key(*d));
        list.dedup();
    }

    // A call pinned to one impl item names that item, not the trait method,
    // so the implementation is a seed in its own right; the trait method is
    // one too, for every call that may run any implementation.
    let mut seeds: Vec<(DefId, Hop)> = undischarged
        .by_trait_method
        .iter()
        .flat_map(|(trait_method, list)| {
            std::iter::once(*trait_method).chain(list.iter().map(|u| u.implementation))
        })
        .map(|d| (d, Hop::Undischarged))
        .chain(
            graph
                .iter()
                .filter(|(_, node)| node.mentions.is_none())
                .map(|(d, _)| (*d, Hop::Unread)),
        )
        .collect();
    seeds.sort_by_key(|(d, hop)| (matches!(hop, Hop::Unread), def_id_key(*d)));

    // Breadth-first from the poison, so each node's hop is on a shortest chain.
    let mut reach: HashMap<DefId, (Hop, usize)> = HashMap::new();
    let mut queue = std::collections::VecDeque::new();
    for (d, hop) in seeds {
        if reach.insert(d, (hop, 0)).is_none() {
            queue.push_back(d);
        }
    }
    while let Some(node) = queue.pop_front() {
        let depth = reach[&node].1;
        for pred in preds.get(&node).into_iter().flatten() {
            if !reach.contains_key(pred) {
                reach.insert(*pred, (Hop::Via(node), depth + 1));
                queue.push_back(*pred);
            }
        }
    }

    let mut out = Vec::new();
    for item in credited {
        // An item's own node is not consulted: a trait method with a default
        // body is itself a seed when an impl fails it, which says nothing
        // about the default body. Only what the item NAMES can poison it.
        let names: Vec<DefId> = match graph.get(&item.def_id) {
            Some(CreditNode {
                mentions: Some(mentions),
                ..
            }) => mentions.iter().chain(item.grants.iter()).copied().collect(),
            _ => {
                out.push(Withdrawal {
                    item,
                    through: Vec::new(),
                    end: ChainEnd::Unread(item.def_id),
                });
                continue;
            }
        };
        let Some(first) = names
            .into_iter()
            .filter(|d| reach.contains_key(d))
            .min_by_key(|d| (reach[d].1, def_id_key(*d)))
        else {
            continue;
        };
        let mut through = Vec::new();
        let mut at = first;
        let end = loop {
            match reach[&at].0 {
                Hop::Undischarged => break ChainEnd::Undischarged(at),
                Hop::Unread => break ChainEnd::Unread(at),
                Hop::Via(next) => {
                    through.push(at);
                    at = next;
                }
            }
        };
        out.push(Withdrawal { item, through, end });
    }
    out
}

/// The impls that left `trait_method` undischarged, rendered for a blame line.
pub(crate) fn culprits(undischarged: &UndischargedTraitContracts, trait_method: DefId) -> String {
    undischarged
        .get(trait_method)
        .unwrap_or_default()
        .iter()
        .map(|u| format!("`{}` {}", u.impl_path, u.reason))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The blame text of one withdrawal whose chain ends at a callee's OWN
/// contract (a local item's postconditions its verification did not
/// discharge), after `verdict withdrawn - `.
pub(crate) fn render_callee_withdrawal(
    withdrawal: &Withdrawal<'_>,
    undischarged: &UndischargedTraitContracts,
    path_of: impl Fn(DefId) -> String,
) -> String {
    let through = if withdrawal.through.is_empty() {
        String::new()
    } else {
        let hops = withdrawal
            .through
            .iter()
            .map(|d| format!("`{}`", path_of(*d)))
            .collect::<Vec<_>>()
            .join(" -> ");
        format!("through {hops}, ")
    };
    match withdrawal.end {
        ChainEnd::Undischarged(callee) => format!(
            "{through}it assumed the contract of `{}` ({})",
            path_of(callee),
            culprits(undischarged, callee)
        ),
        ChainEnd::Unread(owner) => format!(
            "{through}it reaches `{}`, whose MIR the credit walk could not read while a callee's \
             own contract is undischarged",
            path_of(owner)
        ),
    }
}

/// The blame text of one withdrawal, after `verdict withdrawn - `.
pub(crate) fn render_withdrawal(
    withdrawal: &Withdrawal<'_>,
    undischarged: &UndischargedTraitContracts,
    path_of: impl Fn(DefId) -> String,
) -> String {
    let through = if withdrawal.through.is_empty() {
        String::new()
    } else {
        let hops = withdrawal
            .through
            .iter()
            .map(|d| format!("`{}`", path_of(*d)))
            .collect::<Vec<_>>()
            .join(" -> ");
        format!("through {hops}, ")
    };
    match withdrawal.end {
        ChainEnd::Undischarged(end) if undischarged.get(end).is_some() => format!(
            "{through}it assumed trait method contract `{}` ({})",
            path_of(end),
            culprits(undischarged, end)
        ),
        ChainEnd::Undischarged(implementation) => {
            let left = undischarged.left_by(implementation);
            let mut contracts = left
                .iter()
                .map(|(trait_method, _)| format!("`{}`", path_of(*trait_method)))
                .collect::<Vec<_>>();
            contracts.dedup();
            let why = left
                .iter()
                .map(|(_, u)| format!("`{}` {}", u.impl_path, u.reason))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "{through}it assumed trait method contract {} where `{}` runs ({why})",
                contracts.join(", "),
                path_of(implementation)
            )
        }
        ChainEnd::Unread(owner) => format!(
            "{through}it reaches `{}`, whose MIR the credit walk could not read while a trait \
             method contract is undischarged",
            path_of(owner)
        ),
    }
}

#[cfg(test)]
mod tests {
    use rustc_hir::def_id::{CrateNum, DefId, DefIndex};

    use super::*;

    fn def(index: u32) -> DefId {
        DefId {
            krate: CrateNum::from_u32(0),
            index: DefIndex::from_u32(index),
        }
    }

    fn spec() -> StdSpec {
        StdSpec {
            inv_requires: Vec::new(),
            capture_inv_requires: Vec::new(),
            requires: Vec::new(),
            ensures: vec!["result".to_string()],
            param_names: None,
        }
    }

    #[test]
    fn a_trait_spec_hit_is_recorded_and_a_user_only_hit_is_not() {
        reset_grants();
        let mut user = HashMap::new();
        let mut traits = HashMap::new();
        user.insert(def(1), spec());
        traits.insert(def(2), spec());

        assert!(lookup_noting_grant(&user, &traits, def(1), || None).is_some());
        assert!(take_grants().is_empty(), "a user-only spec grants nothing");

        reset_grants();
        assert!(lookup_noting_grant(&user, &traits, def(2), || None).is_some());
        assert_eq!(take_grants(), HashSet::from([def(2)]));

        reset_grants();
        assert!(lookup_noting_grant(&user, &traits, def(3), || None).is_none());
        assert!(take_grants().is_empty(), "a miss grants nothing");
    }

    #[test]
    fn a_grant_pinned_to_one_impl_item_names_that_item() {
        // The spec handed over is still the trait method's; what changes is
        // whose obligation pays for it.
        reset_grants();
        let user = HashMap::new();
        let mut traits = HashMap::new();
        traits.insert(def(2), spec());
        assert!(lookup_noting_grant(&user, &traits, def(2), || Some(def(21))).is_some());
        assert_eq!(take_grants(), HashSet::from([def(21)]));
    }

    #[test]
    fn a_default_method_grants_even_though_the_item_spec_wins() {
        // A contracted trait method with a default body is in BOTH tables. The
        // item-level spec is the one applied, but the callee at a generic call
        // site is still whichever impl the caller instantiates, so the grant
        // has to be recorded.
        reset_grants();
        let mut user = HashMap::new();
        let mut traits = HashMap::new();
        user.insert(def(7), spec());
        traits.insert(def(7), spec());
        assert!(lookup_noting_grant(&user, &traits, def(7), || None).is_some());
        assert_eq!(take_grants(), HashSet::from([def(7)]));
    }

    fn credited(index: u32, grants: &[u32]) -> CreditedItem {
        CreditedItem {
            def_id: def(index),
            def_path: format!("item{index}"),
            grants: grants.iter().map(|g| def(*g)).collect(),
            fn_credits: 1,
            native_only_credits: 0,
            axiom_dep_credits: 0,
            pa_credits: 0,
        }
    }

    fn body(mentions: &[u32]) -> CreditNode {
        CreditNode {
            mentions: Some(mentions.iter().map(|m| def(*m)).collect()),
            implements: None,
        }
    }

    fn path(d: DefId) -> String {
        format!("n{}", d.index.as_u32())
    }

    /// `Rd::rd` = 2 (undischarged by `<W as Rd>::rd` = 3), `gen_read` = 10
    /// names it, `go` = 11 names `gen_read`, `go2` = 12 names `go`, `other` =
    /// 13 names nothing poisoned.
    fn s67_shape() -> (Vec<CreditedItem>, CreditGraph, UndischargedTraitContracts) {
        let mut undischarged = UndischargedTraitContracts::default();
        undischarged.record(
            def(2),
            def(3),
            "<W as Rd>::rd".to_string(),
            "did not prove it",
        );
        let credited = vec![
            credited(10, &[2]),
            credited(11, &[]),
            credited(12, &[]),
            credited(13, &[]),
        ];
        let graph = CreditGraph::from([
            (def(10), body(&[2])),
            (def(11), body(&[10])),
            (def(12), body(&[11])),
            (def(13), body(&[14])),
            (def(14), body(&[])),
        ]);
        (credited, graph, undischarged)
    }

    #[test]
    fn a_direct_grant_and_a_credit_calls_away_are_withdrawn_by_one_walk() {
        let (credited, graph, undischarged) = s67_shape();
        let out = withdrawals(&credited, &graph, &undischarged);
        let by_item: HashMap<u32, &Withdrawal<'_>> = out
            .iter()
            .map(|w| (w.item.def_id.index.as_u32(), w))
            .collect();
        assert_eq!(by_item.len(), 3, "{out:?}");
        assert!(
            !by_item.contains_key(&13),
            "a credit that reaches nothing poisoned stands"
        );

        assert_eq!(by_item[&10].through, Vec::<DefId>::new());
        assert_eq!(by_item[&10].end, ChainEnd::Undischarged(def(2)));
        assert_eq!(by_item[&11].through, vec![def(10)]);
        assert_eq!(by_item[&12].through, vec![def(11), def(10)]);
        assert_eq!(by_item[&12].end, ChainEnd::Undischarged(def(2)));

        let text = render_withdrawal(by_item[&12], &undischarged, path);
        assert_eq!(
            text,
            "through `n11` -> `n10`, it assumed trait method contract `n2` \
             (`<W as Rd>::rd` did not prove it)"
        );
        let direct = render_withdrawal(by_item[&10], &undischarged, path);
        assert_eq!(
            direct,
            "it assumed trait method contract `n2` (`<W as Rd>::rd` did not prove it)"
        );
    }

    #[test]
    fn the_ledger_grant_alone_withdraws_without_a_graph_edge() {
        // The ledger and the walk are one relation: a grant the MIR walk did
        // not see still poisons the item it was handed to.
        let (credited, mut graph, undischarged) = s67_shape();
        graph.insert(def(10), body(&[]));
        let out = withdrawals(&credited, &graph, &undischarged);
        let items: HashSet<u32> = out.iter().map(|w| w.item.def_id.index.as_u32()).collect();
        assert_eq!(items, HashSet::from([10, 11, 12]));
    }

    #[test]
    fn nothing_is_withdrawn_when_every_contract_was_discharged() {
        let (credited, graph, _) = s67_shape();
        let out = withdrawals(&credited, &graph, &UndischargedTraitContracts::default());
        assert!(out.is_empty(), "{out:?}");
    }

    #[test]
    fn a_poisoned_impl_body_poisons_its_trait_method_for_every_caller() {
        // `m` = 20 is a trait method no impl failed directly. Its impl 21's
        // body names `go` = 11, which rests on the undischarged `Rd::rd`, so
        // the impl did not establish `m`'s contract either, and a generic
        // caller 22 of `m` is withdrawn.
        let (mut credited, mut graph, undischarged) = s67_shape();
        graph.insert(
            def(21),
            CreditNode {
                mentions: Some(vec![def(11)]),
                implements: Some(def(20)),
            },
        );
        graph.insert(def(22), body(&[20]));
        credited.push(self::credited(21, &[]));
        credited.push(self::credited(22, &[]));
        let out = withdrawals(&credited, &graph, &undischarged);
        let w = out
            .iter()
            .find(|w| w.item.def_id == def(22))
            .expect("the caller of the poisoned trait method is withdrawn");
        assert_eq!(w.through, vec![def(20), def(21), def(11), def(10)]);
        assert_eq!(w.end, ChainEnd::Undischarged(def(2)));
    }

    #[test]
    fn a_trait_default_body_is_judged_by_what_it_names_not_by_its_own_seed() {
        // Trait method 2 has a default body naming nothing poisoned. An impl
        // failing the trait contract says nothing about that body.
        let (mut credited, mut graph, undischarged) = s67_shape();
        graph.insert(def(2), body(&[14]));
        credited.push(self::credited(2, &[]));
        let out = withdrawals(&credited, &graph, &undischarged);
        assert!(out.iter().all(|w| w.item.def_id != def(2)), "{out:?}");
        // ...but a default body that calls itself at `Self` is handed the
        // contract an impl failed.
        graph.insert(def(2), body(&[2]));
        let out = withdrawals(&credited, &graph, &undischarged);
        assert!(out.iter().any(|w| w.item.def_id == def(2)), "{out:?}");
    }

    #[test]
    fn an_unread_body_on_the_way_withdraws_rather_than_guesses() {
        let (mut credited, mut graph, undischarged) = s67_shape();
        graph.insert(
            def(30),
            CreditNode {
                mentions: None,
                implements: None,
            },
        );
        graph.insert(def(31), body(&[30]));
        credited.push(self::credited(31, &[]));
        // A credited item the graph does not know is unread too.
        credited.push(self::credited(32, &[]));
        let out = withdrawals(&credited, &graph, &undischarged);
        let ends: HashMap<u32, ChainEnd> = out
            .iter()
            .map(|w| (w.item.def_id.index.as_u32(), w.end))
            .collect();
        assert_eq!(ends[&31], ChainEnd::Unread(def(30)));
        assert_eq!(ends[&32], ChainEnd::Unread(def(32)));
        assert!(!ends.contains_key(&13));
    }

    fn impl_body(implements: u32, mentions: &[u32]) -> CreditNode {
        CreditNode {
            mentions: Some(mentions.iter().map(|m| def(*m)).collect()),
            implements: Some(def(implements)),
        }
    }

    /// `Rd::rd` = 2; `<W as Rd>::rd` = 3 failed it, `<V as Rd>::rd` = 4
    /// honours it. `go_vd` = 30 calls `V.rd()` (pinned to 4), `go_wd` = 31
    /// calls `W.rd()` (pinned to 3), `gen_read` = 32 calls `t.rd()` (the trait
    /// method: any implementation).
    fn two_impls_shape() -> (Vec<CreditedItem>, CreditGraph, UndischargedTraitContracts) {
        let mut undischarged = UndischargedTraitContracts::default();
        undischarged.record(
            def(2),
            def(3),
            "<W as Rd>::rd".to_string(),
            "did not prove it",
        );
        let credited = vec![credited(30, &[4]), credited(31, &[3]), credited(32, &[2])];
        let graph = CreditGraph::from([
            (def(3), impl_body(2, &[])),
            (def(4), impl_body(2, &[])),
            (def(30), body(&[4])),
            (def(31), body(&[3])),
            (def(32), body(&[2])),
        ]);
        (credited, graph, undischarged)
    }

    fn withdrawn_ends(out: &[Withdrawal<'_>]) -> HashMap<u32, ChainEnd> {
        out.iter()
            .map(|w| (w.item.def_id.index.as_u32(), w.end))
            .collect()
    }

    #[test]
    fn a_call_pinned_to_an_honouring_impl_stands_while_another_impl_fails() {
        let (credited, graph, undischarged) = two_impls_shape();
        let out = withdrawals(&credited, &graph, &undischarged);
        let ends = withdrawn_ends(&out);
        assert!(!ends.contains_key(&30), "{out:?}");
        assert_eq!(ends[&31], ChainEnd::Undischarged(def(3)));
        assert_eq!(ends[&32], ChainEnd::Undischarged(def(2)));

        let pinned = out.iter().find(|w| w.item.def_id == def(31)).unwrap();
        assert_eq!(
            render_withdrawal(pinned, &undischarged, path),
            "it assumed trait method contract `n2` where `n3` runs \
             (`<W as Rd>::rd` did not prove it)"
        );
    }

    #[test]
    fn a_pinned_impl_whose_body_rests_on_the_poison_is_poisoned_itself() {
        // `<V as Rd>::rd` = 4 honours `Rd::rd` only by calling `gen_read` = 32,
        // which rests on the undischarged contract.
        let (credited, mut graph, undischarged) = two_impls_shape();
        graph.insert(def(4), impl_body(2, &[32]));
        let out = withdrawals(&credited, &graph, &undischarged);
        let w = out
            .iter()
            .find(|w| w.item.def_id == def(30))
            .unwrap_or_else(|| panic!("`go_vd` must be withdrawn: {out:?}"));
        assert_eq!(w.through, vec![def(4), def(32)]);
        assert_eq!(w.end, ChainEnd::Undischarged(def(2)));
    }

    #[test]
    fn an_undischarged_default_body_poisons_the_trait_method_not_an_override() {
        // The trait's default body (the trait method's own `DefId`) failed.
        // A generic call may run it; a call pinned to an overriding impl
        // cannot.
        let (credited, graph, _) = two_impls_shape();
        let mut undischarged = UndischargedTraitContracts::default();
        undischarged.record(
            def(2),
            def(2),
            "Rd::rd (default body)".to_string(),
            "failed",
        );
        let out = withdrawals(&credited, &graph, &undischarged);
        let ends = withdrawn_ends(&out);
        assert_eq!(
            ends.get(&32),
            Some(&ChainEnd::Undischarged(def(2))),
            "{out:?}"
        );
        assert!(!ends.contains_key(&30), "{out:?}");
        assert!(!ends.contains_key(&31), "{out:?}");
    }
}
