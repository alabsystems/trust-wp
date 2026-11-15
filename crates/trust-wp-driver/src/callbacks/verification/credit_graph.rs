// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The local call graph the trait-credit withdrawal walks.
//!
//! A credit rests on every contract its verification conditions were handed,
//! and those contracts belong to what the body NAMES: the function items it
//! calls or passes as values, the closures it builds, the destructors its
//! drops run. The graph is read from the same borrow-checked MIR the
//! verification conditions were generated from (the retained MIR), so a callee
//! the verifier could see is a callee the walk sees.
//!
//! Names are collected from TYPES, not from call terminators: a function item
//! passed to a higher-order function, a closure stored and called later, and a
//! fn pointer reified from an item all leave a `FnDef` or `Closure` type in the
//! body even where no call to it appears. Over-collecting only withdraws more.
//!
//! A trait method's `FnDef` names the one local impl item it resolves to in
//! this body's typing environment, when there is exactly one
//! (`trait_credit::impl_item_that_runs`, the resolver the grant ledger uses
//! for the same call); otherwise it names the trait method, which reaches
//! every implementation.

use std::collections::{BTreeMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        visit::{TyContext, Visitor},
        AggregateKind, Location, Rvalue,
    },
    ty::{Ty, TyCtxt, TyKind},
};

use crate::{
    callbacks::try_get_body_with_context,
    mir_analysis::get_mir_body,
    trait_credit::{impl_item_that_runs, CreditGraph, CreditNode},
};

/// Every local body owner with what its MIR names and the trait method it
/// implements.
pub(super) fn build_credit_graph(tcx: TyCtxt<'_>) -> CreditGraph {
    let mut graph = CreditGraph::new();
    for local in tcx.hir_body_owners() {
        let def_id = local.to_def_id();
        let mentions = try_get_body_with_context(tcx, local).map(|with_facts| {
            let body = get_mir_body(&with_facts);
            let mut collector = MentionCollector {
                tcx,
                owner: body.source.def_id(),
                named: BTreeMap::new(),
                seen_adts: HashSet::new(),
            };
            collector.visit_body(body);
            collector.named.into_values().collect()
        });
        let implements = tcx
            .opt_associated_item(def_id)
            .and_then(|assoc| assoc.trait_item_def_id());
        graph.insert(
            def_id,
            CreditNode {
                mentions,
                implements,
            },
        );
    }
    graph
}

struct MentionCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// The body being read: its typing environment resolves trait calls.
    owner: DefId,
    /// Keyed for a deterministic order (`DefId` has none of its own).
    named: BTreeMap<(u32, u32), DefId>,
    /// Local ADTs whose field types were already walked (recursive types).
    seen_adts: HashSet<DefId>,
}

impl<'tcx> MentionCollector<'tcx> {
    fn name(&mut self, def_id: DefId) {
        self.named
            .insert((def_id.krate.as_u32(), def_id.index.as_u32()), def_id);
    }

    fn note_ty(&mut self, ty: Ty<'tcx>) {
        for arg in ty.walk() {
            let Some(inner) = arg.as_type() else {
                continue;
            };
            match inner.kind() {
                TyKind::FnDef(def_id, args) => self.name(
                    impl_item_that_runs(self.tcx, *def_id, args.skip_binder(), self.owner)
                        .unwrap_or(*def_id),
                ),
                TyKind::Closure(def_id, _)
                | TyKind::Coroutine(def_id, _)
                | TyKind::CoroutineClosure(def_id, _) => self.name(*def_id),
                TyKind::Adt(adt, args) => {
                    // A drop of this value runs its destructor, and a drop of a
                    // local aggregate runs its fields' destructors, although no
                    // call to either appears in the body.
                    if let Some(dtor) = adt.destructor(self.tcx) {
                        self.name(dtor.did);
                    }
                    if adt.did().is_local() && self.seen_adts.insert(adt.did()) {
                        let fields: Vec<Ty<'tcx>> = adt
                            .all_fields()
                            .map(|field| field.ty(self.tcx, *args).skip_norm_wip())
                            .collect();
                        for field_ty in fields {
                            self.note_ty(field_ty);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for MentionCollector<'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>, _context: TyContext) {
        self.note_ty(ty);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Aggregate(kind, _) = rvalue {
            match **kind {
                AggregateKind::Closure(def_id, _)
                | AggregateKind::Coroutine(def_id, _)
                | AggregateKind::CoroutineClosure(def_id, _) => self.name(def_id),
                _ => {}
            }
        }
        self.super_rvalue(rvalue, location);
    }
}
