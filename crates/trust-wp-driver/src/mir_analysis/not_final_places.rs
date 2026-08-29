// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Backward dataflow analysis for final reborrow detection (#2150).
//!
//! Determines whether a mutable reborrow is "final" (source not used afterward).
//! Final reborrows inherit the parent's prophecy variable, enabling the
//! MutRefVarNames 6→2 reduction. Adapted from Creusot's `analysis/not_final_places.rs`.
//!
//! Domain: `MixedBitSet<PlaceId>` — membership means NOT final.
//! Direction: Backward. Bottom: empty (all final).
//! Key rule: writing to `x` kills `*x` (one deref deeper becomes final).

use std::collections::{hash_map, HashMap};

use rustc_abi::FieldIdx;
use rustc_index::{bit_set::MixedBitSet, IndexVec};
use rustc_middle::{
    mir::{
        visit::{MutatingUseContext, NonMutatingUseContext, NonUseContext, PlaceContext, Visitor},
        Body, Local, Location, Place, PlaceRef, Statement, Terminator, TerminatorEdges,
        TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{fmt::DebugWithContext, Analysis, Backward, GenKill, ResultsCursor};

rustc_index::newtype_index! {
    /// An index identifying a tracked place in the `NotFinalPlaces` analysis.
    pub struct PlaceId {}
}

/// Information about a tracked place in the analysis.
#[derive(Clone, Debug)]
struct PlaceInfo<'tcx> {
    /// The original MIR place reference (used by `DebugWithContext` impl).
    place: PlaceRef<'tcx>,
    /// Number of mutable dereferences in this place's projection.
    deref_count: usize,
    /// Set of places that are strict sub-places of this place
    /// (same local, this place's projection is a strict prefix of theirs).
    subplaces: MixedBitSet<PlaceId>,
    /// Set of places that conflict with this place but are NOT sub-places
    /// (same local, their projection is a strict prefix of this one).
    conflicting: MixedBitSet<PlaceId>,
}

/// A hash-friendly projection element that strips types and indices
/// for equality/hashing purposes.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
enum HProjectionElem {
    DerefBox,
    DerefShrBor,
    DerefMutBor,
    Field(FieldIdx),
    Index,
}

impl HProjectionElem {
    fn from_projection_elem<'tcx>(
        p: rustc_middle::mir::ProjectionElem<Local, Ty<'tcx>>,
        place_ty: rustc_middle::mir::PlaceTy<'tcx>,
    ) -> Option<Self> {
        match p {
            rustc_middle::mir::ProjectionElem::Deref => match place_ty.ty.kind() {
                TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) => Some(Self::DerefMutBor),
                TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not) => Some(Self::DerefShrBor),
                TyKind::Adt(def, _) if def.is_box() => Some(Self::DerefBox),
                _ => None,
            },
            rustc_middle::mir::ProjectionElem::Field(field_idx, _) => Some(Self::Field(field_idx)),
            rustc_middle::mir::ProjectionElem::Index(_) => Some(Self::Index),
            _ => None,
        }
    }
}

/// A hash-friendly place representation (local + simplified projection).
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
struct HPlace {
    local: Local,
    projection: Vec<HProjectionElem>,
}

impl HPlace {
    fn from_place<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, p: PlaceRef<'tcx>) -> (Self, bool) {
        let mut place_ty = rustc_middle::mir::PlaceTy::from_ty(body.local_decls[p.local].ty);
        let projection: Vec<HProjectionElem> = p
            .projection
            .iter()
            .map_while(|proj| {
                let r = HProjectionElem::from_projection_elem(*proj, place_ty)?;
                place_ty = place_ty.projection_ty(tcx, *proj);
                Some(r)
            })
            .collect();
        let full = projection.len() == p.projection.len();
        (
            HPlace {
                local: p.local,
                projection,
            },
            full,
        )
    }

    fn ambiguous(&self) -> bool {
        self.projection.contains(&HProjectionElem::Index)
    }
}

/// Backward dataflow analysis computing which places are NOT final.
///
/// A place is "not final" at a program point if it may be used (read, moved,
/// or borrowed) after that point. A place that IS final can have its borrow
/// inherit the parent's prophecy variable.
///
/// Domain: `MixedBitSet<PlaceId>` where membership means NOT final.
/// Direction: Backward.
/// Bottom: empty (all places final).
pub struct NotFinalPlaces<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    /// Maps a hash-friendly place to its analysis ID.
    places_ids: HashMap<HPlace, PlaceId>,
    /// Places organized by their local variable.
    places_per_local: HashMap<Local, MixedBitSet<PlaceId>>,
    /// Per-place metadata.
    infos: IndexVec<PlaceId, PlaceInfo<'tcx>>,
}

impl<'a, 'tcx> NotFinalPlaces<'a, 'tcx> {
    /// Build the analysis for a MIR body.
    ///
    /// Visits all places in the body to populate the place ID mapping,
    /// then precomputes subplace/conflicting relationships and deref counts.
    pub fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        // Phase 1: Visit all places in the body to build the place ID map.
        struct VisitAllPlaces<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            body: &'a Body<'tcx>,
            places: IndexVec<PlaceId, (PlaceRef<'tcx>, HPlace)>,
            places_ids: HashMap<HPlace, PlaceId>,
            places_per_local: HashMap<Local, Vec<PlaceId>>,
        }

        impl<'a, 'tcx> Visitor<'tcx> for VisitAllPlaces<'a, 'tcx> {
            fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
                let place_ref = place.as_ref();
                // Register the place itself and all its projection prefixes.
                for place in place_ref
                    .iter_projections()
                    .map(|(p, _)| p)
                    .chain(std::iter::once(place_ref))
                {
                    let (hplace, true) = HPlace::from_place(self.tcx, self.body, place) else {
                        break;
                    };
                    if let hash_map::Entry::Vacant(entry) = self.places_ids.entry(hplace.clone()) {
                        let id = self.places.push((place, hplace));
                        self.places_per_local
                            .entry(place.local)
                            .or_default()
                            .push(id);
                        entry.insert(id);
                    }
                }
            }
        }

        let mut visitor = VisitAllPlaces {
            tcx,
            body,
            places: IndexVec::default(),
            places_ids: HashMap::default(),
            places_per_local: HashMap::default(),
        };
        visitor.visit_body(body);
        let VisitAllPlaces {
            places,
            places_ids,
            places_per_local: ppl,
            ..
        } = visitor;

        let empty_bs = MixedBitSet::new_empty(places.len());
        let places_per_local: HashMap<Local, MixedBitSet<PlaceId>> = ppl
            .into_iter()
            .map(|(l, ids)| {
                let mut r = empty_bs.clone();
                for id in ids {
                    r.insert(id);
                }
                (l, r)
            })
            .collect();

        // Phase 2: Precompute subplace/conflicting relationships and deref counts.
        let infos = places
            .iter_enumerated()
            .map(|(place_id, &(place, ref hplace))| {
                let (mut conflicting, mut subplaces) = (empty_bs.clone(), empty_bs.clone());
                for other_id in places_per_local[&hplace.local]
                    .iter()
                    .filter(|&other_id| other_id != place_id)
                {
                    let (_, other_hplace) = &places[other_id];
                    // other is a subplace of this: other's projection starts with ours
                    if other_hplace.projection.get(..hplace.projection.len())
                        == Some(&*hplace.projection)
                    {
                        subplaces.insert(other_id);
                    }
                    // other is a superplace: our projection starts with theirs
                    else if hplace.projection.get(..other_hplace.projection.len())
                        == Some(&other_hplace.projection)
                    {
                        conflicting.insert(other_id);
                    }
                }

                let deref_count = hplace
                    .projection
                    .iter()
                    .filter(|&&p| p == HProjectionElem::DerefMutBor)
                    .count();
                PlaceInfo {
                    place,
                    deref_count,
                    subplaces,
                    conflicting,
                }
            })
            .collect();

        Self {
            tcx,
            body,
            places_ids,
            places_per_local,
            infos,
        }
    }

    /// Query whether the borrow of `place` is a final reborrow at `location`.
    ///
    /// Must be called with a cursor from `iterate_to_fixpoint`.
    ///
    /// # Returns
    ///
    /// - `true` if the reborrow is final (source not used afterward).
    ///   The returned `usize` is the projection index of the dereference.
    /// - `false` (via `None`) if the reborrow is NOT final (source may be used).
    pub fn is_final_at(
        cursor: &mut ResultsCursor<'_, 'tcx, Self>,
        place: &Place<'tcx>,
        location: Location,
    ) -> Option<usize> {
        let body = cursor.body();
        let tcx = cursor.analysis().tcx;
        let (hplace, true) = HPlace::from_place(tcx, body, place.as_ref()) else {
            return None;
        };
        // Find the last mut deref in the projection.
        let deref_pos_from_end = hplace
            .projection
            .iter()
            .rev()
            .position(|e| matches!(e, HProjectionElem::DerefMutBor))?;

        cursor.seek_before_primary_effect(location);
        let id = cursor.analysis().places_ids[&hplace];
        if cursor.get().contains(id) {
            // Place is in the "not final" set — the borrow is NOT final.
            None
        } else {
            // Place is NOT in the "not final" set — the borrow IS final.
            Some(hplace.projection.len() - deref_pos_from_end - 1)
        }
    }

    /// Return the number of tracked places.
    pub fn num_places(&self) -> usize {
        self.infos.len()
    }
}

impl<'a, 'tcx> DebugWithContext<NotFinalPlaces<'a, 'tcx>> for MixedBitSet<PlaceId> {
    fn fmt_with(
        &self,
        ctxt: &NotFinalPlaces<'a, 'tcx>,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        f.debug_list()
            .entries(self.iter().map(|id| ctxt.infos[id].place))
            .finish()
    }
}

// ── Dataflow Analysis Implementation ─────────────────────────────────────

impl<'a, 'tcx> Analysis<'tcx> for NotFinalPlaces<'a, 'tcx> {
    type Domain = MixedBitSet<PlaceId>;
    type Direction = Backward;

    const NAME: &'static str = "not_final_places";

    fn bottom_value(&self, _: &Body<'tcx>) -> Self::Domain {
        // Bottom = empty = all borrows are final (most optimistic).
        MixedBitSet::new_empty(self.infos.len())
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, _: &mut Self::Domain) {
        // No initialization needed for backward analysis.
    }

    fn apply_primary_statement_effect(
        &self,
        trans: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        PlaceVisitor { info: self, trans }.visit_statement(statement, location);
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        trans: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let mut visitor = PlaceVisitor { info: self, trans };
        // At function return, all locals are "written" (go out of scope),
        // which makes their 1-deref-deeper sub-borrows final.
        if terminator.kind == TerminatorKind::Return {
            for &l in self.places_per_local.keys() {
                visitor.write_local(l);
            }
        }
        visitor.visit_terminator(terminator, location);
        terminator.edges()
    }
}

// ── Place Visitor for Gen/Kill Operations ────────────────────────────────

struct PlaceVisitor<'a, 'tcx, T> {
    info: &'a NotFinalPlaces<'a, 'tcx>,
    trans: &'a mut T,
}

impl<'tcx, T> PlaceVisitor<'_, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    /// Handle a write to place `p` (changing its current value).
    ///
    /// The key rule: writing to `p` makes `p` and its conflicting places
    /// NOT final (gen). But sub-places with exactly one more deref than `p`
    /// become final (kill), because overwriting `p` means the borrow
    /// through `*p` ends here.
    fn write(&mut self, p: &Place<'tcx>) {
        let (hplace, full) = HPlace::from_place(self.info.tcx, self.info.body, p.as_ref());
        let Some(&id) = self.info.places_ids.get(&hplace) else {
            return;
        };
        let infos = &self.info.infos[id];
        // The written place itself becomes not-final.
        self.trans.gen_(id);
        // Conflicting (super-)places also become not-final.
        self.trans.gen_all(infos.conflicting.iter());
        // Sub-places: those with exactly one more deref become final;
        // others become not-final.
        for subplace_id in infos.subplaces.iter() {
            if self.info.infos[subplace_id].deref_count == infos.deref_count + 1 {
                if full && !hplace.ambiguous() {
                    self.trans.kill(subplace_id);
                }
            } else {
                self.trans.gen_(subplace_id);
            }
        }
    }

    /// Handle a write to local variable `l` (e.g., StorageLive/StorageDead).
    ///
    /// Places with local `l` and exactly 1 deref become final.
    /// Other places with local `l` become not-final.
    fn write_local(&mut self, l: Local) {
        let Some(places) = self.info.places_per_local.get(&l) else {
            return;
        };
        for id in places.iter() {
            if self.info.infos[id].deref_count == 1 {
                self.trans.kill(id);
            } else {
                self.trans.gen_(id);
            }
        }
    }

    /// Handle a move or borrow of place `p`.
    ///
    /// The place, its sub-places, and conflicting places all become not-final
    /// (we can't statically guarantee the current value won't change).
    fn move_or_bor(&mut self, p: &Place<'tcx>) {
        let (hplace, _) = HPlace::from_place(self.info.tcx, self.info.body, p.as_ref());
        let Some(&id) = self.info.places_ids.get(&hplace) else {
            return;
        };
        let infos = &self.info.infos[id];
        self.trans.gen_(id);
        self.trans.gen_all(infos.conflicting.iter());
        self.trans.gen_all(infos.subplaces.iter());
    }
}

impl<'tcx, T> Visitor<'tcx> for PlaceVisitor<'_, 'tcx, T>
where
    T: GenKill<PlaceId>,
{
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _: Location) {
        match context {
            PlaceContext::MutatingUse(
                MutatingUseContext::Store
                | MutatingUseContext::SetDiscriminant
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Call
                | MutatingUseContext::Drop,
            ) => self.write(place),
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)
            | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => self.move_or_bor(place),
            _ => {}
        }
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
        match context {
            PlaceContext::NonUse(NonUseContext::StorageLive | NonUseContext::StorageDead) => {
                self.write_local(local);
            }
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)
            | PlaceContext::MutatingUse(MutatingUseContext::Borrow) => {
                self.move_or_bor(&local.into());
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hprojection_elem_field_equality() {
        let f0 = HProjectionElem::Field(FieldIdx::from_u32(0));
        let f1 = HProjectionElem::Field(FieldIdx::from_u32(1));
        assert_eq!(f0, HProjectionElem::Field(FieldIdx::from_u32(0)));
        assert_ne!(f0, f1);
    }

    #[test]
    fn test_hplace_ambiguous_detection() {
        let deref_only = HPlace {
            local: Local::from_u32(1),
            projection: vec![HProjectionElem::DerefMutBor],
        };
        assert!(!deref_only.ambiguous());
        let with_index = HPlace {
            local: Local::from_u32(1),
            projection: vec![HProjectionElem::DerefMutBor, HProjectionElem::Index],
        };
        assert!(with_index.ambiguous());
    }

    #[test]
    fn test_hplace_equality_and_hashing() {
        let p1 = HPlace {
            local: Local::from_u32(1),
            projection: vec![HProjectionElem::DerefMutBor],
        };
        let p1_clone = p1.clone();
        let p_other_local = HPlace {
            local: Local::from_u32(2),
            projection: vec![HProjectionElem::DerefMutBor],
        };
        assert_eq!(p1, p1_clone);
        assert_ne!(p1, p_other_local);
        let mut map = HashMap::new();
        map.insert(p1.clone(), PlaceId::from_u32(0));
        assert!(map.contains_key(&p1_clone));
        assert!(!map.contains_key(&p_other_local));
    }
}
