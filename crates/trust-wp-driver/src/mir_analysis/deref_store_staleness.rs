// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stale-read detection for values reached through a reference after a STORE
//! through that reference or through one of its aliases. (prophecy-store)
//!
//! The extraction lanes translate a read of `*p` (for a reference `p`) as
//! `Deref(Var(p))`, which the encoders bind to the pointee's ENTRY value
//! (`p_current`). A store `*p = v` / `(*p).f = v` — or `*r = v` with
//! `r = &mut *p` — does not rebind that term, so a callee precondition or a
//! loop-invariant entry check that reads `*p` after the store was discharged
//! against the entry value:
//!
//! ```text
//! #[requires((*p)@ == 0)] fn f(p: &mut i32) { *p = 5; need_zero(*p) }  // verified
//! ```
//!
//! Callers use this analysis to FAIL CLOSED on such reads (the obligation
//! becomes `false`), the same precedent as the `assert!` value-stability gate
//! (`extract/helpers/value_stability.rs`). It only ever removes accept paths.
//!
//! Scope (documented, conservative within it): aliasing is followed through
//! reborrows / borrows of a deref place, plain copies and moves of operands
//! that may carry a borrow, direct borrows of a local, and a borrow put into
//! or taken out of a tuple, struct, enum or array. References returned by
//! CALLS are not unioned with their arguments; stores through such results
//! keep the pre-existing receiver-state promotion lane.
//!
//! A class a HOLDER joined (an aggregate carrying a borrow) is written by
//! more than its deref stores: a call handed any value of the class may write
//! through the borrow the holder carries, and so may a drop of one. The
//! extraction lanes model none of those writes on the borrowed local, whose
//! binding keeps its value from before the borrow: `let t = (&mut a, 0); *t.0
//! = 5; a` returned 3, and so did the same with a callee writing through
//! `&mut t` (D-127). Every call and drop in such a class counts as a store.

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_middle::{
    mir::{
        visit::{PlaceContext, Visitor},
        AggregateKind, BasicBlock, Body, Local, Location, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::TyCtxt,
};

/// Per-body store/alias summary. Build once per body with [`Self::new`].
pub(crate) struct DerefStoreStaleness<'a, 'tcx> {
    body: &'a Body<'tcx>,
    /// Union-find parent over local indices.
    parent: Vec<usize>,
    /// Stores through a deref: the written place and where it happens.
    store_sites: Vec<(Place<'tcx>, Location)>,
    /// Projection-free definition sites per local (assignments and call
    /// destinations).
    defs: HashMap<Local, Vec<Location>>,
    /// Blocks whose stores and hand-offs [`Self::operand_may_read_stale_from`]
    /// leaves to a lane that states them itself (`excluding_stores_in`).
    excluded_store_blocks: HashSet<BasicBlock>,
    /// Locals that joined a class as, or out of, a holder of a borrow: an
    /// aggregate built from an operand that may carry one, and that operand.
    held: HashSet<Local>,
    /// Calls and drops handed a value that may carry a borrow, with the
    /// locals handed over: a store in every holder class one of them is in.
    handoff_sites: Vec<(Vec<Local>, Location)>,
    /// The hand-offs of [`Self::handoff_sites`] that may write: a drop, or a
    /// call handed a local other than a shared reference to memory with no
    /// write capability behind it (`&&mut i32` reads `*` only, as a
    /// `snapshot!` of a held borrow does).
    writing_handoff_sites: Vec<(Vec<Local>, Location)>,
    /// Locals given a borrow by a store into one of their places (`t.0 =
    /// &mut c`): holders whose borrows no extraction lane follows.
    stored_into_holders: HashSet<Local>,
    /// Per local assigned an aggregate, the operand locals that may carry a
    /// borrow.
    aggregate_operands: HashMap<Local, Vec<Local>>,
    /// Per local assigned a borrow, the place it borrows.
    borrowed_places: HashMap<Local, Place<'tcx>>,
    /// Calls whose result may carry a borrow, with the handed locals that
    /// may carry one: the result may be (or hold) a borrow an argument
    /// carries (`t.0 = id(&mut c)`).
    call_results: Vec<(Local, Vec<Local>)>,
    /// Per local assigned a `deref_copy` of a place (`_5 = deref_copy
    /// (h.p)`), that place: a store `(*_5) = 7` is the source's `*h.p = 7`.
    deref_copied_places: HashMap<Local, Place<'tcx>>,
    /// Locals a source variable names (`var_debug_info`): a user's binding,
    /// not a compiler temporary. Read from the debug info, which a body
    /// whose local info is cleared still carries.
    named_locals: HashSet<Local>,
    /// Per local, whether its type may carry a borrow.
    may_carry: Vec<bool>,
}

struct PlaceCollector<'tcx> {
    places: Vec<Place<'tcx>>,
}

impl<'tcx> Visitor<'tcx> for PlaceCollector<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, _context: PlaceContext, _location: Location) {
        self.places.push(*place);
    }
}

fn has_deref(place: &Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|elem| matches!(elem, ProjectionElem::Deref))
}

impl<'a, 'tcx> DerefStoreStaleness<'a, 'tcx> {
    /// `tcx` is what lets the summary see a D-140 hand-off; without it (a
    /// caller that holds none) only stores written in the MIR are counted.
    pub(crate) fn new(tcx: Option<TyCtxt<'tcx>>, body: &'a Body<'tcx>) -> Self {
        let mut this = Self {
            body,
            parent: (0..body.local_decls.len()).collect(),
            store_sites: Vec::new(),
            defs: HashMap::new(),
            excluded_store_blocks: HashSet::new(),
            held: HashSet::new(),
            handoff_sites: Vec::new(),
            writing_handoff_sites: Vec::new(),
            stored_into_holders: HashSet::new(),
            aggregate_operands: HashMap::new(),
            borrowed_places: HashMap::new(),
            call_results: Vec::new(),
            deref_copied_places: HashMap::new(),
            named_locals: body
                .var_debug_info
                .iter()
                .filter_map(|debug| match &debug.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place.local),
                    _ => None,
                })
                .collect(),
            may_carry: locals_that_may_carry_a_borrow(body),
        };
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, stmt) in data.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                match &stmt.kind {
                    StatementKind::Assign((place, rvalue)) => {
                        if has_deref(place) {
                            this.store_sites.push((*place, location));
                        }
                        if place.projection.is_empty() {
                            this.defs.entry(place.local).or_default().push(location);
                            this.record_definition(place.local, rvalue);
                        } else if !has_deref(place) {
                            this.hold_a_borrow_stored_into(place.local, rvalue);
                        }
                        this.union_rvalue_aliases(place.local, rvalue);
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        if has_deref(place) {
                            this.store_sites.push((**place, location));
                        }
                    }
                    _ => {}
                }
            }
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            // D-140: drop glue that may write, run by a `Drop` or by a callee
            // handed the value, stores into every local the value reaches.
            // Each such local is recorded as written at the hand-off, so a
            // read of it (or through it) afterwards is a stale read.
            let handed_off = tcx.and_then(|tcx| {
                crate::mir_analysis::extract::drop_glue_writes::locals_changed_by_handoff(
                    tcx,
                    body,
                    block,
                    data.terminator(),
                )
            });
            if let Some(changed) = handed_off {
                let mut changed: Vec<Local> = changed.into_iter().collect();
                changed.sort();
                for local in changed {
                    this.store_sites.push((Place::from(local), location));
                }
            }
            match &data.terminator().kind {
                TerminatorKind::Call {
                    destination, args, ..
                } => {
                    if has_deref(destination) {
                        this.store_sites.push((*destination, location));
                    }
                    if destination.projection.is_empty() {
                        this.defs
                            .entry(destination.local)
                            .or_default()
                            .push(location);
                    }
                    let handed: Vec<Local> = args
                        .iter()
                        .filter_map(|arg| arg.node.place())
                        .map(|place| place.local)
                        .filter(|local| this.may_carry[local.as_usize()])
                        .collect();
                    let writing: Vec<Local> = handed
                        .iter()
                        .copied()
                        .filter(|local| !reads_only_through(body.local_decls[*local].ty))
                        .collect();
                    if !writing.is_empty() {
                        this.writing_handoff_sites.push((writing, location));
                    }
                    if destination.projection.is_empty()
                        && this.may_carry[destination.local.as_usize()]
                        && !handed.is_empty()
                    {
                        this.call_results.push((destination.local, handed.clone()));
                    }
                    if !handed.is_empty() {
                        this.handoff_sites.push((handed, location));
                    }
                }
                TerminatorKind::Drop { place, .. } if this.may_carry[place.local.as_usize()] => {
                    this.handoff_sites.push((vec![place.local], location));
                    this.writing_handoff_sites
                        .push((vec![place.local], location));
                }
                _ => {}
            }
        }
        this
    }

    /// Stop counting the stores and hand-offs located in `blocks` in
    /// [`Self::operand_may_read_stale_from`], for a caller whose lane states
    /// the effect of every store and hand-off there (the loop lane, for a loop
    /// body).
    pub(crate) fn excluding_stores_in(mut self, blocks: &HashSet<BasicBlock>) -> Self {
        self.excluded_store_blocks.clone_from(blocks);
        self
    }

    fn find(&mut self, local: usize) -> usize {
        let mut x = local;
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: Local, b: Local) {
        let ra = self.find(a.as_usize());
        let rb = self.find(b.as_usize());
        if ra != rb {
            self.parent[ra] = rb;
        }
    }

    fn is_reference_like(&self, local: Local) -> bool {
        let ty = self.body.local_decls[local].ty;
        ty.is_ref() || ty.is_raw_ptr() || ty.is_box()
    }

    fn union_rvalue_aliases(&mut self, dest: Local, rvalue: &Rvalue<'tcx>) {
        match rvalue {
            // `dest = &mut *p`, `dest = &(*p).f`, `dest = &mut v`, raw borrows.
            Rvalue::Ref(_, _, referent) | Rvalue::RawPtr(_, referent) => {
                self.union(dest, referent.local);
            }
            // Only a copied/moved value that may carry a borrow is an alias.
            // Copying a plain VALUE out of a deref place (`v = *bor`) is not:
            // `v` keeps the value it read and later stores through `bor` do
            // not change it. A reference taken out of a holder (`r =
            // move (t.0)`) or a holder moved whole (`u = t`) carries the
            // holder's borrow on.
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _)
            | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
            | Rvalue::CopyForDeref(src)
                if self.is_reference_like(dest)
                    || self.may_carry[dest.as_usize()]
                    || (src.projection.is_empty()
                        && !self.body.local_decls[dest].ty.is_primitive()) =>
            {
                // A whole value moved on (`u = t`) carries whatever it holds,
                // whether or not its type names a region: a struct holding a
                // raw pointer names none.
                self.union(dest, src.local);
            }
            // A borrow put into a tuple, struct, enum or array: the aggregate
            // holds it, and a write through any copy of it lands on the
            // borrowed place. A closure's captures are its own lane's.
            Rvalue::Aggregate(kind, operands)
                if !matches!(
                    **kind,
                    AggregateKind::Closure(..)
                        | AggregateKind::Coroutine(..)
                        | AggregateKind::CoroutineClosure(..)
                ) =>
            {
                for operand in operands {
                    let Some(place) = operand.place() else {
                        continue;
                    };
                    if self.may_carry[place.local.as_usize()] {
                        self.union(dest, place.local);
                        self.held.insert(dest);
                        self.held.insert(place.local);
                    }
                }
            }
            _ => {}
        }
    }

    /// A borrow stored into a place of another local (`t.0 = &mut c`, `m.m =
    /// x`, `arr[i] = x`) makes that local its holder, as building an
    /// aggregate around it does: a write through the place, or a call or
    /// drop handed the holder, lands on the borrowed memory, which the
    /// extraction lanes keep at its value from before (D-128, D-129).
    fn hold_a_borrow_stored_into(&mut self, holder: Local, rvalue: &Rvalue<'tcx>) {
        let stored = match rvalue {
            Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, referent)
                if is_a_plain_value(self.body.local_decls[referent.local].ty, 0) =>
            {
                None
            }
            Rvalue::Ref(_, _, referent) | Rvalue::RawPtr(_, referent) => Some(referent.local),
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _)
            | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
            | Rvalue::CopyForDeref(src)
                if self.may_carry[src.local.as_usize()] =>
            {
                Some(src.local)
            }
            _ => None,
        };
        if let Some(stored) = stored {
            self.held.insert(holder);
            self.held.insert(stored);
            self.stored_into_holders.insert(holder);
        }
    }

    /// Record what a projection-free assignment builds: an aggregate's
    /// borrow-carrying operands, or the place a borrow takes.
    fn record_definition(&mut self, local: Local, rvalue: &Rvalue<'tcx>) {
        match rvalue {
            Rvalue::Aggregate(_, operands) => {
                let carried = operands
                    .iter()
                    .filter_map(Operand::place)
                    .map(|place| place.local)
                    .filter(|operand| self.may_carry[operand.as_usize()])
                    .collect();
                self.aggregate_operands.insert(local, carried);
            }
            Rvalue::Ref(_, _, referent) => {
                self.borrowed_places.insert(local, *referent);
            }
            Rvalue::CopyForDeref(source) => {
                self.deref_copied_places.insert(local, *source);
            }
            // A compiler temporary copying a holder's field to write through
            // it (`_5 = copy (h.p); (*_5) = 7` for `*h.p = 7`). A user's
            // `let r = t.0` is a binding of its own, not followed.
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _)
                if !source.projection.is_empty()
                    && !has_deref(source)
                    && !self.named_locals.contains(&local) =>
            {
                self.deref_copied_places.insert(local, *source);
            }
            _ => {}
        }
    }

    /// Whether the extraction lanes follow a store through a borrow `holder`
    /// holds: `holder` is assigned once, an aggregate built around borrows
    /// each assigned once and taken of a local's own place (`H { p: &mut x
    /// }`, `(&mut c, 0)`), and no borrow is stored into it later. The lanes
    /// bind such a holder's field to the borrowed local and apply `*h.p = 7`
    /// to it; a borrow of a dereferenced place (`(&mut *x, 0)`), a holder
    /// moved to another local, and a borrow stored into a holder's place they
    /// do not follow.
    fn lanes_follow_holder(&self, holder: Local) -> bool {
        let assigned_once =
            |local: Local| self.defs.get(&local).is_some_and(|defs| defs.len() == 1);
        assigned_once(holder)
            && !self.stored_into_holders.contains(&holder)
            && self
                .aggregate_operands
                .get(&holder)
                .is_some_and(|operands| {
                    operands
                        .iter()
                        .all(|operand| self.borrows_a_locals_own_place_once(*operand, 0))
                })
    }

    /// Whether `local` is assigned once a borrow of a local's own place
    /// (`&mut c`), or a reborrow of the referent of such a borrow (`&mut *r`
    /// of `r = &mut c`, as a coercion into a struct field spells it).
    fn borrows_a_locals_own_place_once(&self, local: Local, depth: usize) -> bool {
        if depth > 8 || !self.defs.get(&local).is_some_and(|defs| defs.len() == 1) {
            return false;
        }
        match self.borrowed_places.get(&local) {
            Some(referent) if !has_deref(referent) => true,
            Some(referent) => match referent.projection.as_slice() {
                [ProjectionElem::Deref] => {
                    self.borrows_a_locals_own_place_once(referent.local, depth + 1)
                }
                _ => false,
            },
            None => false,
        }
    }

    /// Whether `local`'s class has a holder of a borrow in it.
    fn class_is_held(&mut self, local: Local) -> bool {
        let root = self.find(local.as_usize());
        let held: Vec<Local> = self.held.iter().copied().collect();
        held.into_iter()
            .any(|member| self.find(member.as_usize()) == root)
    }

    /// The calls and drops that may write through a borrow `local`'s class
    /// holds: every one handed a value of the class, when a holder is in it.
    fn handoff_sites_of(&mut self, local: Local) -> Vec<Location> {
        if !self.class_is_held(local) {
            return Vec::new();
        }
        let root = self.find(local.as_usize());
        let sites = self.handoff_sites.clone();
        sites
            .into_iter()
            .filter(|(handed, _)| {
                handed
                    .iter()
                    .any(|member| self.find(member.as_usize()) == root)
            })
            .map(|(_, location)| location)
            .collect()
    }

    /// `from` strictly precedes `to` on some CFG path.
    fn reaches(&self, from: Location, to: Location) -> bool {
        if from.block == to.block && from.statement_index < to.statement_index {
            return true;
        }
        let mut seen: HashSet<BasicBlock> = HashSet::new();
        let mut queue: VecDeque<BasicBlock> = self.body.basic_blocks[from.block]
            .terminator()
            .successors()
            .collect();
        while let Some(bb) = queue.pop_front() {
            if bb == to.block {
                return true;
            }
            if seen.insert(bb) {
                queue.extend(self.body.basic_blocks[bb].terminator().successors());
            }
        }
        false
    }

    /// Whether a store through `local`'s alias class can execute before `at`.
    pub(crate) fn store_reaches(&mut self, local: Local, at: Location) -> bool {
        let root = self.find(local.as_usize());
        let mut sites: Vec<Location> = self
            .store_sites
            .clone()
            .into_iter()
            .filter_map(|(store_place, loc)| {
                (self.find(store_place.local.as_usize()) == root).then_some(loc)
            })
            .collect();
        sites.extend(self.handoff_sites_of(local));
        sites.into_iter().any(|site| self.reaches(site, at))
    }

    /// The roots of `local`'s class and of every class a call result joins
    /// it through: a call handed a value of a class may return a borrow that
    /// value carries (`r = id(&mut c)`), which the union-find does not follow
    /// (the receiver-state lane keeps those for the other lanes).
    fn classes_reached_through_calls(&mut self, local: Local) -> HashSet<usize> {
        let mut roots: HashSet<usize> = HashSet::from([self.find(local.as_usize())]);
        let edges = self.call_results.clone();
        loop {
            let mut grew = false;
            for (result, handed) in &edges {
                let result_root = self.find(result.as_usize());
                if roots.contains(&result_root) {
                    continue;
                }
                if handed
                    .iter()
                    .any(|member| roots.contains(&self.find(member.as_usize())))
                {
                    roots.insert(result_root);
                    grew = true;
                }
            }
            if !grew {
                return roots;
            }
        }
    }

    /// Whether the extraction lanes carry a store to `place` to the memory
    /// it writes: a store through a `&mut` parameter, or through a local
    /// assigned once a borrow of a local's own place, with no further
    /// dereference (`*x = 7`, `(*x).f = 7`, `*r = 5` of `r = &mut c`); or a
    /// store `*h.p = 7` through a field of a tuple or struct holder the lanes
    /// follow ([`Self::lanes_follow_holder`]). A store through an element
    /// (`*a[0] = 5`), through a reference to a holder (`*r.0 = 5` of `r =
    /// &mut t`), or through a borrow behind a borrow (`**r = 5`) is not
    /// carried: each was measured to leave the borrowed local at its value
    /// from before the store (D-129).
    fn lanes_follow_store(&self, place: &Place<'tcx>) -> bool {
        let assigned_once =
            |local: Local| self.defs.get(&local).is_some_and(|defs| defs.len() == 1);
        // A `deref_copy` temporary is the place it copies: `(*_5) = 7` of
        // `_5 = deref_copy (h.p)` is `*h.p = 7`.
        let mut local = place.local;
        let mut projection: Vec<ProjectionElem<Local, rustc_middle::ty::Ty<'tcx>>> =
            place.projection.iter().collect();
        for _ in 0..8 {
            let Some(source) = self.deref_copied_places.get(&local) else {
                break;
            };
            if !assigned_once(local) {
                return false;
            }
            let mut joined: Vec<_> = source.projection.iter().collect();
            joined.extend(projection);
            projection = joined;
            local = source.local;
        }
        if self.deref_copied_places.contains_key(&local) {
            return false;
        }
        match projection.as_slice() {
            [ProjectionElem::Deref, rest @ ..]
                if !rest
                    .iter()
                    .any(|elem| matches!(elem, ProjectionElem::Deref)) =>
            {
                let is_argument = local.as_usize() >= 1 && local.as_usize() <= self.body.arg_count;
                is_argument || self.borrows_a_locals_own_place_once(local, 0)
            }
            [ProjectionElem::Field(..), ProjectionElem::Deref] => {
                use rustc_middle::ty::TyKind;
                let holder_is_a_tuple_or_struct = match self.body.local_decls[local].ty.kind() {
                    TyKind::Tuple(_) => true,
                    TyKind::Adt(adt, _) => adt.is_struct(),
                    _ => false,
                };
                holder_is_a_tuple_or_struct && self.lanes_follow_holder(local)
            }
            _ => false,
        }
    }

    /// Whether a write the extraction lanes do not carry to the borrowed
    /// local can execute in `local`'s class before `at`, when a holder of a
    /// borrow is in that class or in a class a call result joins it to
    /// ([`Self::classes_reached_through_calls`]): a store the lanes do not
    /// follow ([`Self::lanes_follow_store`]), or a call or drop handed a
    /// value of the classes that may write. The local's binding keeps its
    /// value from before such a write (D-127 item 5, D-129).
    pub(crate) fn holder_write_reaches(&mut self, local: Local, at: Location) -> bool {
        let roots = self.classes_reached_through_calls(local);
        let held: Vec<Local> = self.held.iter().copied().collect();
        if !held
            .into_iter()
            .any(|member| roots.contains(&self.find(member.as_usize())))
        {
            return false;
        }
        let stores = self.store_sites.clone();
        let mut sites: Vec<Location> = stores
            .into_iter()
            .filter_map(|(store_place, loc)| {
                (!self.lanes_follow_store(&store_place)
                    && roots.contains(&self.find(store_place.local.as_usize())))
                .then_some(loc)
            })
            .collect();
        let handoffs = self.writing_handoff_sites.clone();
        sites.extend(handoffs.into_iter().filter_map(|(handed, location)| {
            handed
                .iter()
                .any(|member| roots.contains(&self.find(member.as_usize())))
                .then_some(location)
        }));
        sites.into_iter().any(|site| self.reaches(site, at))
    }

    /// Every site that may write memory `local`'s class reaches and can
    /// execute before `at` (D-185): a store through a dereference in the
    /// class or in a class a call result joins it to, a store a hand-off's
    /// drop glue makes, and a call or drop handed a value of those classes
    /// that may write through it -- whether or not a holder is in the class.
    /// A store carries its place; a hand-off carries none.
    pub(crate) fn write_sites_reaching(
        &mut self,
        local: Local,
        at: Location,
    ) -> Vec<(Location, Option<Place<'tcx>>)> {
        let roots = self.classes_reached_through_calls(local);
        let stores = self.store_sites.clone();
        let mut sites: Vec<(Location, Option<Place<'tcx>>)> = stores
            .into_iter()
            .filter(|(store_place, _)| roots.contains(&self.find(store_place.local.as_usize())))
            .map(|(store_place, location)| (location, Some(store_place)))
            .collect();
        let handoffs = self.writing_handoff_sites.clone();
        sites.extend(handoffs.into_iter().filter_map(|(handed, location)| {
            handed
                .iter()
                .any(|member| roots.contains(&self.find(member.as_usize())))
                .then_some((location, None))
        }));
        sites.retain(|(site, _)| self.reaches(*site, at));
        sites
    }

    /// What this lane knows of the memory read through `local` at `at`
    /// (D-185, D-186): [`CurrentState::Unwritten`] when no write the class
    /// reaches can precede `at`, so the entry value IS the current one;
    /// [`CurrentState::DirectPointeeStores`] when the memory read at `at` is
    /// the value of exactly ONE whole-pointee store `*local = v` through
    /// `local` itself ([`Self::unique_reaching_store`]), which the substitution
    /// walk records as `*local`'s current value; and [`CurrentState::Untracked`]
    /// for anything else (two stores joining at `at`, a store and the entry
    /// value joining there, a store a back edge carries round, a store through
    /// an alias, through a held borrow, into a field, a pointer-slot store, a
    /// call or a drop handed the class).
    pub(crate) fn current_state(&mut self, local: Local, at: Location) -> CurrentState {
        let sites = self.write_sites_reaching(local, at);
        if sites.is_empty() {
            return CurrentState::Unwritten;
        }
        let is_whole_pointee_store = |place: &Option<Place<'tcx>>| {
            place.is_some_and(|place| {
                place.local == local
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
            })
        };
        let kills: HashSet<Location> = sites
            .iter()
            .filter(|(_, place)| is_whole_pointee_store(place))
            .map(|(location, _)| *location)
            .collect();
        match self.unique_reaching_store(&sites, &kills, at) {
            ReachingStore::Entry => CurrentState::Unwritten,
            ReachingStore::One(store)
                if kills.contains(&store) && !self.pointer_rebound_between(local, store, at) =>
            {
                CurrentState::DirectPointeeStores
            }
            _ => CurrentState::Untracked,
        }
    }

    /// Whether `local` itself -- the pointer a store `*local = v` at `store`
    /// went through -- may be given another value on a path from `store` to
    /// `at` (D-187). Re-binding the pointer (`p = b`, `p = &mut z`, a by-`mut`
    /// reference parameter `x = y`) is a definition of what `*local` denotes:
    /// a read at `at` through the new pointer reads memory the store never
    /// wrote, so the recorded value is `*local`'s only when the pointer the
    /// read goes through is the one the store went through on every path.
    /// A definition of `local` that some path runs after the store and before
    /// `at` is such a re-binding; any one counts, whether or not every path
    /// runs it (`if c { p = b; }`).
    fn pointer_rebound_between(&self, local: Local, store: Location, at: Location) -> bool {
        let Some(defs) = self.defs.get(&local) else {
            return false;
        };
        defs.iter()
            .any(|def| self.reaches(store, *def) && self.reaches(*def, at))
    }

    /// The definition of the memory read at `at` (D-186): of the write
    /// `sites`, those a path reaches `at` from without passing one of `kills`
    /// (the writes that overwrite the whole memory) on the way, together with
    /// the entry value when a path from the function's entry passes none of
    /// `sites` that is a kill. [`ReachingStore::One`] only when exactly one
    /// write reaches, the entry value does not, and that write is on no cycle
    /// of the CFG: the substitution walk follows each acyclic path once and
    /// merges the paths at their branch, so a value two writes (or a write
    /// and the entry) leave at a join, and a value a back edge carries from
    /// one iteration into the next, are not the value it recorded.
    fn unique_reaching_store(
        &self,
        sites: &[(Location, Option<Place<'tcx>>)],
        kills: &HashSet<Location>,
        at: Location,
    ) -> ReachingStore {
        let mut reaching: Vec<Location> = sites
            .iter()
            .map(|(location, _)| *location)
            .filter(|location| self.reaches_avoiding(*location, at, kills))
            .collect();
        reaching.sort();
        reaching.dedup();
        let entry_reaches = self.reaches_from_entry_avoiding(at, kills);
        match reaching.as_slice() {
            [] if entry_reaches => ReachingStore::Entry,
            [store] if !entry_reaches && !self.reaches(*store, *store) => {
                ReachingStore::One(*store)
            }
            _ => ReachingStore::Several,
        }
    }

    /// Whether `to` can execute after `from` on a path that executes none of
    /// `kills` in between.
    fn reaches_avoiding(&self, from: Location, to: Location, kills: &HashSet<Location>) -> bool {
        self.reaches_avoiding_from(from.block, from.statement_index + 1, to, kills)
    }

    /// Whether `to` can execute on a path from the function's entry that
    /// executes none of `kills` before it.
    fn reaches_from_entry_avoiding(&self, to: Location, kills: &HashSet<Location>) -> bool {
        self.reaches_avoiding_from(BasicBlock::from_u32(0), 0, to, kills)
    }

    /// Whether `to` can execute on a path that starts at statement
    /// `start_index` of `start_block` and executes none of `kills` before it.
    fn reaches_avoiding_from(
        &self,
        start_block: BasicBlock,
        start_index: usize,
        to: Location,
        kills: &HashSet<Location>,
    ) -> bool {
        // Walk the statements from `start` in a block; a kill ends the path.
        let walk_block = |block: BasicBlock, start: usize| -> (bool, bool) {
            let data = &self.body.basic_blocks[block];
            for statement_index in start..=data.statements.len() {
                let location = Location {
                    block,
                    statement_index,
                };
                if location == to {
                    return (true, false);
                }
                if kills.contains(&location) {
                    return (false, false);
                }
            }
            (false, true)
        };
        let (found, open) = walk_block(start_block, start_index);
        if found {
            return true;
        }
        if !open {
            return false;
        }
        let mut queue: VecDeque<BasicBlock> = self.body.basic_blocks[start_block]
            .terminator()
            .successors()
            .collect();
        let mut seen: HashSet<BasicBlock> = HashSet::new();
        while let Some(block) = queue.pop_front() {
            if !seen.insert(block) {
                continue;
            }
            let (found, open) = walk_block(block, 0);
            if found {
                return true;
            }
            if open {
                queue.extend(self.body.basic_blocks[block].terminator().successors());
            }
        }
        false
    }

    /// What this lane knows of the place `bound` (a name bound to a
    /// projection of a local, as a closure's capture `*((*_1).0)` is) at `at`
    /// (D-185, D-186): [`CurrentState::Unwritten`] when no write that may
    /// overlap it can precede `at`; [`CurrentState::DirectPlaceStores`] when
    /// the value read at `at` is that of exactly one store to exactly
    /// `bound` ([`Self::unique_reaching_store`]), which the walk records under
    /// the name; [`CurrentState::Untracked`] otherwise. A store to a sibling
    /// field of the same base cannot change `bound` and is not counted.
    pub(crate) fn current_state_of_place(
        &mut self,
        bound: Place<'tcx>,
        at: Location,
    ) -> CurrentState {
        let referent: Referent<'tcx> = (bound.local, bound.projection.to_vec());
        let sites: Vec<(Location, Option<Place<'tcx>>, Option<Referent<'tcx>>)> = self
            .write_sites_reaching(bound.local, at)
            .into_iter()
            .map(|(location, place)| {
                (
                    location,
                    place,
                    place.map(|place| self.through_deref_copies(place)),
                )
            })
            .filter(|(_, _, written)| {
                written
                    .as_ref()
                    .is_none_or(|written| may_overlap_referents(written, &referent))
            })
            .collect();
        if sites.is_empty() {
            return CurrentState::Unwritten;
        }
        let kills: HashSet<Location> = sites
            .iter()
            .filter(|(_, _, written)| {
                written
                    .as_ref()
                    .is_some_and(|written| same_place(written, &referent))
            })
            .map(|(location, _, _)| *location)
            .collect();
        let sites: Vec<(Location, Option<Place<'tcx>>)> = sites
            .into_iter()
            .map(|(location, place, _)| (location, place))
            .collect();
        match self.unique_reaching_store(&sites, &kills, at) {
            ReachingStore::Entry => CurrentState::Unwritten,
            ReachingStore::One(store) if kills.contains(&store) => CurrentState::DirectPlaceStores,
            _ => CurrentState::Untracked,
        }
    }

    /// `place` with every `deref_copy` temporary it is rooted at replaced by
    /// the place it copies (`(*_5)` of `_5 = deref_copy ((*_1).0)` is
    /// `(*((*_1).0))`), as far as each temporary is assigned once.
    fn through_deref_copies(&self, place: Place<'tcx>) -> Referent<'tcx> {
        let assigned_once =
            |local: Local| self.defs.get(&local).is_some_and(|defs| defs.len() == 1);
        let mut local = place.local;
        let mut projection: Vec<ProjectionElem<Local, rustc_middle::ty::Ty<'tcx>>> =
            place.projection.iter().collect();
        for _ in 0..8 {
            let Some(source) = self.deref_copied_places.get(&local) else {
                break;
            };
            if !assigned_once(local) {
                break;
            }
            let mut joined: Vec<_> = source.projection.iter().collect();
            joined.extend(projection);
            projection = joined;
            local = source.local;
        }
        (local, projection)
    }

    /// Whether some store a write to memory `local` reaches stores through a
    /// dereference rooted at `local` itself: the memory behind `local`, not
    /// `local`'s own (a store `*r = 5` through a borrow `r = &mut c` writes
    /// `c`'s own memory, which the governed write-back lane rebinds `c` to).
    fn stores_behind(&mut self, local: Local, at: Location) -> bool {
        self.write_sites_reaching(local, at)
            .iter()
            .any(|(_, place)| place.is_some_and(|place| place.local == local && has_deref(&place)))
    }

    /// Like [`Self::store_reaches`], but a store only counts when its written
    /// place may overlap one of `targets` — the memory the returned borrow
    /// points at. (handback-entry-value)
    pub(crate) fn overlapping_store_reaches(
        &mut self,
        local: Local,
        at: Location,
        targets: &[Referent<'tcx>],
    ) -> bool {
        let root = self.find(local.as_usize());
        let mut sites: Vec<Location> = self
            .store_sites
            .clone()
            .into_iter()
            .filter_map(|(store_place, loc)| {
                (self.find(store_place.local.as_usize()) == root
                    && targets
                        .iter()
                        .any(|target| may_overlap(&store_place, target)))
                .then_some(loc)
            })
            .collect();
        // A hand-off names no written place, so it may overlap any target.
        sites.extend(self.handoff_sites_of(local));
        sites.into_iter().any(|site| self.reaches(site, at))
    }

    /// Like [`Self::store_reaches`], but only stores located OUTSIDE `exclude`
    /// count (a loop's own body blocks, whose stores the preservation phase
    /// owns, for the loop-entry check).
    pub(crate) fn store_outside_reaches(
        &mut self,
        local: Local,
        at: Location,
        exclude: &HashSet<BasicBlock>,
    ) -> bool {
        let root = self.find(local.as_usize());
        let mut sites: Vec<Location> = self
            .store_sites
            .clone()
            .into_iter()
            .filter_map(|(store_place, loc)| {
                (!exclude.contains(&loc.block) && self.find(store_place.local.as_usize()) == root)
                    .then_some(loc)
            })
            .collect();
        sites.extend(
            self.handoff_sites_of(local)
                .into_iter()
                .filter(|loc| !exclude.contains(&loc.block)),
        );
        sites.into_iter().any(|site| self.reaches(site, at))
    }

    /// Whether the value `operand` denotes at `at` may be read through a
    /// reference after a store through that reference's alias class — directly
    /// (`*p`, `&(*p)`, passing `p` itself) or through the definitions of the
    /// temporaries/locals it is computed from.
    pub(crate) fn operand_may_read_stale(&mut self, operand: &Operand<'tcx>, at: Location) -> bool {
        self.operand_may_read_stale_from(operand, at, &|_| true)
    }

    /// [`Self::operand_may_read_stale`] counting only the store sites
    /// `counts` accepts (by the place written). A caller that can prove a
    /// class of stores cannot change what it reads — a pointer-slot store
    /// `*tt = &mut y` redirects later derefs but leaves every VALUE local as
    /// it was — passes the narrower predicate; everything else keeps the
    /// full class.
    pub(crate) fn operand_may_read_stale_from(
        &mut self,
        operand: &Operand<'tcx>,
        at: Location,
        counts: &dyn Fn(&Place<'tcx>) -> bool,
    ) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let mut visited = HashSet::new();
                self.place_may_read_stale(*place, at, &mut visited, counts)
            }
            _ => false,
        }
    }

    /// [`Self::store_reaches`] restricted to the store sites `counts` accepts
    /// outside the excluded blocks.
    fn store_reaches_from(
        &mut self,
        local: Local,
        at: Location,
        counts: &dyn Fn(&Place<'tcx>) -> bool,
    ) -> bool {
        let root = self.find(local.as_usize());
        let held = self.class_is_held(local);
        let mut sites: Vec<Location> = self
            .store_sites
            .clone()
            .into_iter()
            .filter_map(|(store_place, loc)| {
                // In a holder's class a store's type says nothing of what it
                // reaches: `*t.0 = 5` writes the `i32` a borrowed `a` is.
                (!self.excluded_store_blocks.contains(&loc.block)
                    && (held || counts(&store_place))
                    && self.find(store_place.local.as_usize()) == root)
                    .then_some(loc)
            })
            .collect();
        let handoffs = self.handoff_sites_of(local);
        sites.extend(
            handoffs
                .into_iter()
                .filter(|loc| !self.excluded_store_blocks.contains(&loc.block)),
        );
        sites.into_iter().any(|site| self.reaches(site, at))
    }

    fn place_may_read_stale(
        &mut self,
        place: Place<'tcx>,
        at: Location,
        visited: &mut HashSet<Local>,
        counts: &dyn Fn(&Place<'tcx>) -> bool,
    ) -> bool {
        // Any read in the alias class of a store that can precede it: `*p`,
        // `&(*p).f`, the reference `p` itself, and also a borrowed local `v`
        // written through `r = &mut v; *r = 5` (the read of `v` is translated
        // from `v`'s binding, which the store through `r` does not update).
        if self.store_reaches_from(place.local, at, counts) {
            return true;
        }
        if !visited.insert(place.local) {
            return false;
        }
        let Some(defs) = self.defs.get(&place.local).cloned() else {
            return false;
        };
        for def in defs {
            let data = &self.body.basic_blocks[def.block];
            let mut collector = PlaceCollector { places: Vec::new() };
            if def.statement_index < data.statements.len() {
                if let StatementKind::Assign((_, rvalue)) =
                    &data.statements[def.statement_index].kind
                {
                    collector.visit_rvalue(rvalue, def);
                }
            } else if let TerminatorKind::Call { args, .. } = &data.terminator().kind {
                for arg in args {
                    collector.visit_operand(&arg.node, def);
                }
            }
            for read in collector.places {
                if self.place_may_read_stale(read, def, visited, counts) {
                    return true;
                }
            }
        }
        false
    }
}

/// The first of `names` (a source variable's name) that `body` binds to a
/// local a write through a holder of its borrow may have changed before `at`
/// ([`DerefStoreStaleness::holder_write_reaches`]). Every local a name is
/// bound to counts, a shadowed one included: a read the lane resolves to
/// either would be stale.
pub(crate) fn first_name_written_through_a_holder<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    at: Location,
    names: &HashSet<String>,
) -> Option<String> {
    let mut staleness = DerefStoreStaleness::new(Some(tcx), body);
    body.var_debug_info.iter().find_map(|debug| {
        let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value else {
            return None;
        };
        let name = debug.name.to_string();
        (names.contains(&name) && staleness.holder_write_reaches(place.local, at)).then_some(name)
    })
}

/// The definition of memory a read at a program point sees
/// ([`DerefStoreStaleness::unique_reaching_store`], D-186).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReachingStore {
    /// No write reaches the point: the entry value is read.
    Entry,
    /// Exactly one write, on no cycle, reaches the point on every path.
    One(Location),
    /// Two or more definitions join at the point, or the one that reaches
    /// it is carried round a back edge.
    Several,
}

/// What a lane knows of the memory read through a local at a program point
/// ([`DerefStoreStaleness::current_state`], D-185).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CurrentState {
    /// No write can precede the point: the entry value is the current one.
    Unwritten,
    /// Every write that can precede the point is `*local = v` through the
    /// local itself.
    DirectPointeeStores,
    /// The name is bound to a projection of a local (a closure's capture),
    /// and every write that can precede the point is a store to exactly that
    /// place.
    DirectPlaceStores,
    /// Some write that can precede the point is one no lane records as the
    /// memory's current value.
    Untracked,
}

/// The source names `body` binds whose reads at `at` go through memory a
/// write may have changed (D-185), with what is known of it
/// ([`DerefStoreStaleness::current_state`]). A name counts when its type
/// reads through memory (a reference, a raw pointer, a `Box`, or a value
/// that may carry a borrow) or when a store through a dereference rooted at
/// its own local reaches `at` (`*x.b = 5` of a by-value `x` with a `Box`
/// field); a plain value local written through a borrow of it is the
/// governed write-back lane's, which rebinds the local itself. Every local a
/// name is bound to counts, a shadowed one included, and the least-known
/// state wins.
pub(crate) fn names_read_through_written_memory<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    at: Location,
) -> HashMap<String, CurrentState> {
    let mut staleness = DerefStoreStaleness::new(Some(tcx), body);
    let mut states: HashMap<String, CurrentState> = HashMap::new();
    for debug in &body.var_debug_info {
        let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        let local = place.local;
        let ty = body.local_decls[local].ty;
        let is_argument = (1..=body.arg_count).contains(&local.as_usize());
        // A shared reference PARAMETER to memory no shared path can write (no
        // `UnsafeCell` and no raw pointer anywhere behind it) is the same
        // memory at every point of the call: nothing writes it. A local
        // shared borrow is not: `let r = &*x;` borrows memory a `&mut` owns,
        // which `*x = 5` writes once `r` is no longer used, and the walk's
        // `*r` (spelled `*x` once `r` resolves) is then the written value
        // (D-186).
        if place.projection.is_empty() && is_argument && shared_reference_to_frozen_memory(tcx, ty)
        {
            continue;
        }
        // A value that may carry a borrow reads borrowed memory when it is a
        // parameter (the caller's borrow) or a local that holds one in this
        // body (built around a borrow, or given one by a store): a local of
        // a generic type nothing in the body lends a borrow to is its own
        // memory, which the call and write-back lanes rebind.
        let holds_a_borrow = staleness.may_carry[local.as_usize()]
            && (is_argument || staleness.class_is_held(local));
        let reads_memory = place.projection.is_empty()
            && (ty.is_ref() || ty.is_raw_ptr() || ty.is_box() || holds_a_borrow);
        // A name bound to a projection of a local (a closure's capture,
        // `(*_1).0`) reads through that local's memory.
        let reads_memory = reads_memory || !place.projection.is_empty();
        if !reads_memory && !staleness.stores_behind(local, at) {
            continue;
        }
        let state = if place.projection.is_empty() {
            staleness.current_state(local, at)
        } else {
            staleness.current_state_of_place(*place, at)
        };
        if state == CurrentState::Unwritten {
            continue;
        }
        let name = debug.name.to_string();
        // Two bindings of one name known in two ways are not known as one.
        let merged = match states.get(&name) {
            Some(known) if *known != state => CurrentState::Untracked,
            _ => state,
        };
        states.insert(name, merged);
    }
    states
}

/// The names of [`names_read_through_written_memory`] whose memory exists at
/// the function's entry (D-185): a binding rooted at an argument, the
/// parameters and a closure's captures. Their `Deref(Var name)` (or the
/// capture's name) is the ENTRY value the preconditions and every copy taken
/// before the write speak of, so a fact stating the current value under that
/// symbol conflates the two. A local borrow's symbol names no entry value.
pub(crate) fn entry_memory_names_written_before<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    at: Location,
) -> HashSet<String> {
    let written = names_read_through_written_memory(tcx, body, at);
    let mut staleness = DerefStoreStaleness::new(Some(tcx), body);
    // The classes of the parameters whose own memory is written before `at`
    // (a `&mut` parameter's pointee, not a by-value parameter a local borrow
    // writes, which the governed write-back lane rebinds).
    let mut argument_classes: HashSet<usize> = HashSet::new();
    for debug in &body.var_debug_info {
        let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        if (1..=body.arg_count).contains(&place.local.as_usize())
            && written.contains_key(debug.name.as_str())
        {
            argument_classes.insert(staleness.find(place.local.as_usize()));
        }
    }
    body.var_debug_info
        .iter()
        .filter_map(|debug| {
            let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value else {
                return None;
            };
            let is_argument = (1..=body.arg_count).contains(&place.local.as_usize());
            // A local borrow of a parameter's memory (`let r = &*x;`) names
            // the parameter's entry symbol once it resolves (`*r` is `*x`):
            // its current-value binding is the same conflation (D-186).
            let borrows_entry_memory =
                argument_classes.contains(&staleness.find(place.local.as_usize()));
            let name = debug.name.to_string();
            ((is_argument || borrows_entry_memory) && written.contains_key(&name)).then_some(name)
        })
        .collect()
}

/// Per statement and call of `body`, the places it reads through a
/// dereference whose memory a write may have changed before it (D-185),
/// with what is known of that memory ([`DerefStoreStaleness::current_state`]).
/// A borrow taken of such a place (`&mut *x`, `&raw (*x).f`) reads no value
/// and is not listed.
///
/// The substitution walk translates a read of `*x` as the ENTRY pointee
/// (`Deref(Var x)`, which the encoders name `x_current`): `let v = *x` after
/// `*x = 5` bound `v` to the entry value, so `proof_assert!(v == 0)` under
/// `#[requires(*x == 0)]` was credited although `v` is 5. A read listed here
/// must take the value the walk recorded for that memory, or none.
pub(crate) fn written_deref_reads<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> HashMap<Location, Vec<(Place<'tcx>, CurrentState)>> {
    let mut staleness = DerefStoreStaleness::new(Some(tcx), body);
    let mut reads_at: HashMap<Location, Vec<(Place<'tcx>, CurrentState)>> = HashMap::new();
    let mut note = |staleness: &mut DerefStoreStaleness<'_, 'tcx>,
                    places: Vec<Place<'tcx>>,
                    location: Location| {
        for place in places {
            if !has_deref(&place) {
                continue;
            }
            let state = staleness.current_state(place.local, location);
            if state != CurrentState::Unwritten {
                reads_at.entry(location).or_default().push((place, state));
            }
        }
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let StatementKind::Assign((_, rvalue)) = &stmt.kind else {
                continue;
            };
            if matches!(rvalue, Rvalue::Ref(..) | Rvalue::RawPtr(..)) {
                continue;
            }
            let mut collector = PlaceCollector { places: Vec::new() };
            collector.visit_rvalue(rvalue, location);
            note(&mut staleness, collector.places, location);
        }
        if let TerminatorKind::Call { args, .. } = &data.terminator().kind {
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            let places = args.iter().filter_map(|arg| arg.node.place()).collect();
            note(&mut staleness, places, location);
        }
    }
    reads_at
}

/// Whether `ty` is `&T` with nothing a shared path reaches from `T` that
/// can be written through it (D-185): no `UnsafeCell`, no raw pointer, no
/// type this walk cannot see into (a parameter, a projection, a trait object,
/// a closure). A `&mut` reached through `&` gives shared access only, and a
/// `Box` owns its contents, so both are followed. A recursive type is read
/// once per definition.
fn shared_reference_to_frozen_memory<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    use rustc_middle::ty::TyKind;
    fn frozen<'tcx>(
        tcx: TyCtxt<'tcx>,
        ty: rustc_middle::ty::Ty<'tcx>,
        seen: &mut HashSet<rustc_hir::def_id::DefId>,
        depth: usize,
    ) -> bool {
        if depth > 16 {
            return false;
        }
        match ty.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Never => true,
            TyKind::Ref(_, inner, _) | TyKind::Array(inner, _) | TyKind::Slice(inner) => {
                frozen(tcx, *inner, seen, depth + 1)
            }
            TyKind::Tuple(fields) => fields
                .iter()
                .all(|field| frozen(tcx, field, seen, depth + 1)),
            TyKind::Adt(adt, args) => {
                if adt.is_unsafe_cell() {
                    return false;
                }
                if adt.is_phantom_data() {
                    return true;
                }
                if adt.is_box() {
                    return args.types().all(|arg| frozen(tcx, arg, seen, depth + 1));
                }
                if !seen.insert(adt.did()) {
                    return true;
                }
                adt.all_fields()
                    .all(|field| frozen(tcx, field.ty(tcx, *args).skip_norm_wip(), seen, depth + 1))
            }
            _ => false,
        }
    }
    match ty.kind() {
        TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Not) => {
            frozen(tcx, *inner, &mut HashSet::new(), 0)
        }
        _ => false,
    }
}

/// Per local of `body`, whether its type may carry a borrow a holder writes
/// through ([`ty_may_carry_a_borrow`]).
fn locals_that_may_carry_a_borrow(body: &Body<'_>) -> Vec<bool> {
    body.local_decls
        .iter()
        .map(|decl| ty_may_carry_a_borrow(decl.ty, 0))
        .collect()
}

/// Whether a value of `ty` may carry a borrow a holder writes through: a
/// `&mut` or a raw pointer; a shared reference to anything but plain values
/// (a `Cell` behind it is written through it); an ADT generic over a region,
/// or over a type that may carry one; a tuple, array or slice of those; or a
/// type whose contents this walk cannot see (a type parameter, a projection,
/// a trait object, a closure or coroutine, a foreign type). An ADT's fields
/// are not read here: a whole value moved on is unioned anyway. Over-counting
/// only makes more reads stale.
fn ty_may_carry_a_borrow(ty: rustc_middle::ty::Ty<'_>, depth: usize) -> bool {
    use rustc_middle::ty::TyKind;
    const MAX_DEPTH: usize = 8;
    if depth > MAX_DEPTH {
        return true;
    }
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never
        | TyKind::FnDef(..)
        | TyKind::FnPtr(..) => false,
        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) | TyKind::RawPtr(..) => true,
        TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Not) => {
            !is_a_plain_value(*inner, depth + 1) || ty_may_carry_a_borrow(*inner, depth + 1)
        }
        TyKind::Adt(_, args) => {
            args.regions().next().is_some()
                || args
                    .types()
                    .any(|arg| ty_may_carry_a_borrow(arg, depth + 1))
        }
        TyKind::Tuple(fields) => fields
            .iter()
            .any(|field| ty_may_carry_a_borrow(field, depth + 1)),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => ty_may_carry_a_borrow(*inner, depth + 1),
        _ => true,
    }
}

/// Whether `ty` is a shared reference through which nothing is written: the
/// memory behind it is scalars, `str`, and references, tuples, arrays and
/// slices of those, so no interior mutability and no raw pointer is reached
/// (a `&mut` behind a `&` gives shared access only).
fn reads_only_through(ty: rustc_middle::ty::Ty<'_>) -> bool {
    fn no_write_capability(ty: rustc_middle::ty::Ty<'_>, depth: usize) -> bool {
        use rustc_middle::ty::TyKind;
        if depth > 8 {
            return false;
        }
        match ty.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Never => true,
            TyKind::Ref(_, inner, _) | TyKind::Array(inner, _) | TyKind::Slice(inner) => {
                no_write_capability(*inner, depth + 1)
            }
            TyKind::Tuple(fields) => fields
                .iter()
                .all(|field| no_write_capability(field, depth + 1)),
            _ => false,
        }
    }
    match ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Not) => {
            no_write_capability(*inner, 0)
        }
        // A closure whose every capture is such a shared reference (the
        // closure `snapshot!(p.0)` hands `Snapshot::from_fn`) writes nothing
        // through them.
        rustc_middle::ty::TyKind::Closure(_, args) => args
            .as_closure()
            .upvar_tys()
            .iter()
            .all(|upvar| reads_only_through(upvar)),
        // A struct whose every field is a `PhantomData` holds no memory to
        // write through (the zero-sized `SnapshotCaptureSelect<&mut i32>`
        // selector a `snapshot!` hands its capture).
        rustc_middle::ty::TyKind::Adt(adt, _) if adt.is_struct() => {
            rustc_middle::ty::tls::with_opt(|tcx| {
                tcx.is_some_and(|tcx| {
                    adt.all_fields()
                        .all(|field| tcx.type_of(field.did).skip_binder().is_phantom_data())
                })
            })
        }
        _ => false,
    }
}

/// Whether `ty` is built of scalars and `str` alone, so no shared reference to
/// it is written through.
fn is_a_plain_value(ty: rustc_middle::ty::Ty<'_>, depth: usize) -> bool {
    use rustc_middle::ty::TyKind;
    if depth > 8 {
        return false;
    }
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never => true,
        TyKind::Tuple(fields) => fields
            .iter()
            .all(|field| is_a_plain_value(field, depth + 1)),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => is_a_plain_value(*inner, depth + 1),
        TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Not) => {
            is_a_plain_value(*inner, depth + 1)
        }
        _ => false,
    }
}

/// A referent the returned borrow points at: a base local plus the projection
/// that reaches the borrowed sub-place. Owned (not an interned `Place`) because
/// resolving `_0 = move _1` has to synthesize the `*_1` referent, which needs no
/// `TyCtxt` in this form.
type Referent<'tcx> = (
    Local,
    Vec<ProjectionElem<Local, rustc_middle::ty::Ty<'tcx>>>,
);

/// Do a written place and a returned referent denote overlapping memory?
///
/// Conservative: `true` whenever the two cannot be compared (different base
/// locals — the alias class already said they may be the same borrow — or a
/// projection pair this function does not decide). `false` only on a PROVEN
/// divergence: two different fields, two different enum variants, or two
/// different constant indices of the same base.
fn may_overlap<'tcx>(store: &Place<'tcx>, referent: &Referent<'tcx>) -> bool {
    may_overlap_referents(&(store.local, store.projection.to_vec()), referent)
}

/// Whether two referents name the same place, the types a projection carries
/// aside (a field's type differs by region between a store and the debug
/// info naming the place).
fn same_place<'tcx>(a: &Referent<'tcx>, b: &Referent<'tcx>) -> bool {
    a.0 == b.0
        && a.1.len() == b.1.len()
        && a.1.iter().zip(b.1.iter()).all(|(x, y)| match (x, y) {
            (ProjectionElem::Field(i, _), ProjectionElem::Field(j, _)) => i == j,
            (ProjectionElem::Deref, ProjectionElem::Deref) => true,
            (ProjectionElem::Downcast(_, v), ProjectionElem::Downcast(_, w)) => v == w,
            _ => false,
        })
}

/// [`may_overlap`] of two places given as referents.
fn may_overlap_referents<'tcx>(store: &Referent<'tcx>, referent: &Referent<'tcx>) -> bool {
    if store.0 != referent.0 {
        return true;
    }
    for (a, b) in store.1.iter().copied().zip(referent.1.iter()) {
        if a == *b {
            continue;
        }
        match (a, b) {
            (ProjectionElem::Field(i, _), ProjectionElem::Field(j, _)) if i != *j => return false,
            (ProjectionElem::Downcast(_, v1), ProjectionElem::Downcast(_, v2)) if v1 != *v2 => {
                return false
            }
            (
                ProjectionElem::ConstantIndex {
                    offset: o1,
                    from_end: e1,
                    ..
                },
                ProjectionElem::ConstantIndex {
                    offset: o2,
                    from_end: e2,
                    ..
                },
            ) if e1 == *e2 && o1 != *o2 => return false,
            _ => return true,
        }
    }
    // One projection is a prefix of the other: the places nest, so they overlap.
    true
}

/// The unique `L = &PLACE` / `L = &mut PLACE` definition of `L`, when that is
/// the ONLY assignment to `L` in the body. Anything else (no definition,
/// several, a call destination, a different rvalue) yields `None`.
fn sole_borrow_source<'tcx>(body: &Body<'tcx>, local: Local) -> Option<Place<'tcx>> {
    let mut found: Option<Place<'tcx>> = None;
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            let StatementKind::Assign((place, rvalue)) = &stmt.kind else {
                continue;
            };
            if place.local != local {
                continue;
            }
            if !place.projection.is_empty() || found.is_some() {
                return None;
            }
            match rvalue {
                Rvalue::Ref(_, _, src) | Rvalue::RawPtr(_, src) => found = Some(*src),
                _ => return None,
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
            if destination.local == local {
                return None;
            }
        }
    }
    found
}

/// Rewrite `(L, [Deref, ..rest])` into the place `L` was borrowed from, so a
/// referent reached through a chain of reborrows is expressed over the same
/// base local the stores are written through. Stops at the first step it cannot
/// resolve exactly, which keeps the result conservative: an unresolved base
/// simply never proves disjointness in [`may_overlap`].
fn normalize_referent<'tcx>(body: &Body<'tcx>, referent: Referent<'tcx>) -> Referent<'tcx> {
    let mut current = referent;
    for _ in 0..MAX_REBORROW_CHAIN {
        let Some((first, tail)) = current.1.split_first() else {
            break;
        };
        if !matches!(first, ProjectionElem::Deref) {
            break;
        }
        let Some(src) = sole_borrow_source(body, current.0) else {
            break;
        };
        let mut projection = src.projection.to_vec();
        projection.extend_from_slice(tail);
        current = (src.local, projection);
    }
    current
}

/// Depth cap for [`normalize_referent`].
const MAX_REBORROW_CHAIN: usize = 8;

/// The referents the function's return value borrows, when this pass can
/// resolve them exactly. `None` means "unresolved" and every caller must then
/// fall back to the alias-class-only answer.
fn returned_referents<'tcx>(body: &Body<'tcx>) -> Option<Vec<Referent<'tcx>>> {
    let mut out = Vec::new();
    let mut visited = HashSet::new();
    resolve_referents(body, Local::from_u32(0), &mut visited, &mut out)?;
    let out: Vec<Referent<'tcx>> = out
        .into_iter()
        .map(|referent| normalize_referent(body, referent))
        .collect();
    (!out.is_empty()).then_some(out)
}

fn resolve_referents<'tcx>(
    body: &Body<'tcx>,
    local: Local,
    visited: &mut HashSet<Local>,
    out: &mut Vec<Referent<'tcx>>,
) -> Option<()> {
    if !visited.insert(local) {
        return Some(());
    }
    // A parameter slot is never reassigned in post-borrowck MIR of the shapes
    // this pass resolves; reaching one means the borrow IS that parameter, and
    // its referent is `*param`.
    let mut saw_def = false;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            let StatementKind::Assign((place, rvalue)) = &stmt.kind else {
                continue;
            };
            if place.local != local || !place.projection.is_empty() {
                continue;
            }
            saw_def = true;
            match rvalue {
                Rvalue::Ref(_, _, src) | Rvalue::RawPtr(_, src) => {
                    out.push((src.local, src.projection.to_vec()));
                }
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _)
                | Rvalue::CopyForDeref(src) => {
                    if src.projection.is_empty() {
                        resolve_referents(body, src.local, visited, out)?;
                    } else if src.projection.len() == 1
                        && matches!(src.projection[0], ProjectionElem::Deref)
                    {
                        // `_k = (*_j)` on a reference-typed local is a reborrow
                        // of `_j`'s referent in disguise only when `_k` is a
                        // reference; anything else is a value read, which this
                        // pass does not model.
                        return None;
                    } else {
                        return None;
                    }
                }
                _ => return None,
            }
        }
        let _ = block;
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
            if destination.local == local && destination.projection.is_empty() {
                // A borrow that came out of a call: its referent is the
                // callee's business, not resolvable here.
                return None;
            }
        }
    }
    if !saw_def {
        if body.args_iter().any(|arg| arg == local) {
            // The return value IS the parameter borrow; its referent is `*p`.
            out.push((local, vec![ProjectionElem::Deref]));
        } else {
            return None;
        }
    }
    Some(())
}

/// The parameters whose pointee can be written through — directly, or through
/// an alias of the parameter's borrow — on a path that reaches a `Return`, by a
/// store that may overlap the memory the RETURNED borrow points at.
/// (handback-entry-value)
///
/// A parameter in this set is one whose borrow, if it is handed back as (part
/// of) the return value, is NOT the entry borrow any more: the returned
/// reference's CURRENT pointee is the value the body last stored, while the
/// extraction lanes translate the returned expression as `Var(p)`, whose
/// `current` component the encoders bind to the ENTRY pointee. Discharging
/// `result == p` against that binding is the false accept this set closes:
///
/// ```text
/// #[ensures(result == p)] fn f(p: &mut u32) -> &mut u32 { *p = 9; p }
/// ```
///
/// Creusot reads `result == p` on a `&mut` as `*result == *p && ^result == ^p`
/// with `*p` the ENTRY pointee, so this body does not satisfy its own contract.
///
/// The analysis is the flow-sensitive store/alias summary already used for
/// stale callee-precondition reads, asked at each `Return` instead of at a
/// call, and narrowed to stores that may overlap the returned referent so a
/// write to a SIBLING field (`s.1 = 9; &mut s.0`) does not withdraw a true
/// claim. It is an over-approximation everywhere it cannot decide, and callers
/// use it only to DELETE an accept path.
pub(crate) fn params_written_before_return<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> HashSet<String> {
    let returns: Vec<Location> = body
        .basic_blocks
        .iter_enumerated()
        .filter(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Return))
        .map(|(block, data)| Location {
            block,
            statement_index: data.statements.len(),
        })
        .collect();
    if returns.is_empty() {
        return HashSet::new();
    }
    let referents = returned_referents(body);
    let mut staleness = DerefStoreStaleness::new(Some(tcx), body);
    let mut written = HashSet::new();
    for (idx, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(idx + 1);
        if local.as_usize() >= body.local_decls.len() {
            continue;
        }
        let hit = match referents.as_ref() {
            Some(targets) => returns
                .iter()
                .any(|at| staleness.overlapping_store_reaches(local, *at, targets)),
            None => returns.iter().any(|at| staleness.store_reaches(local, *at)),
        };
        if hit {
            written.insert(name.clone());
        }
    }
    written
}
