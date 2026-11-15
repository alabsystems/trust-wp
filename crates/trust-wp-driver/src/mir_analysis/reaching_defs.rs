// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Which definitions of a local reach a program point?
//!
//! The owner resolver used to ask "does the WHOLE BODY contain exactly one
//! definition of this local?", which is the wrong question: a borrow local
//! reassigned anywhere governs a different place at different points, and a
//! body-wide answer would have to guess which definition speaks. The question
//! this module answers instead is "which definitions reach THIS point?", and
//! the resolver may only take credit when the answer is a single definition.
//!
//! A may-analysis: the reaching set over-approximates, so a missed KILL is the
//! hazard, not a missed gen. Every write into a local's storage that this
//! module cannot read a value out of is still recorded as a definition — an
//! [`DefKind::Opaque`] one — precisely so that it kills the definitions before
//! it and the resolver refuses at points it reaches.
//!
//! Results are owned and hold no reference into the body: a `Location` is
//! meaningful only against the body it was computed on, and handing out an
//! rvalue borrowed from one body while the caller walks another is how a
//! confidently wrong owner gets stated. Every query takes the body back.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
        BasicBlock, Body, Local, Location, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::TyCtxt,
};

/// What a definition says about the local's value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum DefKind {
    /// `l = rv`: the rvalue of the statement at this location is the new value.
    Direct,
    /// `(*a) = rv` through an alias of `l`'s own slot: the same rvalue, reached
    /// the other way round. Only ever recorded for a slot whose every store
    /// resolved to exactly this local.
    Indirect,
    /// A write into the local's storage no value can be read out of — a call
    /// destination, a store into a field, a discriminant, an asm output — or
    /// the end of its storage. It kills what came before it and resolves to
    /// nothing.
    Opaque,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Def {
    pub(crate) loc: Location,
    pub(crate) kind: DefKind,
}

/// One statement's effect on one local: it always kills that local's earlier
/// definitions, and may add one of its own.
#[derive(Clone, Copy)]
struct Effect {
    local: Local,
    gen_def: Option<usize>,
}

/// A set of definition indices.
type Bits = Vec<bool>;

fn union_into(dest: &mut Bits, src: &Bits) -> bool {
    let mut changed = false;
    for (d, s) in dest.iter_mut().zip(src.iter()) {
        if *s && !*d {
            *d = true;
            changed = true;
        }
    }
    changed
}

pub(crate) struct ReachingDefs {
    /// Flat numbering; `defs[i].0` is the local the definition writes.
    defs: Vec<(Local, Def)>,
    of_local: HashMap<Local, Vec<usize>>,
    effects: HashMap<Location, Vec<Effect>>,
    entry: Vec<Bits>,
    /// Locals whose slot some alias can store through by a route this module
    /// cannot follow. Their value at any point is unknowable here.
    unresolvable: HashSet<Local>,
}

impl ReachingDefs {
    /// Is `local`'s own slot redirectable by an alias this module cannot follow?
    pub(crate) fn is_unresolvable(&self, local: Local) -> bool {
        self.unresolvable.contains(&local)
    }

    /// The definitions of `local` that reach the point just BEFORE the
    /// statement or terminator at `at`.
    ///
    /// An empty answer means no definition reaches: the local is unwritten on
    /// some path to here, or its storage ended. Callers refuse on it, the same
    /// as they refuse an [`DefKind::Opaque`] one.
    pub(crate) fn reaching(&self, body: &Body<'_>, local: Local, at: Location) -> Vec<Def> {
        let Some(indices) = self.of_local.get(&local) else {
            return Vec::new();
        };
        let Some(state) = self.state_before(body, at) else {
            return Vec::new();
        };
        indices
            .iter()
            .filter(|&&i| state[i])
            .map(|&i| self.defs[i].1)
            .collect()
    }

    /// The dataflow state before the statement at `at`: the block's entry set
    /// replayed through the statements that precede it.
    fn state_before(&self, body: &Body<'_>, at: Location) -> Option<Bits> {
        let block = at.block;
        if block.as_usize() >= self.entry.len() {
            return None;
        }
        let data = &body.basic_blocks[block];
        if at.statement_index > data.statements.len() {
            return None;
        }
        let mut state = self.entry[block.as_usize()].clone();
        for index in 0..at.statement_index {
            self.apply_at(
                &mut state,
                Location {
                    block,
                    statement_index: index,
                },
            );
        }
        Some(state)
    }

    fn apply_at(&self, state: &mut Bits, loc: Location) {
        let Some(effects) = self.effects.get(&loc) else {
            return;
        };
        for effect in effects {
            if let Some(indices) = self.of_local.get(&effect.local) {
                for &i in indices {
                    state[i] = false;
                }
            }
            if let Some(i) = effect.gen_def {
                state[i] = true;
            }
        }
    }
}

/// Build the reaching-definition facts for `body`.
///
/// Three strata, each monotone: the escape scan, the base analysis with every
/// escaped local refused, and — only for a slot whose every store through an
/// alias resolves to that slot itself — a rebuild with those stores folded in
/// as definitions.
pub(crate) fn compute<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> ReachingDefs {
    let mut unresolvable = HashSet::new();
    let mut redirected: Vec<(Local, Vec<Location>)> = Vec::new();
    for local in escaped_slots(body) {
        match slot_scan(body, local) {
            SlotVerdict::Stable => {}
            SlotVerdict::Opaque => {
                unresolvable.insert(local);
            }
            SlotVerdict::Redirected(sites) => {
                unresolvable.insert(local);
                redirected.push((local, sites));
            }
        }
    }

    let base = build(body, &unresolvable, &[]);
    if redirected.is_empty() {
        return base;
    }

    // A slot every alias store resolves back to is not a guess: the store IS
    // the definition, and folding it in kills the definition it replaces. A
    // slot with one store this resolver cannot pin down stays refused —
    // crediting the others would leave the unfollowed one speaking for a place
    // it no longer names.
    let mut promoted: Vec<(Local, Location)> = Vec::new();
    for (local, sites) in &redirected {
        let all_exact = sites
            .iter()
            .all(|&site| super::governed_place::resolves_to_owner(tcx, body, &base, *local, site));
        if all_exact {
            for &site in sites {
                promoted.push((*local, site));
            }
        }
    }
    if promoted.is_empty() {
        return base;
    }
    for (local, _) in &promoted {
        unresolvable.remove(local);
    }
    build(body, &unresolvable, &promoted)
}

/// The forward may-analysis itself.
///
/// Hand-rolled rather than run through `rustc_mir_dataflow` because the result
/// must outlive the body borrow it was computed from: the framework's cursor
/// keeps that borrow, and the resolver needs to hand the facts back with a
/// different body reference in hand so a mismatch is a type error rather than
/// a silently wrong answer.
fn build(
    body: &Body<'_>,
    unresolvable: &HashSet<Local>,
    indirect: &[(Local, Location)],
) -> ReachingDefs {
    let mut defs: Vec<(Local, Def)> = Vec::new();
    let mut effects: HashMap<Location, Vec<Effect>> = HashMap::new();

    let record = |defs: &mut Vec<(Local, Def)>,
                  effects: &mut HashMap<Location, Vec<Effect>>,
                  local: Local,
                  loc: Location,
                  kind: Option<DefKind>| {
        let gen_def = kind.map(|kind| {
            defs.push((local, Def { loc, kind }));
            defs.len() - 1
        });
        effects
            .entry(loc)
            .or_default()
            .push(Effect { local, gen_def });
    };

    let indirect_at: HashMap<Location, Local> = indirect.iter().map(|&(l, s)| (s, l)).collect();

    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (index, stmt) in data.statements.iter().enumerate() {
            let loc = Location {
                block,
                statement_index: index,
            };
            match &stmt.kind {
                StatementKind::Assign((dest, _)) => {
                    let through_deref = dest
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Deref));
                    if dest.projection.is_empty() {
                        record(
                            &mut defs,
                            &mut effects,
                            dest.local,
                            loc,
                            Some(DefKind::Direct),
                        );
                    } else if !through_deref {
                        // A store into a field can redirect a borrow the
                        // aggregate hop would otherwise read straight out of
                        // the constructor. Field-precise tracking would make
                        // this a definition of one field; a definition of the
                        // whole local that resolves to nothing is the same
                        // refusal this resolver has always made, without the
                        // precision that would have to be right.
                        record(
                            &mut defs,
                            &mut effects,
                            dest.local,
                            loc,
                            Some(DefKind::Opaque),
                        );
                    }
                    if let Some(&owner) = indirect_at.get(&loc) {
                        record(&mut defs, &mut effects, owner, loc, Some(DefKind::Indirect));
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if !place
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Deref))
                    {
                        record(
                            &mut defs,
                            &mut effects,
                            place.local,
                            loc,
                            Some(DefKind::Opaque),
                        );
                    }
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    // No read of the local is admitted across either without an
                    // intervening definition, so killing here loses nothing and
                    // stops a dead definition reaching a join.
                    record(&mut defs, &mut effects, *local, loc, None);
                }
                _ => {}
            }
        }
        let loc = Location {
            block,
            statement_index: data.statements.len(),
        };
        match &data.terminator().kind {
            TerminatorKind::Call { destination, .. } => {
                if !destination
                    .projection
                    .iter()
                    .any(|elem| matches!(elem, ProjectionElem::Deref))
                {
                    record(
                        &mut defs,
                        &mut effects,
                        destination.local,
                        loc,
                        Some(DefKind::Opaque),
                    );
                }
            }
            TerminatorKind::Yield { resume_arg, .. } => {
                record(
                    &mut defs,
                    &mut effects,
                    resume_arg.local,
                    loc,
                    Some(DefKind::Opaque),
                );
            }
            TerminatorKind::InlineAsm { operands, .. } => {
                for operand in operands {
                    for place in asm_output_places(operand) {
                        record(
                            &mut defs,
                            &mut effects,
                            place.local,
                            loc,
                            Some(DefKind::Opaque),
                        );
                    }
                }
            }
            _ => {}
        }
    }

    let mut of_local: HashMap<Local, Vec<usize>> = HashMap::new();
    for (i, (local, _)) in defs.iter().enumerate() {
        of_local.entry(*local).or_default().push(i);
    }

    let n = defs.len();
    let block_count = body.basic_blocks.len();
    let mut entry: Vec<Bits> = vec![vec![false; n]; block_count];
    let mut partial = ReachingDefs {
        defs,
        of_local,
        effects,
        entry: Vec::new(),
        unresolvable: unresolvable.clone(),
    };

    // Worklist to fixpoint. The domain is finite and every transfer is
    // monotone, so the loop terminates; the bound is belt-and-braces. Reaching
    // it would leave a state that has not converged, and a not-yet-converged
    // MAY-analysis UNDER-approximates — it could show one definition where two
    // reach, which is the credit direction. So the bound does not break out
    // with what it has: it refuses every local in the body.
    let mut worklist: Vec<BasicBlock> = body.basic_blocks.indices().collect();
    let mut guard = 0usize;
    let bound = block_count
        .saturating_mul(n + 1)
        .saturating_add(block_count)
        + 1;
    let mut converged = true;
    while let Some(block) = worklist.pop() {
        guard += 1;
        if guard > bound {
            converged = false;
            break;
        }
        let data = &body.basic_blocks[block];
        let mut state = entry[block.as_usize()].clone();
        for index in 0..=data.statements.len() {
            partial.apply_at(
                &mut state,
                Location {
                    block,
                    statement_index: index,
                },
            );
        }
        for succ in data.terminator().successors() {
            if union_into(&mut entry[succ.as_usize()], &state) {
                worklist.push(succ);
            }
        }
    }
    partial.entry = entry;
    if !converged {
        partial.unresolvable.extend(body.local_decls.indices());
    }
    partial
}

fn asm_output_places<'tcx>(
    operand: &rustc_middle::mir::InlineAsmOperand<'tcx>,
) -> Vec<Place<'tcx>> {
    use rustc_middle::mir::InlineAsmOperand as Op;
    match operand {
        Op::Out { place, .. }
        | Op::InOut {
            out_place: place, ..
        } => place.iter().copied().collect(),
        Op::Label { .. }
        | Op::In { .. }
        | Op::Const { .. }
        | Op::SymFn { .. }
        | Op::SymStatic { .. } => Vec::new(),
    }
}

/// Locals whose own slot is borrowed somewhere: `&mut l` / `&l` / `&raw l`
/// with nothing between the borrow and the local. `&mut *l` and `&mut l.f`
/// reach past the slot and cannot redirect it.
fn escaped_slots(body: &Body<'_>) -> Vec<Local> {
    let mut found: Vec<Local> = Vec::new();
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            let StatementKind::Assign((_, rvalue)) = &stmt.kind else {
                continue;
            };
            let (Rvalue::Ref(_, _, src) | Rvalue::RawPtr(_, src)) = rvalue else {
                continue;
            };
            if src.projection.is_empty() && !found.contains(&src.local) {
                found.push(src.local);
            }
        }
    }
    found
}

enum SlotVerdict {
    /// No alias can store through the slot.
    Stable,
    /// Aliases store into the slot at these locations, and every other use of
    /// every alias is one this scan can account for.
    Redirected(Vec<Location>),
    /// An alias reached code this scan cannot follow.
    Opaque,
}

/// What can happen to `local`'s own slot through the aliases of it?
///
/// Reading through an alias is harmless — that is how `&mut **x` reaches its
/// pointee — so the test is on what each alias is USED for. A store through an
/// alias is the one use that is neither harmless nor unfollowable: it is a
/// definition, and it is reported as one.
fn slot_scan(body: &Body<'_>, local: Local) -> SlotVerdict {
    // Aliases of the slot, to a fixpoint: a bare borrow of the local, and a
    // mutable reborrow of an alias, which is the same name a second time.
    let mut aliases: Vec<Local> = Vec::new();
    let mut reborrow_sites: HashMap<Location, (Local, Local)> = HashMap::new();
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            let StatementKind::Assign((dest, rvalue)) = &stmt.kind else {
                continue;
            };
            let (Rvalue::Ref(_, _, src) | Rvalue::RawPtr(_, src)) = rvalue else {
                continue;
            };
            if src.local != local || !src.projection.is_empty() {
                continue;
            }
            // A borrow of the slot stored into a field hands the slot's address
            // to a carrier this scan does not follow.
            if !dest.projection.is_empty() {
                return SlotVerdict::Opaque;
            }
            if !aliases.contains(&dest.local) {
                aliases.push(dest.local);
            }
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (index, stmt) in data.statements.iter().enumerate() {
                let StatementKind::Assign((dest, Rvalue::Ref(_, kind, src))) = &stmt.kind else {
                    continue;
                };
                if !kind.mutability().is_mut() {
                    continue;
                }
                if !aliases.contains(&src.local)
                    || src.projection.len() != 1
                    || !matches!(src.projection.first(), Some(ProjectionElem::Deref))
                    || !dest.projection.is_empty()
                {
                    continue;
                }
                let loc = Location {
                    block,
                    statement_index: index,
                };
                reborrow_sites.insert(loc, (src.local, dest.local));
                if !aliases.contains(&dest.local) {
                    aliases.push(dest.local);
                    changed = true;
                }
            }
        }
    }

    let mut store_sites: HashSet<Location> = HashSet::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (index, stmt) in data.statements.iter().enumerate() {
            let StatementKind::Assign((dest, _)) = &stmt.kind else {
                continue;
            };
            if aliases.contains(&dest.local)
                && dest.projection.len() == 1
                && matches!(dest.projection.first(), Some(ProjectionElem::Deref))
            {
                store_sites.insert(Location {
                    block,
                    statement_index: index,
                });
            }
        }
    }

    struct Scan<'a> {
        aliases: &'a [Local],
        reborrow_sites: &'a HashMap<Location, (Local, Local)>,
        store_sites: &'a HashSet<Location>,
        followable: bool,
        stores: HashSet<Location>,
    }
    impl<'tcx> Visitor<'tcx> for Scan<'_> {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            if !self.aliases.contains(&place.local) {
                return;
            }
            let through_deref = matches!(place.projection.first(), Some(ProjectionElem::Deref));
            let slot_depth = through_deref && place.projection.len() == 1;
            let ok = match context {
                PlaceContext::NonUse(_) => true,
                PlaceContext::MutatingUse(MutatingUseContext::Store) if slot_depth => {
                    // The redirect itself. It is a definition of the slot, not
                    // a reason to refuse it — as long as everything else about
                    // the alias is followable and the store resolves back here.
                    if self.store_sites.contains(&location) {
                        self.stores.insert(location);
                        true
                    } else {
                        false
                    }
                }
                PlaceContext::MutatingUse(
                    MutatingUseContext::Store
                    | MutatingUseContext::Call
                    | MutatingUseContext::SetDiscriminant
                    | MutatingUseContext::AsmOutput
                    | MutatingUseContext::Yield,
                ) => place.projection.is_empty(),
                PlaceContext::MutatingUse(MutatingUseContext::Borrow) if slot_depth => self
                    .reborrow_sites
                    .get(&location)
                    .is_some_and(|&(src, _)| src == place.local),
                PlaceContext::MutatingUse(
                    MutatingUseContext::Borrow | MutatingUseContext::RawBorrow,
                )
                | PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow) => {
                    through_deref && place.projection.len() >= 2
                }
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::SharedBorrow
                    | NonMutatingUseContext::FakeBorrow
                    | NonMutatingUseContext::Inspect
                    | NonMutatingUseContext::PlaceMention,
                ) => true,
                PlaceContext::NonMutatingUse(_) => through_deref,
                _ => false,
            };
            if !ok {
                self.followable = false;
            }
        }
    }
    let mut scan = Scan {
        aliases: &aliases,
        reborrow_sites: &reborrow_sites,
        store_sites: &store_sites,
        followable: true,
        stores: HashSet::new(),
    };
    scan.visit_body(body);
    if !scan.followable {
        return SlotVerdict::Opaque;
    }
    if scan.stores.is_empty() {
        return SlotVerdict::Stable;
    }
    let mut sites: Vec<Location> = scan.stores.into_iter().collect();
    sites.sort_by_key(|loc| (loc.block.as_usize(), loc.statement_index));
    SlotVerdict::Redirected(sites)
}

thread_local! {
    /// Bodies are copied once per compilation and never replaced, so a body
    /// pointer names the same body for the session. The shape fields are a
    /// second check: an answer computed on one body and handed out for another
    /// would index a different statement at the same location and name a
    /// confidently wrong owner.
    static MEMO: std::cell::RefCell<Vec<(usize, usize, usize, std::rc::Rc<ReachingDefs>)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

const MEMO_CAPACITY: usize = 8;

/// The reaching-definition facts for `body`, computed once per body.
pub(crate) fn for_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> std::rc::Rc<ReachingDefs> {
    let key = (
        std::ptr::from_ref(body) as usize,
        body.basic_blocks.len(),
        body.local_decls.len(),
    );
    if let Some(hit) = MEMO.with(|memo| {
        memo.borrow()
            .iter()
            .find(|entry| (entry.0, entry.1, entry.2) == key)
            .map(|entry| entry.3.clone())
    }) {
        return hit;
    }
    let computed = std::rc::Rc::new(compute(tcx, body));
    MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.len() >= MEMO_CAPACITY {
            memo.remove(0);
        }
        memo.push((key.0, key.1, key.2, computed.clone()));
    });
    computed
}
