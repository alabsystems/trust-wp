// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Value stability of a `SwitchInt` discriminant (FRONT H step 1).
//!
//! A panic arm's condition becomes a proof OBLIGATION built from the
//! extractor's `local_exprs` translation of the switch operand. That
//! translation only follows projection-free assignments. A write through a
//! projection (`*x = -1`, `s.f = 0`), through a `&mut`/raw-mut borrow of a
//! local, or through a `&mut`-typed local is invisible to it, so the
//! translated condition can denote a STALE value — and a stale value that
//! happens to satisfy the assertion would discharge the obligation for a
//! program that panics on every run (`h1_assert_after_deref_write`).
//!
//! [`switch_discr_is_value_stable`] answers, conservatively, whether the
//! operand's transitive MIR def-use dependencies are free of every such
//! write. Callers emit the obligation `false` when it returns `false`:
//! refusing costs completeness, never soundness.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
        BasicBlock, Body, Local, Location, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind, UnOp,
    },
    ty::TyCtxt,
};

#[derive(Default)]
struct LocalCollector {
    locals: Vec<Local>,
}

impl<'tcx> Visitor<'tcx> for LocalCollector {
    fn visit_local(&mut self, local: Local, _context: PlaceContext, _location: Location) {
        self.locals.push(local);
    }
}

#[derive(Default)]
struct IndirectWriteCollector {
    indirect: HashSet<Local>,
    /// The subset whose write or `&mut` borrow reaches the local's OWN storage:
    /// the place has no `Deref`, so it is not memory the local points to.
    own_storage: HashSet<Local>,
}

impl<'tcx> Visitor<'tcx> for IndirectWriteCollector {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        let borrowed_mutably = matches!(
            context,
            PlaceContext::MutatingUse(MutatingUseContext::Borrow | MutatingUseContext::RawBorrow)
        );
        if borrowed_mutably || (context.is_mutating_use() && !place.projection.is_empty()) {
            self.indirect.insert(place.local);
            if !place
                .projection
                .iter()
                .any(|elem| matches!(elem, ProjectionElem::Deref))
            {
                self.own_storage.insert(place.local);
            }
        }
        self.super_place(place, context, location);
    }
}

/// What a transitive read needs to be unchanged.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Demand {
    /// The local's whole value.
    Value,
    /// Only the length a slice pointer carries. The length is part
    /// of the pointer VALUE, not of the memory it points to: a write through
    /// the pointer (`(*p)[i] = v`, `&mut *p`) cannot change it, and `[T]` is
    /// unsized, so nothing can assign a pointee of another length in place.
    /// Only a write to the local's OWN storage (`p = q`, `&mut p`) can.
    SliceLength,
}

/// How one projection-free definition reads the locals it depends on.
enum DefReads {
    /// Every read local, at whatever the definition is demanded at.
    All(Vec<Local>),
    /// `PtrMetadata(p)`: the value is the length `p` carries, whatever the
    /// definition is demanded at.
    LengthOf(Local),
    /// `q = p` (a copy or move), or `q = &*p` / `&raw (fake) *p` over a slice
    /// pointee: `q` carries `p`'s length. Demanded at its length, it
    /// demands `p`'s length; demanded whole, every read local whole.
    SamePointer { source: Local, reads: Vec<Local> },
}

/// A place that is exactly `*p`, dereferencing a pointer to a slice.
fn slice_pointee_of<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    place: &Place<'tcx>,
) -> Option<Local> {
    let [ProjectionElem::Deref] = place.projection.as_slice() else {
        return None;
    };
    let pointee = place.ty(&body.local_decls, tcx).ty;
    pointee.is_slice().then_some(place.local)
}

/// The plain local an operand copies or moves, if it has no projection.
fn plain_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
    }
}

fn rvalue_reads<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    location: Location,
) -> DefReads {
    let mut reads = LocalCollector::default();
    reads.visit_rvalue(rvalue, location);
    let pointer = |local: Local| {
        let ty = body.local_decls[local].ty;
        ty.builtin_deref(true)
            .is_some_and(|pointee| pointee.is_slice())
    };
    match rvalue {
        Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => match plain_local(operand) {
            Some(source) if pointer(source) => DefReads::LengthOf(source),
            _ => DefReads::All(reads.locals),
        },
        Rvalue::Use(operand, _) => match plain_local(operand) {
            Some(source) if pointer(source) => DefReads::SamePointer {
                source,
                reads: reads.locals,
            },
            _ => DefReads::All(reads.locals),
        },
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
            match slice_pointee_of(body, tcx, place) {
                Some(source) => DefReads::SamePointer {
                    source,
                    reads: reads.locals,
                },
                None => DefReads::All(reads.locals),
            }
        }
        _ => DefReads::All(reads.locals),
    }
}

/// Return `true` only when every local the switch operand transitively reads
/// is provably unaffected by writes the extractor cannot see.
///
/// `flow_insensitive` selects the stricter rule for walkers that resolve
/// `local_exprs` without following control flow (`call_effect_blocks`): there a
/// user variable or parameter is pinned to its symbolic name and a temporary
/// keeps its FIRST resolved assignment, so any direct reassignment of a user
/// variable/parameter, or a temporary with more than one assignment site, is
/// also refused.
///
/// A read of a slice pointer's LENGTH (the `PtrMetadata` of a bounds check)
/// demands only that the pointer itself is unchanged ([`Demand::SliceLength`]),
/// never its pointee, so `a[2] = 3` on `a: &mut [u32]` does not make `a`'s
/// bounds checks unstable.
pub(in crate::mir_analysis) fn switch_discr_is_value_stable<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    discr: &Operand<'tcx>,
    flow_insensitive: bool,
) -> bool {
    stable_discr_dependencies(tcx, body, discr, flow_insensitive).is_some()
}

/// Whether a switch operand translated with the path walk's bindings at the
/// switch (`call_effect_paths`, which follow every projection-free
/// assignment and call destination path by path) denotes the value the
/// switch tests (D-244): [`switch_discr_is_value_stable`]'s rule for writes
/// the walk does not see, and no parameter among the locals it transitively
/// reads is ever reassigned. The walk spells a parameter's name for its entry
/// value; a reassigned one's name may stand for another value where the
/// condition is read. A user variable or temporary reassigned elsewhere is
/// read at its value on the path to the switch, so it is no reason to refuse
/// (`if lim > 100 { lim = 100 }`), as the flow-insensitive rule must.
pub(in crate::mir_analysis) fn switch_discr_is_path_stable<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    discr: &Operand<'tcx>,
) -> bool {
    let Some(dependencies) = stable_discr_dependencies(tcx, body, discr, false) else {
        return false;
    };
    let params: Vec<Local> = dependencies
        .into_iter()
        .filter(|local| local.as_usize() >= 1 && local.as_usize() <= body.arg_count)
        .collect();
    if params.is_empty() {
        return true;
    }
    let mut writes = ParamDefinitions {
        params: &params,
        defined: false,
    };
    writes.visit_body(body);
    !writes.defined
}

/// Whether any of `params` is the place of a projection-free assignment or a
/// call's destination.
struct ParamDefinitions<'a> {
    params: &'a [Local],
    defined: bool,
}

impl<'tcx> Visitor<'tcx> for ParamDefinitions<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if self.params.contains(&place.local)
            && matches!(
                context,
                PlaceContext::MutatingUse(
                    MutatingUseContext::Store
                        | MutatingUseContext::Call
                        | MutatingUseContext::AsmOutput
                        | MutatingUseContext::Yield
                        | MutatingUseContext::SetDiscriminant
                )
            )
        {
            self.defined = true;
        }
        self.super_place(place, context, location);
    }
}

/// [`switch_discr_is_value_stable`], and every local the operand transitively
/// reads has a type through which nothing can be written behind a shared
/// read: no `&mut`, no raw pointer, no reachable `UnsafeCell`.
///
/// Such an operand denotes the SAME value at every point of the body where its
/// translation is read, so a condition built from it may guard an obligation
/// found later in the arm even when it reads through a shared reference or a
/// closure capture (`if x != 0 { callee(x) }` with `x = *p`, `p: &u32`): the
/// store that would make `guard ==> obligation` read two different values
/// through one term is one this body cannot perform.
pub(in crate::mir_analysis) fn switch_discr_reads_frozen_memory<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    discr: &Operand<'tcx>,
) -> bool {
    use rustc_middle::ty::TyKind;
    let Some(dependencies) = stable_discr_dependencies(tcx, body, discr, false) else {
        return false;
    };
    dependencies.into_iter().all(|local| {
        let ty = body.local_decls[local].ty;
        !ty.walk().any(|arg| {
            arg.as_type().is_some_and(|component| {
                matches!(
                    component.kind(),
                    TyKind::RawPtr(..) | TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                )
            })
        }) && !super::super::loop_body::local_type_may_reach_interior_mutability(tcx, body, local)
    })
}

/// Whether `discr` reads, unchanged, the value ONE call site returned: it is a
/// plain local whose only mutating use in the body is that call's destination,
/// it is never borrowed, and neither the call's block nor the switch's block
/// lies on a cycle.
///
/// The walk spells such a local as the call's own result symbol, which denotes
/// the value the call returned whatever memory its arguments read, so a
/// condition that IS that symbol is the value the switch tests, even when
/// [`switch_discr_is_value_stable`] refuses it for a `&mut` argument
/// (`x.id_ghost() == y.id_ghost()` on `x: &mut _`). One definition that no
/// cycle repeats is one value per execution; a second definition or a cycle
/// would make the one symbol stand for two values.
pub(in crate::mir_analysis) fn switch_discr_is_single_call_result<'tcx>(
    body: &Body<'tcx>,
    discr: &Operand<'tcx>,
    switch_bb: BasicBlock,
) -> Option<Local> {
    let local = plain_local(discr)?;
    let mut uses = LocalMutations {
        local,
        mutations: Vec::new(),
        borrowed: false,
    };
    uses.visit_body(body);
    let [(def_bb, MutatingUseContext::Call)] = uses.mutations.as_slice() else {
        return None;
    };
    if uses.borrowed || block_on_cycle(body, *def_bb) || block_on_cycle(body, switch_bb) {
        return None;
    }
    Some(local)
}

/// Every mutating use of one local, and whether it is borrowed at all.
struct LocalMutations {
    local: Local,
    mutations: Vec<(BasicBlock, MutatingUseContext)>,
    borrowed: bool,
}

impl<'tcx> Visitor<'tcx> for LocalMutations {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if place.local == self.local {
            match context {
                PlaceContext::MutatingUse(
                    MutatingUseContext::Borrow | MutatingUseContext::RawBorrow,
                )
                | PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::SharedBorrow
                    | NonMutatingUseContext::FakeBorrow
                    | NonMutatingUseContext::RawBorrow,
                ) => self.borrowed = true,
                PlaceContext::MutatingUse(kind) => self.mutations.push((location.block, kind)),
                PlaceContext::NonMutatingUse(_) | PlaceContext::NonUse(_) => {}
            }
        }
        self.super_place(place, context, location);
    }
}

/// Whether `bb` can reach itself.
fn block_on_cycle(body: &Body<'_>, bb: BasicBlock) -> bool {
    let mut seen = HashSet::new();
    let mut stack: Vec<BasicBlock> = body.basic_blocks[bb].terminator().successors().collect();
    while let Some(next) = stack.pop() {
        if next == bb {
            return true;
        }
        if seen.insert(next) {
            stack.extend(body.basic_blocks[next].terminator().successors());
        }
    }
    false
}

/// The locals `discr` transitively reads, at either demand, or `None` when one
/// of them may be written where the extractor cannot see it.
fn stable_discr_dependencies<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    discr: &Operand<'tcx>,
    flow_insensitive: bool,
) -> Option<HashSet<Local>> {
    let mut indirect = IndirectWriteCollector::default();
    indirect.visit_body(body);
    let IndirectWriteCollector {
        indirect,
        own_storage,
    } = indirect;

    // Projection-free definition sites and how each one reads.
    let mut defs: HashMap<Local, Vec<DefReads>> = HashMap::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    let location = Location {
                        block: bb,
                        statement_index,
                    };
                    defs.entry(place.local)
                        .or_default()
                        .push(rvalue_reads(body, tcx, rvalue, location));
                }
            }
        }
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
        {
            if destination.projection.is_empty() {
                let location = Location {
                    block: bb,
                    statement_index: data.statements.len(),
                };
                let mut reads = LocalCollector::default();
                reads.visit_operand(func, location);
                for arg in args {
                    reads.visit_operand(&arg.node, location);
                }
                defs.entry(destination.local)
                    .or_default()
                    .push(DefReads::All(reads.locals));
            }
        }
    }

    let user_variables: HashSet<Local> = body
        .var_debug_info
        .iter()
        .filter_map(|info| match &info.value {
            rustc_middle::mir::VarDebugInfoContents::Place(place)
                if place.projection.is_empty() =>
            {
                Some(place.local)
            }
            _ => None,
        })
        .collect();
    let is_param = |local: Local| local.as_usize() >= 1 && local.as_usize() <= body.arg_count;

    let mut worklist = Vec::new();
    {
        let mut roots = LocalCollector::default();
        roots.visit_operand(
            discr,
            Location {
                block: rustc_middle::mir::START_BLOCK,
                statement_index: 0,
            },
        );
        worklist.extend(roots.locals.into_iter().map(|local| (local, Demand::Value)));
    }
    let mut visited = HashSet::new();
    while let Some((local, demand)) = worklist.pop() {
        if !visited.insert((local, demand)) {
            continue;
        }
        let unstable = match demand {
            Demand::Value => {
                indirect.contains(&local) || body.local_decls[local].ty.is_mutable_ptr()
            }
            Demand::SliceLength => own_storage.contains(&local),
        };
        if unstable {
            return None;
        }
        let local_defs = defs.get(&local);
        let def_count = local_defs.map_or(0, Vec::len);
        if flow_insensitive
            && (def_count >= 2
                || (def_count >= 1 && (is_param(local) || user_variables.contains(&local))))
        {
            return None;
        }
        for reads in local_defs.into_iter().flatten() {
            match (reads, demand) {
                (DefReads::LengthOf(source), _)
                | (DefReads::SamePointer { source, .. }, Demand::SliceLength) => {
                    worklist.push((*source, Demand::SliceLength));
                }
                (DefReads::All(reads) | DefReads::SamePointer { reads, .. }, _) => {
                    worklist.extend(reads.iter().map(|&read| (read, Demand::Value)));
                }
            }
        }
    }
    Some(visited.into_iter().map(|(local, _)| local).collect())
}
