// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The values a call in a block some loop reaches reads, as the block-slice
//! walker (`collect_call_effects_for_blocks`) names them.
//!
//! The function-level VC of a function with a loop states the code after the
//! loop against the loop's exit state: a local is named by its bare name, and
//! the loop lane's exit premises (the invariant, the exit condition, the
//! frame) bind that name to the value the local holds where the loop exits.
//! The walker's entry walk cannot reach past a loop, so it must not resolve a
//! read there through a value it bound before the loop (`i = 7` before a loop
//! that sets `i = 0`, then `need7(i)`), and the bare name is the value at the
//! call only when nothing changes the local between the loop's exit and the
//! call (`i = 0; need7(i)` after the loop). [`PastLoopNames`] decides, for one
//! call, whether every value its arguments read is the one the walker names;
//! where it is not, the call's precondition is refused and its postcondition
//! is not assumed.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use rustc_middle::{
    mir::{
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
        BasicBlock, Body, BorrowKind, Local, Location, MutBorrowKind, Operand, Place,
        ProjectionElem, Rvalue, StatementKind, TerminatorKind, VarDebugInfoContents,
    },
    ty::TyCtxt,
};

use super::loop_merges::normal_successors;

/// Where each block lies relative to the body's cycles, and what changes
/// each local.
pub(super) struct PastLoopNames<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    /// Blocks on a cycle: a loop's header and body.
    in_loop: HashSet<BasicBlock>,
    /// Blocks off every cycle that a cycle reaches: code after a loop.
    past: HashSet<BasicBlock>,
    /// Blocks the entry reaches without entering a cycle.
    before: HashSet<BasicBlock>,
    /// User variables and parameters: the locals the VC names by their name.
    named: HashSet<Local>,
    /// Every place in the body that changes each local: an assignment or a
    /// write through a projection of it, a call's destination, a `&mut` or
    /// raw borrow of it. A parameter's entry value is not a change.
    changes: HashMap<Local, Vec<Location>>,
    /// Locals some `&mut` or raw borrow of their own storage lends out: a
    /// write through a pointer may change them.
    lent: HashSet<Local>,
    /// The changes in `changes` that are such borrows: they lend the value
    /// without binding the local to another one.
    lending_changes: HashSet<Location>,
    /// Sites that may write through a pointer: a store or a `&mut` through a
    /// `Deref`, a call handed a value that may carry a mutable pointer, a drop
    /// whose glue may write, inline assembly.
    pointer_writes: Vec<Location>,
    /// Blocks reachable from each block's successors.
    after: RefCell<HashMap<BasicBlock, HashSet<BasicBlock>>>,
}

impl<'a, 'tcx> PastLoopNames<'a, 'tcx> {
    pub(super) fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        let in_loop = blocks_on_a_cycle(body);
        let mut past = HashSet::new();
        let mut stack: Vec<BasicBlock> = in_loop
            .iter()
            .flat_map(|&bb| normal_successors(body, bb))
            .collect();
        while let Some(bb) = stack.pop() {
            if in_loop.contains(&bb) || !past.insert(bb) {
                continue;
            }
            stack.extend(normal_successors(body, bb));
        }
        let mut before = HashSet::new();
        let mut stack = vec![rustc_middle::mir::START_BLOCK];
        while let Some(bb) = stack.pop() {
            if in_loop.contains(&bb) || !before.insert(bb) {
                continue;
            }
            stack.extend(normal_successors(body, bb));
        }
        let mut named: HashSet<Local> = body.args_iter().collect();
        for info in &body.var_debug_info {
            if let VarDebugInfoContents::Place(place) = &info.value {
                if place.projection.is_empty() {
                    named.insert(place.local);
                }
            }
        }
        let mut sites = ChangeSites {
            tcx,
            body,
            changes: HashMap::new(),
            lent: HashSet::new(),
            lending_changes: HashSet::new(),
            pointer_writes: Vec::new(),
        };
        sites.visit_body(body);
        Self {
            tcx,
            body,
            in_loop,
            past,
            before,
            named,
            changes: sites.changes,
            lent: sites.lent,
            lending_changes: sites.lending_changes,
            pointer_writes: sites.pointer_writes,
            after: RefCell::new(HashMap::new()),
        }
    }

    /// Whether `bb` is code after a loop, which the walker reads with the
    /// loop-exit names rather than with the values its entry walk bound.
    pub(super) fn is_past_a_loop(&self, bb: BasicBlock) -> bool {
        self.past.contains(&bb)
    }

    /// Whether `bb` lies on a cycle: a loop's header or body.
    pub(super) fn is_in_loop(&self, bb: BasicBlock) -> bool {
        self.in_loop.contains(&bb)
    }

    /// Whether `bb` is the first block, by index, on any cycle: the header of
    /// the outermost loop the loop lane reads first.
    pub(super) fn is_first_cycle_block(&self, bb: BasicBlock) -> bool {
        self.in_loop.iter().min() == Some(&bb)
    }

    /// Whether `local` has exactly one change in the body: its name then
    /// denotes that one value wherever the local is read after it.
    pub(super) fn changes_once(&self, local: Local) -> bool {
        self.changes
            .get(&local)
            .is_some_and(|changes| changes.len() == 1)
    }

    /// Whether every change of `local` is a whole definition (a
    /// projection-free assignment, or a call's projection-free destination)
    /// and nothing writes it through a pointer: a walk that follows those
    /// definitions sees every value the local takes (D-243).
    pub(super) fn changed_only_by_whole_definitions(&self, local: Local) -> bool {
        !self.reachable_through_a_pointer(local)
            && self
                .changes
                .get(&local)
                .into_iter()
                .flatten()
                .all(|&change| {
                    self.is_whole_assignment(local, change)
                        || self.is_destination_of_call(local, change)
                })
    }

    /// Whether `local` may change again after the call ending `call_bb`
    /// before a loop is entered: a change of it in a block the call reaches
    /// that lies on no cycle and after none, or, for a local whose storage is
    /// lent, a write through a pointer there. The call's result is then not
    /// the local's value where a loop is entered (D-243). A write through a
    /// pointer the local's value holds is not counted: the walker reads such
    /// a local by its name before the loops as it always has (a generic
    /// value "may hold" one, and every later call would count).
    pub(super) fn changed_again_before_the_loops(&self, call_bb: BasicBlock, local: Local) -> bool {
        let after = self.after(call_bb);
        let before_the_loops = |bb: BasicBlock| {
            after.contains(&bb) && !self.in_loop.contains(&bb) && !self.past.contains(&bb)
        };
        self.changes
            .get(&local)
            .into_iter()
            .flatten()
            .any(|change| before_the_loops(change.block))
            || self.lent.contains(&local)
                && self
                    .pointer_writes
                    .iter()
                    .any(|site| before_the_loops(site.block))
    }

    /// Whether the bare name of `local`, wherever a value the path walk binds
    /// before the loops reads it, denotes the value a loop-entry fact read at
    /// a loop's entry and after the loops gives it (D-243, D-244). The walk
    /// spells a parameter's name for its entry value: it qualifies when
    /// nothing changes it and no pointer reaches it. Any other local's name is
    /// spelled only where it is that local's value from there to the loops:
    /// a call's result named by its anchored destination
    /// (`changed_again_before_the_loops`), the one change of a local whose
    /// value does not translate, or a value the walk followed every
    /// definition of. It qualifies when every change of it is a whole
    /// definition the walk follows and none is made once a loop is entered,
    /// or, for a fact read at the entry of the first loop alone
    /// (`at_first_loop_entry`), when its value there is all that is read.
    pub(super) fn names_its_walk_value(&self, local: Local, at_first_loop_entry: bool) -> bool {
        if self.body.args_iter().any(|arg| arg == local) {
            return !self.reachable_through_a_pointer(local)
                && self.changes.get(&local).is_none_or(Vec::is_empty);
        }
        self.changed_only_by_whole_definitions(local)
            && (at_first_loop_entry || self.changed_only_before_every_loop(local))
    }

    /// Whether a write through a pointer may change `local`: it is lent, or
    /// its type lends a write.
    fn reachable_through_a_pointer(&self, local: Local) -> bool {
        self.lent.contains(&local)
            || super::loop_condition_writes::ty_lends_write(
                self.tcx,
                self.body,
                self.body.local_decls[local].ty,
                &mut HashSet::new(),
                0,
            )
    }

    /// Whether every change of `local` lies in a block that no loop reaches
    /// and that is on no cycle: once a loop is entered, the local keeps the
    /// value it had there.
    pub(super) fn changed_only_before_every_loop(&self, local: Local) -> bool {
        self.changes
            .get(&local)
            .into_iter()
            .flatten()
            .all(|change| {
                !self.in_loop.contains(&change.block) && !self.past.contains(&change.block)
            })
    }

    /// Whether the change at `location` is a whole assignment to `local`,
    /// wherever it lies.
    fn is_whole_assignment(&self, local: Local, location: Location) -> bool {
        let data = &self.body.basic_blocks[location.block];
        matches!(
            data.statements.get(location.statement_index).map(|stmt| &stmt.kind),
            Some(StatementKind::Assign((place, _)))
                if place.local == local && place.projection.is_empty()
        )
    }

    /// Whether a loop the call ending `call_bb` reaches may change `local`:
    /// a change of it in that loop (an assignment, a write through a
    /// projection, a call's destination, a `&mut` or raw borrow), or, for a
    /// local that is lent or whose type lends a write, any write through a
    /// pointer there. That loop's exit premises bind the local's name to the
    /// value it holds at the exit, so a postcondition stated about the name
    /// at the call is a premise about another value after it (D-243).
    pub(super) fn later_loop_may_change(&self, call_bb: BasicBlock, local: Local) -> bool {
        let after = self.after(call_bb);
        let in_later_loop = |bb: BasicBlock| self.in_loop.contains(&bb) && after.contains(&bb);
        if self
            .changes
            .get(&local)
            .into_iter()
            .flatten()
            .any(|change| in_later_loop(change.block))
        {
            return true;
        }
        self.reachable_through_a_pointer(local)
            && self
                .pointer_writes
                .iter()
                .any(|site| in_later_loop(site.block))
    }

    /// Whether some block of `slice` runs after a loop the call ending
    /// `call_bb` reaches: the goals and premises the slice feeds then read
    /// names at that loop's exit.
    pub(super) fn slice_runs_after_a_later_loop(
        &self,
        call_bb: BasicBlock,
        slice: &HashSet<BasicBlock>,
    ) -> bool {
        let after = self.after(call_bb);
        after.iter().any(|&bb| self.in_loop.contains(&bb))
            && slice
                .iter()
                .any(|bb| self.past.contains(bb) && after.contains(bb))
    }

    /// The binding the walker gives `local` in a block after a loop, when it
    /// is the value of the local's one definition: the local has exactly one
    /// change in the body, and it is a whole assignment in a block after a
    /// loop. Every read of the local runs after that definition and sees it.
    pub(super) fn single_past_definition(&self, local: Local) -> Option<&'a Rvalue<'tcx>> {
        let [location] = self.changes.get(&local)?.as_slice() else {
            return None;
        };
        self.past_definition(local, *location)
    }

    /// The whole assignment to `local` at `location`, in a block after a loop.
    fn past_definition(&self, local: Local, location: Location) -> Option<&'a Rvalue<'tcx>> {
        if !self.past.contains(&location.block) {
            return None;
        }
        let data = &self.body.basic_blocks[location.block];
        let StatementKind::Assign((place, rvalue)) =
            &data.statements.get(location.statement_index)?.kind
        else {
            return None;
        };
        (place.local == local && place.projection.is_empty()).then_some(rvalue)
    }

    /// Whether the call ending `call_bb`, after a loop, reads every argument
    /// at the value the walker names it by. The reads are followed through
    /// each temporary's, or local's, one definition after the loop, which the
    /// walker resolves it to; the locals they end at are read by their
    /// loop-exit names. Such a local must be unchanged between the loop's exit
    /// and the call, and, when a loop runs after the call, from the call on:
    /// that loop's exit premises bind the same name. One that is lent, or
    /// that holds a pointer, must meet no write through a pointer on the way,
    /// other than the borrows the reads themselves make. A block the entry
    /// also reaches without passing a loop has no single exit state to name.
    pub(super) fn call_reads_named_values(
        &self,
        call_bb: BasicBlock,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
    ) -> bool {
        if self.before.contains(&call_bb) {
            return false;
        }
        let call_location = self.body.terminator_loc(call_bb);
        // The sites the reads run at: the call, and each definition followed.
        // A borrow made there (`_5 = &mut x` handed to the call, a reborrow
        // `&mut *p`) is the read, not a change of what it reads.
        let mut read_sites: HashSet<Location> = HashSet::from([call_location]);
        let mut leaves: Vec<Local> = Vec::new();
        // Each read with the site that reads it.
        let mut worklist: Vec<(Local, Location)> = Vec::new();
        for arg in args {
            let mut reads = LocalReads::default();
            reads.visit_operand(&arg.node, call_location);
            worklist.extend(reads.0.into_iter().map(|local| (local, call_location)));
        }
        let mut visited = HashSet::new();
        while let Some((local, read_at)) = worklist.pop() {
            if !visited.insert((local, read_at)) {
                continue;
            }
            // The definitions the read sees: every change but the borrow the
            // read itself makes (`_t = &mut iter` handed to `next`).
            let definitions: Vec<Location> = self
                .changes
                .get(&local)
                .into_iter()
                .flatten()
                .copied()
                .filter(|&change| change != read_at)
                .collect();
            if let [only] = definitions[..] {
                if self.past.contains(&only.block) {
                    if let Some(rvalue) = self.past_definition(local, only) {
                        let mut reads = LocalReads::default();
                        reads.visit_rvalue(rvalue, only);
                        worklist.extend(reads.0.into_iter().map(|read| (read, only)));
                        read_sites.insert(only);
                        continue;
                    }
                    if self.is_destination_of_call(local, only) {
                        continue;
                    }
                    return false;
                }
            }
            if !self.named.contains(&local) {
                return false;
            }
            leaves.push(local);
        }
        let loop_after_call = !self.after(call_bb).is_disjoint(&self.in_loop);
        let pointer_write_on_the_way = self.pointer_writes.iter().any(|&site| {
            !read_sites.contains(&site)
                && self.past.contains(&site.block)
                && self.reaches(site, call_bb)
        });
        leaves.into_iter().all(|local| {
            let changes = self.changes.get(&local).map_or(&[][..], Vec::as_slice);
            let changed_since_exit = changes.iter().any(|&change| {
                !read_sites.contains(&change)
                    && self.past.contains(&change.block)
                    && self.reaches(change, call_bb)
            });
            let changed_before_a_later_loop = loop_after_call
                && changes.iter().any(|&change| {
                    change == call_location || self.after(call_bb).contains(&change.block)
                });
            let reachable_through_a_pointer = self.lent.contains(&local)
                || super::loop_condition_writes::ty_lends_write(
                    self.tcx,
                    self.body,
                    self.body.local_decls[local].ty,
                    &mut HashSet::new(),
                    0,
                );
            let written_through_a_pointer =
                reachable_through_a_pointer && (loop_after_call || pointer_write_on_the_way);
            !(changed_since_exit || changed_before_a_later_loop || written_through_a_pointer)
        })
    }

    /// Whether the postcondition of the call ending `call_bb`, after a loop,
    /// may be stated about the name its destination has: the destination is
    /// a whole local this call is the one definition of, so no loop-exit
    /// premise or other call binds that name to another value.
    pub(super) fn destination_names_only_this_result(
        &self,
        call_bb: BasicBlock,
        destination: &Place<'tcx>,
    ) -> bool {
        let call_location = self.body.terminator_loc(call_bb);
        // A later borrow lends the result on; it binds the name to no other
        // value, and a read after it is checked as changed since the exit.
        destination.projection.is_empty()
            && self
                .changes
                .get(&destination.local)
                .into_iter()
                .flatten()
                .all(|&change| {
                    change == call_location
                        || (self.lending_changes.contains(&change)
                            && self.past.contains(&change.block)
                            && self.after(call_bb).contains(&change.block))
                })
    }

    fn is_destination_of_call(&self, local: Local, location: Location) -> bool {
        let data = &self.body.basic_blocks[location.block];
        location.statement_index == data.statements.len()
            && matches!(
                &data.terminator().kind,
                TerminatorKind::Call { destination, .. }
                    if destination.local == local && destination.projection.is_empty()
            )
    }

    /// Whether the change at `site` can run before the terminator of
    /// `call_bb`: earlier in the same block, or in a block from which the
    /// call's block is reachable.
    fn reaches(&self, site: Location, call_bb: BasicBlock) -> bool {
        if site.block == call_bb
            && site.statement_index < self.body.basic_blocks[call_bb].statements.len()
        {
            return true;
        }
        self.after(site.block).contains(&call_bb)
    }

    fn after(&self, bb: BasicBlock) -> std::cell::Ref<'_, HashSet<BasicBlock>> {
        if !self.after.borrow().contains_key(&bb) {
            let mut seen = HashSet::new();
            let mut stack = normal_successors(self.body, bb);
            while let Some(next) = stack.pop() {
                if seen.insert(next) {
                    stack.extend(normal_successors(self.body, next));
                }
            }
            self.after.borrow_mut().insert(bb, seen);
        }
        std::cell::Ref::map(self.after.borrow(), |after| &after[&bb])
    }
}

/// Blocks on a cycle of the body's normal control flow.
fn blocks_on_a_cycle(body: &Body<'_>) -> HashSet<BasicBlock> {
    // Kosaraju: finish order on the graph, then components on its reverse.
    let blocks: Vec<BasicBlock> = body.basic_blocks.indices().collect();
    let mut order = Vec::with_capacity(blocks.len());
    let mut seen = HashSet::new();
    for &root in &blocks {
        if !seen.insert(root) {
            continue;
        }
        let mut stack = vec![(root, normal_successors(body, root).into_iter())];
        while let Some((bb, successors)) = stack.last_mut() {
            let bb = *bb;
            if let Some(next) = successors.next() {
                if seen.insert(next) {
                    stack.push((next, normal_successors(body, next).into_iter()));
                }
            } else {
                order.push(bb);
                stack.pop();
            }
        }
    }
    let mut predecessors: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
    for &bb in &blocks {
        for next in normal_successors(body, bb) {
            predecessors.entry(next).or_default().push(bb);
        }
    }
    let mut on_cycle = HashSet::new();
    let mut assigned = HashSet::new();
    for &root in order.iter().rev() {
        if !assigned.insert(root) {
            continue;
        }
        let mut component = vec![root];
        let mut stack = vec![root];
        while let Some(bb) = stack.pop() {
            for &pred in predecessors.get(&bb).into_iter().flatten() {
                if assigned.insert(pred) {
                    component.push(pred);
                    stack.push(pred);
                }
            }
        }
        let self_loop = normal_successors(body, root).contains(&root);
        if component.len() > 1 || self_loop {
            on_cycle.extend(component);
        }
    }
    on_cycle
}

#[derive(Default)]
struct LocalReads(Vec<Local>);

impl<'tcx> Visitor<'tcx> for LocalReads {
    fn visit_local(&mut self, local: Local, _context: PlaceContext, _location: Location) {
        self.0.push(local);
    }
}

struct ChangeSites<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    changes: HashMap<Local, Vec<Location>>,
    lent: HashSet<Local>,
    lending_changes: HashSet<Location>,
    pointer_writes: Vec<Location>,
}

impl<'tcx> Visitor<'tcx> for ChangeSites<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        let changes = match context {
            PlaceContext::MutatingUse(MutatingUseContext::Drop) => false,
            PlaceContext::MutatingUse(_)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow) => true,
            _ => false,
        };
        if changes {
            let through_pointer = place
                .projection
                .iter()
                .any(|elem| matches!(elem, ProjectionElem::Deref));
            // A write or a `&mut` through a pointer changes the memory it
            // points to, not the pointer local.
            if through_pointer {
                self.pointer_writes.push(location);
            } else {
                self.changes.entry(place.local).or_default().push(location);
                if matches!(
                    context,
                    PlaceContext::MutatingUse(
                        MutatingUseContext::Borrow | MutatingUseContext::RawBorrow
                    ) | PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow)
                ) {
                    self.lent.insert(place.local);
                    self.lending_changes.insert(location);
                }
            }
        }
        self.super_place(place, context, location);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        // A two-phase borrow (`v.push(v.len())`'s receiver) writes nothing
        // until the call it activates at, which is a write through a pointer
        // to a lent local: it lends `v` without changing it here.
        if let Rvalue::Ref(
            _,
            BorrowKind::Mut {
                kind: MutBorrowKind::TwoPhaseBorrow,
            },
            borrowed,
        ) = rvalue
        {
            if borrowed
                .projection
                .iter()
                .any(|elem| matches!(elem, ProjectionElem::Deref))
            {
                self.pointer_writes.push(location);
            } else {
                self.lent.insert(borrowed.local);
            }
            self.visit_place(
                place,
                PlaceContext::MutatingUse(MutatingUseContext::Store),
                location,
            );
            return;
        }
        self.super_assign(place, rvalue, location);
    }

    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        match &terminator.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                if args.iter().any(|arg| {
                    super::unannotated_loops::operand_may_carry_mutable_pointer(
                        self.body, &arg.node,
                    )
                }) {
                    self.pointer_writes.push(location);
                }
            }
            // A drop writes only where its glue may write (D-140).
            TerminatorKind::Drop { place, .. } => {
                if super::drop_glue_writes::locals_changed_by_drop(self.tcx, self.body, place)
                    .is_some()
                {
                    self.pointer_writes.push(location);
                }
            }
            TerminatorKind::InlineAsm { .. } => self.pointer_writes.push(location),
            _ => {}
        }
        self.super_terminator(terminator, location);
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;
    use rustc_middle::ty::TyCtxt;

    use super::*;

    static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

    /// Whether each call to `need` in `f`, in block order, reads its
    /// argument at the value the walker names it by.
    struct NeedCalls {
        verdicts: Option<Vec<bool>>,
    }

    impl Callbacks for NeedCalls {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for local_def_id in tcx.hir_body_owners() {
                if tcx.def_path_str(local_def_id) != "f" {
                    continue;
                }
                let body = tcx.optimized_mir(local_def_id.to_def_id());
                let names = PastLoopNames::new(tcx, body);
                let mut verdicts = Vec::new();
                for (bb, data) in body.basic_blocks.iter_enumerated() {
                    let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
                        continue;
                    };
                    let Some((def_id, _)) = func.const_fn_def() else {
                        continue;
                    };
                    if tcx.def_path_str(def_id) == "need" {
                        assert!(names.is_past_a_loop(bb), "test calls follow a loop");
                        verdicts.push(names.call_reads_named_values(bb, args));
                    }
                }
                self.verdicts = Some(verdicts);
            }
            Compilation::Stop
        }
    }

    fn need_calls(source: &str) -> Vec<bool> {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_past_loop_names_{}_{}",
            std::process::id(),
            unique
        ));
        fs::create_dir_all(&temp_dir).expect("create test temp dir");
        let source_path = temp_dir.join("test.rs");
        fs::write(&source_path, format!("pub fn need(_k: u32) {{}}\n{source}"))
            .expect("write test source");
        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_past_loop_names_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];
        let mut callbacks = NeedCalls { verdicts: None };
        run_compiler(&args, &mut callbacks);
        let _ = fs::remove_dir_all(&temp_dir);
        callbacks.verdicts.expect("function `f` found")
    }

    /// A local the loop writes, or one defined once after it, is read at
    /// the name the walker gives it.
    #[test]
    fn a_local_unchanged_since_the_loop_exit_is_read_by_its_name() {
        assert_eq!(
            need_calls(
                "pub fn f() { let mut n = 0u32; let mut i = 7u32; \
                 while n < 3 { i = 0; n += 1; } need(i); let k = n; need(k); }"
            ),
            vec![true, true]
        );
    }

    /// An assignment, a `&mut` handed to a call, or a store through a pointer
    /// to a lent local between the loop's exit and the call; the call before
    /// a later loop that writes the local; and a block the entry reaches
    /// without the loop.
    #[test]
    fn a_local_changed_since_the_loop_exit_is_not() {
        assert_eq!(
            need_calls(
                "pub fn f() { let mut n = 0u32; let mut i = 7u32; \
                 while n < 3 { n += 1; } need(i); i = n - 3; need(i); }"
            ),
            vec![true, false]
        );
        assert_eq!(
            need_calls(
                "fn zero(k: &mut u32) { *k = 0; } \
                 pub fn f() { let mut n = 0u32; let mut i = 7u32; \
                 while n < 3 { n += 1; } zero(&mut i); need(i); }"
            ),
            vec![false]
        );
        assert_eq!(
            need_calls(
                "pub fn f() { let mut n = 0u32; let mut i = 7u32; let r = &mut i; \
                 while n < 3 { n += 1; } *r = 0; need(i); }"
            ),
            vec![false]
        );
        assert_eq!(
            need_calls(
                "pub fn f() { let mut n = 0u32; let mut k = 0u32; let mut i = 7u32; \
                 while n < 3 { n += 1; } need(i); while k < 2 { i = 0; k += 1; } }"
            ),
            vec![false]
        );
        assert_eq!(
            need_calls(
                "pub fn f(c: bool) { let mut n = 0u32; let mut i = 7u32; \
                 if c { while n < 3 { i = 0; n += 1; } } need(i); }"
            ),
            vec![false]
        );
    }
}
