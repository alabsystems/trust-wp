// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Which locals a write, a call or a drop may change — by reference flow,
//! not by "everything whose address was ever taken".
//!
//! The arithmetic-panic region walk re-binds locals whose value may have
//! changed without a direct assignment: at a projected write (`*r = ..`), at
//! a call return and at a `Drop`. Re-binding EVERY address-taken local at
//! every such point is sound but throws away every fact the walk holds about
//! unrelated references: in `inc_max_3`, `*ma += 2` forgot `*mb`, and each
//! `swap(&mut ma, &mut mb)` forgot `*mc`, so `*mb += 1` was owed over an
//! unconstrained value.
//!
//! Safe Rust bounds what a write can reach. Memory is written only through a
//! path that starts at some local of this body, and two paths reach the same
//! memory only when a reference flowed between their locals inside the body
//! — a borrow (`&mut x`, `&raw mut x`), a move or copy of a reference-holding
//! value, a deref-copy, a cast, an aggregate that packs one, or a call whose
//! result can hold a borrow of its arguments. Two live `&mut` locals with no
//! such flow (two `&mut` parameters, or `ma` and `mb` after a `swap`) never
//! alias: that is the borrow checker's guarantee, not an assumption of this
//! module. So the locals a write through `L` may change are `L`'s connected
//! component in that flow graph; a call may change the components of its
//! arguments; drop glue the component of the dropped place. Interior
//! mutability and raw pointers escape this reasoning (memory behind an
//! `UnsafeCell`, or reached through a `*mut`, can change without any flow
//! this graph sees), so every local whose type can reach either is still
//! re-bound at every point, exactly as before.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::Spanned;

use super::{
    closure::local_type_may_hold_borrow, loop_body::local_type_may_reach_interior_mutability,
};

/// The locals a write through (or a drop of) a place based at `base` may
/// change: `base`'s reference-flow component, plus every local whose type
/// can reach interior mutability or a raw pointer.
pub(super) fn locals_a_write_may_change<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    base: Local,
) -> HashSet<Local> {
    let components = reference_flow_components(body, false);
    let mut changed = always_rebound_locals(tcx, body);
    changed.extend(component_of(&components, base));
    changed.insert(base);
    changed
}

/// The locals drop glue run on a value based at one of `roots` may change
/// (D-140): as [`locals_a_write_may_change`], over a flow graph in which a
/// call also joins its borrow-holding ARGUMENTS with one another. The glue
/// writes through borrows the dropped value holds, and a callee handed
/// `&mut v` beside `G(&mut c)` may store the second into the first
/// (`v.push(G(&mut c))`) with no borrow flowing into the call's result; the
/// write lanes need not see that flow, since `c` is not written until the
/// glue runs, but the glue's reach does.
pub(super) fn locals_drop_glue_may_change<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    roots: &[Local],
) -> HashSet<Local> {
    let components = reference_flow_components(body, true);
    let mut changed = always_rebound_locals(tcx, body);
    for root in roots {
        changed.extend(component_of(&components, *root));
        changed.insert(*root);
    }
    changed
}

/// The locals a call may change: the reference-flow components of every
/// argument, plus every local whose type can reach interior mutability or a
/// raw pointer. A callee reaches memory only through what it is handed.
pub(super) fn locals_a_call_may_change<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> HashSet<Local> {
    let components = reference_flow_components(body, false);
    let mut changed = always_rebound_locals(tcx, body);
    for arg in args {
        if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
            changed.extend(component_of(&components, place.local));
            changed.insert(place.local);
        }
    }
    changed
}

fn always_rebound_locals<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    body.local_decls
        .indices()
        .filter(|local| local_type_may_reach_interior_mutability(tcx, body, *local))
        .collect()
}

fn component_of(
    components: &HashMap<Local, usize>,
    local: Local,
) -> impl Iterator<Item = Local> + '_ {
    let id = components.get(&local).copied();
    components
        .iter()
        .filter(move |(_, c)| Some(**c) == id)
        .map(|(l, _)| *l)
}

/// Connected components of the reference-flow graph over the body's locals.
/// `join_call_arguments` also joins every borrow-holding argument of a call
/// with the others, for [`locals_drop_glue_may_change`].
fn reference_flow_components(body: &Body<'_>, join_call_arguments: bool) -> HashMap<Local, usize> {
    let n = body.local_decls.len();
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    let mut union = |a: Local, b: Local| {
        let (ra, rb) = (
            find(&mut parent, a.as_usize()),
            find(&mut parent, b.as_usize()),
        );
        if ra != rb {
            parent[ra] = rb;
        }
    };
    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            let StatementKind::Assign((dst, rvalue)) = &stmt.kind else {
                continue;
            };
            let flows_reference = match rvalue {
                Rvalue::Ref(..) | Rvalue::RawPtr(..) | Rvalue::CopyForDeref(_) => true,
                _ => local_type_may_hold_borrow(body, dst.local),
            };
            if !flows_reference {
                continue;
            }
            for local in rvalue_place_locals(rvalue) {
                union(dst.local, local);
            }
        }
        if let TerminatorKind::Call {
            args, destination, ..
        } = &bb_data.terminator().kind
        {
            if local_type_may_hold_borrow(body, destination.local) {
                for arg in args {
                    if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                        union(destination.local, place.local);
                    }
                }
            }
            if join_call_arguments {
                let holders: Vec<Local> = args
                    .iter()
                    .filter_map(|arg| match &arg.node {
                        Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
                    })
                    .filter(|local| local_type_may_hold_borrow(body, *local))
                    .collect();
                for pair in holders.windows(2) {
                    union(pair[0], pair[1]);
                }
            }
        }
    }
    (0..n)
        .map(|i| (Local::from_usize(i), find(&mut parent, i)))
        .collect()
}

/// Every local named by a place the rvalue reads (operands, borrowed places,
/// deref bases, index locals).
fn rvalue_place_locals<'tcx>(rvalue: &Rvalue<'tcx>) -> Vec<Local> {
    use rustc_middle::mir::visit::{PlaceContext, Visitor};
    struct Locals(Vec<Local>);
    impl<'tcx> Visitor<'tcx> for Locals {
        fn visit_local(
            &mut self,
            local: Local,
            _context: PlaceContext,
            _location: rustc_middle::mir::Location,
        ) {
            self.0.push(local);
        }
    }
    let mut locals = Locals(Vec::new());
    locals.visit_rvalue(rvalue, rustc_middle::mir::Location::START);
    locals.0
}
