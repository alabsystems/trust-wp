// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The owner place a write through a `&mut` lands on.
//!
//! Both write-back lanes have to answer one question — "which place does this
//! `&mut` govern?" — and both answered it with a local-to-local edge map that
//! cannot express a projection (`&mut s.a`), cannot see through an aggregate
//! that carries the borrow (`H { p: &mut x }`), and is severed by the
//! `StorageDead` of the coercion temporary an explicit type annotation
//! introduces. Each gap is a write that reaches nothing, which leaves the
//! borrowed place reporting its entry value — a false accept, not an
//! `unknown`.
//!
//! This resolver answers the question over the MIR itself, so it is immune to
//! all three: it never consults the edge map, so no `StorageDead` can sever
//! it, and its answer is a base local plus a field path rather than a bare
//! local.
//!
//! Every hop is evaluated AT THE POINT OF THE DEFINITION IT CAME FROM, not at
//! the write. That is what lets a reassigned borrow be resolved at all: the
//! definition that reaches the write is the one that speaks, and the places
//! its own operands named are the ones they named where it stands. It is also
//! what makes `r = &mut *r` terminate with the right answer rather than with
//! the depth cap — at the reborrow's own point, `r`'s reaching definition is
//! still the original one.
//!
//! It is exact, it is an exhaustive list of candidates, or it is `Unknown`. A
//! write-back aimed at the wrong place is a false accept in the other
//! direction — strictly worse than the lost write it would be repairing — so
//! credit is reserved for a SINGLE reaching definition resolving to a single
//! owner. More than one owner may only be invalidated, never credited, and a
//! list that is not exhaustive is not a list: it is `Unknown`.

use std::collections::HashSet;

use rustc_middle::{
    mir::{
        Body, Local, Location, Operand, Place, PlaceElem, ProjectionElem, Rvalue, StatementKind,
    },
    ty::TyCtxt,
};

use super::reaching_defs::{DefKind, ReachingDefs};

/// Depth cap for the resolution walk. A borrow chain longer than this is
/// refused rather than followed. Cycles are cut by the visited set; this is a
/// second bound on a pathological chain.
const MAX_RESOLUTION_DEPTH: usize = 16;

/// How many owners one write may fan out to before the fan-out is no longer
/// worth enumerating. An answer over the cap is `Unknown`, never a truncated
/// list: a truncated list leaves the owners it dropped reporting their entry
/// values, which is the same false accept, quieter.
const MAX_CANDIDATES: usize = 4;

/// The place a write through a `&mut` lands on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Governed {
    /// One owner, from one reaching definition. The only answer that may be
    /// credited.
    Exact(Local, Vec<usize>),
    /// Two or more owners, EXHAUSTIVELY enumerated: the write lands on one of
    /// them and this resolver does not know which. Every one of them must lose
    /// whatever was recorded for it; none of them may be told what it now
    /// holds.
    Candidates(Vec<(Local, Vec<usize>)>),
    /// The write lands somewhere this resolver cannot name. Nothing is
    /// credited and nothing is invalidated.
    Unknown,
}

/// Resolution state for one top-level query.
struct Ctx {
    /// `(local, point)` pairs on the current path. A repeat is a loop-carried
    /// chain, which has no single answer.
    visited: HashSet<(Local, Location)>,
}

/// The place a write through `write` at `at` actually lands on.
///
/// `write` must contain a `Deref`; a write that needs no resolution is the
/// caller's own business. `rd` must have been computed on `body`.
pub(crate) fn governed_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rd: &ReachingDefs,
    write: &Place<'tcx>,
    at: Location,
) -> Governed {
    debug_assert!(
        statement_writes(body, at, write),
        "the reaching-definition facts are indexed by a point in THIS body; \
         a location naming a different statement would answer confidently and wrongly"
    );
    if !write
        .projection
        .iter()
        .any(|elem| matches!(elem, ProjectionElem::Deref))
    {
        return Governed::Unknown;
    }
    let mut ctx = Ctx {
        visited: HashSet::new(),
    };
    let Some(owners) = resolve_place(tcx, body, rd, write, at, 0, &mut ctx) else {
        return Governed::Unknown;
    };
    // Compared with regions erased: this guard is about the SORT the fact
    // would be stated at, and a post-borrowck body still carries inference
    // regions, so `&'?8 mut i32` and `&'?10 mut i32` are the same place type
    // wearing two names. Region-sensitive equality here refuses a resolution
    // that is exactly right, which is a lost write, not a safe one.
    let write_ty = tcx.erase_and_anonymize_regions(write.ty(&body.local_decls, tcx).ty);
    let mut out: Vec<(Local, Vec<usize>)> = Vec::with_capacity(owners.len());
    for (base, elems) in &owners {
        // The owner place must have the same type as the place being written.
        // Without this the resolver can hand back a place one level of
        // indirection away from the write — a `&mut &mut i32` unnesting whose
        // root is a reference, not the integer the write stores — and the
        // write-back would then state a fact about the wrong sort, which can
        // make an unrelated goal provable for no reason at all. One candidate
        // failing it refuses the WHOLE answer: a smaller list is not the list.
        let owner_ty = tcx
            .erase_and_anonymize_regions(Place::ty_from(*base, elems, &body.local_decls, tcx).ty);
        if owner_ty != write_ty {
            return Governed::Unknown;
        }
        let mut path = Vec::with_capacity(elems.len());
        for elem in elems {
            let ProjectionElem::Field(field, _) = elem else {
                return Governed::Unknown;
            };
            path.push(field.as_usize());
        }
        out.push((*base, path));
    }
    match out.len() {
        0 => Governed::Unknown,
        1 => {
            let (base, path) = out.pop().expect("checked");
            Governed::Exact(base, path)
        }
        _ => Governed::Candidates(out),
    }
}

/// Does the store at `site` land on exactly the whole of `owner`?
///
/// The promotion test for a slot an alias stores through: only a store that
/// resolves back to the slot itself may be folded in as a definition of it.
pub(crate) fn resolves_to_owner<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rd: &ReachingDefs,
    owner: Local,
    site: Location,
) -> bool {
    let Some(stmt) = body.basic_blocks[site.block]
        .statements
        .get(site.statement_index)
    else {
        return false;
    };
    let StatementKind::Assign((dest, _)) = &stmt.kind else {
        return false;
    };
    matches!(
        governed_place(tcx, body, rd, dest, site),
        Governed::Exact(base, ref path) if base == owner && path.is_empty()
    )
}

fn statement_writes<'tcx>(body: &Body<'tcx>, at: Location, write: &Place<'tcx>) -> bool {
    let Some(stmt) = body.basic_blocks[at.block]
        .statements
        .get(at.statement_index)
    else {
        return false;
    };
    matches!(&stmt.kind, StatementKind::Assign((dest, _)) if dest == write)
}

/// The owner places `place` denotes at `at`, with every `Deref` resolved away.
fn resolve_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rd: &ReachingDefs,
    place: &Place<'tcx>,
    at: Location,
    depth: usize,
    ctx: &mut Ctx,
) -> Option<Vec<(Local, Vec<PlaceElem<'tcx>>)>> {
    if depth > MAX_RESOLUTION_DEPTH {
        return None;
    }
    let mut owners: Vec<(Local, Vec<PlaceElem<'tcx>>)> = vec![(place.local, Vec::new())];
    for elem in place.projection.iter() {
        match elem {
            ProjectionElem::Field(..) => {
                for (_, elems) in &mut owners {
                    elems.push(elem);
                }
            }
            ProjectionElem::Deref => {
                let mut next: Vec<(Local, Vec<PlaceElem<'tcx>>)> = Vec::new();
                for (local, elems) in &owners {
                    let hop = pointee(tcx, body, rd, *local, elems, at, depth + 1, ctx)?;
                    merge(&mut next, hop)?;
                }
                owners = next;
            }
            // An index, a slice or a downcast names a place this resolver
            // cannot pin down to one field path, and a guess is the false
            // accept it exists to avoid.
            _ => return None,
        }
    }
    if owners.is_empty() {
        return None;
    }
    Some(owners)
}

fn merge<'tcx>(
    dest: &mut Vec<(Local, Vec<PlaceElem<'tcx>>)>,
    src: Vec<(Local, Vec<PlaceElem<'tcx>>)>,
) -> Option<()> {
    for entry in src {
        if !dest.contains(&entry) {
            dest.push(entry);
        }
    }
    if dest.len() > MAX_CANDIDATES {
        return None;
    }
    Some(())
}

/// The places the `&mut` stored at `(local, elems)` points at, as of `at`.
fn pointee<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rd: &ReachingDefs,
    local: Local,
    elems: &[PlaceElem<'tcx>],
    at: Location,
    depth: usize,
    ctx: &mut Ctx,
) -> Option<Vec<(Local, Vec<PlaceElem<'tcx>>)>> {
    if depth > MAX_RESOLUTION_DEPTH {
        return None;
    }
    // A parameter's pointee is the prophecy lane's property: `^p` is credited
    // there, and a write-back granted here would be the same fact granted
    // twice by code that does not know about the other.
    if body.args_iter().any(|arg| arg == local) {
        return None;
    }
    // A slot some alias can redirect by a route the reaching analysis could
    // not follow: no definition list over it means anything.
    if rd.is_unresolvable(local) {
        return None;
    }
    if !ctx.visited.insert((local, at)) {
        return None;
    }
    let answer = (|| {
        let defs = rd.reaching(body, local, at);
        // No definition reaches this point, or one of them wrote a value this
        // resolver cannot read: either way the local's value is unknown here.
        if defs.is_empty() || defs.iter().any(|def| def.kind == DefKind::Opaque) {
            return None;
        }
        let mut owners: Vec<(Local, Vec<PlaceElem<'tcx>>)> = Vec::new();
        for def in defs {
            let hop = pointee_from_def(tcx, body, rd, &def, elems, depth, ctx)?;
            merge(&mut owners, hop)?;
        }
        if owners.is_empty() {
            return None;
        }
        Some(owners)
    })();
    ctx.visited.remove(&(local, at));
    answer
}

/// The pointee one definition states, read at that definition's own point.
fn pointee_from_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rd: &ReachingDefs,
    def: &super::reaching_defs::Def,
    elems: &[PlaceElem<'tcx>],
    depth: usize,
    ctx: &mut Ctx,
) -> Option<Vec<(Local, Vec<PlaceElem<'tcx>>)>> {
    let stmt = body.basic_blocks[def.loc.block]
        .statements
        .get(def.loc.statement_index)?;
    let StatementKind::Assign((_, rvalue)) = &stmt.kind else {
        return None;
    };
    let at = def.loc;
    let Some((first, rest)) = elems.split_first() else {
        return match rvalue {
            Rvalue::Ref(_, _, src) | Rvalue::RawPtr(_, src) => {
                resolve_place(tcx, body, rd, src, at, depth + 1, ctx)
            }
            // The local holds a copy of a reference read out of `src`, so its
            // pointee is whatever `src` holds points at — at this point.
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
            | Rvalue::CopyForDeref(src) => {
                let holders = resolve_place(tcx, body, rd, src, at, depth + 1, ctx)?;
                let mut owners = Vec::new();
                for (holder, holder_elems) in holders {
                    let hop = pointee(tcx, body, rd, holder, &holder_elems, at, depth + 1, ctx)?;
                    merge(&mut owners, hop)?;
                }
                Some(owners)
            }
            _ => None,
        };
    };
    // The reference lives in a field of an aggregate the local was built from:
    // `let h = H { p: &mut x }; *h.p = 7`. Read the operand back out of the
    // constructor, which is exact as long as this definition is the one that
    // reaches the read (a later store into a field is a definition of its own
    // and kills this one).
    let ProjectionElem::Field(field, _) = first else {
        return None;
    };
    let Rvalue::Aggregate(_, operands) = rvalue else {
        return None;
    };
    let operand = operands.iter().nth(field.as_usize())?;
    let (Operand::Copy(src) | Operand::Move(src)) = operand else {
        return None;
    };
    let holders = resolve_place(tcx, body, rd, src, at, depth + 1, ctx)?;
    let mut owners = Vec::new();
    for (holder, mut holder_elems) in holders {
        holder_elems.extend_from_slice(rest);
        let hop = pointee(tcx, body, rd, holder, &holder_elems, at, depth + 1, ctx)?;
        merge(&mut owners, hop)?;
    }
    Some(owners)
}
