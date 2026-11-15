// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Borrows lent into the return value.
//!
//! A `&mut` parameter (or a borrow reachable from a parameter) that flows
//! into the function's return value is NOT resolved inside the callee: the
//! caller keeps writing through the returned borrow, so the parameter's
//! prophecy `^p` is determined by the caller, not by the callee body. Any
//! `final_values` entry for such a parameter — identity (`*p`), branch-merged
//! (`if c { *p } else { *p }`) or a field reconstruction — is a FALSE premise.
//!
//! This module computes, flow-insensitively over the whole MIR body, the set
//! of parameters whose borrow may reach `RETURN_PLACE` on ANY path. It is a
//! deliberate over-approximation: marking a parameter lent only DELETES
//! premises (its prophecy becomes free), which can never cause a false accept.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        visit::{PlaceContext, Visitor},
        Body, Local, Location, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
        RETURN_PLACE,
    },
    ty::{Ty, TyCtxt, TyKind, TypeVisitableExt, TypingEnv},
};

const MAX_CARRY_DEPTH: usize = 8;

/// Could a value of this type carry a (mutable) borrow derived from another
/// value? Conservative: unknown shapes answer `true`. A shared reference
/// carries one when its holder can write through it: its referent is not
/// `Freeze` (`&Cell<T>`), or interior-mutable memory is reachable from it by
/// a route `Freeze` does not look through (`&Box<Cell<T>>`, a struct, tuple
/// or `Option` holding one), which `extract::ty_exposes_interior_mutability`
/// walks.
pub(in crate::mir_analysis) fn may_carry_borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    depth: usize,
) -> bool {
    if depth > MAX_CARRY_DEPTH {
        return true;
    }
    let may_carry_borrow = |ty, depth| may_carry_borrow(tcx, typing_env, ty, depth);
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
            !is_freeze(tcx, typing_env, *inner)
                || crate::mir_analysis::extract::ty_exposes_interior_mutability(
                    tcx,
                    typing_env,
                    tcx.erase_and_anonymize_regions(ty),
                )
                || may_carry_borrow(*inner, depth + 1)
        }
        TyKind::Tuple(fields) => fields
            .iter()
            .any(|field_ty| may_carry_borrow(field_ty, depth + 1)),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => may_carry_borrow(*inner, depth + 1),
        TyKind::Adt(adt_def, args) => {
            if args.regions().next().is_some() {
                return true;
            }
            if args.types().any(|arg| may_carry_borrow(arg, depth + 1)) {
                return true;
            }
            if adt_def.is_box() {
                return false;
            }
            adt_def.all_fields().any(|field| {
                let field_ty = field.ty(tcx, *args).skip_norm_wip();
                may_carry_borrow(field_ty, depth + 1)
            })
        }
        // Type parameters, aliases, trait objects, closures, coroutines,
        // foreign types, and anything else: assume they can carry a borrow.
        _ => true,
    }
}

/// Whether `ty` is known to have no interior mutability. A type the query
/// cannot be asked about (bound or unnormalized) is not known to be.
pub(in crate::mir_analysis) fn is_freeze<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    // `is_freeze` is a cached query keyed on a hash of the type, and a type read
    // from borrow-checked MIR still carries region inference variables, which
    // rustc refuses to hash (an ICE, not a verdict). Freezeness never depends on
    // regions, so they are erased before asking.
    let ty = tcx.erase_and_anonymize_regions(ty);
    !ty.has_escaping_bound_vars() && !ty.has_aliases() && ty.is_freeze(tcx, typing_env)
}

struct LocalCollector(Vec<Local>);

impl<'tcx> Visitor<'tcx> for LocalCollector {
    fn visit_local(&mut self, local: Local, _context: PlaceContext, _location: Location) {
        self.0.push(local);
    }
}

pub(super) fn rvalue_locals<'tcx>(rvalue: &Rvalue<'tcx>, location: Location) -> Vec<Local> {
    let mut collector = LocalCollector(Vec::new());
    collector.visit_rvalue(rvalue, location);
    collector.0
}

fn operand_locals<'tcx>(operand: &Operand<'tcx>, location: Location) -> Vec<Local> {
    let mut collector = LocalCollector(Vec::new());
    collector.visit_operand(operand, location);
    collector.0
}

/// One abstract assignment: the borrows carried by `sources` flow into
/// `dest` (and, for writes through a pointer, into everything `dest` may
/// point to).
struct Flow {
    dest: Local,
    indirect: bool,
    /// A call result or a call's pointer argument (opaque callee behaviour).
    from_call: bool,
    sources: Vec<Local>,
}

/// Result of the lent-borrow analysis.
pub(super) struct LentAnalysis {
    /// Argument locals whose borrow may reach `RETURN_PLACE` on some path.
    pub(super) lent: HashSet<Local>,
    /// Per local: may a value of its type carry a borrow?
    pub(super) carries: Vec<bool>,
    /// True when every flow that carries an argument borrow is a direct
    /// (non-indirect, non-call) statement assignment. Only then does a
    /// path-sensitive replay of statement assignments see EVERY route by
    /// which an argument borrow can reach the return value, so a path on
    /// which the replay finds a param not returned really does not lend it.
    pub(super) refinable: bool,
}

/// Compute the parameter locals whose borrow may flow into the return value.
pub(super) fn analyze_lent_borrows<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> LentAnalysis {
    let carries: Vec<bool> = body
        .local_decls
        .iter()
        .map(|decl| may_carry_borrow(tcx, body.typing_env(tcx), decl.ty, 0))
        .collect();
    if !carries[RETURN_PLACE.as_usize()] {
        return LentAnalysis {
            lent: HashSet::new(),
            carries,
            refinable: false,
        };
    }

    let mut flows: Vec<Flow> = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let location = Location {
                block: bb,
                statement_index,
            };
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                flows.push(Flow {
                    dest: place.local,
                    indirect: place
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Deref)),
                    from_call: false,
                    sources: rvalue_locals(rvalue, location),
                });
            }
        }
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let location = Location {
            block: bb,
            statement_index: data.statements.len(),
        };
        let args: Vec<&Operand<'tcx>> = match &terminator.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                args.iter().map(|arg| &arg.node).collect()
            }
            _ => continue,
        };
        let sources: Vec<Local> = args
            .iter()
            .flat_map(|arg| operand_locals(arg, location))
            .collect();
        match &terminator.kind {
            TerminatorKind::Call { destination, .. } => {
                flows.push(Flow {
                    dest: destination.local,
                    indirect: destination
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Deref)),
                    from_call: true,
                    sources: sources.clone(),
                });
            }
            TerminatorKind::TailCall { .. } => flows.push(Flow {
                dest: RETURN_PLACE,
                indirect: false,
                from_call: true,
                sources: sources.clone(),
            }),
            _ => {}
        }
        // A call can store any argument's borrow behind any pointer argument.
        for arg in &args {
            if let Operand::Copy(place) | Operand::Move(place) = arg {
                flows.push(Flow {
                    dest: place.local,
                    indirect: true,
                    from_call: true,
                    sources: sources.clone(),
                });
            }
        }
    }

    // Pointer-alias components: locals connected by a borrow-carrying flow.
    // A write through `*d` may land in any local of `d`'s component.
    let n = body.local_decls.len();
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    for flow in &flows {
        if !carries[flow.dest.as_usize()] && !flow.indirect {
            continue;
        }
        for src in &flow.sources {
            if carries[src.as_usize()] {
                let a = find(&mut parent, flow.dest.as_usize());
                let b = find(&mut parent, src.as_usize());
                parent[a] = b;
            }
        }
    }
    let mut components: HashMap<usize, Vec<Local>> = HashMap::new();
    for local in body.local_decls.indices() {
        let root = find(&mut parent, local.as_usize());
        components.entry(root).or_default().push(local);
    }

    // Taint: which argument borrows each local may carry.
    let mut taint: Vec<HashSet<Local>> = vec![HashSet::new(); n];
    for arg in body.args_iter() {
        taint[arg.as_usize()].insert(arg);
    }
    loop {
        let mut changed = false;
        for flow in &flows {
            let incoming: HashSet<Local> = flow
                .sources
                .iter()
                .flat_map(|src| taint[src.as_usize()].iter().copied().collect::<Vec<_>>())
                .collect();
            if incoming.is_empty() {
                continue;
            }
            let targets: Vec<Local> = if flow.indirect {
                let root = find(&mut parent, flow.dest.as_usize());
                components.get(&root).cloned().unwrap_or_default()
            } else {
                vec![flow.dest]
            };
            for target in targets {
                if !carries[target.as_usize()] {
                    continue;
                }
                let set = &mut taint[target.as_usize()];
                for local in &incoming {
                    changed |= set.insert(*local);
                }
            }
        }
        if !changed {
            break;
        }
    }

    let refinable = flows.iter().all(|flow| {
        if !(flow.indirect || flow.from_call) {
            return true;
        }
        flow.sources
            .iter()
            .all(|src| taint[src.as_usize()].is_empty())
    });

    LentAnalysis {
        lent: taint[RETURN_PLACE.as_usize()].clone(),
        carries,
        refinable,
    }
}

/// Marker wrapped (at `Return`) around a param's tracked pointee value on a
/// path where the param's borrow is returned. The value is NOT that borrow's
/// prophecy; entry.rs never emits a resolution for a marked leaf.
pub(super) const LENT_ON_PATH_MARKER: &str = "__trust_wp_lent_on_path";
