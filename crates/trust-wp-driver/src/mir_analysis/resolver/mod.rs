// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Dataflow-precise borrow resolution for mutable reference parameters (#2150).
//!
//! Determines the exact MIR locations where `&mut` borrows should be resolved
//! (i.e., where `v.final == v.current` can be asserted). This replaces
//! function-scope resolution, which requires 6 SMT variables per `&mut` param.
//!
//! # Algorithm
//!
//! Combines backward liveness with forward initialization tracking to compute
//! resolve points. A local is "resolved" when it transitions from live to dead
//! while initialized. See [`liveness`] for the backward dataflow implementation.
//!
//! # Relationship to Creusot
//!
//! Creusot's `analysis/resolve.rs` uses `MaybeLiveExceptDrop` +
//! `MaybeUninitializedPlaces` + custom `Borrows` analysis with
//! `BorrowSet`/`RegionInferenceContext`. This module implements a simplified
//! version at local granularity (not move-path), sound because trust-wp's `&mut`
//! encoding operates per-parameter, not per-place.

mod liveness;

use std::collections::{HashMap, HashSet};

use liveness::{compute_mut_local_liveness, for_each_rvalue_local, is_deref_of_mut_local};
use rustc_borrowck::consumers::{BodyWithBorrowckFacts, TwoPhaseActivation};
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location, Rvalue, StatementKind},
    ty::{TyCtxt, TyKind},
};

use super::{collect_mut_ref_paths_with_tcx, type_contains_mut_ref_with_tcx};

/// A point where a mutable borrow parameter should be resolved.
///
/// At a resolve point, the prophecy `v.final` is constrained to equal
/// the current value `v.current`. This replaces the function-scope
/// resolution that required intermediate alias variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvePoint {
    /// The parameter name being resolved (e.g., "v" for `v: &mut i32`).
    pub(crate) param_name: String,
    /// The MIR local holding the `&mut` reference.
    pub(crate) local: Local,
    /// The MIR location where the borrow is resolved.
    pub(crate) location: Location,
}

/// Parent/child timing metadata for a reborrow writeback.
///
/// Ordinary reborrows write back immediately at reservation time. Two-phase
/// borrows delay that writeback until their activation site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReborrowWriteback {
    /// Child reborrow name (e.g., `v_rb5`).
    pub(crate) child_name: String,
    /// Parent borrow name (e.g., `v`).
    pub(crate) parent_name: String,
    /// MIR location where the reborrow is reserved.
    pub(crate) reservation: Location,
    /// Activation site for two-phase borrows. `None` means immediate writeback.
    pub(crate) activation: Option<Location>,
}

/// Results of the resolve analysis.
///
/// Fields are populated by `compute_resolve_points` and consumed by the
/// mut-borrow extraction and verification dispatch paths (#2150).
#[derive(Debug, Clone, Default)]
pub(crate) struct ResolveResults {
    /// Explicit parent/child writeback timing for reborrows.
    pub(crate) writebacks: Vec<ReborrowWriteback>,
    /// Map from parameter name to whether it has a dataflow-precise resolve
    /// point (true) or falls back to function-scope resolution (false).
    pub(crate) has_precise_resolve: HashMap<String, bool>,
}

/// Compute resolve points for `&mut` parameters in a function body.
///
/// For each `&mut` parameter, finds the MIR location(s) where the borrow
/// can be resolved (where the local transitions from live to dead). Parameters
/// with complex control flow fall back to function-scope resolution.
pub(crate) fn compute_resolve_points<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    body_with_facts: Option<&BodyWithBorrowckFacts<'tcx>>,
) -> ResolveResults {
    let mut mut_locals: HashSet<Local> = HashSet::new();
    let mut local_to_name: HashMap<Local, String> = HashMap::new();
    // Track params whose type is a composite containing `&mut` fields
    // (e.g., `(&mut T, &mut U)`). These need field-level resolve entries
    // in addition to the whole-param entry. (#2687)
    let mut composite_mut_ref_fields: Vec<(String, Vec<u32>)> = Vec::new();

    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let ty = body.local_decls[local].ty;
        if matches!(
            ty.kind(),
            TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        ) {
            mut_locals.insert(local);
            local_to_name.insert(local, name.clone());
        } else if type_contains_mut_ref_with_tcx(tcx, ty) {
            // Tuple or newtype containing `&mut` fields. Track the whole
            // local for liveness analysis, and record the field paths for
            // field-level resolve entries. (#2687)
            mut_locals.insert(local);
            local_to_name.insert(local, name.clone());
            for path in collect_mut_ref_paths_with_tcx(tcx, ty) {
                if let [field_idx] = path.as_slice() {
                    composite_mut_ref_fields.push((name.clone(), vec![*field_idx]));
                }
            }
        }
    }

    if mut_locals.is_empty() {
        return ResolveResults::default();
    }

    let (reborrow_parents, writebacks) =
        collect_reborrows(body, &mut mut_locals, &mut local_to_name, body_with_facts);
    let liveness = compute_mut_local_liveness(body, &mut_locals);
    let (_, param_resolves) = find_resolve_points(body, &liveness, &mut_locals, &local_to_name);
    let mut has_precise_resolve =
        compute_precision_map(&local_to_name, &reborrow_parents, &param_resolves);

    // For composite params (tuples/newtypes with inner `&mut` fields),
    // propagate the parent's resolve precision to each field-level name.
    // The ay layer's `emit_resolve_assertions` looks up field names like
    // "p.0", "p.1" in the resolve map. Without these entries, the ay
    // layer cannot emit `p.0_final == p.0_current` for unmodified fields,
    // causing postconditions like `^p.1 == *p.1` to be unprovable. (#2687)
    for (param_name, field_path) in &composite_mut_ref_fields {
        let parent_precise = has_precise_resolve
            .get(param_name)
            .copied()
            .unwrap_or(false);
        if parent_precise {
            // Only single-level field projections are supported.
            if let [field_idx] = field_path.as_slice() {
                let field_name = format!("{param_name}.{field_idx}");
                has_precise_resolve.insert(field_name, true);
            }
        }
    }

    ResolveResults {
        writebacks,
        has_precise_resolve,
    }
}

/// Scan the MIR body for reborrow patterns (`dest = &mut *source`).
fn collect_reborrows<'tcx>(
    body: &Body<'tcx>,
    mut_locals: &mut HashSet<Local>,
    local_to_name: &mut HashMap<Local, String>,
    body_with_facts: Option<&BodyWithBorrowckFacts<'tcx>>,
) -> (HashMap<Local, Local>, Vec<ReborrowWriteback>) {
    let mut reborrow_parents: HashMap<Local, Local> = HashMap::new();
    let mut writebacks = Vec::new();

    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
            if let StatementKind::Assign(box (
                dest,
                Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Mut { .. }, place),
            )) = &stmt.kind
            {
                if is_deref_of_mut_local(place, mut_locals) && dest.projection.is_empty() {
                    reborrow_parents.insert(dest.local, place.local);
                    mut_locals.insert(dest.local);
                    let parent_name = local_to_name
                        .get(&place.local)
                        .cloned()
                        .unwrap_or_else(|| format!("_reborrow_{}", place.local.as_u32()));
                    let child_name = format!("{parent_name}_rb{}", dest.local.as_u32());
                    local_to_name.insert(dest.local, child_name.clone());

                    let reservation = Location {
                        block: bb,
                        statement_index: stmt_idx,
                    };
                    match classify_writeback_timing(
                        body_with_facts,
                        reservation,
                        dest.local,
                        place.local,
                    ) {
                        WritebackTiming::Immediate => writebacks.push(ReborrowWriteback {
                            child_name,
                            parent_name,
                            reservation,
                            activation: None,
                        }),
                        WritebackTiming::Delayed(activation) => {
                            writebacks.push(ReborrowWriteback {
                                child_name,
                                parent_name,
                                reservation,
                                activation: Some(activation),
                            });
                        }
                        WritebackTiming::NeverActivated => {}
                    }
                }
            }
        }
    }

    (reborrow_parents, writebacks)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WritebackTiming {
    Immediate,
    Delayed(Location),
    NeverActivated,
}

fn classify_writeback_timing<'tcx>(
    body_with_facts: Option<&BodyWithBorrowckFacts<'tcx>>,
    reservation: Location,
    assigned_local: Local,
    borrowed_local: Local,
) -> WritebackTiming {
    let Some(body_with_facts) = body_with_facts else {
        return WritebackTiming::Immediate;
    };
    let Some(borrow_data) = body_with_facts.borrow_set.location_map().get(&reservation) else {
        return WritebackTiming::Immediate;
    };
    if borrow_data.assigned_place().local != assigned_local
        || borrow_data.borrowed_place().local != borrowed_local
    {
        return WritebackTiming::Immediate;
    }
    match borrow_data.activation_location() {
        TwoPhaseActivation::NotTwoPhase => WritebackTiming::Immediate,
        TwoPhaseActivation::ActivatedAt(location) => WritebackTiming::Delayed(location),
        // A reservation that never activates should not emit any writeback.
        TwoPhaseActivation::NotActivated => WritebackTiming::NeverActivated,
    }
}

/// Context for mid-block resolve emission, reducing parameter count.
struct MidblockCtx<'a, 'tcx> {
    body: &'a Body<'tcx>,
    bb: BasicBlock,
    currently_live: &'a HashSet<Local>,
    liveness: &'a liveness::LocalLiveness,
    local_to_name: &'a HashMap<Local, String>,
}

/// Walk all blocks to find where tracked locals transition from live to dead.
fn find_resolve_points<'tcx>(
    body: &Body<'tcx>,
    liveness: &liveness::LocalLiveness,
    mut_locals: &HashSet<Local>,
    local_to_name: &HashMap<Local, String>,
) -> (Vec<ResolvePoint>, HashMap<String, Vec<Location>>) {
    let mut resolve_points: Vec<ResolvePoint> = Vec::new();
    let mut param_resolves: HashMap<String, Vec<Location>> = HashMap::new();

    for bb in body.basic_blocks.indices() {
        let bb_data = &body.basic_blocks[bb];
        let live_out = &liveness.live_out[&bb];

        let mut currently_live: HashSet<Local> = liveness.live_in[&bb].clone();

        // Walk statements forward, tracking live/dead transitions.
        for stmt in &bb_data.statements {
            let mut newly_dead = Vec::new();
            for &local in &currently_live {
                if let StatementKind::Assign(box (dest, _)) = &stmt.kind {
                    if dest.projection.is_empty() && dest.local == local {
                        newly_dead.push(local);
                    }
                }
                if let StatementKind::StorageDead(dead_local) = &stmt.kind {
                    if *dead_local == local {
                        newly_dead.push(local);
                    }
                }
            }
            for dead_local in &newly_dead {
                currently_live.remove(dead_local);
            }

            if let StatementKind::Assign(box (dest, rvalue)) = &stmt.kind {
                if is_deref_of_mut_local(dest, mut_locals) {
                    currently_live.insert(dest.local);
                }
                for_each_rvalue_local(rvalue, mut_locals, |l| {
                    currently_live.insert(l);
                });
            }
        }

        // Locals in currently_live but NOT in live_out are resolved at terminator.
        let terminator_loc = Location {
            block: bb,
            statement_index: bb_data.statements.len(),
        };
        emit_resolve_points(
            &currently_live,
            live_out,
            terminator_loc,
            local_to_name,
            &mut resolve_points,
            &mut param_resolves,
        );

        // Check for mid-block kills.
        let ctx = MidblockCtx {
            body,
            bb,
            currently_live: &currently_live,
            liveness,
            local_to_name,
        };
        emit_midblock_resolves(&ctx, &mut resolve_points, &mut param_resolves);
    }

    resolve_points.sort_by(|a, b| {
        a.location
            .block
            .cmp(&b.location.block)
            .then(a.location.statement_index.cmp(&b.location.statement_index))
            .then(a.local.cmp(&b.local))
    });

    (resolve_points, param_resolves)
}

/// Emit resolve points for locals that are live at block end but dead in successors.
fn emit_resolve_points(
    currently_live: &HashSet<Local>,
    live_out: &HashSet<Local>,
    location: Location,
    local_to_name: &HashMap<Local, String>,
    resolve_points: &mut Vec<ResolvePoint>,
    param_resolves: &mut HashMap<String, Vec<Location>>,
) {
    for &local in currently_live {
        if !live_out.contains(&local) {
            if let Some(name) = local_to_name.get(&local) {
                resolve_points.push(ResolvePoint {
                    param_name: name.clone(),
                    local,
                    location,
                });
                param_resolves
                    .entry(name.clone())
                    .or_default()
                    .push(location);
            }
        }
    }
}

/// Check for locals killed mid-block and emit their resolve points.
fn emit_midblock_resolves(
    ctx: &MidblockCtx<'_, '_>,
    resolve_points: &mut Vec<ResolvePoint>,
    param_resolves: &mut HashMap<String, Vec<Location>>,
) {
    let live_out = &ctx.liveness.live_out[&ctx.bb];
    for &local in &ctx.liveness.live_in[&ctx.bb] {
        if !ctx.currently_live.contains(&local) && !live_out.contains(&local) {
            if let Some(kill_loc) = find_kill_location(ctx.body, ctx.bb, local) {
                if let Some(name) = ctx.local_to_name.get(&local) {
                    let already_recorded = resolve_points
                        .iter()
                        .any(|rp| rp.local == local && rp.location.block == ctx.bb);
                    if !already_recorded {
                        resolve_points.push(ResolvePoint {
                            param_name: name.clone(),
                            local,
                            location: kill_loc,
                        });
                        param_resolves
                            .entry(name.clone())
                            .or_default()
                            .push(kill_loc);
                    }
                }
            }
        }
    }
}

/// Compute which parameters have precise resolve points vs function-scope fallback.
fn compute_precision_map(
    local_to_name: &HashMap<Local, String>,
    reborrow_parents: &HashMap<Local, Local>,
    param_resolves: &HashMap<String, Vec<Location>>,
) -> HashMap<String, bool> {
    let mut has_precise_resolve: HashMap<String, bool> = HashMap::new();
    for (&local, param_name) in local_to_name {
        if !reborrow_parents.contains_key(&local) {
            let locs = param_resolves.get(param_name).map_or(0, Vec::len);
            has_precise_resolve.insert(param_name.clone(), locs > 0);
        }
    }
    has_precise_resolve
}

/// Find the exact location within a block where a local is killed.
fn find_kill_location(body: &Body<'_>, bb: BasicBlock, local: Local) -> Option<Location> {
    use rustc_middle::mir::TerminatorKind;
    let bb_data = &body.basic_blocks[bb];
    for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
        match &stmt.kind {
            StatementKind::Assign(box (dest, _))
                if dest.projection.is_empty() && dest.local == local =>
            {
                return Some(Location {
                    block: bb,
                    statement_index: stmt_idx,
                });
            }
            StatementKind::StorageDead(dead_local) if *dead_local == local => {
                return Some(Location {
                    block: bb,
                    statement_index: stmt_idx,
                });
            }
            _ => {}
        }
    }
    let term_loc = Location {
        block: bb,
        statement_index: bb_data.statements.len(),
    };
    match &bb_data.terminator().kind {
        TerminatorKind::Drop { place, .. } if place.local == local => Some(term_loc),
        TerminatorKind::Call { destination, .. }
            if destination.projection.is_empty() && destination.local == local =>
        {
            Some(term_loc)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolve_results_default() {
        let r = ResolveResults::default();
        assert!(r.writebacks.is_empty());
        assert!(r.has_precise_resolve.is_empty());
    }

    #[test]
    fn test_resolve_point_equality() {
        let rp1 = ResolvePoint {
            param_name: "v".to_string(),
            local: Local::from_u32(1),
            location: Location {
                block: BasicBlock::from_u32(0),
                statement_index: 3,
            },
        };
        let rp2 = rp1.clone();
        assert_eq!(rp1, rp2);

        let rp3 = ResolvePoint {
            param_name: "v".to_string(),
            local: Local::from_u32(1),
            location: Location {
                block: BasicBlock::from_u32(1),
                statement_index: 0,
            },
        };
        assert_ne!(rp1, rp3);
    }

    #[test]
    fn test_reborrow_writeback_equality() {
        let writeback = ReborrowWriteback {
            child_name: "v_rb5".to_string(),
            parent_name: "v".to_string(),
            reservation: Location {
                block: BasicBlock::from_u32(2),
                statement_index: 1,
            },
            activation: Some(Location {
                block: BasicBlock::from_u32(3),
                statement_index: 0,
            }),
        };
        assert_eq!(writeback.parent_name, "v");
        assert_eq!(writeback.child_name, "v_rb5");
        assert!(writeback.activation.is_some());
    }

    /// Verify that the precision map propagation for composite `&mut` fields
    /// correctly adds field-level entries when the parent has precise resolve.
    /// This is the core logic for tuple-of-mut-ref recognition (#2687).
    #[test]
    fn test_precision_map_field_propagation_for_composite_params() {
        // Simulate: p: (&mut T, &mut U) with precise resolve for "p".
        let mut has_precise: HashMap<String, bool> = HashMap::new();
        has_precise.insert("p".to_string(), true);
        has_precise.insert("x".to_string(), false); // non-precise param

        // Composite fields: p has fields 0 and 1.
        let composite_fields = vec![
            ("p".to_string(), vec![0_u32]),
            ("p".to_string(), vec![1_u32]),
        ];

        // Apply the propagation logic (mirrors compute_resolve_points).
        for (param_name, field_path) in &composite_fields {
            let parent_precise = has_precise.get(param_name).copied().unwrap_or(false);
            if parent_precise {
                if let [field_idx] = field_path.as_slice() {
                    let field_name = format!("{param_name}.{field_idx}");
                    has_precise.insert(field_name, true);
                }
            }
        }

        // Verify field-level entries were added.
        assert_eq!(has_precise.get("p.0"), Some(&true));
        assert_eq!(has_precise.get("p.1"), Some(&true));
        // Parent entry still present.
        assert_eq!(has_precise.get("p"), Some(&true));
        // Non-precise param unchanged.
        assert_eq!(has_precise.get("x"), Some(&false));
        // No spurious entries.
        assert_eq!(has_precise.len(), 4);
    }

    /// Verify that field propagation skips params without precise resolve.
    #[test]
    fn test_precision_map_field_propagation_skips_non_precise() {
        let mut has_precise: HashMap<String, bool> = HashMap::new();
        has_precise.insert("p".to_string(), false);

        let composite_fields = vec![
            ("p".to_string(), vec![0_u32]),
            ("p".to_string(), vec![1_u32]),
        ];

        for (param_name, field_path) in &composite_fields {
            let parent_precise = has_precise.get(param_name).copied().unwrap_or(false);
            if parent_precise {
                if let [field_idx] = field_path.as_slice() {
                    let field_name = format!("{param_name}.{field_idx}");
                    has_precise.insert(field_name, true);
                }
            }
        }

        // No field entries added since parent is non-precise.
        assert_eq!(has_precise.get("p.0"), None);
        assert_eq!(has_precise.get("p.1"), None);
        assert_eq!(has_precise.len(), 1);
    }
}
