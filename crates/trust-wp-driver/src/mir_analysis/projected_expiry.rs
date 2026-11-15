// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Caller-side expiry pins for `&mut` borrows that arrive INSIDE a call result
//! (#prophecy-slots, Fix B M5 — the death machinery).
//!
//! ## What was missing, and why the existing lanes could not supply it
//!
//! Two prophecy-pin lanes exist before this module:
//!
//! * `mut_borrow::entry` pins a `&mut` PARAMETER at the function's `Return`
//!   (`final_values`, keyed by name, tuple fields keyed `"x.0"`);
//! * `extract::borrow_carriers` (#124) pins a LOCALLY-ROOTED borrow — one the
//!   body itself created with `&mut x` — at its expiry, keying on the borrow
//!   LOCAL inside a fully-known unique-assignment chain down to a non-reference
//!   root.
//!
//! A `&mut` that is minted inside a CALLEE and handed back inside a payload
//! (`Option<&mut T>`, `Option<(&mut T, &mut [T])>`, `(&mut V, &mut Map)`) is
//! neither. It has no local root — the chain walk bottoms out at a call
//! destination, not at a `&mut x` — and its expiry is not the function's
//! `Return`: it dies somewhere in OUR body, and until it does, its prophecy is
//! genuinely free. That death point is the fact this module proves.
//!
//! ## What is emitted
//!
//! One [`ProjectedFinalPin`] per proven death:
//!
//! ```text
//! (no variant on the path)   ^<payload> == <death value>
//! (variant on the path)      is-<Ctor>(root) ==> ^<payload> == <death value>
//! ```
//!
//! ## ★FA discipline: a pin at an unproven death point is a false-accept factory
//!
//! Every condition below is a PROOF OBLIGATION on the producer, not a heuristic.
//! Failing any one of them emits NOTHING for that shape (a weakening — always
//! the safe direction) and records the reason in the report's disarm table.
//!
//! | # | Condition | Why it is load-bearing |
//! |---|---|---|
//! | R0 | the call destination is uniquely assigned | a second assignment makes "the" result ambiguous under control flow |
//! | R1 | the payload binder is uniquely assigned and `&mut`-typed | ditto, and a non-`&mut` binder has no prophecy |
//! | R2 | the extraction, every write, and the death all sit in ONE basic block | no path conditions to model; the walk cannot be wrong about ordering |
//! | R3 | a variant-bearing path requires the block to be reachable ONLY through the `SwitchInt` edge selecting exactly that variant | this is what makes `is-<Ctor>(root)` provably equivalent to the branch condition — an unguarded or mis-guarded pin on the other arm is a fact about a term that denotes nothing |
//! | R4 | a variant-bearing path requires the ROOT to have a source name | without a name there is no symbol to test, so the guard cannot be expressed — and an UNGUARDED enum-payload pin is precisely the `optmut_none_branch_pin` adversarial shape |
//! | R5 | the payload local occurs NOWHERE outside the proven region | no move, no reborrow, no call argument, no aggregate, no return — the borrow cannot escape our tracking |
//! | R6 | the root local occurs nowhere except the call, the discriminant read, the switch, the downcast and its storage markers | the carrier cannot be re-read, moved, or mutated behind our back |
//! | R7 | every statement in the region is either a tracked single-deref write through the payload or mentions neither the payload nor the root | any deeper-projected write (`(*p).f = ..`, `**p = ..`) or unknown statement makes the tracked death value stale |
//! | R8 | every tracked write's value translates to a GROUND CONSTANT tree | an identity-bearing value would need the full extraction environment to be correct; refusing is cheaper than being wrong |
//! | R9 | at least one write was tracked | a zero-write pin degenerates to the resolve identity `^p == *p`, the exact premise class `should_fail/final_borrows.rs` gates; it adds no information the resolve lane does not already own |
//! | R10 | `NotFinalPlaces::is_final_at(*payload, death)` proves the referent is not used after the death point | an INDEPENDENT dataflow corroboration of R2/R5/R7, computed by the analysis Creusot uses for exactly this question |
//! | R11 | the region contains no terminator-level call and the death is a `StorageDead` STATEMENT in the block | a call could write through any live borrow; a death that is only the block boundary is not a proven kill |
//!
//! R3 deserves its own sentence, because it is the only condition whose failure
//! is silent. The guard we emit is `is-<Ctor>(root)`. That is sound *precisely
//! because* the downcast block is dominated by — and reachable only through —
//! the discriminant test for that constructor. If the block had a second
//! predecessor, the pin would assert the arm's death value on a path the arm
//! never ran, and no vacuity counter would see it (the premise set stays SAT).

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::TyCtxt,
};
use rustc_mir_dataflow::Analysis;
use tracing::debug;
use trust_wp_core::formula::{FinalPinTarget, PinStep, ProjectedFinalPin, PureExpr};

use crate::mir_analysis::{
    extract::expr_is_ground_constant_tree,
    mut_borrow::type_analysis::{collect_mut_ref_pin_paths_with_tcx, MutRefPinStep},
    not_final_places::NotFinalPlaces,
    translate::{translate_rvalue, ty_to_expr_sort_enriched},
};

/// Why a candidate shape was refused. Kept as data (not just a log line) so the
/// per-shape emit/disarm table can be reported and pinned by tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DisarmReason {
    /// R0/R1: a local in the shape is assigned more than once.
    NotUniquelyAssigned,
    /// R2/R11: extraction, writes and death are not confined to one block, or
    /// the death is not a `StorageDead` statement in that block.
    DeathNotInRegion,
    /// R3: the downcast block has a predecessor that is not the matching
    /// `SwitchInt` edge.
    VariantGuardNotProvable,
    /// R4: a variant-bearing path whose root carries no source name.
    RootUnnamed,
    /// R5/R6: the payload or root local escapes the proven region.
    LocalEscapes,
    /// R7: a statement in the region touches the shape in an unmodelled way.
    UnmodelledStatement,
    /// R8: a write value did not translate to a ground constant tree.
    ValueNotGround,
    /// R9: no write was tracked, so the pin would be the resolve identity.
    NoTrackedWrite,
    /// R10: the backward finality analysis says the referent may still be used.
    ReferentNotFinal,
    /// The payload binder has no source name and neither does the root, so the
    /// pin would attach to a symbol nothing else in the VC mentions.
    NoAddressableSymbol,
}

impl DisarmReason {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            DisarmReason::NotUniquelyAssigned => "not_uniquely_assigned",
            DisarmReason::DeathNotInRegion => "death_not_in_region",
            DisarmReason::VariantGuardNotProvable => "variant_guard_not_provable",
            DisarmReason::RootUnnamed => "root_unnamed",
            DisarmReason::LocalEscapes => "local_escapes",
            DisarmReason::UnmodelledStatement => "unmodelled_statement",
            DisarmReason::ValueNotGround => "value_not_ground",
            DisarmReason::NoTrackedWrite => "no_tracked_write",
            DisarmReason::ReferentNotFinal => "referent_not_final",
            DisarmReason::NoAddressableSymbol => "no_addressable_symbol",
        }
    }
}

/// One refused candidate, for the audit table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DisarmRecord {
    /// `<root local>/<payload local>` — enough to locate the shape in MIR.
    pub(crate) shape: String,
    pub(crate) reason: DisarmReason,
}

/// Result of the death analysis for one body.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ProjectedExpiryReport {
    /// Pins whose death point is PROVEN. Safe to assert.
    pub(crate) pins: Vec<ProjectedFinalPin>,
    /// Candidates refused, with the failing condition.
    pub(crate) disarms: Vec<DisarmRecord>,
}

impl ProjectedExpiryReport {
    pub(crate) fn is_empty(&self) -> bool {
        self.pins.is_empty()
    }
}

/// Maximum `Goto`/`FalseEdge` hops between the discriminant test and the
/// downcast. Two is what rustc emits for a `match`/`if let` arm; the budget is
/// small on purpose — a long chain is a region this lane does not model.
const MAX_GUARD_CHAIN_HOPS: usize = 4;

/// A payload-extraction site: `payload = move ((root as Ctor).f)` or
/// `payload = move (root.f)`.
struct Extraction {
    root: Local,
    payload: Local,
    block: BasicBlock,
    stmt_idx: usize,
    /// Steps from `root` down to `payload`, in encoder vocabulary.
    steps: Vec<PinStep>,
    /// MIR variant index when the extraction goes through a `Downcast`.
    variant_idx: Option<u32>,
}

/// Collect the provable caller-side expiry pins for `body`.
///
/// Returns an empty report (no pins) for every body that has no candidate
/// shape, which is the overwhelmingly common case; the walk is a single linear
/// scan plus one backward dataflow run gated on a candidate actually existing,
/// so the cost on such bodies is a scan of the terminators.
pub(crate) fn collect_projected_expiry_pins<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> ProjectedExpiryReport {
    let mut report = ProjectedExpiryReport::default();

    let extractions = collect_extractions(tcx, body);
    if extractions.is_empty() {
        return report;
    }
    // Whole-local assignment counts, the R0/R1 authority: computed once for
    // the body and read by `adjudicate` for every candidate.
    let assign_counts = assignment_counts(body);

    // The finality analysis is only built when a candidate exists (R10).
    let analysis = NotFinalPlaces::new(tcx, body);
    let results = analysis.iterate_to_fixpoint(tcx, body, None);
    let mut cursor = results.into_results_cursor(body);

    for extraction in extractions {
        let shape = format!(
            "_{}/_{}",
            extraction.root.as_u32(),
            extraction.payload.as_u32()
        );
        match adjudicate(
            tcx,
            body,
            arg_names,
            &assign_counts,
            &extraction,
            &mut cursor,
        ) {
            Ok(pin) => {
                debug!(
                    "projected_expiry: PROVEN death for {shape} -> {:?} == {:?}",
                    pin.target, pin.value
                );
                report.pins.push(pin);
            }
            Err(reason) => {
                debug!("projected_expiry: DISARMED {shape} ({})", reason.as_str());
                report.disarms.push(DisarmRecord { shape, reason });
            }
        }
    }
    report.pins.sort_by(|a, b| a.provenance.cmp(&b.provenance));
    report.disarms.sort_by(|a, b| a.shape.cmp(&b.shape));
    report
}

/// Whole-local assignment counts (statement assigns + call destinations).
fn assignment_counts(body: &Body<'_>) -> HashMap<Local, usize> {
    let mut counts: HashMap<Local, usize> = HashMap::new();
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            if let StatementKind::Assign((place, _)) = &statement.kind {
                if place.projection.is_empty() {
                    *counts.entry(place.local).or_insert(0) += 1;
                }
            }
        }
        if let Some(terminator) = &block.terminator {
            if let TerminatorKind::Call { destination, .. } = &terminator.kind {
                if destination.projection.is_empty() {
                    *counts.entry(destination.local).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

/// Find `payload = move ((root as Ctor).f)` / `payload = move (root.f)` where
/// `root` is a uniquely-assigned CALL destination whose type embeds a `&mut`
/// behind at least one projection step.
fn collect_extractions<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<Extraction> {
    // Call destinations, so a non-call root (an aggregate the body itself
    // built) never enters this lane — that borrow is locally rooted and belongs
    // to the #124 carrier lane.
    let mut call_dests: HashSet<Local> = HashSet::new();
    for block in body.basic_blocks.iter() {
        if let Some(terminator) = &block.terminator {
            if let TerminatorKind::Call { destination, .. } = &terminator.kind {
                if destination.projection.is_empty() {
                    call_dests.insert(destination.local);
                }
            }
        }
    }

    let mut out = Vec::new();
    for (block_idx, block) in body.basic_blocks.iter_enumerated() {
        for (stmt_idx, statement) in block.statements.iter().enumerate() {
            let StatementKind::Assign((dest, rvalue)) = &statement.kind else {
                continue;
            };
            if !dest.projection.is_empty() {
                continue;
            }
            let Rvalue::Use(Operand::Move(src) | Operand::Copy(src), _) = rvalue else {
                continue;
            };
            let root = src.local;
            if !call_dests.contains(&root) {
                continue;
            }
            if !is_mut_ref_local(body, dest.local) {
                continue;
            }
            let Some((steps, variant_idx)) = projection_steps(src) else {
                continue;
            };
            if steps.is_empty() {
                continue; // a whole-local move is not a projected payload
            }
            // The root's TYPE must actually admit this path — the enum-aware
            // collector is the authority (M5 (1)). This also rejects shapes the
            // encoder could not address, e.g. a projection through a `Box`.
            let root_ty = body.local_decls[root].ty;
            let admitted = collect_mut_ref_pin_paths_with_tcx(tcx, root_ty)
                .into_iter()
                .any(|path| pin_path_matches(&path, &steps, variant_idx));
            if !admitted {
                continue;
            }
            // Non-unique assignment is NOT filtered here: the candidate is
            // recorded so `adjudicate` (R0/R1, over the body's assignment
            // counts) can put it in the disarm table with its reason, which
            // is what makes the emit/disarm table auditable.
            out.push(Extraction {
                root,
                payload: dest.local,
                block: block_idx,
                stmt_idx,
                steps,
                variant_idx,
            });
        }
    }
    out
}

/// Translate a MIR place projection into encoder-vocabulary pin steps.
///
/// Accepts exactly `[.f]`, `[Downcast(v), .f]` — one level. Anything else
/// (indexing, deref, a second field) is refused: the pin lane only addresses
/// shapes it can prove, and each extra step is another aliasing question.
fn projection_steps(place: &Place<'_>) -> Option<(Vec<PinStep>, Option<u32>)> {
    let projections: &[_] = place.projection.as_ref();
    match projections {
        [ProjectionElem::Field(field, _)] => Some((vec![PinStep::Field(field.as_usize())], None)),
        [ProjectionElem::Downcast(name, variant), ProjectionElem::Field(field, _)] => {
            let ctor = name.map(|sym| sym.to_string())?;
            Some((
                vec![PinStep::Variant {
                    ctor,
                    field: field.as_usize(),
                }],
                u32::try_from(variant.as_usize()).ok(),
            ))
        }
        _ => None,
    }
}

/// Does the type-level pin path describe the same one-step projection the MIR
/// statement performs?
fn pin_path_matches(path: &[MutRefPinStep], steps: &[PinStep], variant_idx: Option<u32>) -> bool {
    if path.len() != steps.len() {
        return false;
    }
    path.iter()
        .zip(steps)
        .all(|(type_step, mir_step)| match (type_step, mir_step) {
            (MutRefPinStep::Field(a), PinStep::Field(b)) => *a as usize == *b,
            (
                MutRefPinStep::Variant {
                    variant_idx: tv,
                    ctor: tc,
                    field: tf,
                },
                PinStep::Variant { ctor, field },
            ) => Some(*tv) == variant_idx && tc == ctor && *tf as usize == *field,
            _ => false,
        })
}

fn is_mut_ref_local(body: &Body<'_>, local: Local) -> bool {
    matches!(
        body.local_decls[local].ty.kind(),
        rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
    )
}

/// Run every condition R0..R11 for one candidate; produce the pin or the
/// reason it was refused.
fn adjudicate<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    assign_counts: &HashMap<Local, usize>,
    extraction: &Extraction,
    cursor: &mut rustc_mir_dataflow::ResultsCursor<'_, 'tcx, NotFinalPlaces<'_, 'tcx>>,
) -> Result<ProjectedFinalPin, DisarmReason> {
    // R0 / R1
    if assign_counts.get(&extraction.root).copied() != Some(1)
        || assign_counts.get(&extraction.payload).copied() != Some(1)
    {
        return Err(DisarmReason::NotUniquelyAssigned);
    }

    let block_data = &body.basic_blocks[extraction.block];

    // R2 / R11: the death must be a StorageDead of the payload IN this block,
    // after the extraction.
    let death_idx = block_data
        .statements
        .iter()
        .enumerate()
        .skip(extraction.stmt_idx + 1)
        .find(|(_, statement)| {
            matches!(statement.kind, StatementKind::StorageDead(local) if local == extraction.payload)
        })
        .map(|(idx, _)| idx)
        .ok_or(DisarmReason::DeathNotInRegion)?;

    // R3 / R4: the variant guard.
    if let Some(variant_idx) = extraction.variant_idx {
        prove_variant_guard(tcx, body, extraction, variant_idx)?;
    }
    let root_name =
        crate::mir_analysis::extract::source_name_for_local(body, extraction.root, arg_names);
    if extraction.variant_idx.is_some() && root_name.is_none() {
        return Err(DisarmReason::RootUnnamed);
    }

    // R7 / R8 / R9: walk the region, tracking the death value.
    let mut death_value: Option<PureExpr> = None;
    let empty_locals: HashMap<Local, PureExpr> = HashMap::new();
    for statement in &block_data.statements[extraction.stmt_idx + 1..death_idx] {
        match &statement.kind {
            StatementKind::Assign((place, rvalue)) => {
                let touches_payload = place.local == extraction.payload
                    || rvalue_mentions(rvalue, extraction.payload)
                    || rvalue_mentions(rvalue, extraction.root);
                if place.local == extraction.root {
                    return Err(DisarmReason::UnmodelledStatement);
                }
                if !touches_payload {
                    // A statement over unrelated locals cannot reach `*payload`.
                    // R5 (`prove_no_escape`, run below — both must pass for a
                    // pin) establishes that NO borrow of the payload exists
                    // anywhere in the body, so no other local can alias it.
                    continue;
                }
                let projections: &[_] = place.projection.as_ref();
                if place.local != extraction.payload || projections != [ProjectionElem::Deref] {
                    // A deeper-projected or root-touching write: the whole-value
                    // death tracking would be stale.
                    return Err(DisarmReason::UnmodelledStatement);
                }
                let value = translate_rvalue(rvalue, &empty_locals, Some(body))
                    .ok_or(DisarmReason::ValueNotGround)?;
                if !expr_is_ground_constant_tree(&value) {
                    return Err(DisarmReason::ValueNotGround);
                }
                death_value = Some(value);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                if *local == extraction.root || *local == extraction.payload {
                    return Err(DisarmReason::UnmodelledStatement);
                }
            }
            StatementKind::FakeRead(..)
            | StatementKind::Nop
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(_)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. } => {}
            StatementKind::SetDiscriminant { place, .. } => {
                if place.local == extraction.root || place.local == extraction.payload {
                    return Err(DisarmReason::UnmodelledStatement);
                }
            }
            _ => return Err(DisarmReason::UnmodelledStatement),
        }
    }
    let death_value = death_value.ok_or(DisarmReason::NoTrackedWrite)?;

    // R5 / R6: nothing outside the proven region may mention either local.
    prove_no_escape(body, extraction, death_idx)?;

    // R10: independent dataflow corroboration that `*payload` is not used
    // after the death point.
    let death_location = rustc_middle::mir::Location {
        block: extraction.block,
        statement_index: death_idx,
    };
    let deref_place = Place {
        local: extraction.payload,
        projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
    };
    if NotFinalPlaces::is_final_at(cursor, &deref_place, death_location).is_none() {
        return Err(DisarmReason::ReferentNotFinal);
    }

    // Address the pin. A variant-bearing path is always addressed through the
    // named root, so the tester has a receiver; a variant-free path prefers the
    // payload binder's own name (the symbol the rest of the VC already uses).
    let payload_name =
        crate::mir_analysis::extract::source_name_for_local(body, extraction.payload, arg_names);
    let target = if extraction.variant_idx.is_some() {
        let root = root_name.ok_or(DisarmReason::RootUnnamed)?;
        FinalPinTarget::Projection {
            root,
            root_sort: ty_to_expr_sort_enriched(tcx, body.local_decls[extraction.root].ty),
            path: extraction.steps.clone(),
        }
    } else if let Some(name) = payload_name {
        FinalPinTarget::Local(name)
    } else if let Some(root) = root_name {
        FinalPinTarget::Projection {
            root,
            root_sort: ty_to_expr_sort_enriched(tcx, body.local_decls[extraction.root].ty),
            path: extraction.steps.clone(),
        }
    } else {
        return Err(DisarmReason::NoAddressableSymbol);
    };

    Ok(ProjectedFinalPin {
        target,
        value: death_value,
        provenance: format!(
            "bb{}/stmt{}#_{}",
            extraction.block.as_u32(),
            death_idx,
            extraction.payload.as_u32()
        ),
    })
}

/// R3: the downcast block must be reachable ONLY through the `SwitchInt` edge
/// that selects exactly `variant_idx` of the root's discriminant.
///
/// Two routes qualify, and nothing else does.
///
/// * **A single-variant enum.** There is no `SwitchInt` at all, because there is
///   nothing to decide: `is-<Ctor>(root)` is valid, so the guard is vacuous and
///   the pin is unconditional in fact as well as in form.
/// * **An explicit or `otherwise` edge that denotes exactly this variant.** The
///   `otherwise` case is admitted only when every OTHER variant's discriminant
///   is listed among the switch's explicit targets — then "otherwise" IS this
///   constructor, provably. `Option` lowers as `[0: None, otherwise: Some]`, so
///   refusing `otherwise` outright would refuse the primary target shape; but
///   admitting it blindly on a 3-variant enum would make the guard cover two
///   constructors and the pin would assert the arm's death value on a path the
///   arm never ran. The discriminant VALUES (not variant indices) are used, so
///   enums with explicit discriminants are handled exactly.
fn prove_variant_guard<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    extraction: &Extraction,
    variant_idx: u32,
) -> Result<(), DisarmReason> {
    let root_ty = body.local_decls[extraction.root].ty;
    let rustc_middle::ty::TyKind::Adt(adt_def, _) = root_ty.kind() else {
        return Err(DisarmReason::VariantGuardNotProvable);
    };
    if !adt_def.is_enum() {
        return Err(DisarmReason::VariantGuardNotProvable);
    }
    if adt_def.variants().len() == 1 {
        // Nothing to decide; the tester is valid.
        return Ok(());
    }
    let want_discriminant = adt_def
        .discriminants(tcx)
        .find(|(candidate, _)| candidate.as_u32() == variant_idx)
        .map(|(_, discr)| discr.val)
        .ok_or(DisarmReason::VariantGuardNotProvable)?;

    // Walk back to the `SwitchInt`. rustc does not put the downcast in the
    // switch's immediate target: a match arm reaches it through a `FalseEdge`
    // (borrowck's imaginary edge) and possibly a `Goto`. Each hop must be the
    // ONLY way into the block it leaves, must be the REAL edge, and must carry
    // no statement touching the shape — otherwise something we do not model
    // runs between the test and the downcast.
    let predecessors = body.basic_blocks.predecessors();
    let mut entry = extraction.block;
    let mut switch_block = None;
    for _ in 0..MAX_GUARD_CHAIN_HOPS {
        let [pred] = predecessors[entry].as_slice() else {
            return Err(DisarmReason::VariantGuardNotProvable);
        };
        let pred = *pred;
        let Some(terminator) = &body.basic_blocks[pred].terminator else {
            return Err(DisarmReason::VariantGuardNotProvable);
        };
        match &terminator.kind {
            TerminatorKind::SwitchInt { .. } => {
                switch_block = Some(pred);
                break;
            }
            TerminatorKind::Goto { target, .. } if *target == entry => {}
            TerminatorKind::FalseEdge { real_target, .. } if *real_target == entry => {}
            _ => return Err(DisarmReason::VariantGuardNotProvable),
        }
        if body.basic_blocks[pred].statements.iter().any(|statement| {
            statement_mentions_local(statement, extraction.root)
                || statement_mentions_local(statement, extraction.payload)
        }) {
            return Err(DisarmReason::VariantGuardNotProvable);
        }
        entry = pred;
    }
    let Some(switch_block) = switch_block else {
        return Err(DisarmReason::VariantGuardNotProvable);
    };
    let Some(terminator) = &body.basic_blocks[switch_block].terminator else {
        return Err(DisarmReason::VariantGuardNotProvable);
    };
    let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind else {
        return Err(DisarmReason::VariantGuardNotProvable);
    };
    // The switch must be on `discriminant(root)`, read into a local by the
    // predecessor block itself.
    let discr_local = match discr {
        Operand::Move(place) | Operand::Copy(place) if place.projection.is_empty() => place.local,
        _ => return Err(DisarmReason::VariantGuardNotProvable),
    };
    let reads_root_discriminant =
        body.basic_blocks[switch_block]
            .statements
            .iter()
            .any(|statement| {
                matches!(
                    &statement.kind,
                    StatementKind::Assign((place, Rvalue::Discriminant(source)))
                        if place.local == discr_local
                            && place.projection.is_empty()
                            && source.local == extraction.root
                            && source.projection.is_empty()
                )
            });
    if !reads_root_discriminant {
        return Err(DisarmReason::VariantGuardNotProvable);
    }
    let explicit: Vec<u128> = targets
        .iter()
        .filter(|(_, target)| *target == entry)
        .map(|(value, _)| value)
        .collect();
    let via_otherwise = targets.otherwise() == entry;
    // Two routes into the same block would make the guard a disjunction.
    if explicit.len() > 1 || (!explicit.is_empty() && via_otherwise) {
        return Err(DisarmReason::VariantGuardNotProvable);
    }
    if let Some(&value) = explicit.first() {
        if value != want_discriminant {
            return Err(DisarmReason::VariantGuardNotProvable);
        }
        return Ok(());
    }
    if !via_otherwise {
        return Err(DisarmReason::VariantGuardNotProvable);
    }
    // `otherwise` denotes exactly our constructor iff every other variant's
    // discriminant is explicitly listed and ours is not.
    let listed: HashSet<u128> = targets.iter().map(|(value, _)| value).collect();
    for (candidate, discr) in adt_def.discriminants(tcx) {
        let is_ours = candidate.as_u32() == variant_idx;
        if is_ours == listed.contains(&discr.val) {
            return Err(DisarmReason::VariantGuardNotProvable);
        }
    }
    Ok(())
}

/// R5 / R6: the payload local may appear only inside the proven region; the
/// root local may appear only at its defining call, the discriminant read, the
/// extraction, and borrowck-only markers.
///
/// The scan is a `Visitor` over the whole body rather than a hand-matched list
/// of statement and terminator shapes. That matters: a hand-matched list has a
/// default arm, and a default arm that says "not an escape" about a terminator
/// it does not recognise (`Assert`, `Yield`, `InlineAsm`, `TailCall`, ...) is
/// exactly how a borrow slips out of a tracking analysis unnoticed. Every real
/// USE is collected and then has to be justified.
fn prove_no_escape(
    body: &Body<'_>,
    extraction: &Extraction,
    death_idx: usize,
) -> Result<(), DisarmReason> {
    use rustc_middle::mir::{
        visit::{PlaceContext, Visitor},
        Location,
    };

    struct UseCollector {
        payload: Local,
        root: Local,
        payload_uses: Vec<Location>,
        root_uses: Vec<Location>,
    }

    impl<'tcx> Visitor<'tcx> for UseCollector {
        fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
            // `NonUse` covers storage markers, var-debug-info and ascriptions:
            // no read, no write, no borrow, so nothing that can invalidate a
            // death value.
            if matches!(context, PlaceContext::NonUse(_)) {
                return;
            }
            if local == self.payload {
                self.payload_uses.push(location);
            }
            if local == self.root {
                self.root_uses.push(location);
            }
        }
    }

    let mut collector = UseCollector {
        payload: extraction.payload,
        root: extraction.root,
        payload_uses: Vec::new(),
        root_uses: Vec::new(),
    };
    collector.visit_body(body);

    let in_region = |location: Location| {
        location.block == extraction.block
            && location.statement_index >= extraction.stmt_idx
            && location.statement_index <= death_idx
    };
    if !collector.payload_uses.iter().copied().all(in_region) {
        return Err(DisarmReason::LocalEscapes);
    }

    for location in collector.root_uses {
        if in_region(location) {
            // Only the extraction statement itself reads the root in-region;
            // the region walk has already refused anything else touching it.
            continue;
        }
        let block = &body.basic_blocks[location.block];
        let Some(statement) = block.statements.get(location.statement_index) else {
            // A terminator use: the ONLY admissible one is the defining call.
            let is_defining_call = matches!(
                &block.terminator().kind,
                TerminatorKind::Call { destination, .. }
                    if destination.local == extraction.root
                        && destination.projection.is_empty()
            );
            if is_defining_call {
                continue;
            }
            return Err(DisarmReason::LocalEscapes);
        };
        // Reads that cannot change the pointee: the discriminant feeding the
        // guard's switch, and the borrowck-only markers.
        let harmless = match &statement.kind {
            StatementKind::Assign((place, Rvalue::Discriminant(source))) => {
                place.projection.is_empty() && source.local == extraction.root
            }
            _ => !statement_mentions_local(statement, extraction.root),
        };
        if !harmless {
            return Err(DisarmReason::LocalEscapes);
        }
    }
    Ok(())
}

fn rvalue_mentions(rvalue: &Rvalue<'_>, local: Local) -> bool {
    let mut found = false;
    let mut visit_place = |place: &Place<'_>| {
        if place.local == local {
            found = true;
        }
    };
    match rvalue {
        Rvalue::Use(operand, _)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Repeat(operand, _) => {
            if operand_mentions(operand, local) {
                found = true;
            }
        }
        Rvalue::BinaryOp(_, (left, right)) => {
            if operand_mentions(left, local) || operand_mentions(right, local) {
                found = true;
            }
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place) => visit_place(place),
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                if operand_mentions(operand, local) {
                    found = true;
                }
            }
        }
        _ => {
            // Unknown rvalue shapes are treated as MENTIONING the local: the
            // escape check must never say "safe" about something it cannot read.
            found = true;
        }
    }
    found
}

fn operand_mentions(operand: &Operand<'_>, local: Local) -> bool {
    match operand {
        Operand::Move(place) | Operand::Copy(place) => place.local == local,
        Operand::Constant(_) => false,
        // Fail-closed: an operand shape this lane does not model is assumed to
        // mention the local, so the escape check can never say "safe" about
        // something it cannot read.
        _ => true,
    }
}

/// Whether a statement outside the proven region could reach `local`'s
/// referent.
///
/// Borrowck-only markers (`FakeRead`, `PlaceMention`, `AscribeUserType`,
/// coverage/counters) and storage markers carry no runtime effect on the
/// pointee: they neither write through the borrow nor create a new one, so they
/// cannot invalidate a death value. Everything else this lane does not model is
/// assumed to mention the local — the escape check must never say "safe" about
/// something it cannot read.
fn statement_mentions_local(statement: &rustc_middle::mir::Statement<'_>, local: Local) -> bool {
    match &statement.kind {
        StatementKind::SetDiscriminant { place, .. } => place.local == local,
        StatementKind::Nop
        | StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::FakeRead(..)
        | StatementKind::PlaceMention(_)
        | StatementKind::AscribeUserType(..)
        | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter
        | StatementKind::BackwardIncompatibleDropHint { .. } => false,
        // Anything we do not model is assumed to mention it (fail-closed).
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disarm_reason_names_are_stable() {
        // The emit/disarm table is quoted in the campaign log; these names are
        // part of the contract with that table.
        assert_eq!(
            DisarmReason::VariantGuardNotProvable.as_str(),
            "variant_guard_not_provable"
        );
        assert_eq!(DisarmReason::RootUnnamed.as_str(), "root_unnamed");
        assert_eq!(DisarmReason::NoTrackedWrite.as_str(), "no_tracked_write");
        assert_eq!(
            DisarmReason::ReferentNotFinal.as_str(),
            "referent_not_final"
        );
    }

    #[test]
    fn empty_report_emits_nothing() {
        let report = ProjectedExpiryReport::default();
        assert!(report.is_empty());
        assert!(report.pins.is_empty());
        assert!(report.disarms.is_empty());
    }

    /// ★PIN (#prophecy-slots M5): only the two one-step payload projections are
    /// addressable. Anything deeper (a second field, an index, a deref) is a
    /// fresh aliasing question the death proof does not answer, so it must not
    /// produce a pin path at all.
    #[test]
    fn operand_mentions_ignores_constants_only() {
        let local = Local::from_u32(3);
        let place = Place {
            local,
            projection: rustc_middle::ty::List::empty(),
        };
        assert!(operand_mentions(&Operand::Move(place), local));
        assert!(operand_mentions(&Operand::Copy(place), local));
        assert!(!operand_mentions(&Operand::Move(place), Local::from_u32(4)));
    }
}
