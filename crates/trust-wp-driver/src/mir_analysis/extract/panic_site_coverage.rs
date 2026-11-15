// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Panic sites of a body that no obligation lane is trusted to discharge.
//!
//! A function-level `verified` claims that no execution of the body panics.
//! The extractors state obligations for machine-integer arithmetic asserts
//! and index bounds checks (`is_charged_assert`, every reachable one of
//! which extraction's structural coverage check requires a kept lane to have
//! charged), operator-trait calls on integers, and the preconditions of
//! callees with a checked (user or trait) spec; they do NOT discharge any
//! other panic site:
//! - every other `Assert` kind;
//! - diverging calls (`panic!`/`assert!` arms, `unreachable!`, `abort`,
//!   `exit`, `-> !` callees) that some path reaches without crossing a switch
//!   edge the primary walk proved dead (below);
//! - every other call: a std/extern spec states no panic precondition the
//!   callee's body is checked against (`Vec::remove`, `Iterator::sum`), and an
//!   indirect call through a fn pointer or vtable has no known target. A call
//!   into a local body that carries a contract is one of these unless that
//!   body is itself clean ([`unchecked_panic_sites`]);
//! - `Drop` of a value with drop glue: it runs `Drop` impls no lane examines.
//!
//! A clause-free body whose only checked obligations are those lanes must
//! therefore never be reported `verified` while such a site is reachable.
//!
//! "Reachable" is read on the CFG less the switch edges the primary walk
//! proved dead for this verdict (D-142): on every path from the entry to the
//! switch, an arm whose unreachability the switch lane charged as a kept
//! obligation, or an edge a value-stable literal discriminant never selects.
//! A site only such an edge leads to never runs while the verdict holds, so
//! the charge that proves the edge dead is the same obligation that lifts the
//! site out of the cap. A charge is proved from the verdict's premises, so the
//! edges count only while no premise is a program-point fact the walk does
//! not scope to its path and no two values share one symbol (D-143:
//! [`record_opaque_binding`], `partial_verdict::dead_edges_the_proof_owns`),
//! and only in a body that computes with nothing the encoder reads inexactly
//! (D-147, D-149: [`computes_inexactly`]).

use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap, HashSet},
};

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{BasicBlock, Body, Operand, TerminatorKind, START_BLOCK},
    ty::{ClosureKind, GenericArgs, TyCtxt, TyKind},
};
use trust_wp_driver::StdSpec;

use super::{
    super::call_resolve::extract_closure_def_id_from_fn_call,
    assertion::{is_charged_assert, is_integer_operator_call},
    call_resolve_util::resolve_unique_call_fn_def,
    call_spec::entered_body_def_id,
    helpers::is_panic_entry_point,
    loop_body::primary_arithmetic_is_exact,
};

/// Switch edges `(switch block, arm entry)` of ONE body that its primary walk
/// proved are never taken, as obligations of the verdict they are read beside
/// (D-142). Empty unless [`with_dead_edge_recording`] proved one.
#[derive(Debug, Default)]
pub(crate) struct ProvedDeadEdges {
    /// The body whose walk proved the edges; block ids mean nothing elsewhere.
    body: Option<DefId>,
    edges: HashSet<(BasicBlock, BasicBlock)>,
}

impl ProvedDeadEdges {
    /// Whether no edge was proved dead.
    pub(crate) fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }

    /// Whether the edge `from -> to` of `body` is proved never taken.
    fn cuts(&self, body: &Body<'_>, from: BasicBlock, to: BasicBlock) -> bool {
        body.source.promoted.is_none()
            && self.body == Some(body.source.def_id())
            && self.edges.contains(&(from, to))
    }
}

/// One switch edge as the primary walk crossed it.
struct EdgeRecord {
    /// Whether EVERY crossing proved the edge dead. One crossing without a
    /// proof clears it for good, so a proof stated on one path never covers
    /// another.
    proved: bool,
    /// The block set of each walked path the edge was crossed on (see
    /// [`walked_path`]).
    paths: HashSet<Vec<BasicBlock>>,
}

type EdgeRecords = HashMap<(BasicBlock, BasicBlock), EdgeRecord>;

/// What the primary walk of one body recorded.
struct Recording {
    body: DefId,
    edges: EdgeRecords,
    /// The walk bound a local to the symbol of its source name because its
    /// right-hand side has no translation. That symbol is shared by every such
    /// binding of the name and by a parameter spelled the same, so a guard the
    /// walk read off one value is a fact about another
    /// (clause_free_panic_arm_guard_on_opaque_rebinding.rs).
    opaque_binding: bool,
}

thread_local! {
    /// The switch edges of the body being recorded. Active only inside
    /// [`with_dead_edge_recording`].
    static DEAD_EDGE_RECORDER: RefCell<Option<Recording>> = const { RefCell::new(None) };
}

/// Restores the enclosing recorder even when the walk unwinds, so a recorder
/// is never left active for a walk nobody reads.
struct RecorderGuard {
    previous: Option<Option<Recording>>,
}

impl Drop for RecorderGuard {
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            DEAD_EDGE_RECORDER.with(|rec| rec.replace(previous));
        }
    }
}

/// Run the primary extraction `f` of `body`, returning the switch edges it
/// proved dead.
///
/// An edge `switch -> target` is proved dead when (a) the primary walk's
/// values are exact (`primary_arithmetic_is_exact`: no CFG cycle, no write
/// through a borrow or a projection) — there, and only there, the primary walk
/// is the one lane that states a switch's arm obligations and every one it
/// states is kept in the verdict's goals; (b) every crossing of the edge proved
/// it not taken on that crossing's path ([`record_switch_edge`]); and (c) the
/// walk crossed it on EVERY path from the entry to the switch. (c) is what a
/// walk that gave up on one path cannot fake: a path it abandoned, or an arm a
/// lane skipped, is a path to the switch with no proof on it, and the proof
/// stated on another path's condition says nothing about it. (d) The walk
/// bound no local to a shared opaque symbol ([`record_opaque_binding`]).
/// (e) The body computes with nothing the encoder reads inexactly
/// ([`computes_inexactly`]).
pub(crate) fn with_dead_edge_recording<'tcx, R>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    f: impl FnOnce() -> R,
) -> (R, ProvedDeadEdges) {
    let def_id = body.source.def_id();
    let mut guard = RecorderGuard {
        previous: Some(DEAD_EDGE_RECORDER.with(|rec| {
            rec.replace(Some(Recording {
                body: def_id,
                edges: HashMap::new(),
                opaque_binding: false,
            }))
        })),
    };
    let value = f();
    let previous = guard.previous.take().unwrap_or(None);
    let Some(recorded) = DEAD_EDGE_RECORDER.with(|rec| rec.replace(previous)) else {
        return (value, ProvedDeadEdges::default());
    };
    let trace = std::env::var_os("TRUST_WP_AUTHORITY_TRACE").is_some();
    if recorded.opaque_binding && trace && !recorded.edges.is_empty() {
        eprintln!(
            "[TWP_AUTH] switch edges of {def_id:?}: none dead, an opaque binding shares a symbol"
        );
    }
    if recorded.opaque_binding
        || body.source.promoted.is_some()
        || !primary_arithmetic_is_exact(tcx, body)
        || computes_inexactly(tcx, body)
    {
        return (value, ProvedDeadEdges::default());
    }
    let paths = RuntimePaths::new(body);
    let edges: HashSet<(BasicBlock, BasicBlock)> = recorded
        .edges
        .into_iter()
        .filter(|((switch, target), record)| {
            let dead = record.proved && paths.all_walked(*switch, &record.paths);
            if trace {
                eprintln!(
                    "[TWP_AUTH] switch edge {switch:?}->{target:?} of {def_id:?}: proved={} \
                     walked_paths={} dead={dead}",
                    record.proved,
                    record.paths.len(),
                );
            }
            dead
        })
        .map(|(edge, _)| edge)
        .collect();
    let body = (!edges.is_empty()).then_some(def_id);
    (value, ProvedDeadEdges { body, edges })
}

/// The block set of the path a walk took to a switch of `body` (`visited`, as
/// the walker threads it), or `None` when no recorder is active for `body`.
pub(super) fn walked_path(
    body: &Body<'_>,
    visited: &HashSet<BasicBlock>,
) -> Option<Vec<BasicBlock>> {
    if body.source.promoted.is_some() {
        return None;
    }
    let def_id = body.source.def_id();
    let active = DEAD_EDGE_RECORDER.with(|rec| {
        rec.borrow()
            .as_ref()
            .is_some_and(|recording| recording.body == def_id)
    });
    active.then(|| {
        let mut path: Vec<BasicBlock> = visited.iter().copied().collect();
        path.sort();
        path
    })
}

/// Record that a walk along `walked` ([`walked_path`]) crossed the switch edge
/// `switch -> target` of `body`, and whether it proved the edge dead: it
/// stated, as a kept obligation, that the edge is not taken on this path, or
/// the discriminant is a value-stable literal that never selects it. Only the
/// switch handlers call this, and they pass `proved` only for a value-stable
/// discriminant.
pub(super) fn record_switch_edge(
    body: &Body<'_>,
    switch: BasicBlock,
    target: BasicBlock,
    proved: bool,
    walked: Option<&Vec<BasicBlock>>,
) {
    let Some(walked) = walked else {
        return;
    };
    let def_id = body.source.def_id();
    DEAD_EDGE_RECORDER.with(|rec| {
        let mut rec = rec.borrow_mut();
        let Some(recording) = rec.as_mut() else {
            return;
        };
        if recording.body != def_id {
            return;
        }
        let record = recording
            .edges
            .entry((switch, target))
            .or_insert_with(|| EdgeRecord {
                proved: true,
                paths: HashSet::new(),
            });
        record.proved &= proved;
        record.paths.insert(walked.clone());
    });
}

/// Record that a walk bound a local to the opaque symbol of its source name
/// (see [`Recording::opaque_binding`]): no edge of the body being recorded is
/// then proved dead. A body the walk entered on the way (a closure's) binds
/// into the same formula, so its binding counts too.
pub(super) fn record_opaque_binding() {
    DEAD_EDGE_RECORDER.with(|rec| {
        if let Some(recording) = rec.borrow_mut().as_mut() {
            recording.opaque_binding = true;
        }
    });
}

/// Whether `body` computes with a float, a 128-bit integer, an integer
/// complement or a shift.
///
/// A charge is only as good as the translation of its guard, and the encoder
/// reads these inexactly: a float as a real number (no NaN, no rounding), a
/// bit operation at 64 bits whatever the type (`!x` on a `u8`; `&`, `|`, `^`
/// or a bit count on a `u128`), and a shift without dropping the bits it
/// moves out of the type. A charge over such a value can be proved where Rust
/// takes the arm (clause_free_u8_bitnot_assert_read_at_64_bits.rs,
/// clause_free_u128_bitand_read_at_64_bits.rs,
/// clause_free_f64_eq_assert_despite_nan.rs). A contracted body verifies the
/// same wrong goal (u8_bitnot_read_at_64_bits.rs,
/// u128_bitand_read_at_64_bits.rs); this keeps D-142 from widening it to
/// clause-free bodies (D-147, D-149). The test is by the body, not by the
/// charge: a value read inexactly reaches a charge through any binding. A
/// 128-bit value is refused whole, because its bit operation can be a
/// credited call (`trailing_zeros`) as well as an operator
/// (clause_free_u128_trailing_zeros_read_at_64_bits.rs). `!` on a `bool` is
/// read exactly.
fn computes_inexactly<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    use rustc_middle::{
        mir::{
            visit::{PlaceContext, Visitor},
            BinOp, ConstOperand, Location, Place, Rvalue, UnOp,
        },
        ty::{IntTy, Ty, UintTy},
    };
    fn read_inexactly(ty: Ty<'_>) -> bool {
        ty.is_floating_point()
            || matches!(
                ty.kind(),
                TyKind::Int(IntTy::I128) | TyKind::Uint(UintTy::U128)
            )
    }
    struct Scan<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for Scan<'_, 'tcx> {
        // A place read through a projection (`p.0`, `*r`, `a[0]`) has the
        // type its base local does not.
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            self.found |= read_inexactly(place.ty(self.body, self.tcx).ty);
            self.super_place(place, context, location);
        }
        fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
            self.found |= read_inexactly(constant.ty());
            self.super_const_operand(constant, location);
        }
        fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
            self.found |= match rvalue {
                Rvalue::BinaryOp(
                    BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked,
                    _,
                ) => true,
                Rvalue::UnaryOp(UnOp::Not, operand) => !operand.ty(self.body, self.tcx).is_bool(),
                _ => read_inexactly(rvalue.ty(self.body, self.tcx)),
            };
            self.super_rvalue(rvalue, location);
        }
    }
    let mut scan = Scan {
        tcx,
        body,
        found: body.local_decls.iter().any(|decl| read_inexactly(decl.ty)),
    };
    scan.visit_body(body);
    scan.found
}

/// The paths an execution of a loop-free body can take from its entry.
///
/// An execution leaves a block only along a non-cleanup successor, and a
/// `FalseEdge`/`FalseUnwind` only along its real target: the imaginary edge
/// exists for borrowck and is never taken. A path is identified by its block
/// set, which in an acyclic CFG orders into exactly one path.
struct RuntimePaths {
    successors: HashMap<BasicBlock, Vec<BasicBlock>>,
    /// Position in reverse postorder, a topological order of the DAG.
    position: HashMap<BasicBlock, usize>,
    /// Number of distinct paths from the entry, saturating.
    count: HashMap<BasicBlock, u64>,
}

impl RuntimePaths {
    fn new(body: &Body<'_>) -> Self {
        let order = body.basic_blocks.reverse_postorder();
        let mut successors = HashMap::new();
        let mut position = HashMap::new();
        let mut count: HashMap<BasicBlock, u64> = HashMap::new();
        count.insert(START_BLOCK, 1);
        for (index, &bb) in order.iter().enumerate() {
            position.insert(bb, index);
            let data = &body.basic_blocks[bb];
            let mut next: Vec<BasicBlock> = match &data.terminator().kind {
                TerminatorKind::FalseEdge { real_target, .. }
                | TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
                kind => kind.successors().collect(),
            };
            next.retain(|succ| !body.basic_blocks[*succ].is_cleanup);
            next.sort();
            next.dedup();
            let here = if data.is_cleanup {
                0
            } else {
                count.get(&bb).copied().unwrap_or(0)
            };
            for &succ in &next {
                let entry = count.entry(succ).or_insert(0);
                *entry = entry.saturating_add(here);
            }
            successors.insert(bb, next);
        }
        Self {
            successors,
            position,
            count,
        }
    }

    /// Whether `walked` holds every path from the entry to `switch`. Each set
    /// that orders into a real path names a distinct one; any other set (a
    /// lane that consumed a block without entering it) names none, so it can
    /// only make the count fall short.
    fn all_walked(&self, switch: BasicBlock, walked: &HashSet<Vec<BasicBlock>>) -> bool {
        let Some(&total) = self.count.get(&switch) else {
            return false;
        };
        let real = walked
            .iter()
            .filter(|path| self.is_path_to(switch, path))
            .count() as u64;
        total > 0 && total != u64::MAX && real == total
    }

    fn is_path_to(&self, switch: BasicBlock, blocks: &[BasicBlock]) -> bool {
        let mut ordered: Vec<(usize, BasicBlock)> = Vec::with_capacity(blocks.len());
        for &bb in blocks {
            let Some(&index) = self.position.get(&bb) else {
                return false;
            };
            ordered.push((index, bb));
        }
        ordered.sort();
        ordered.first().map(|(_, bb)| *bb) == Some(START_BLOCK)
            && ordered.last().map(|(_, bb)| *bb) == Some(switch)
            && ordered.windows(2).all(|pair| {
                self.successors
                    .get(&pair[0].1)
                    .is_some_and(|next| next.contains(&pair[1].1))
            })
    }
}

/// Core inherent methods of the primitive integer types whose documented
/// semantics are total: they return a value for every input and never panic
/// (no `# Panics` section; their bodies are intrinsics with no MIR `Assert`,
/// independent of `overflow-checks`). `wrapping_div`/`saturating_div`/`pow`/
/// `div_euclid` and friends can panic and are deliberately absent.
const TOTAL_INTEGER_METHODS: &[&str] = &[
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "wrapping_neg",
    "wrapping_shl",
    "wrapping_shr",
    "saturating_add",
    "saturating_sub",
    "saturating_mul",
    "overflowing_add",
    "overflowing_sub",
    "overflowing_mul",
    "checked_add",
    "checked_sub",
    "checked_mul",
    "checked_div",
    "checked_rem",
    "checked_neg",
    "abs_diff",
    "count_ones",
    "count_zeros",
    "leading_zeros",
    "trailing_zeros",
];

/// Core inherent methods of the slice type `[T]` that are total: they read
/// the length out of the fat pointer's metadata and never panic. `len` is the
/// upper bound of every checked index (`if i < v.len() { v[i] }`), so without
/// it a clause-free body whose bounds goal is discharged would still be capped.
const TOTAL_SLICE_METHODS: &[&str] = &["len", "is_empty"];

fn is_total_integer_inherent_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    core_inherent_method_self_ty(tcx, def_id, TOTAL_INTEGER_METHODS)
        .is_some_and(|kind| matches!(kind, TyKind::Int(_) | TyKind::Uint(_)))
}

fn is_total_slice_inherent_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    core_inherent_method_self_ty(tcx, def_id, TOTAL_SLICE_METHODS)
        .is_some_and(|kind| matches!(kind, TyKind::Slice(_)))
}

/// The self type of `def_id` when it is a `core` inherent (not trait) method
/// named in `names`; classification by `DefId` provenance, never by a path.
fn core_inherent_method_self_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    names: &[&str],
) -> Option<TyKind<'tcx>> {
    if tcx.crate_name(def_id.krate).as_str() != "core"
        || !names.contains(&tcx.item_name(def_id).as_str())
    {
        return None;
    }
    let impl_id = tcx.impl_of_assoc(def_id)?;
    if tcx.trait_of_assoc(def_id).is_some()
        || !matches!(
            tcx.def_kind(impl_id),
            rustc_hir::def::DefKind::Impl { of_trait: false }
        )
    {
        return None;
    }
    Some(
        *tcx.type_of(impl_id)
            .instantiate_identity()
            .skip_norm_wip()
            .kind(),
    )
}

/// The local closure whose body a `Fn::call` / `FnOnce::call_once` site
/// enters, or `None`.
///
/// The closure is read through `extract_closure_def_id_from_fn_call`, the
/// resolver the call lane uses to charge the closure's OWN `requires` at this
/// site in place of the generic `precondition(args)`. Crediting a site that
/// resolver does not reach would account a body whose precondition nobody
/// owes here. The closure's capture type invariants are not owed at a call
/// site at all: they are charged once, where the closure is built (D-76).
///
/// That is why a `FnMut::call_mut` site resolves to nothing. The body is
/// granted `inv(capture)` at EVERY entry, an `FnMut` body can break a captured
/// invariant before it returns, and from the second call on nobody owes that
/// premise (D-77), so the body's own verdict does not answer for its panic
/// paths at a re-entry (D-104).
///
/// `FnOnce::call_once` on a closure whose kind is `Fn` or `FnMut` does not
/// enter the body alone: the once-shim drops the closure after the body
/// returns, and that drop glue belongs to neither body, so such a site
/// resolves to nothing as well.
fn fn_trait_call_local_closure<'tcx>(
    func: &Operand<'tcx>,
    called_as: ClosureKind,
    generic_args: GenericArgs<'tcx>,
) -> Option<DefId> {
    let closure_def_id = extract_closure_def_id_from_fn_call(func)?;
    let self_ty = generic_args.first()?.as_type()?;
    let TyKind::Closure(self_def_id, closure_args) = self_ty.kind() else {
        return None;
    };
    if *self_def_id != closure_def_id || !closure_def_id.is_local() {
        return None;
    }
    let entered = match called_as {
        ClosureKind::Fn => true,
        ClosureKind::FnMut => false,
        ClosureKind::FnOnce => closure_args.as_closure().kind() == ClosureKind::FnOnce,
    };
    entered.then_some(closure_def_id)
}

/// What the account may read of a body a credited call enters.
pub(crate) enum EnteredBody<'tcx> {
    /// The borrow-checked MIR its own lane verifies.
    Mir(std::sync::Arc<crate::callbacks::thread_locals::RetainedBorrowckBody<'tcx>>),
    /// A `#[trusted]` item. No lane reads its body; its contract is an
    /// assumption the run reports as trusted, and the credit rests on that
    /// assumption as it did before D-104 — reading the body would neither make
    /// the assumption sound nor check the arithmetic in it.
    Trusted,
}

/// The walk behind [`unchecked_panic_sites`], with the entered bodies it has
/// already decided.
struct PanicAccount<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    user_specs: &'a HashMap<DefId, StdSpec>,
    trait_specs: &'a HashMap<DefId, StdSpec>,
    bodies: &'a dyn Fn(LocalDefId) -> Option<EnteredBody<'tcx>>,
    /// Whether every body reachable from an entered body is free of unchecked
    /// panic sites. An answer is recorded only once the WHOLE reachable set
    /// was read, never while a body in it is still being walked, so a
    /// recursive cycle cannot record a guess.
    clean: HashMap<DefId, bool>,
}

/// The panic sites of ONE body, without looking into the bodies it calls.
struct DirectSites {
    /// Sites no lane discharges, whatever any callee's body says.
    unchecked: BTreeSet<String>,
    /// Calls into a spec-bearing local body, each with the label it carries
    /// when that body is not clean.
    entered: Vec<(DefId, String)>,
}

impl<'tcx> PanicAccount<'_, 'tcx> {
    /// The local body a call enters, when the call lane charges a contract at
    /// this site, or `None`.
    ///
    /// The charge is read off the tables exactly where the call lane reads it:
    /// a `Fn*` call into a local closure owes that closure's own spec
    /// (`resolve_effective_spec`), every other call owes the spec of the callee
    /// it NAMES (`lookup_user_or_trait_spec`). The body is read separately —
    /// the closure through [`fn_trait_call_local_closure`], anything else
    /// through `entered_body_def_id`, the resolver the invariant charge asks
    /// which body runs — so a trait method call enters the impl or default
    /// body its instance resolves to and a generic one enters nothing. A body
    /// with a contract the call lane does not charge here (an impl method more
    /// demanding than an uncontracted declaration) is not credited: its own
    /// `requires` is what its lane assumed, and nobody owes it at this site.
    fn charged_entered_body(
        &self,
        body: &Body<'tcx>,
        func: &Operand<'tcx>,
        callee: DefId,
        generic_args: GenericArgs<'tcx>,
    ) -> Option<DefId> {
        let fn_trait = self
            .tcx
            .trait_of_assoc(callee)
            .and_then(|trait_id| self.tcx.fn_trait_kind_from_def_id(trait_id));
        let entered = match fn_trait {
            Some(called_as) => fn_trait_call_local_closure(func, called_as, generic_args)
                .filter(|closure| self.user_specs.contains_key(closure))?,
            // Resolved only once the charge is known, so an uncharged call
            // (every std call) never reaches instance resolution.
            None if self.user_specs.contains_key(&callee)
                || self.trait_specs.contains_key(&callee) =>
            {
                entered_body_def_id(self.tcx, body, func, callee)?
            }
            None => return None,
        };
        entered.is_local().then_some(entered)
    }

    /// `dead_edges` are switch edges proved never taken for the verdict this
    /// account caps; nothing is crossed through one. An entered body is read
    /// with none: its proofs belong to its own verdict, not this one.
    fn direct_sites(&self, body: &Body<'tcx>, dead_edges: &ProvedDeadEdges) -> DirectSites {
        let tcx = self.tcx;
        let typing_env = body.typing_env(tcx);
        let mut sites = DirectSites {
            unchecked: BTreeSet::new(),
            entered: Vec::new(),
        };
        let mut seen: HashSet<BasicBlock> = HashSet::new();
        let mut stack = vec![START_BLOCK];
        while let Some(bb) = stack.pop() {
            if !seen.insert(bb) {
                continue;
            }
            let bb_data = &body.basic_blocks[bb];
            if bb_data.is_cleanup {
                continue;
            }
            let terminator = bb_data.terminator();
            match &terminator.kind {
                TerminatorKind::Assert { msg, .. } if !is_charged_assert(msg) => {
                    sites.unchecked.insert("runtime check".to_string());
                }
                TerminatorKind::Call { func, target, .. } => {
                    match resolve_unique_call_fn_def(body, func) {
                        Some((def_id, _)) if is_panic_entry_point(tcx, def_id) => {
                            sites.unchecked.insert("panic call".to_string());
                        }
                        _ if target.is_none() => {
                            sites.unchecked.insert("diverging call".to_string());
                        }
                        Some((def_id, generic_args))
                            if !is_integer_operator_call(tcx, def_id, generic_args)
                                && !is_total_integer_inherent_method(tcx, def_id)
                                && !is_total_slice_inherent_method(tcx, def_id) =>
                        {
                            let label = format!("call to {}", tcx.def_path_str(def_id));
                            match self.charged_entered_body(body, func, def_id, generic_args) {
                                Some(entered) => sites.entered.push((
                                    entered,
                                    format!(
                                        "{label} (unchecked panic paths in {})",
                                        tcx.def_path_str(entered)
                                    ),
                                )),
                                None => {
                                    sites.unchecked.insert(label);
                                }
                            }
                        }
                        Some(_) => {}
                        None => {
                            sites.unchecked.insert("indirect call".to_string());
                        }
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    let ty = place.ty(&body.local_decls, tcx).ty;
                    if ty.needs_drop(tcx, typing_env) {
                        sites.unchecked.insert(format!("drop of {ty}"));
                    }
                }
                TerminatorKind::TailCall { .. } => {
                    sites.unchecked.insert("tail call".to_string());
                }
                TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => {
                    sites.unchecked.insert("unmodelled terminator".to_string());
                }
                _ => {}
            }
            for successor in terminator.successors() {
                if !body.basic_blocks[successor].is_cleanup && !dead_edges.cuts(body, bb, successor)
                {
                    stack.push(successor);
                }
            }
        }
        sites
    }

    /// Whether no body reachable from `entered` through spec-bearing calls has
    /// an unchecked panic site. A body whose MIR is not available is not clean;
    /// a `#[trusted]` one is not read.
    fn enters_clean_body(&mut self, entered: DefId) -> bool {
        if let Some(&known) = self.clean.get(&entered) {
            return known;
        }
        let mut reached: HashSet<DefId> = HashSet::new();
        let mut pending = vec![entered];
        let mut clean = true;
        while let Some(next) = pending.pop() {
            if !reached.insert(next) || self.clean.get(&next) == Some(&true) {
                continue;
            }
            let body = match next.as_local().and_then(|local| (self.bodies)(local)) {
                Some(EnteredBody::Mir(body)) => body,
                Some(EnteredBody::Trusted) => continue,
                None => {
                    clean = false;
                    break;
                }
            };
            let sites = self.direct_sites(&body.body, &ProvedDeadEdges::default());
            if !sites.unchecked.is_empty()
                || sites
                    .entered
                    .iter()
                    .any(|(callee, _)| self.clean.get(callee) == Some(&false))
            {
                clean = false;
                break;
            }
            pending.extend(sites.entered.into_iter().map(|(callee, _)| callee));
        }
        if clean {
            // Every body reached is clean for the same reason: its own
            // reachable set is a subset of the one just read.
            for body in reached {
                self.clean.insert(body, true);
            }
        } else {
            self.clean.insert(entered, false);
        }
        clean
    }
}

/// Labels of the panic sites reachable from the entry of `body` (unwind
/// cleanup excluded) that no obligation lane discharges. Empty only when every
/// reachable panic site is a charged assert (arithmetic or bounds), an integer
/// operator-trait call, a total core integer or slice method, or a call into a clean
/// spec-bearing local body, and no reachable `Drop` runs drop glue.
///
/// A call into a local body that carries a contract (its own, or the trait
/// contract it implements) is accounted only when that body is CLEAN: it and
/// every spec-bearing body it enters in turn have no unchecked panic site of
/// their own. Its contract does not answer for the rest. A spec-bearing body
/// is never capped by `cap_clause_free_verdict`, and its lane trusts every std
/// spec that states no panic precondition, so its `verified` says nothing
/// about a `Vec::with_capacity(usize::MAX)` inside it; the caller's clause-free
/// `verified` would inherit that weaker standard
/// (`closure_spec_call_unchecked_std_call_credited.rs`,
/// `local_spec_callee_unchecked_std_call_credited.rs`). What IS accounted in
/// the entered body — its arithmetic and its own callees' preconditions — is
/// discharged by that body's own lane, which is why it must be a verification
/// target at all. A call into a contract-free body stays unaccounted
/// (`closure_contract_free_unchecked_std_call_unaccounted.rs`).
///
/// `bodies` answers, for an entered local item, the borrow-checked MIR every
/// verification lane reads, or that the item is `#[trusted]`. `dead_edges` are
/// the switch edges of `body` its own extraction proved never taken, as goals
/// of the verdict being capped ([`with_dead_edge_recording`]).
pub(crate) fn unchecked_panic_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    bodies: &dyn Fn(LocalDefId) -> Option<EnteredBody<'tcx>>,
    dead_edges: &ProvedDeadEdges,
) -> Vec<String> {
    let mut account = PanicAccount {
        tcx,
        user_specs,
        trait_specs,
        bodies,
        clean: HashMap::new(),
    };
    let DirectSites {
        mut unchecked,
        entered,
    } = account.direct_sites(body, dead_edges);
    for (callee, label) in entered {
        if !account.enters_clean_body(callee) {
            unchecked.insert(label);
        }
    }
    unchecked.into_iter().collect()
}
