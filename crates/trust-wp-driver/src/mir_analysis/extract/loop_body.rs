// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop body extraction support — call obligation collection and recursive call
//! argument extraction.
//!
//! This module handles two independent MIR analyses for loop verification:
//!
//! 1. **Call obligation collection** ([`collect_loop_body_call_obligations`]):
//!    Walks loop body blocks to find function calls and collect their
//!    precondition obligations, wrapped with path condition guards.
//!
//! 2. **Recursive call extraction** ([`extract_recursive_call_args`]):
//!    Walks the full CFG to find self-recursive calls and extract their
//!    arguments for variant decrease verification.
//!
//! Both analyses have their own CFG walkers and are independent from the
//! main `extract_from_block_with_context` extraction path.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        call_resolve::{arg_names_for_def_id, resolve_trait_method_def_id, ufcs_path_for_call},
        effects::{fail_closed_marker, CallEffects},
        loops::LoopAnalysis,
        spec_apply::{
            apply_postconditions_with_effects, collect_precondition_obligations, TranslatedArg,
        },
        translate::{translate_operand, translate_typed_field_place, ty_to_expr_sort_enriched},
    },
    assertion::{arithmetic_panic_obligation, machine_int_range_fact, operator_call_obligation},
    call_args::call_result_symbol,
    helpers::{
        block_diverges_via_panic, block_must_diverge, capture_const_body_obligations,
        switch_discr_is_value_stable, translate_rvalue_with_enum_variants,
    },
    translate_call_args_for_substitutions_with_tcx,
};

mod recursive_calls;
mod switch_conditions;

pub(crate) use recursive_calls::{extract_recursive_call_args, RecursiveCallSite};
pub(super) use switch_conditions::switch_branch_conditions;

/// Read-only context for loop body obligation collection.
///
/// Bundles the spec lookup maps and loop body block sets that are
/// threaded unchanged through every recursive call of
/// [`collect_guarded_obligations`], keeping argument counts below
/// clippy's `too_many_arguments` threshold.
pub(crate) struct LoopBodySpecContext<'a> {
    pub(crate) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(crate) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(crate) extern_specs: &'a HashMap<String, StdSpec>,
    pub(crate) body_blocks: &'a HashSet<BasicBlock>,
    /// Blocks whose assignments should force debug-name restoration.
    ///
    /// For nested loops this includes enclosing loop bodies as well as the
    /// current loop. A value assigned by an outer loop but read by an inner
    /// loop is loop-carried, so call obligations must use the symbolic debug
    /// name constrained by invariants rather than the pre-loop initializer.
    pub(crate) name_restore_blocks: Option<&'a HashSet<BasicBlock>>,
    /// `Some` switches the walk to ARITHMETIC-PANIC mode: only machine-int
    /// arithmetic panic obligations (see `arithmetic_panic_obligation`) are
    /// collected — call preconditions are left to the ordinary walk — and
    /// every loop-carried local is re-bound on loop entry so no obligation is
    /// ever stated over a stale pre-loop value.
    pub(crate) arithmetic: Option<ArithmeticWalk<'a>>,
    /// Every loop of the body. When present, the walk continues THROUGH an
    /// inner loop header (re-binding what the inner loop may write) instead of
    /// stopping at it.
    pub(crate) all_loops: Option<&'a [super::super::loops::LoopInfo]>,
    /// The `SwitchInt` block whose in-body arm establishes the loop condition
    /// the group's VC assumes (`LoopBodyExpr::condition_switch`). Obligations
    /// reached on a path that has NOT taken that arm (the loop-exit arm, code
    /// before the condition switch) are collected condition-free.
    pub(crate) condition_switch: Option<BasicBlock>,
}

/// The loop lane's obligations for one loop, split by the assumption they may
/// be checked under.
#[derive(Default)]
pub(crate) struct LoopBodyObligations {
    /// Reached only through the in-body arm of the condition switch: checked
    /// under `requires ∧ invariants ∧ condition`.
    pub(crate) obligations: Vec<PureExpr>,
    /// Reached on a path where the loop condition is NOT established (a
    /// loop-exit arm whose tail diverges, a panic arm of the condition switch,
    /// code before the condition switch): checked WITHOUT the condition.
    /// Assuming it there makes `¬cond ⇒ ob` vacuous.
    pub(crate) condition_free_obligations: Vec<PureExpr>,
    /// Blocks outside `body_blocks` (must-diverge arms) this walk processed;
    /// the flow-insensitive block-slice walker may leave their checks to the
    /// loop lane (see `call_effect_blocks::unique_predecessor_guard`).
    pub(crate) off_body_blocks: HashSet<BasicBlock>,
    /// Whether `obligations` (resp. `condition_free_obligations`) holds a
    /// fail-closed `false` this walk injected for a construct it could not
    /// model, under the path that reaches it. The marker makes the VC
    /// unprovable; a model of it reaches the construct and says nothing about
    /// the program (loop_call_obligation_after_param_store_control), so a
    /// group that holds one refutes nothing (D-27's marker, guarded).
    pub(crate) injected_fail_closed: bool,
    pub(crate) condition_free_injected_fail_closed: bool,
    /// Havoc variables the arithmetic walk bound, at the loop header, for
    /// locals no loop writes (`seed_arithmetic_walk_state`). Code before the
    /// loop fixes each one's value there and the VC states none of it, so a
    /// model picks it freely: a refutation of an obligation that reads one is
    /// no run of the program (loop_overflow_after_param_store_control).
    pub(crate) unstated_entry_values: HashSet<String>,
}

impl LoopBodyObligations {
    /// Every obligation, for lanes that assume no loop condition.
    pub(crate) fn into_all(self) -> Vec<PureExpr> {
        let mut all = self.obligations;
        all.extend(self.condition_free_obligations);
        all
    }

    fn push(&mut self, condition_established: bool, obligation: PureExpr) {
        if condition_established {
            self.obligations.push(obligation);
        } else {
            self.condition_free_obligations.push(obligation);
        }
    }

    /// Push the fail-closed marker `path ⇒ false` and record that it is one.
    /// `marker` is the `false` itself, built where the walk gave up.
    fn push_fail_closed(
        &mut self,
        condition_established: bool,
        path_conditions: &[PureExpr],
        marker: PureExpr,
    ) {
        if condition_established {
            self.injected_fail_closed = true;
        } else {
            self.condition_free_injected_fail_closed = true;
        }
        self.push(
            condition_established,
            wrap_with_guard(path_conditions, marker),
        );
    }
}

/// Configuration of an arithmetic-panic obligation walk.
#[derive(Clone, Copy)]
pub(crate) struct ArithmeticWalk<'a> {
    /// Function argument names (for parameter re-binding).
    pub(crate) arg_names: &'a [String],
    /// `true`: a loop-carried local with a UNIQUE debug name (or a parameter)
    /// is re-bound to that symbolic name — the convention loop invariants and
    /// loop-exit facts constrain. `false`: every loop-carried local is re-bound
    /// to a fresh, range-guarded havoc variable (no invariant: Creusot's
    /// implicit `invariant true`).
    pub(crate) named_loop_carried_symbolic: bool,
    /// For each loop header, the locals that loop may write. Crossing into an
    /// inner loop header during a walk re-binds those locals.
    pub(crate) loop_assigned_by_header: &'a HashMap<BasicBlock, HashSet<Local>>,
}

/// A CFG region walked for arithmetic panic obligations.
pub(crate) struct ArithmeticRegion<'a> {
    pub(crate) start: BasicBlock,
    pub(crate) region_blocks: &'a HashSet<BasicBlock>,
    /// Blocks whose writes make a local loop-carried at `start`.
    pub(crate) loop_carried_blocks: &'a HashSet<BasicBlock>,
    pub(crate) named_loop_carried_symbolic: bool,
    /// Every loop of the body. When present, a walk that reaches an inner loop
    /// header (other than `start`) continues at that inner loop's exits from a
    /// state in which everything the inner loop may write is fresh havoc, so
    /// code after an inner loop inside this region is walked. Without it that
    /// code is reached only through the inner condition block, outside the
    /// region, and no lane states its obligations.
    pub(crate) all_loops: Option<&'a [super::super::loops::LoopInfo]>,
    /// The loop-condition switch of the loop whose group assumes its
    /// condition (`None`: every obligation is condition-free).
    pub(crate) condition_switch: Option<BasicBlock>,
}

thread_local! {
    /// Charged assert sites (`is_charged_assert`: arithmetic panic asserts
    /// and index bounds checks) walked by an obligation lane whose
    /// obligations the caller keeps: `(body def_id, blocks)`. Active only
    /// inside [`with_charged_assert_recording`].
    static CHARGED_ASSERT_RECORDER: std::cell::RefCell<Option<(DefId, HashSet<BasicBlock>)>> =
        const { std::cell::RefCell::new(None) };
}

/// Run `f`, returning the charged assert blocks of `body` for which
/// an obligation was stated while `f` ran (nested recordings of other bodies
/// are kept apart; a nested recording of the same body is folded in).
pub(crate) fn with_charged_assert_recording<'tcx, R>(
    body: &Body<'tcx>,
    f: impl FnOnce() -> R,
) -> (R, HashSet<BasicBlock>) {
    let def_id = body.source.def_id();
    let previous = CHARGED_ASSERT_RECORDER.with(|rec| rec.replace(Some((def_id, HashSet::new()))));
    let value = f();
    let recorded = CHARGED_ASSERT_RECORDER
        .with(|rec| rec.replace(previous))
        .map(|(_, blocks)| blocks)
        .unwrap_or_default();
    CHARGED_ASSERT_RECORDER.with(|rec| {
        if let Some((outer, blocks)) = rec.borrow_mut().as_mut() {
            if *outer == def_id {
                blocks.extend(recorded.iter().copied());
            }
        }
    });
    (value, recorded)
}

/// Record that an obligation was stated for the charged assert (arithmetic
/// panic assert or index bounds check) whose `AssertKind` is `msg`
/// (identified by address) in `body`. Call it only where the obligation is
/// kept AND was computed from values the lane models exactly: the record is
/// what lifts the site out of the clause-free cap.
pub(super) fn record_charged_assert_site<'tcx>(
    body: &Body<'tcx>,
    msg: &rustc_middle::mir::AssertKind<rustc_middle::mir::Operand<'tcx>>,
) {
    if body.source.promoted.is_some() {
        return;
    }
    let def_id = body.source.def_id();
    CHARGED_ASSERT_RECORDER.with(|rec| {
        let mut rec = rec.borrow_mut();
        let Some((active, blocks)) = rec.as_mut() else {
            return;
        };
        if *active != def_id {
            return;
        }
        for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
            if let TerminatorKind::Assert { msg: site, .. } = &bb_data.terminator().kind {
                if std::ptr::eq::<rustc_middle::mir::AssertKind<rustc_middle::mir::Operand<'tcx>>>(
                    &**site, msg,
                ) {
                    blocks.insert(bb);
                }
            }
        }
    });
}

/// Charged assert blocks (arithmetic panic asserts and index bounds checks)
/// reachable from the entry of `body` (unwind cleanup excluded) that are not
/// in `covered`.
pub(crate) fn unwalked_charged_assert_sites(
    body: &Body<'_>,
    covered: &HashSet<BasicBlock>,
) -> Vec<BasicBlock> {
    let mut missing = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![rustc_middle::mir::START_BLOCK];
    while let Some(bb) = stack.pop() {
        if !seen.insert(bb) {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        if bb_data.is_cleanup {
            continue;
        }
        let terminator = bb_data.terminator();
        if let TerminatorKind::Assert { msg, .. } = &terminator.kind {
            if super::assertion::is_charged_assert(msg) && !covered.contains(&bb) {
                missing.push(bb);
            }
        }
        stack.extend(terminator.successors());
    }
    missing.sort();
    missing
}

/// Whether `bb` heads a (reducible) loop: some predecessor is dominated by it.
fn is_loop_header_block(body: &Body<'_>, bb: BasicBlock) -> bool {
    let dominators = body.basic_blocks.dominators();
    body.basic_blocks.predecessors()[bb]
        .iter()
        .any(|pred| dominators.dominates(bb, *pred))
}

const ARITHMETIC_HAVOC_PREFIX: &str = "__trust_wp_arith_havoc_";

thread_local! {
    static ARITHMETIC_HAVOC_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn fresh_arithmetic_havoc_name(local: Local) -> String {
    let generation = ARITHMETIC_HAVOC_GENERATION.with(|g| {
        let next = g.get().wrapping_add(1);
        g.set(next);
        next
    });
    format!("{ARITHMETIC_HAVOC_PREFIX}{}_{generation}", local.as_u32())
}

/// Locals whose storage may be written through a `&mut`/raw pointer anywhere
/// in the body: their value can change without a direct assignment.
///
/// Besides `&mut place` / `&raw mut place`, a `&mut`/`*mut` VALUE handed to a
/// call (`<u8 as AddAssign<&u8>>::add_assign(copy _1, ..)` passes the `&mut`
/// parameter itself, with no reborrow statement) lets the callee write its
/// pointee, which later reads of `*_1` observe.
fn address_taken_mutable_locals<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    let mut locals = HashSet::new();
    // Interior mutability: a `&Cell<T>` (or any value from which an
    // `UnsafeCell` or a raw pointer is reachable) lets a callee, or drop glue,
    // change memory that later reads through the same value observe, although
    // no `&mut` is ever taken. Such locals are written through exactly like
    // address-taken ones, so two `c.get()` reads around `c.set(..)` never
    // share one value.
    let typing_env = body.typing_env(tcx);
    for (local, decl) in body.local_decls.iter_enumerated() {
        if ty_may_reach_interior_mutability(tcx, typing_env, decl.ty) {
            locals.insert(local);
        }
    }
    for bb_data in body.basic_blocks.iter() {
        if let TerminatorKind::Call { args, .. } = &bb_data.terminator().kind {
            for arg in args {
                if let rustc_middle::mir::Operand::Copy(place)
                | rustc_middle::mir::Operand::Move(place) = &arg.node
                {
                    if place_may_hold_mutable_pointer(body, place) {
                        locals.insert(place.local);
                    }
                }
            }
        }
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((_, rvalue)) = &stmt.kind {
                match rvalue {
                    // The `&raw const (fake)` pointer a bounds check builds is
                    // read by `PtrMetadata` alone and never written through.
                    rustc_middle::mir::Rvalue::RawPtr(
                        rustc_middle::mir::RawPtrKind::FakeForPtrMetadata,
                        _,
                    ) => {}
                    rustc_middle::mir::Rvalue::Ref(
                        _,
                        rustc_middle::mir::BorrowKind::Mut { .. },
                        place,
                    )
                    | rustc_middle::mir::Rvalue::RawPtr(_, place) => {
                        locals.insert(place.local);
                    }
                    _ => {}
                }
            }
        }
    }
    locals
}

/// Primary-lane counterpart of the region walks' call-site rebinding: on
/// entry to `bb`, when `bb` is the return target of a call or of a `Drop`
/// with drop glue, every local whose type can reach interior mutability is
/// rebound to a fresh symbol of its sort. The callee (or the `Drop` impl) may
/// have written memory those locals reach (`c.set(0)` through `c: &Cell<u8>`,
/// a static atomic, ...), so no value read through them before the call may
/// be identified with one read after it.
pub(super) fn rebind_interior_mutable_locals_at_effect_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    local_exprs: &mut HashMap<Local, PureExpr>,
) {
    let typing_env = body.typing_env(tcx);
    let is_effect_target = body.basic_blocks.predecessors()[bb].iter().any(|pred| {
        let pred_data = &body.basic_blocks[*pred];
        match &pred_data.terminator().kind {
            TerminatorKind::Call { target, .. } => *target == Some(bb),
            TerminatorKind::Drop { place, target, .. } => {
                *target == bb
                    && place
                        .ty(&body.local_decls, tcx)
                        .ty
                        .needs_drop(tcx, typing_env)
            }
            _ => false,
        }
    });
    if !is_effect_target {
        return;
    }
    for (local, decl) in body.local_decls.iter_enumerated() {
        if !ty_may_reach_interior_mutability(tcx, typing_env, decl.ty) {
            continue;
        }
        let base = match local_exprs.get(&local) {
            Some(PureExpr::Var(name, _)) => name.clone(),
            Some(_) => format!("_{}", local.as_u32()),
            None => continue,
        };
        let sort = ty_to_expr_sort_enriched(tcx, decl.ty);
        local_exprs.insert(
            local,
            PureExpr::Var(format!("{base}__after_effect_bb{}", bb.as_u32()), sort),
        );
    }
}

/// [`ty_may_reach_interior_mutability`] for a type read in `typing_env`.
pub(super) fn ty_may_reach_interior_mutability_in<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    ty_may_reach_interior_mutability(tcx, typing_env, ty)
}

/// [`ty_may_reach_interior_mutability`] for a local of `body`.
pub(super) fn local_type_may_reach_interior_mutability<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
) -> bool {
    ty_may_reach_interior_mutability(tcx, body.typing_env(tcx), body.local_decls[local].ty)
}

/// Whether memory reachable from a value of type `ty` may be mutated while
/// only shared access to that value exists, in a way a specification can
/// observe.
///
/// Rust's `Freeze` is structural: shared-access mutation of a value's own
/// memory exists only inside an `UnsafeCell` (`Cell`, `RefCell`, atomics,
/// `Mutex`, ... are built on it). The walk follows exactly that structure:
/// ADT fields (instantiated), tuple/array/slice elements, reference and
/// raw-pointer pointees, closure captures. It answers `true` at an
/// `UnsafeCell`, and conservatively at any type it cannot follow (coroutines,
/// foreign types, too many types).
///
/// Type parameters, projections and trait objects count as stable: the only
/// specifications that read memory behind an `UnsafeCell` are the std specs of
/// the concrete interior-mutability types, which a generic body cannot call on
/// a `T`/`dyn Trait` value. Every other specification observes a value through
/// its logical model, which Creusot's logic cannot make depend on interior
/// memory, so it is the same before and after a call.
fn ty_may_reach_interior_mutability<'tcx>(
    tcx: TyCtxt<'tcx>,
    _typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    const MAX_TYPES: usize = 256;
    use rustc_middle::ty::TyKind;
    let mut seen: HashSet<rustc_middle::ty::Ty<'tcx>> = HashSet::new();
    let mut stack = vec![ty];
    while let Some(ty) = stack.pop() {
        if !seen.insert(ty) {
            continue;
        }
        if seen.len() > MAX_TYPES {
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
            | TyKind::FnPtr(..)
            | TyKind::Param(_)
            | TyKind::Alias(..)
            | TyKind::Dynamic(..) => {}
            TyKind::Ref(_, inner, _)
            | TyKind::RawPtr(inner, _)
            | TyKind::Slice(inner)
            | TyKind::Array(inner, _)
            | TyKind::Pat(inner, _) => {
                stack.push(*inner);
            }
            TyKind::Tuple(items) => stack.extend(items.iter()),
            TyKind::Adt(adt, args) => {
                if adt.is_unsafe_cell() {
                    return true;
                }
                for field in adt.all_fields() {
                    stack.push(field.ty(tcx, *args).skip_norm_wip());
                }
            }
            TyKind::Closure(_, args) => {
                stack.push(args.as_closure().tupled_upvars_ty());
            }
            _ => return true,
        }
    }
    false
}

/// Whether `place`'s type may be (or, when its type cannot be followed,
/// might be) a `&mut` reference or a `*mut` pointer.
fn place_may_hold_mutable_pointer<'tcx>(
    body: &Body<'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
) -> bool {
    use rustc_middle::{mir::ProjectionElem, ty::TyKind};
    let mut ty = body.local_decls[place.local].ty;
    for elem in place.projection {
        ty = match elem {
            ProjectionElem::Field(_, field_ty) => field_ty,
            ProjectionElem::Deref => match ty.builtin_deref(true) {
                Some(inner) => inner,
                None => return true,
            },
            _ => return true,
        };
    }
    matches!(
        ty.kind(),
        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            | TyKind::RawPtr(_, rustc_middle::ty::Mutability::Mut)
    )
}

/// Locals written (directly, through a projection, as a call destination, or
/// via a mutable borrow) by the given blocks.
fn locals_written_in_blocks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    blocks: &HashSet<BasicBlock>,
) -> HashSet<Local> {
    let mut written = HashSet::new();
    if blocks.is_empty() {
        return written;
    }
    written.extend(address_taken_mutable_locals(tcx, body));
    for &bb in blocks {
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            match &stmt.kind {
                StatementKind::Assign((place, _))
                | StatementKind::SetDiscriminant {
                    place: deref!(place),
                    ..
                } => {
                    written.insert(place.local);
                }
                _ => {}
            }
        }
        if let Some(terminator) = &bb_data.terminator {
            if let TerminatorKind::Call { destination, .. } = &terminator.kind {
                written.insert(destination.local);
            }
        }
    }
    written
}

/// For every loop header, the locals its body may write.
pub(crate) fn loop_assigned_locals_by_header<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    analysis: &LoopAnalysis,
) -> HashMap<BasicBlock, HashSet<Local>> {
    analysis
        .loops
        .iter()
        .map(|info| {
            (
                info.header,
                locals_written_in_blocks(tcx, body, &info.body_blocks),
            )
        })
        .collect()
}

/// Re-bind loop-carried locals so obligations never read a stale value.
fn rebind_loop_carried_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    walk: ArithmeticWalk<'_>,
    carried: &HashSet<Local>,
    local_exprs: &mut HashMap<Local, PureExpr>,
) {
    let mut debug_name_counts: HashMap<String, usize> = HashMap::new();
    let mut debug_names: HashMap<Local, String> = HashMap::new();
    for var_debug in &body.var_debug_info {
        let name = var_debug.name.to_string();
        *debug_name_counts.entry(name.clone()).or_default() += 1;
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty() {
                debug_names.insert(place.local, name);
            }
        }
    }
    for &local in carried {
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        // A parameter's name denotes its ENTRY value (the one `requires`
        // constrains), so a parameter the loop writes is never re-bound to
        // it. A local is re-bound to its debug name only when that name is
        // unique in the body and shadows no parameter.
        let symbolic = walk.named_loop_carried_symbolic.then(|| {
            let index = local.as_usize();
            if index >= 1 && index <= walk.arg_names.len() {
                None
            } else {
                debug_names
                    .get(&local)
                    .filter(|name| debug_name_counts.get(*name).copied() == Some(1))
                    .filter(|name| !walk.arg_names.iter().any(|arg| arg == *name))
                    .cloned()
            }
        });
        let name = symbolic
            .flatten()
            .unwrap_or_else(|| fresh_arithmetic_havoc_name(local));
        local_exprs.insert(local, PureExpr::Var(name, sort));
    }
}

/// Re-bind one local to a fresh, range-guarded havoc variable.
fn havoc_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    walk: ArithmeticWalk<'_>,
    local: Local,
    local_exprs: &mut HashMap<Local, PureExpr>,
) {
    let walk = ArithmeticWalk {
        named_loop_carried_symbolic: false,
        ..walk
    };
    let single = HashSet::from([local]);
    rebind_loop_carried_locals(tcx, body, walk, &single, local_exprs);
}

/// Whether the CFG of `body` contains any cycle (reducible or not), by an
/// iterative three-colour depth-first search from every block.
fn cfg_has_cycle(body: &Body<'_>) -> bool {
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        White,
        Grey,
        Black,
    }
    let n = body.basic_blocks.len();
    let mut colour = vec![Colour::White; n];
    for root in body.basic_blocks.indices() {
        if colour[root.as_usize()] != Colour::White {
            continue;
        }
        let mut stack: Vec<(BasicBlock, Vec<BasicBlock>)> = Vec::new();
        colour[root.as_usize()] = Colour::Grey;
        stack.push((
            root,
            body.basic_blocks[root].terminator().successors().collect(),
        ));
        while let Some((bb, succs)) = stack.last_mut() {
            if let Some(next) = succs.pop() {
                match colour[next.as_usize()] {
                    Colour::Grey => return true,
                    Colour::White => {
                        colour[next.as_usize()] = Colour::Grey;
                        let next_succs =
                            body.basic_blocks[next].terminator().successors().collect();
                        stack.push((next, next_succs));
                    }
                    Colour::Black => {}
                }
            } else {
                colour[bb.as_usize()] = Colour::Black;
                stack.pop();
            }
        }
    }
    false
}

/// Whether the primary extractor's `local_exprs` are exact at every
/// arithmetic panic site of `body`, so it may state those obligations itself.
///
/// The primary walk visits each block once per path: through a CFG cycle it
/// keeps a one-iteration value, and it does not re-bind a local written
/// through a `&mut`/raw pointer or through a field projection. Bodies with
/// any of those have their arithmetic obligations collected by the
/// region walks instead (`collect_unannotated_loop_arithmetic_obligations`
/// or the loop-VC region walks), which re-bind conservatively.
pub(crate) fn primary_arithmetic_is_exact<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    if cfg_has_cycle(body) || !address_taken_mutable_locals(tcx, body).is_empty() {
        return false;
    }
    !body.basic_blocks.iter().any(|bb_data| {
        bb_data.statements.iter().any(|stmt| match &stmt.kind {
            StatementKind::Assign((place, _)) => !place.projection.is_empty(),
            StatementKind::SetDiscriminant { .. } => true,
            _ => false,
        }) || matches!(
            &bb_data.terminator().kind,
            TerminatorKind::Call { destination, .. } if !destination.projection.is_empty()
        )
    })
}

/// Every local an rvalue reads: operand locals, deref bases, index locals.
fn rvalue_read_locals<'tcx>(
    rvalue: &rustc_middle::mir::Rvalue<'tcx>,
    location: rustc_middle::mir::Location,
) -> Vec<Local> {
    use rustc_middle::mir::visit::{PlaceContext, Visitor};
    struct Reads(Vec<Local>);
    impl<'tcx> Visitor<'tcx> for Reads {
        fn visit_local(
            &mut self,
            local: Local,
            _context: PlaceContext,
            _location: rustc_middle::mir::Location,
        ) {
            self.0.push(local);
        }
    }
    let mut reads = Reads(Vec::new());
    reads.visit_rvalue(rvalue, location);
    reads.0
}

/// The walk state at `start` for an arithmetic-panic region walk.
///
/// From the function entry the state is exact: parameters at their entry
/// names, nothing else bound. From any other start (a loop header, a loop
/// exit) only facts that hold on EVERY path to `start` are kept:
/// - a local with a single definition site that no loop writes and whose
///   address is never mutably taken has one value wherever it is
///   initialized, so it is bound to its translated definition (processed in
///   reverse postorder, so definitions precede uses);
/// - every other local (multiply-defined, loop-written, address-taken, or
///   with an untranslatable definition) is bound to a fresh range-guarded
///   havoc variable, except the walk's own `carried` locals in named mode,
///   which take their unique debug name (the loop-invariant convention).
///
/// Also returns the havoc variables that stand for a local no loop writes:
/// its value at `start` is the one code before the loop gave it, which the
/// havoc leaves free. A loop-written local's havoc is Creusot's implicit
/// `invariant true` and is not among them.
fn seed_arithmetic_walk_state<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    start: BasicBlock,
    walk: ArithmeticWalk<'_>,
    carried: &HashSet<Local>,
) -> (HashMap<Local, PureExpr>, HashSet<String>) {
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    for (i, name) in walk.arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        if local.as_usize() >= body.local_decls.len() {
            break;
        }
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }
    if start == rustc_middle::mir::START_BLOCK && carried.is_empty() {
        return (local_exprs, HashSet::new());
    }

    // Definition sites per local (parameters: the entry binding is one).
    let mut def_sites: HashMap<Local, usize> = HashMap::new();
    for i in 0..walk.arg_names.len() {
        *def_sites.entry(Local::from_usize(i + 1)).or_default() += 1;
    }
    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            match &stmt.kind {
                StatementKind::Assign((place, _))
                | StatementKind::SetDiscriminant {
                    place: deref!(place),
                    ..
                } => {
                    // A projected write is a (partial) redefinition.
                    *def_sites.entry(place.local).or_default() +=
                        if place.projection.is_empty() { 1 } else { 2 };
                }
                _ => {}
            }
        }
        if let TerminatorKind::Call { destination, .. } = &bb_data.terminator().kind {
            *def_sites.entry(destination.local).or_default() += if destination.projection.is_empty()
            {
                1
            } else {
                2
            };
        }
    }
    let mut unstable: HashSet<Local> = def_sites
        .iter()
        .filter(|(_, count)| **count >= 2)
        .map(|(local, _)| *local)
        .collect();
    unstable.extend(address_taken_mutable_locals(tcx, body));
    let analysis = crate::mir_analysis::detect_loops(body);
    let all_loop_blocks: HashSet<BasicBlock> = analysis
        .loops
        .iter()
        .flat_map(|info| info.body_blocks.iter().copied())
        .collect();
    let loop_written = locals_written_in_blocks(tcx, body, &all_loop_blocks);
    unstable.extend(loop_written.iter().copied());
    unstable.extend(carried.iter().copied());

    // Every unstable local is havocked for the definition pass, carried ones
    // included: a stable definition such as `t = i` (before a loop that
    // writes `i`) must capture `i`'s pre-loop value, never the symbolic
    // in-loop name bound below.
    let havoc_walk = ArithmeticWalk {
        named_loop_carried_symbolic: false,
        ..walk
    };
    rebind_loop_carried_locals(tcx, body, havoc_walk, &unstable, &mut local_exprs);
    // The havoc variables standing for UNSTABLE locals denote no single
    // program point's value: an unstable local may hold different values at
    // two definitions that read it. A stable definition may therefore keep
    // its translation only when it reads no unstable local (checked on the
    // MIR rvalue, deref bases and index locals included) and its translation
    // mentions none of those havoc variables. Otherwise the stable local is
    // bound to a FRESH havoc of its own: it still has exactly one value, so
    // later stable definitions that read it remain exact.
    let unstable_havocs: HashSet<String> = unstable
        .iter()
        .filter_map(|local| local_exprs.get(local))
        .flat_map(PureExpr::free_vars)
        .filter(|name| name.starts_with(ARITHMETIC_HAVOC_PREFIX))
        .collect();

    for &bb in body.basic_blocks.reverse_postorder() {
        let bb_data = &body.basic_blocks[bb];
        for (statement_index, stmt) in bb_data.statements.iter().enumerate() {
            let StatementKind::Assign((place, rvalue)) = &stmt.kind else {
                continue;
            };
            if !place.projection.is_empty() || unstable.contains(&place.local) {
                continue;
            }
            let reads_unstable = rvalue_read_locals(
                rvalue,
                rustc_middle::mir::Location {
                    block: bb,
                    statement_index,
                },
            )
            .iter()
            .any(|read| unstable.contains(read));
            let translated = if reads_unstable {
                None
            } else {
                capture_const_body_obligations(|| {
                    super::primary::translate_struct_aggregate_as_tuple(
                        tcx,
                        rvalue,
                        &local_exprs,
                        None,
                    )
                    .or_else(|| {
                        translate_rvalue_with_enum_variants(
                            tcx,
                            rvalue,
                            &local_exprs,
                            Some(body),
                            None,
                            None,
                        )
                    })
                    .or_else(|| translate_loop_assignment_fallback(tcx, body, rvalue, &local_exprs))
                })
                .0
                .filter(|expr| {
                    expr.free_vars()
                        .iter()
                        .all(|name| !unstable_havocs.contains(name))
                })
            };
            match translated {
                Some(expr) => {
                    local_exprs.insert(place.local, expr);
                }
                None => havoc_local(tcx, body, walk, place.local, &mut local_exprs),
            }
        }
        if let TerminatorKind::Call { destination, .. } = &bb_data.terminator().kind {
            if destination.projection.is_empty() && !unstable.contains(&destination.local) {
                havoc_local(tcx, body, walk, destination.local, &mut local_exprs);
            }
        }
    }
    rebind_loop_carried_locals(tcx, body, walk, carried, &mut local_exprs);
    let unstated_entry_values = local_exprs
        .iter()
        .filter(|(local, _)| !loop_written.contains(*local) && !carried.contains(*local))
        .flat_map(|(_, expr)| expr.free_vars())
        .filter(|name| name.starts_with(ARITHMETIC_HAVOC_PREFIX))
        .collect();
    (local_exprs, unstated_entry_values)
}

/// Guard an arithmetic obligation with the machine-int range of every havoc
/// variable it mentions (a literal consequence of the local's Rust type).
fn guard_arithmetic_havoc_ranges<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    obligation: PureExpr,
) -> PureExpr {
    let mut names: Vec<String> = obligation
        .free_vars()
        .into_iter()
        .filter(|name| name.starts_with(ARITHMETIC_HAVOC_PREFIX))
        .collect();
    names.sort();
    let mut facts = Vec::new();
    for name in names {
        let Some(index) = name
            .strip_prefix(ARITHMETIC_HAVOC_PREFIX)
            .and_then(|rest| rest.split('_').next())
            .and_then(|digits| digits.parse::<usize>().ok())
        else {
            continue;
        };
        if index >= body.local_decls.len() {
            continue;
        }
        let ty = body.local_decls[Local::from_usize(index)].ty;
        let sort = ty_to_expr_sort_enriched(tcx, ty);
        if let Some(fact) = machine_int_range_fact(tcx, ty, PureExpr::Var(name, sort)) {
            facts.push(fact);
        }
    }
    let Some(guard) = facts
        .into_iter()
        .reduce(|acc, fact| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(fact)))
    else {
        return obligation;
    };
    PureExpr::BinOp(Arc::new(guard), BinOp::Implies, Arc::new(obligation))
}

/// Collect machine-int arithmetic panic obligations (checked `+ - *`, signed
/// `MIN / -1`, signed negation, division/remainder by zero) for one region.
#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_arithmetic_panic_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    region: &ArithmeticRegion<'_>,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    loop_assigned_by_header: &HashMap<BasicBlock, HashSet<Local>>,
) -> LoopBodyObligations {
    let spec_ctx = LoopBodySpecContext {
        user_specs,
        trait_specs,
        extern_specs,
        body_blocks: region.region_blocks,
        name_restore_blocks: Some(region.loop_carried_blocks),
        all_loops: region.all_loops,
        arithmetic: Some(ArithmeticWalk {
            arg_names,
            named_loop_carried_symbolic: region.named_loop_carried_symbolic,
            loop_assigned_by_header,
        }),
        condition_switch: region.condition_switch,
    };
    collect_loop_body_call_obligations_split(tcx, body, arg_names, region.start, &spec_ctx)
}

/// Arithmetic panic obligations for a function whose loops carry NO
/// invariant (so no loop VC exists): every loop body, and every region after
/// a loop exit, is walked with loop-carried locals havocked (Creusot's
/// implicit `invariant true`). The primary extractor skips loop bodies and
/// keeps pre-loop values past the loop, so without this walk those panic
/// sites would never be examined.
pub(crate) fn collect_unannotated_loop_arithmetic_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Vec<PureExpr> {
    if primary_arithmetic_is_exact(tcx, body) {
        // The primary extractor states every obligation of this body.
        return Vec::new();
    }
    let analysis = crate::mir_analysis::detect_loops(body);
    let by_header = loop_assigned_locals_by_header(tcx, body, &analysis);
    let all_loop_blocks: HashSet<BasicBlock> = analysis
        .loops
        .iter()
        .flat_map(|info| info.body_blocks.iter().copied())
        .collect();
    let mut obligations = Vec::new();
    // The entry region (up to the first loop header), walked exactly from
    // the function entry: the primary extractor defers it here.
    let entry_region: HashSet<BasicBlock> = body
        .basic_blocks
        .indices()
        .filter(|bb| !all_loop_blocks.contains(bb))
        .collect();
    obligations.extend(
        collect_arithmetic_panic_obligations(
            tcx,
            body,
            arg_names,
            &ArithmeticRegion {
                start: rustc_middle::mir::START_BLOCK,
                region_blocks: &entry_region,
                loop_carried_blocks: &HashSet::new(),
                named_loop_carried_symbolic: false,
                all_loops: None,
                condition_switch: None,
            },
            user_specs,
            trait_specs,
            extern_specs,
            &by_header,
        )
        .into_all(),
    );
    if !analysis.has_loops {
        return obligations;
    }
    for info in &analysis.loops {
        let mut exclusive = info.body_blocks.clone();
        let mut carried_blocks = info.body_blocks.clone();
        for other in &analysis.loops {
            if other.header == info.header {
                continue;
            }
            if info.body_blocks.contains(&other.header) {
                for bb in &other.body_blocks {
                    if *bb != other.header {
                        exclusive.remove(bb);
                    }
                }
            }
            if other.body_blocks.contains(&info.header) {
                carried_blocks.extend(other.body_blocks.iter().copied());
            }
        }
        obligations.extend(
            collect_arithmetic_panic_obligations(
                tcx,
                body,
                arg_names,
                &ArithmeticRegion {
                    start: info.header,
                    region_blocks: &exclusive,
                    loop_carried_blocks: &carried_blocks,
                    named_loop_carried_symbolic: false,
                    all_loops: Some(&analysis.loops),
                    condition_switch: None,
                },
                user_specs,
                trait_specs,
                extern_specs,
                &by_header,
            )
            .into_all(),
        );
    }
    obligations.extend(collect_post_loop_arithmetic_obligations(
        tcx,
        body,
        arg_names,
        &all_loop_blocks,
        false,
        user_specs,
        trait_specs,
        extern_specs,
        &by_header,
    ));
    obligations
}

/// Arithmetic panic obligations for the non-loop blocks reached from each
/// loop exit, with every local any loop may write re-bound at the exit.
#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_post_loop_arithmetic_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    all_loop_blocks: &HashSet<BasicBlock>,
    named_loop_carried_symbolic: bool,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    loop_assigned_by_header: &HashMap<BasicBlock, HashSet<Local>>,
) -> Vec<PureExpr> {
    let non_loop_blocks: HashSet<BasicBlock> = body
        .basic_blocks
        .indices()
        .filter(|bb| !all_loop_blocks.contains(bb))
        .collect();
    let predecessors = body.basic_blocks.predecessors();
    // The loop verifier's own exit recovery: the resolved exit edge of each
    // loop is always a post-loop start.
    let resolved_exits: HashSet<BasicBlock> = crate::mir_analysis::detect_loops(body)
        .loops
        .iter()
        .filter_map(|info| super::loop_merges::loop_exit_edge(body, info).map(|(_, exit)| exit))
        .collect();
    // Every other block entered from a loop block (a `break`, an in-loop
    // `return` path) is a start too, EXCEPT an in-loop arm that can only
    // diverge (`if i == 5 { let _z = i - 1; spin() }`): it never leaves the
    // iteration, and the enclosing loop's region walk states its obligations
    // under the arm's path guard (the `block_must_diverge` exception in
    // `collect_guarded_obligations`). Walking it here would drop that guard
    // (s40v3_loop_nooverflow_before_spin_control). The coverage check
    // (`unwalked_charged_assert_sites`) fails closed if no walk reaches it.
    let mut exits: Vec<BasicBlock> = non_loop_blocks
        .iter()
        .copied()
        .filter(|bb| {
            predecessors[*bb]
                .iter()
                .any(|pred| all_loop_blocks.contains(pred))
        })
        .filter(|bb| {
            resolved_exits.contains(bb) || !block_must_diverge(body, *bb, &mut HashSet::new())
        })
        .collect();
    exits.sort();
    let mut obligations = Vec::new();
    for exit in exits {
        obligations.extend(
            collect_arithmetic_panic_obligations(
                tcx,
                body,
                arg_names,
                &ArithmeticRegion {
                    start: exit,
                    region_blocks: &non_loop_blocks,
                    loop_carried_blocks: all_loop_blocks,
                    named_loop_carried_symbolic,
                    all_loops: None,
                    condition_switch: None,
                },
                user_specs,
                trait_specs,
                extern_specs,
                loop_assigned_by_header,
            )
            .into_all(),
        );
    }
    obligations
}

/// Mutable per-branch state for loop body obligation collection.
///
/// Bundles the three owned collections that are cloned at each
/// `SwitchInt` branch point during [`collect_guarded_obligations`]
/// traversal.
#[derive(Clone)]
struct ObligationWalkState {
    local_exprs: HashMap<Local, PureExpr>,
    visited: HashSet<BasicBlock>,
    path_conditions: Vec<PureExpr>,
    /// Header of the loop whose group is being collected.
    walk_header: BasicBlock,
    arg_count: usize,
    /// Whether this path has taken the in-body arm of the condition switch.
    condition_established: bool,
}

/// Collect call-site precondition obligations from loop body blocks.
///
/// Walks the given set of loop body blocks, finds `Call` terminators, looks up
/// specs, and returns substituted precondition obligations. Unlike
/// `extract_return_expr_with_context` (which bails at `FalseUnwind` loop
/// headers), this function specifically targets in-loop call sites.
///
/// These obligations should be verified under `requires ∧ invariants ∧ loop_condition`,
/// since they only execute when the loop condition is true.
///
/// # Arguments
/// * `tcx` - Type context for resolving function paths
/// * `body` - The MIR body containing the loop
/// * `arg_names` - Function argument names for symbolic representation
/// * `body_blocks` - Set of basic blocks that constitute the loop body
/// * `user_specs` - User-defined function specs
/// * `trait_specs` - Trait method specs
///
/// Test-only convenience over [`collect_loop_body_call_obligations_split`]
/// (the production callers consume the split form directly).
#[cfg(test)]
pub(crate) fn collect_loop_body_call_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    header: BasicBlock,
    spec_ctx: &LoopBodySpecContext<'_>,
) -> Vec<PureExpr> {
    let split = collect_loop_body_call_obligations_split(tcx, body, arg_names, header, spec_ctx);
    let mut obligations = split.obligations;
    obligations.extend(split.condition_free_obligations);
    obligations
}

/// [`collect_loop_body_call_obligations`], split by whether the loop condition
/// may be assumed (see [`LoopBodyObligations`]).
pub(crate) fn collect_loop_body_call_obligations_split<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    header: BasicBlock,
    spec_ctx: &LoopBodySpecContext<'_>,
) -> LoopBodyObligations {
    let body_blocks = spec_ctx.body_blocks;
    if let Some(walk) = spec_ctx.arithmetic {
        let name_restore_blocks = spec_ctx.name_restore_blocks.unwrap_or(body_blocks);
        let carried = locals_written_in_blocks(tcx, body, name_restore_blocks);
        let (local_exprs, unstated_entry_values) =
            seed_arithmetic_walk_state(tcx, body, header, walk, &carried);
        let mut obligations =
            walk_arithmetic_region(tcx, body, arg_names, header, spec_ctx, local_exprs);
        obligations.unstated_entry_values = unstated_entry_values;
        return obligations;
    }
    // Build local_exprs from arguments and debug info (same as extract_loop_body).
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    let param_locals: HashSet<Local> = (0..arg_names.len())
        .map(|i| Local::from_usize(i + 1))
        .collect();

    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }

    // Seed with debug info variable names for symbolic resolution.
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty() && !param_locals.contains(&place.local) {
                let name = var_debug.name.to_string();
                let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
                local_exprs.insert(place.local, PureExpr::Var(name, sort));
            }
        }
    }

    // Also resolve pre-loop temporaries by walking from bb0 to the loop,
    // so that argument expressions used at call sites resolve correctly.
    //
    // After the walk, restore debug-info Var names for locals that are
    // assigned inside the loop body. These are loop-modified variables
    // (e.g., `door` in `door += pass`) whose pre-loop value (e.g., `pass`)
    // is NOT the in-loop value. The invariant constrains the symbolic name
    // (`door@`), so the obligation must use the same symbolic name.
    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut worklist = vec![BasicBlock::from_u32(0)];
    while let Some(bb) = worklist.pop() {
        if body_blocks.contains(&bb) || !visited.insert(bb) {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    if let Some(expr) = translate_rvalue_with_enum_variants(
                        tcx,
                        rvalue,
                        &local_exprs,
                        Some(body),
                        None,
                        None,
                    )
                    .or_else(|| translate_loop_assignment_fallback(tcx, body, rvalue, &local_exprs))
                    {
                        local_exprs.insert(place.local, expr);
                    }
                }
            }
        }
        for succ in bb_data.terminator().successors() {
            worklist.push(succ);
        }
    }

    // Collect locals assigned inside the loop body blocks, plus any enclosing
    // loop body blocks supplied by the caller.
    let mut body_assigned_locals: HashSet<Local> = HashSet::new();
    let name_restore_blocks = spec_ctx.name_restore_blocks.unwrap_or(body_blocks);
    for &bb in name_restore_blocks {
        for stmt in &body.basic_blocks[bb].statements {
            if let StatementKind::Assign((place, _)) = &stmt.kind {
                if place.projection.is_empty() {
                    body_assigned_locals.insert(place.local);
                }
            }
        }
    }

    // A local that a `&mut` call argument, or a store through a pointer, may
    // write is modified too: otherwise `while .. { setneg(&mut x); }` leaves
    // `x` folded to its bb0 initializer and `need_pos(x)` in the body is
    // discharged against a value the loop has already overwritten. The same
    // holds for a local a PRIOR loop (an enclosing or preceding one) may
    // write: no pre-loop assignment of it survives to this header.
    {
        let write_sites = crate::mir_analysis::loops::WriteSites::new(body);
        for (local, _) in write_sites.writes_in_blocks(name_restore_blocks.iter().copied()) {
            body_assigned_locals.insert(local);
        }
        if let Some(loops) = spec_ctx.all_loops {
            if let Some(info) = loops.iter().find(|info| info.header == header) {
                let prior = crate::mir_analysis::loops::prior_loop_blocks(body, info, loops);
                for (local, _) in write_sites.writes_in_blocks(prior) {
                    body_assigned_locals.insert(local);
                }
            }
        }
    }

    // Restore debug-info names for loop-body-modified locals.
    // The pre-loop walk may have resolved them through pre-loop assignments
    // (e.g., `door = pass`), but inside the loop, these variables are modified
    // by the loop body and constrained by invariants. Using the pre-loop
    // resolved value would produce incorrect obligations.
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty()
                && !param_locals.contains(&place.local)
                && body_assigned_locals.contains(&place.local)
            {
                let name = var_debug.name.to_string();
                let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
                local_exprs.insert(place.local, PureExpr::Var(name, sort));
            }
        }
    }

    walk_arithmetic_region(tcx, body, arg_names, header, spec_ctx, local_exprs)
}

fn walk_arithmetic_region<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    header: BasicBlock,
    spec_ctx: &LoopBodySpecContext<'_>,
    local_exprs: HashMap<Local, PureExpr>,
) -> LoopBodyObligations {
    let mut obligations = LoopBodyObligations::default();

    // Walk the CFG from the loop header, tracking path conditions at SwitchInt
    // terminators so that guarded calls get wrapped as `guard ==> obligation`.
    // This prevents false "incomplete" results for calls under conditionals
    // (e.g., `if i < v.len() { v[i] = 0; }` where the guard provides the
    // precondition).
    let state = ObligationWalkState {
        local_exprs,
        visited: HashSet::new(),
        path_conditions: Vec::new(),
        walk_header: header,
        arg_count: arg_names.len(),
        condition_established: false,
    };
    collect_guarded_obligations(tcx, body, header, state, spec_ctx, &mut obligations);

    if spec_ctx.arithmetic.is_some() {
        for list in [
            &mut obligations.obligations,
            &mut obligations.condition_free_obligations,
        ] {
            *list = std::mem::take(list)
                .into_iter()
                .map(|obligation| guard_arithmetic_havoc_ranges(tcx, body, obligation))
                .collect();
        }
    }
    obligations
}

fn translate_loop_assignment_fallback<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rvalue: &rustc_middle::mir::Rvalue<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    match rvalue {
        rustc_middle::mir::Rvalue::Ref(_, _, place)
        | rustc_middle::mir::Rvalue::CopyForDeref(place) => {
            translate_typed_field_place(tcx, body, place, local_exprs)
        }
        _ => None,
    }
}

/// Walk the CFG within a loop body, accumulating path conditions at branch
/// points and wrapping call-site precondition obligations with their guards.
///
/// At each `SwitchInt` terminator, each successor gets the current
/// path conditions extended with the branch predicate. When a `Call`
/// terminator is reached, any non-empty path conditions are folded into
/// an implication: `(guard₁ ∧ guard₂ ∧ …) ==> obligation`.
fn collect_guarded_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    mut state: ObligationWalkState,
    spec_ctx: &LoopBodySpecContext<'_>,
    obligations: &mut LoopBodyObligations,
) {
    // Only visit blocks within the loop body, and avoid revisiting.
    //
    // EXCEPTION: a block that can only DIVERGE (an in-loop arm ending in a
    // trusted inert spin, `if i == 0 { let _z = i - 1; spin() }`) never
    // reaches the back-edge, so it is not part of `body_blocks` — yet it
    // executes within the current iteration, under this walk's path guard.
    // Its checks and call preconditions are obligations here; skipping it
    // drops them (no other lane walks an in-loop diverging arm).
    let in_body = spec_ctx.body_blocks.contains(&bb);
    // An arithmetic walk never ENTERS a loop through that exception: in a body
    // that can never return (`while i < n { i += 1 } let _y = n - i; spin()`)
    // the loop header itself "must diverge", and walking it from the entry /
    // post-loop regions would re-bind the loop-carried locals to havoc that no
    // invariant constrains, owing `n - i` on the exit tail for any `i`
    // (s40v4_tail_loopvar_exit_control). The loop's own region walk states
    // those blocks' obligations (under its invariant and path guards), and
    // `unwalked_charged_assert_sites` fails closed on any site no kept lane
    // stated.
    let off_body_admitted = !in_body
        && block_must_diverge(body, bb, &mut HashSet::new())
        && !(spec_ctx.arithmetic.is_some() && is_loop_header_block(body, bb));
    if (!in_body && !off_body_admitted) || !state.visited.insert(bb) {
        return;
    }
    if !in_body {
        obligations.off_body_blocks.insert(bb);
    }

    // An inner loop header: the inner body is owned by the inner loop's own
    // group, but code AFTER the inner loop (its exit arm, its break paths)
    // belongs to this group. Continue there from a state in which everything
    // the inner loop may write is a fresh variable. Stopping here instead
    // drops a `never()` after the inner loop, because the exclusive block set
    // excludes the inner condition block through which it is reached.
    if bb != state.walk_header {
        if let Some(inner) = spec_ctx
            .all_loops
            .and_then(|loops| loops.iter().find(|info| info.header == bb))
        {
            let region = super::loop_merges::loop_region(body, inner)
                .unwrap_or_else(|| inner.body_blocks.clone());
            let (written, _) = super::loop_merges::region_effects(body, state.arg_count, &region);
            if let Some(walk) = spec_ctx.arithmetic {
                // Arithmetic mode: everything the inner loop (its whole region,
                // its body blocks, and any call / drop / pointer write in it)
                // may change is re-bound to fresh, range-guarded havoc.
                let mut carried: HashSet<Local> = written;
                carried.extend(locals_written_in_blocks(tcx, body, &region));
                carried.extend(locals_written_in_blocks(tcx, body, &inner.body_blocks));
                if let Some(assigned) = walk.loop_assigned_by_header.get(&bb) {
                    carried.extend(assigned.iter().copied());
                }
                carried.extend(address_taken_mutable_locals(tcx, body));
                let walk = ArithmeticWalk {
                    named_loop_carried_symbolic: false,
                    ..walk
                };
                rebind_loop_carried_locals(tcx, body, walk, &carried, &mut state.local_exprs);
            } else {
                let mut written: Vec<Local> = written.into_iter().collect();
                written.sort();
                for local in written {
                    let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
                    let name =
                        super::unannotated_loops::fresh_name(&format!("inner{}", local.as_usize()));
                    state.local_exprs.insert(local, PureExpr::Var(name, sort));
                }
            }
            let mut exits: Vec<BasicBlock> = inner
                .body_blocks
                .iter()
                .flat_map(|&inner_bb| super::loop_merges::normal_successors(body, inner_bb))
                .filter(|succ| !inner.body_blocks.contains(succ))
                .collect();
            exits.sort();
            exits.dedup();
            for exit in exits {
                collect_guarded_obligations(tcx, body, exit, state.clone(), spec_ctx, obligations);
            }
            return;
        }
    }

    let bb_data = &body.basic_blocks[bb];

    // Arithmetic-panic mode: entering a loop header other than the walk's
    // own start re-binds everything that inner loop may write, to FRESH
    // havoc variables. Re-binding to the symbolic debug name would identify
    // the post-inner-loop value with the walk-start value that the path
    // conditions gathered so far (and the enclosing invariant) constrain.
    if let Some(walk) = spec_ctx.arithmetic {
        if state.visited.len() > 1 {
            if let Some(carried) = walk.loop_assigned_by_header.get(&bb) {
                let walk = ArithmeticWalk {
                    named_loop_carried_symbolic: false,
                    ..walk
                };
                rebind_loop_carried_locals(tcx, body, walk, carried, &mut state.local_exprs);
            }
        }
    }

    // Resolve assignments in this block so call-site arguments translate.
    for stmt in &bb_data.statements {
        if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
            if place.projection.is_empty() {
                let (translated, const_body_obligations) = capture_const_body_obligations(|| {
                    // Arithmetic mode translates struct aggregates exactly as
                    // the primary extractor does, so a later field read
                    // (`a.0 -= 1` on `IsZero(0)`) stays exact.
                    spec_ctx
                        .arithmetic
                        .and_then(|_| {
                            super::primary::translate_struct_aggregate_as_tuple(
                                tcx,
                                rvalue,
                                &state.local_exprs,
                                None,
                            )
                        })
                        .or_else(|| {
                            translate_rvalue_with_enum_variants(
                                tcx,
                                rvalue,
                                &state.local_exprs,
                                Some(body),
                                None,
                                None,
                            )
                        })
                        .or_else(|| {
                            translate_loop_assignment_fallback(
                                tcx,
                                body,
                                rvalue,
                                &state.local_exprs,
                            )
                        })
                });
                if spec_ctx.arithmetic.is_some() {
                    for obligation in const_body_obligations {
                        obligations.push(
                            state.condition_established,
                            wrap_with_guard(&state.path_conditions, obligation),
                        );
                    }
                }
                if let Some(expr) = translated {
                    state.local_exprs.insert(place.local, expr);
                } else if let Some(walk) = spec_ctx.arithmetic {
                    // An untranslatable write still changes the local: never
                    // keep its previous binding.
                    havoc_local(tcx, body, walk, place.local, &mut state.local_exprs);
                }
            } else if let Some(walk) = spec_ctx.arithmetic {
                // A projected write (`*r = ..`, `s.f = ..`) may change the
                // base local and whatever aliases it by reference flow
                // (`write_aliases`), never an unrelated live `&mut`.
                let carried =
                    super::write_aliases::locals_a_write_may_change(tcx, body, place.local);
                let walk = ArithmeticWalk {
                    named_loop_carried_symbolic: false,
                    ..walk
                };
                rebind_loop_carried_locals(tcx, body, walk, &carried, &mut state.local_exprs);
            }
        } else if let StatementKind::SetDiscriminant {
            place: deref!(place),
            ..
        } = &stmt.kind
        {
            if let Some(walk) = spec_ctx.arithmetic {
                havoc_local(tcx, body, walk, place.local, &mut state.local_exprs);
            }
        }
    }

    let Some(ref terminator) = bb_data.terminator else {
        return;
    };

    match &terminator.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            if let Some(obligation) =
                super::assertion::call_type_obligation(tcx, body, bb, func, spec_ctx.user_specs)
            {
                obligations.push(
                    state.condition_established,
                    wrap_with_guard(&state.path_conditions, obligation),
                );
            }
            // A core operator-trait call on primitive integers owes the
            // primitive operation's obligation at this program point.
            if spec_ctx.arithmetic.is_some() {
                if let Some(obligation) = operator_call_obligation(
                    tcx,
                    func,
                    args,
                    destination.ty(&body.local_decls, tcx).ty,
                    &state.local_exprs,
                    body,
                ) {
                    obligations.push(
                        state.condition_established,
                        wrap_with_guard(&state.path_conditions, obligation),
                    );
                }
            }
            let mut destination_modeled = false;
            // Arithmetic mode: the walk state at the call, and the callee
            // contract to hand a fresh `&mut` reborrow's prophecy back with
            // (see `reborrow_handback`), both consumed after the re-binding.
            let pre_call_exprs = spec_ctx.arithmetic.map(|_| state.local_exprs.clone());
            let mut reborrow_handback: Option<(
                Vec<String>,
                trust_wp_core::formula::elaborate::Signature,
                Option<Vec<String>>,
                Vec<TranslatedArg>,
            )> = None;
            // A call through a fn pointer resolves to its target only when the
            // pointer local can hold nothing else; an unknown target owes its
            // (unknown) precondition, which no proof discharges. The decision
            // is SHARED with the unannotated lane (`unannotated_loops.rs`) so
            // the two cannot drift; a generic `Fn*`-bound call
            // is refused here for the same reason it is refused there — its
            // `precondition_F f args` goal is one neither lane can state.
            let call_target =
                super::call_resolve_util::classify_loop_call_target(tcx, body, bb, func);
            let call_def_id = match call_target {
                super::call_resolve_util::LoopCallTarget::Resolved(def_id) => Some(def_id),
                _ => None,
            };
            if call_def_id.is_none() && spec_ctx.arithmetic.is_none() {
                obligations.push_fail_closed(
                    state.condition_established,
                    &state.path_conditions,
                    fail_closed_marker("loop-body-no-callee"),
                );
            }
            if let Some(def_id) = call_def_id {
                let translated_args = translate_call_args_for_substitutions_with_tcx(
                    args,
                    &state.local_exprs,
                    Some(body),
                    Some(tcx),
                );

                let hir_param_names = arg_names_for_def_id(tcx, def_id);

                // Look up spec: user_specs -> trait_specs -> UFCS -> plain path
                // -> trait method fallback: the same table-lookup order and
                // admission as `resolve_call` steps 4-6. It stops one step
                // short: `resolve_call` refines a table hit through
                // `collect_gate::refine_collect_spec` and this lane does not,
                // so a `collect`-shaped callee can carry a coarser spec here.
                let extern_opt = if spec_ctx.extern_specs.is_empty() {
                    None
                } else {
                    Some(spec_ctx.extern_specs)
                };
                let user_or_trait_spec = spec_ctx
                    .user_specs
                    .get(&def_id)
                    .or_else(|| spec_ctx.trait_specs.get(&def_id))
                    .cloned()
                    .map(|spec| {
                        crate::logic::identity_typed::instantiate_generic_markers_for_call(
                            tcx, body, func, def_id, spec,
                        )
                    });
                let from_user_or_trait_table = user_or_trait_spec.is_some();
                let record_path_postconditions = def_id.is_local() || from_user_or_trait_table;
                let spec = user_or_trait_spec
                    .or_else(|| {
                        ufcs_path_for_call(tcx, func).and_then(|ufcs_path| {
                            crate::provenance::lookup_spec_for_def(
                                tcx,
                                def_id,
                                crate::provenance::builtin_spec_admission_for_operand(
                                    tcx,
                                    func,
                                    Some(body.source.def_id()),
                                ),
                                extern_opt,
                                &ufcs_path,
                                crate::provenance::CallSite::of_operand(
                                    func,
                                    Some(body.source.def_id()),
                                ),
                            )
                        })
                    })
                    .or_else(|| {
                        let path = tcx.def_path_str(def_id);
                        crate::provenance::lookup_spec_for_def(
                            tcx,
                            def_id,
                            crate::provenance::builtin_spec_admission_for_operand(
                                tcx,
                                func,
                                Some(body.source.def_id()),
                            ),
                            extern_opt,
                            &path,
                            crate::provenance::CallSite::of_operand(
                                func,
                                Some(body.source.def_id()),
                            ),
                        )
                    })
                    .or_else(|| {
                        let trait_method_id = resolve_trait_method_def_id(tcx, def_id)?;
                        let trait_path = tcx.def_path_str(trait_method_id);
                        crate::provenance::lookup_spec_for_def(
                            tcx,
                            trait_method_id,
                            crate::provenance::builtin_spec_admission_for_operand(
                                tcx,
                                func,
                                Some(body.source.def_id()),
                            ),
                            extern_opt,
                            &trait_path,
                            crate::provenance::CallSite::of_operand(
                                func,
                                Some(body.source.def_id()),
                            ),
                        )
                    });

                if let Some(spec) = spec {
                    let param_names = hir_param_names.or_else(|| spec.param_names.clone());
                    // Collect raw obligations into CallEffects, then wrap
                    // each with path conditions before adding to the final
                    // obligation set.
                    let mut call_effects = CallEffects::new();
                    collect_precondition_obligations(
                        &spec.requires,
                        &translated_args,
                        param_names.as_deref(),
                        &mut call_effects,
                    );
                    // A refused grant is owed UNGUARDED: whatever path
                    // reaches the call, the grant it cannot state is owed.
                    if from_user_or_trait_table
                        && super::call_spec::charge_callee_invariant_grant(
                            tcx,
                            body,
                            func,
                            def_id,
                            (spec_ctx.user_specs, spec_ctx.trait_specs),
                            &translated_args,
                            &mut call_effects,
                        )
                        .is_err()
                    {
                        obligations.push(state.condition_established, PureExpr::Bool(false));
                    }
                    // prophecy-store: an argument read through a reference
                    // after a store through it (or an alias) denotes the
                    // pointee's ENTRY value here; fail closed.
                    if !call_effects.obligations.is_empty() {
                        let call_location = Location {
                            block: bb,
                            statement_index: bb_data.statements.len(),
                        };
                        let mut staleness =
                            crate::mir_analysis::deref_store_staleness::DerefStoreStaleness::new(
                                Some(tcx),
                                body,
                            );
                        if args
                            .iter()
                            .any(|arg| staleness.operand_may_read_stale(&arg.node, call_location))
                        {
                            call_effects.obligations.clear();
                            if spec_ctx.arithmetic.is_none() {
                                obligations.push_fail_closed(
                                    state.condition_established,
                                    &state.path_conditions,
                                    fail_closed_marker("loop-body-stale-arg"),
                                );
                            }
                        }
                    }
                    // A `false` beyond the ones the callee's author wrote is
                    // the marker for a clause that did not translate.
                    let mut markers =
                        trust_wp_ay::fail_closed_marker_count(&call_effects.obligations)
                            .saturating_sub(call_effects.user_written_false_obligations);
                    for ob in call_effects.obligations.drain(..) {
                        if spec_ctx.arithmetic.is_some() {
                            continue;
                        }
                        if markers > 0 && matches!(ob, PureExpr::Bool(false)) {
                            markers -= 1;
                            obligations.push_fail_closed(
                                state.condition_established,
                                &state.path_conditions,
                                ob,
                            );
                        } else {
                            obligations.push(
                                state.condition_established,
                                wrap_with_guard(&state.path_conditions, ob),
                            );
                        }
                    }

                    if !spec.ensures.is_empty() {
                        let result_var = state
                            .local_exprs
                            .get(&destination.local)
                            .cloned()
                            .unwrap_or_else(|| call_result_symbol(body, destination.local, tcx));
                        let mut post_effects = CallEffects::new();
                        // Always model the call result from spec ensures so
                        // subsequent in-loop `SwitchInt` translations can
                        // resolve the call destination to its symbolic
                        // expression (e.g., `_call_X` → `view(v).len()`).
                        // Without this binding, branch conditions like
                        // `i < v.len()` cannot translate at the SwitchInt and
                        // the call obligation `i < v.view().len()` loses its
                        // guard. Predicate-style postcondition assumptions
                        // (the path-condition append below) remain gated by
                        // `record_path_postconditions` to avoid noisy
                        // extern-spec ensures pollution.
                        let modeled_result = apply_postconditions_with_effects(
                            &spec.ensures,
                            &crate::mir_analysis::call_signature(
                                tcx,
                                def_id,
                                param_names.as_deref(),
                                Some(crate::mir_analysis::CallSite { body, func }),
                            ),
                            &result_var,
                            &translated_args,
                            param_names.as_deref(),
                            &mut post_effects,
                            record_path_postconditions,
                        );
                        for ob in post_effects.obligations.drain(..) {
                            if spec_ctx.arithmetic.is_none() {
                                obligations.push(
                                    state.condition_established,
                                    wrap_with_guard(&state.path_conditions, ob),
                                );
                            }
                        }
                        if destination.projection.is_empty() {
                            state.local_exprs.insert(destination.local, modeled_result);
                            destination_modeled = true;
                        } else {
                            state.local_exprs.remove(&destination.local);
                        }
                        // For a variant-preserving `Option` adapter — a spec that
                        // ensures BOTH `self.is_some() => result.is_some()` and
                        // `self.is_none() => result.is_none()` (as_ref/as_mut/
                        // as_deref/as_deref_mut) — link the result's Some-ness to
                        // the receiver's, so a subsequent `.unwrap()` precondition
                        // `is_some(result)` can be discharged from `is_some(*self)`
                        // (which the recursive-fn unfolder derives via
                        // `¬is_some(l.1) => len(l)==1`). The Option-sorted result
                        // cannot ride `append_result_guarded_postconditions`
                        // (Bool-sort gate), and the extern spec disables
                        // `record_path_postconditions`, so we push the link
                        // directly. SOUND: `is_some(result)==is_some(*self)` is a
                        // literal consequence of the two spec ensures. Gated by
                        // `TRUST_WP_OFFLOOP` with the recursive-fn unfolder, whose
                        // target shape (`l = l.1.as_mut().unwrap()` chains) needs
                        // this link to discharge the `.unwrap()`.
                        if std::env::var_os("TRUST_WP_OFFLOOP").is_some() {
                            // Some-preserving: `self.is_some() ==> result.is_some()`.
                            // None-preserving: `self.is_none() ==> result.is_none()`
                            // or the equivalent `self.is_none() ==> result == None`.
                            let preserves_variant = spec.ensures.iter().any(|e| {
                                e.contains("self.is_some()") && e.contains("result.is_some()")
                            }) && spec.ensures.iter().any(|e| {
                                e.contains("self.is_none()")
                                    && (e.contains("result.is_none()")
                                        || e.contains("result == None"))
                            });
                            if let Some(p) = std::env::var_os("TRUST_WP_FACTA_DBG") {
                                use std::io::Write as _;
                                if let Ok(mut f) = std::fs::OpenOptions::new()
                                    .create(true)
                                    .append(true)
                                    .open(p)
                                {
                                    let _ = writeln!(
                                        f,
                                        "[factA] preserves={preserves_variant} ensures={:?} arg0={:?}",
                                        spec.ensures,
                                        translated_args
                                            .first()
                                            .map(|a| (a.is_fallback, format!("{:.120?}", a.expr)))
                                    );
                                }
                            }
                            if preserves_variant {
                                if let Some(self_expr) = translated_args
                                    .first()
                                    .filter(|a| !a.is_fallback)
                                    .map(|a| a.expr.clone())
                                {
                                    let is_some = |e: PureExpr| PureExpr::MethodCall {
                                        receiver: Arc::new(e),
                                        method: "is_some".to_string(),
                                        args: Vec::new(),
                                    };
                                    let link = PureExpr::BinOp(
                                        Arc::new(is_some(result_var.clone())),
                                        trust_wp_core::formula::BinOp::Eq,
                                        Arc::new(is_some(self_expr)),
                                    );
                                    if !state.path_conditions.contains(&link) {
                                        state.path_conditions.push(link);
                                    }
                                }
                            }
                        }
                        if record_path_postconditions {
                            let path_relevant_assumptions = post_effects
                                .assumptions
                                .into_iter()
                                .filter(|assumption| {
                                    postcondition_assumption_is_loop_path_relevant(
                                        assumption,
                                        &result_var,
                                    )
                                })
                                .collect();
                            append_result_guarded_postconditions(
                                &mut state.path_conditions,
                                &result_var,
                                path_relevant_assumptions,
                            );
                        }
                    }
                    if pre_call_exprs.is_some() {
                        let callee = crate::mir_analysis::call_signature(
                            tcx,
                            def_id,
                            param_names.as_deref(),
                            Some(crate::mir_analysis::CallSite { body, func }),
                        );
                        reborrow_handback =
                            Some((spec.ensures.clone(), callee, param_names, translated_args));
                    }
                }
            }
            // Arithmetic-panic mode: a call may write whatever its arguments
            // reach (`write_aliases`), and a destination without a modeled
            // result holds an unknown value of its type (never its previous
            // binding).
            if let Some(walk) = spec_ctx.arithmetic {
                if !destination_modeled {
                    havoc_local(tcx, body, walk, destination.local, &mut state.local_exprs);
                }
                // The destination was just bound (modeled result or havoc):
                // it reaches the arguments by reference flow, but re-binding
                // it here would discard the callee's stated result.
                let mut carried = super::write_aliases::locals_a_call_may_change(tcx, body, args);
                // D-140: glue the callee may run reaches further than the
                // arguments' own flow (`v.push(G(&mut c))`, then `v.clear()`).
                carried.extend(
                    super::drop_glue_writes::locals_changed_by_call(
                        tcx,
                        body,
                        bb,
                        func,
                        args,
                        destination,
                    )
                    .unwrap_or_default(),
                );
                carried.remove(&destination.local);
                if !carried.is_empty() {
                    let walk = ArithmeticWalk {
                        named_loop_carried_symbolic: false,
                        ..walk
                    };
                    rebind_loop_carried_locals(tcx, body, walk, &carried, &mut state.local_exprs);
                }
                // A re-bound local that was lent to the callee as a fresh
                // `&mut` reborrow takes the callee's stated `^p` as its
                // post-call value (literal consequence of the contract).
                if let (Some(pre_exprs), Some((ensures, callee, param_names, translated_args))) =
                    (pre_call_exprs.as_ref(), reborrow_handback.as_ref())
                {
                    super::reborrow_handback::assume_reborrow_handbacks(
                        tcx,
                        body,
                        args,
                        destination,
                        ensures,
                        callee,
                        param_names.as_deref(),
                        translated_args,
                        pre_exprs,
                        &state.local_exprs,
                        &mut state.path_conditions,
                    );
                }
            }
            // Continue to the call's return target.
            if let Some(target_bb) = target {
                collect_guarded_obligations(tcx, body, *target_bb, state, spec_ctx, obligations);
            }
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            let branch_conditions =
                switch_branch_conditions(discr, targets, &state.local_exprs, body, None)
                    .unwrap_or_default();

            for target_bb in targets.all_targets() {
                // An arm that diverges into a panic entry point
                // (`assert!`/`assert_eq!`/`panic!`/`unreachable!`) must be PROVED
                // unreachable on this path — Creusot's `Abort`. Its condition is
                // an obligation, never a silent drop. An untranslatable condition
                // fails closed as `path ==> false`.
                if block_diverges_via_panic(tcx, body, *target_bb) {
                    // A condition read through memory this walker cannot track
                    // may be stale: fail closed (see `switch_discr_is_value_stable`).
                    match branch_conditions
                        .get(target_bb)
                        .filter(|_| switch_discr_is_value_stable(tcx, body, discr, false))
                    {
                        Some(cond) => obligations.push(
                            state.condition_established,
                            wrap_with_guard(
                                &state.path_conditions,
                                PureExpr::UnOp(UnOp::Not, Arc::new(cond.clone())),
                            ),
                        ),
                        None => obligations.push_fail_closed(
                            state.condition_established,
                            &state.path_conditions,
                            fail_closed_marker("walk-panic-arm-guard-unstable"),
                        ),
                    }
                }
                let mut branch_state = state.clone();
                if let Some(cond) = branch_conditions.get(target_bb) {
                    branch_state.path_conditions.push(cond.clone());
                }
                // The in-body arm of the condition switch establishes the loop
                // condition the group's VC assumes; its exit arm does not.
                if spec_ctx.condition_switch == Some(bb) && spec_ctx.body_blocks.contains(target_bb)
                {
                    branch_state.condition_established = true;
                }
                collect_guarded_obligations(
                    tcx,
                    body,
                    *target_bb,
                    branch_state,
                    spec_ctx,
                    obligations,
                );
            }
        }
        TerminatorKind::Goto { target, .. } => {
            collect_guarded_obligations(tcx, body, *target, state, spec_ctx, obligations);
        }
        TerminatorKind::Drop { place, target, .. } => {
            if let Some(obligation) =
                super::assertion::drop_glue_obligation(tcx, body, place, spec_ctx.user_specs)
            {
                obligations.push(
                    state.condition_established,
                    wrap_with_guard(&state.path_conditions, obligation),
                );
            }
            // Drop glue runs arbitrary `Drop` impls: like a call, it may write
            // through any reachable interior mutability, and whatever the
            // dropped place reaches by reference flow (`write_aliases`).
            if let Some(walk) = spec_ctx.arithmetic {
                let mut carried =
                    super::write_aliases::locals_a_write_may_change(tcx, body, place.local);
                // D-140: the glue's own reach.
                carried.extend(
                    super::drop_glue_writes::locals_changed_by_drop(tcx, body, place)
                        .unwrap_or_default(),
                );
                if !carried.is_empty() {
                    let walk = ArithmeticWalk {
                        named_loop_carried_symbolic: false,
                        ..walk
                    };
                    rebind_loop_carried_locals(tcx, body, walk, &carried, &mut state.local_exprs);
                }
            }
            collect_guarded_obligations(tcx, body, *target, state, spec_ctx, obligations);
        }
        TerminatorKind::Assert {
            cond,
            expected,
            msg,
            target,
            ..
        } => {
            // Arithmetic panic site: owe the path-guarded obligation BEFORE
            // the assert's own condition joins the path conditions, so the
            // obligation is never guarded by itself.
            if spec_ctx.arithmetic.is_some() {
                if let Some(obligation) =
                    arithmetic_panic_obligation(tcx, cond, *expected, msg, &state.local_exprs, body)
                {
                    obligations.push(
                        state.condition_established,
                        wrap_with_guard(&state.path_conditions, obligation),
                    );
                    record_charged_assert_site(body, msg);
                }
            }
            // Built-in index bounds check: an obligation on this path, not
            // only a path fact (Creusot: `ix@ < self@.len()`).
            if let Some(obligation) = super::assertion::bounds_check_obligation(
                tcx,
                cond,
                *expected,
                msg,
                &state.local_exprs,
                body,
                false,
            ) {
                obligations.push(
                    state.condition_established,
                    wrap_with_guard(&state.path_conditions, obligation),
                );
                // Recorded only by the region walks, exactly where the
                // arithmetic sites are: their values are re-bound
                // conservatively and their obligations are kept, which is
                // what the record certifies.
                if spec_ctx.arithmetic.is_some() {
                    record_charged_assert_site(body, msg);
                }
            }
            // An assert on a path that can only diverge (e.g. before a trusted
            // inert spin) is an obligation under the path guard; its condition
            // is then not assumed for the (diverging) rest of the path.
            if block_must_diverge(body, *target, &mut HashSet::new()) {
                obligations.push(
                    state.condition_established,
                    wrap_with_guard(
                        &state.path_conditions,
                        super::assertion::diverging_path_assert_obligation(
                            tcx,
                            body,
                            cond,
                            *expected,
                            msg,
                            &state.local_exprs,
                            false,
                        ),
                    ),
                );
            } else if let Some(cond_expr) = translate_operand(cond, &state.local_exprs) {
                let asserted_cond = if *expected {
                    cond_expr
                } else {
                    PureExpr::UnOp(UnOp::Not, Arc::new(cond_expr))
                };
                state.path_conditions.push(asserted_cond);
            }
            collect_guarded_obligations(tcx, body, *target, state, spec_ctx, obligations);
        }
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => {
            collect_guarded_obligations(tcx, body, *real_target, state, spec_ctx, obligations);
        }
        // Return, Resume, Unreachable, etc. — no successors to follow.
        _ => {}
    }
}

fn append_result_guarded_postconditions(
    path_conditions: &mut Vec<PureExpr>,
    result_var: &PureExpr,
    assumptions: Vec<PureExpr>,
) {
    let PureExpr::Var(result_name, Some(ExprSort::Bool)) = result_var else {
        return;
    };

    for assumption in assumptions {
        if assumption.free_vars().contains(result_name) && !path_conditions.contains(&assumption) {
            path_conditions.push(assumption);
        }
    }
}

/// Wrap an obligation with path condition guards using implication.
///
/// If no guards are active, the obligation is returned unchanged.
/// With guards, returns `(g₁ ∧ g₂ ∧ …) ==> obligation` so that
/// the verification only checks the obligation in states where the
/// guards hold.
fn wrap_with_guard(path_conditions: &[PureExpr], obligation: PureExpr) -> PureExpr {
    if path_conditions.is_empty() {
        return obligation;
    }
    let guard = path_conditions
        .iter()
        .cloned()
        .reduce(|acc, cond| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(cond)))
        .expect("invariant: path_conditions is non-empty (checked above)");
    PureExpr::BinOp(Arc::new(guard), BinOp::Implies, Arc::new(obligation))
}

fn postcondition_assumption_is_loop_path_relevant(
    assumption: &PureExpr,
    result_var: &PureExpr,
) -> bool {
    expr_contains_expr(assumption, result_var) && !expr_mentions_iterator_state(assumption)
}

fn expr_contains_expr(expr: &PureExpr, needle: &PureExpr) -> bool {
    if expr == needle {
        return true;
    }

    match expr {
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_contains_expr(lhs, needle) || expr_contains_expr(rhs, needle)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_contains_expr(inner, needle),
        PureExpr::Let { value, body, .. } => {
            expr_contains_expr(value, needle) || expr_contains_expr(body, needle)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_contains_expr(assumption, needle) || expr_contains_expr(body, needle)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_contains_expr(obligation, needle) || expr_contains_expr(body, needle)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_expr(cond, needle)
                || expr_contains_expr(then_expr, needle)
                || expr_contains_expr(else_expr, needle)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            expr_contains_expr(body, needle)
                || triggers
                    .iter()
                    .flatten()
                    .any(|trigger| expr_contains_expr(trigger, needle))
        }
        PureExpr::LogicFnCall { args, .. } => {
            args.iter().any(|arg| expr_contains_expr(arg, needle))
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_expr(receiver, needle)
                || args.iter().any(|arg| expr_contains_expr(arg, needle))
        }
        PureExpr::Closure { body, .. } => expr_contains_expr(body, needle),
        _ => false,
    }
}

fn expr_mentions_iterator_state(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name.contains("iter_current") || name.starts_with("$for_iter_"),
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_mentions_iterator_state(lhs) || expr_mentions_iterator_state(rhs)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_mentions_iterator_state(inner),
        PureExpr::Let { value, body, .. } => {
            expr_mentions_iterator_state(value) || expr_mentions_iterator_state(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_mentions_iterator_state(assumption) || expr_mentions_iterator_state(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_mentions_iterator_state(obligation) || expr_mentions_iterator_state(body)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_mentions_iterator_state(cond)
                || expr_mentions_iterator_state(then_expr)
                || expr_mentions_iterator_state(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            expr_mentions_iterator_state(body)
                || triggers.iter().flatten().any(expr_mentions_iterator_state)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(expr_mentions_iterator_state),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_mentions_iterator_state(receiver) || args.iter().any(expr_mentions_iterator_state)
        }
        PureExpr::Closure { body, .. } => expr_mentions_iterator_state(body),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, PureExpr};

    use super::LoopBodyObligations;

    /// A marker is pushed under its path and recorded on the side it lands on,
    /// so the group that holds it knows it refutes nothing
    /// (loop_call_obligation_after_param_store_control).
    #[test]
    fn a_fail_closed_marker_is_guarded_and_recorded_on_its_side() {
        let path = PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(3)),
        );
        let mut split = LoopBodyObligations::default();
        split.push(true, path.clone());
        assert!(!split.injected_fail_closed && !split.condition_free_injected_fail_closed);
        split.push_fail_closed(true, std::slice::from_ref(&path), PureExpr::Bool(false));
        assert!(split.injected_fail_closed && !split.condition_free_injected_fail_closed);
        assert_eq!(
            split.obligations.last(),
            Some(&PureExpr::BinOp(
                Arc::new(path.clone()),
                BinOp::Implies,
                Arc::new(PureExpr::Bool(false)),
            ))
        );
        split.push_fail_closed(false, &[], PureExpr::Bool(false));
        assert!(split.condition_free_injected_fail_closed);
        assert_eq!(
            split.condition_free_obligations,
            vec![PureExpr::Bool(false)]
        );
    }
}
