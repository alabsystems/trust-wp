// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Small utility functions for MIR expression extraction.

use std::{collections::HashSet, sync::Arc};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location, Operand, Rvalue, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::Span;
use trust_wp_core::formula::{BinOp, PureExpr};

mod projected_write_facts;
mod unevaluated_const;
mod value_stability;

#[allow(unused_imports)]
pub(super) use projected_write_facts::{
    expr_references_var_name, invalidate_overlapping_projected_write_facts,
    record_projected_write_fact, translate_projected_write_lhs, wrap_projected_facts,
};
pub(super) use unevaluated_const::capture_const_body_obligations;
pub(crate) use unevaluated_const::collect_generic_assoc_const_definitions;
pub(in crate::mir_analysis) use unevaluated_const::translate_rvalue_with_enum_variants;
pub(super) use value_stability::{
    switch_discr_is_path_stable, switch_discr_is_single_call_result, switch_discr_is_value_stable,
    switch_discr_reads_frozen_memory,
};

/// Whether `name` is a positional name `name_unnamed_params` gave a
/// parameter with no source name. A source parameter spelled `arg0` is not
/// one: its name is its own.
pub(super) fn is_fallback_arg_name(name: &str) -> bool {
    // `name_unnamed_params` moves a fallback that would duplicate a real
    // parameter name into the reserved anonymous-parameter namespace.
    if let Some(rest) = name.strip_prefix(crate::mir_analysis::ANON_PARAM_PREFIX) {
        return !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit() || b == b'_');
    }
    let Some(rest) = name.strip_prefix(crate::mir_analysis::POSITIONAL_PARAM_PREFIX) else {
        return false;
    };
    !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit())
}

pub(super) fn expr_mentions_any_fallback_arg(
    expr: &PureExpr,
    fallback_arg_names: &HashSet<String>,
) -> bool {
    expr.any_free_var(|name, _| fallback_arg_names.contains(name))
}

pub(super) fn local_has_source_binding<'tcx>(
    body: &Body<'tcx>,
    local: Local,
    arg_names: &[String],
) -> bool {
    let idx = local.as_u32() as usize;
    if idx >= 1 && idx <= arg_names.len() {
        return true;
    }

    body.var_debug_info.iter().any(|info| {
        matches!(
            &info.value,
            rustc_middle::mir::VarDebugInfoContents::Place(place)
                if place.local == local && place.projection.is_empty()
        )
    })
}

/// Find the source-level name for a MIR local, if one exists.
///
/// Checks function arguments first, then var_debug_info. Returns the
/// highest-index binding (latest in source order) to handle shadowing.
pub(in crate::mir_analysis) fn source_name_for_local<'tcx>(
    body: &Body<'tcx>,
    local: Local,
    arg_names: &[String],
) -> Option<String> {
    let idx = local.as_u32() as usize;
    if idx >= 1 && idx <= arg_names.len() {
        return Some(arg_names[idx - 1].clone());
    }
    // Use the first debug binding for this local (MIR debug info is ordered
    // by source position, so the first match is the binding site).
    for info in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value {
            if place.local == local && place.projection.is_empty() {
                return Some(info.name.to_string());
            }
        }
    }
    None
}

/// Check whether a `PureExpr` contains any `Final(...)` nodes.
///
/// `Final` nodes indicate that a variable's state has been advanced by a
/// mutating closure call (e.g., `FnMut::call_mut`). When present in a
/// local's expression, the reference identity should preserve the advanced
/// state rather than reverting to a bare `Var(name)`.
pub(super) fn expr_contains_final(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Final(_)))
}

pub(super) fn span_contains_cutoff(span: Span, cutoff: Span) -> bool {
    let lhs = span.source_callsite();
    let rhs = cutoff.source_callsite();
    if lhs.is_dummy() || rhs.is_dummy() {
        return false;
    }
    lhs.lo() <= rhs.lo() && lhs.hi() >= rhs.hi()
}

pub(super) fn join_with_or(exprs: Vec<PureExpr>) -> Option<PureExpr> {
    exprs
        .into_iter()
        .reduce(|a, b| PureExpr::BinOp(Arc::new(a), BinOp::Or, Arc::new(b)))
}

pub(super) fn join_with_and(exprs: Vec<PureExpr>) -> Option<PureExpr> {
    exprs
        .into_iter()
        .reduce(|a, b| PureExpr::BinOp(Arc::new(a), BinOp::And, Arc::new(b)))
}

/// Return true when a basic block can reach the proof_assert cutoff span.
///
/// This is used to distinguish "branch does not contain this assertion point"
/// from "branch extraction failed". If a branch cannot syntactically reach the
/// cutoff span, it is safe to ignore when extracting scoped state for that
/// assertion.
pub(super) fn block_can_reach_cutoff<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    cutoff_span: Span,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        return false;
    }

    let bb_data = &body.basic_blocks[bb];
    if bb_data
        .statements
        .iter()
        .any(|stmt| span_contains_cutoff(stmt.source_info.span, cutoff_span))
    {
        return true;
    }
    if span_contains_cutoff(bb_data.terminator().source_info.span, cutoff_span) {
        return true;
    }

    let successors = match &bb_data.terminator().kind {
        TerminatorKind::Goto { target, .. }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => vec![*target],
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
        TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
        TerminatorKind::Call {
            target: Some(next), ..
        } => vec![*next],
        TerminatorKind::Return
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::Call { target: None, .. }
        | TerminatorKind::TailCall { .. }
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. } => return false,
    };

    successors
        .into_iter()
        .any(|target| block_can_reach_cutoff(body, target, cutoff_span, visited))
}

/// Return true when a basic block can reach the proof_assert cutoff location.
///
/// This is the location-precise counterpart to `block_can_reach_cutoff`.
pub(super) fn block_can_reach_location<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    cutoff_location: Location,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        return false;
    }

    if bb == cutoff_location.block {
        return true;
    }

    let bb_data = &body.basic_blocks[bb];
    let successors = match &bb_data.terminator().kind {
        TerminatorKind::Goto { target, .. }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => vec![*target],
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
        TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
        TerminatorKind::Call {
            target: Some(next), ..
        } => vec![*next],
        TerminatorKind::Return
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::Call { target: None, .. }
        | TerminatorKind::TailCall { .. }
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. } => return false,
    };

    successors
        .into_iter()
        .any(|target| block_can_reach_location(body, target, cutoff_location, visited))
}

/// Return true when every path from `bb` diverges before returning.
///
/// This is used by scoped proof_assert extraction to drop panic-only branches.
/// If a branch provably diverges, it cannot reach the assertion point.
pub(in crate::mir_analysis) fn block_must_diverge<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        // A cycle back to an already-visited block means this path loops
        // without reaching `Return`. Since `SwitchInt` uses `all()` (every
        // branch must diverge), any branch that can reach `Return` will have
        // already returned `false` before the cycle is encountered. Therefore
        // a cycle on the remaining path is genuinely divergent (infinite loop).
        // This handles `loop {}` and abort-based unreachable match arms.
        return true;
    }

    let term = body.basic_blocks[bb].terminator();
    match &term.kind {
        TerminatorKind::Call { target: None, .. } => true,
        TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable
        | TerminatorKind::CoroutineDrop => true,
        TerminatorKind::Return => false,
        TerminatorKind::Goto { target, .. }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => block_must_diverge(body, *target, visited),
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => {
            block_must_diverge(body, *real_target, visited)
        }
        TerminatorKind::SwitchInt { targets, .. } => targets
            .all_targets()
            .iter()
            .copied()
            .all(|target| block_must_diverge(body, target, visited)),
        TerminatorKind::Call {
            target: Some(next), ..
        } => block_must_diverge(body, *next, visited),
        TerminatorKind::TailCall { .. }
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. } => false,
    }
}

/// Return true when a call to `def_id` must be treated like a panic: the arm
/// that reaches it must be PROVED unreachable (Creusot's `Abort`), never
/// assumed away.
///
/// Covers:
/// * std/core/alloc panic entry points — the callee a plain `assert!`,
///   `assert_eq!`/`assert_ne!` (`assert_failed`), `panic!`, `unreachable!`,
///   `todo!`, or a const-panic (`panic_const_*`) lowers to — and the other
///   library calls that never return (`process::abort`/`exit`,
///   `alloc::handle_alloc_error`, ...);
/// * EVERY `-> !` function without a visible, inert local body: any foreign
///   `-> !` function (std/core/alloc or another crate) and any `extern`
///   block item. Creusot gives an external function with no contract an
///   impossible precondition, so reaching one must be proved impossible;
/// * a LOCAL `-> !` function whose body is not trivially inert (it may call
///   something, panic on an `Assert`, or evaluate arithmetic) — see
///   [`local_never_fn_body_is_inert`].
///
/// A local `-> !` function whose body provably does nothing but spin
/// (`fn spin() -> ! { loop {} }`) keeps the #1075/#1401 surviving-path
/// treatment: its continuation is unreachable, and no panic can happen.
///
/// Classification is by `DefId` provenance (`tcx.crate_name(def_id.krate)` for
/// the library list, `is_local`/`is_foreign_item` for the `-> !` rule), never
/// by a printed path. Over-approximating here only turns an assumption into an
/// obligation, so it can cost completeness but never soundness.
/// (Overlaps with the s38 `provenance` helper, `ItemProvenance::Std`; kept
/// local because that helper is not merged into this branch. Same crate set:
/// core, alloc, std.)
pub(super) fn is_panic_entry_point(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if is_library_panic_entry_point(tcx, def_id) {
        return true;
    }
    if !fn_returns_never(tcx, def_id) {
        return false;
    }
    if !def_id.is_local() || tcx.is_foreign_item(def_id) {
        return true;
    }
    !local_never_fn_body_is_inert(tcx, def_id)
}

fn is_library_panic_entry_point(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if def_id.is_local() {
        return false;
    }
    let krate = tcx.crate_name(def_id.krate);
    if !matches!(krate.as_str(), "core" | "alloc" | "std") {
        return false;
    }
    let segments: Vec<String> = tcx
        .def_path(def_id)
        .data
        .iter()
        .filter_map(|component| component.data.get_opt_name())
        .map(|name| name.to_string())
        .collect();
    let segments: Vec<&str> = segments.iter().map(String::as_str).collect();
    match segments.as_slice() {
        ["panicking", ..] => true,
        ["rt", "begin_panic"] => true,
        // Other library calls that never return to the caller. Creusot gives
        // none of them a satisfiable way to reach the next statement:
        // `hint::unreachable_unchecked` is `#[requires(false)]` in creusot-std,
        // and the rest are unspecified diverging externs (panic/abort/exit).
        // Their reachability must be PROVED impossible, never assumed.
        ["panic", "panic_any" | "resume_unwind" | "begin_panic"]
        | ["process", "abort" | "exit"]
        | ["intrinsics", "abort" | "unreachable"]
        | ["hint", "unreachable_unchecked"]
        | ["alloc", "handle_alloc_error" | "rust_oom" | "__rdl_oom"]
        | ["raw_vec", "capacity_overflow" | "handle_error"] => true,
        _ => false,
    }
}

/// The concrete callee of a diverging call (`target: None`) that may be
/// trusted as an inert spin: the call's continuation is unreachable, and
/// reaching the call cannot panic.
///
/// Returns `Some(resolved)` ONLY when all of these hold:
/// * the callee operand is a constant `FnDef` (no fn pointer, no `dyn`);
/// * it is not a library panic entry point;
/// * `Instance::try_resolve` with the call-site generic args, in the caller's
///   post-analysis typing environment, selects exactly one
///   `InstanceKind::Item` — no trait dispatch is left (an unresolved
///   `T::die()` resolves to `None`), no shim, no virtual call;
/// * the resolved item is LOCAL and its body is trivially inert
///   ([`local_never_fn_body_is_inert`]) — so a trait default body is judged
///   only when it is the body that actually runs.
///
/// Anything else returns `None` and the call is a panic leaf. Failing to
/// resolve only turns an assumption into an obligation (completeness cost,
/// never soundness).
pub(super) fn trusted_inert_spin_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
) -> Option<DefId> {
    use rustc_middle::ty::{Instance, InstanceKind, TypeVisitableExt, TypingEnv};
    let rustc_middle::mir::Operand::Constant(constant) = func else {
        return None;
    };
    let rustc_middle::ty::TyKind::FnDef(def_id, args) = constant.const_.ty().kind() else {
        return None;
    };
    if is_library_panic_entry_point(tcx, *def_id) {
        return None;
    }
    // Resolution normalizes; an unnormalizable projection can ICE, so refuse
    // (fail closed) rather than risk it.
    if args.has_aliases() || args.has_escaping_bound_vars() {
        return None;
    }
    let args = tcx.erase_and_anonymize_regions(*args);
    let typing_env = TypingEnv::post_analysis(tcx, body.source.def_id());
    let instance = Instance::try_resolve(tcx, typing_env, *def_id, args.skip_binder())
        .ok()
        .flatten()?;
    let InstanceKind::Item(resolved) = instance.def else {
        return None;
    };
    (resolved.is_local()
        && !tcx.is_foreign_item(resolved)
        && local_never_fn_body_is_inert(tcx, resolved))
    .then_some(resolved)
}

/// True when `def_id` is a function (free, associated, or `extern` block item)
/// whose declared return type is `!`.
fn fn_returns_never(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    use rustc_hir::def::DefKind;
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }
    tcx.fn_sig(def_id)
        .skip_binder()
        .output()
        .skip_binder()
        .is_never()
}

/// True when the borrow-checked MIR of the LOCAL function `def_id` is visible
/// and every block reachable from the entry along normal (non-unwind) edges
/// does nothing that can panic, call, or have an effect: its terminators are
/// only `Goto`/`FalseEdge`/`FalseUnwind`/`SwitchInt`, and its statements carry
/// no arithmetic (`BinaryOp`/`UnaryOp`, which may overflow in Creusot's
/// semantics even when the build disabled overflow checks) and no assignment
/// through a projection. `fn spin() -> ! { loop {} }` qualifies.
///
/// Anything else — no body in the cache, a `Call`, an `Assert`, a `Drop`,
/// `Unreachable` — is NOT inert, and calls to it are treated as panics.
fn local_never_fn_body_is_inert(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    use rustc_middle::mir::StatementKind;
    let Some(local_def_id) = def_id.as_local() else {
        return false;
    };
    let Some(body_with_facts) = crate::callbacks::try_get_body_with_context(tcx, local_def_id)
    else {
        return false;
    };
    let body = &body_with_facts.body;
    let mut visited = HashSet::new();
    let mut worklist = vec![rustc_middle::mir::START_BLOCK];
    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        let data = &body.basic_blocks[bb];
        for stmt in &data.statements {
            match &stmt.kind {
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::FakeRead(_)
                | StatementKind::PlaceMention(_)
                | StatementKind::Coverage(_)
                | StatementKind::ConstEvalCounter
                | StatementKind::BackwardIncompatibleDropHint { .. }
                | StatementKind::AscribeUserType(..) => {}
                StatementKind::Assign((place, rvalue)) => {
                    if !place.projection.is_empty()
                        || matches!(rvalue, Rvalue::BinaryOp(..) | Rvalue::UnaryOp(..))
                    {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        match &data.terminator().kind {
            TerminatorKind::Goto { target, .. } => worklist.push(*target),
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => worklist.push(*real_target),
            TerminatorKind::SwitchInt { targets, .. } => {
                worklist.extend(targets.all_targets().iter().copied());
            }
            _ => return false,
        }
    }
    true
}

/// Return true when the function body can never reach `Return`: every path
/// from the entry block diverges, and at least one diverging leaf is a panic
/// entry point ([`is_panic_entry_point`]).
///
/// Such a body has no final state, so no switch arm carries the panic
/// obligation (there is no switch): the caller must emit the obligation that
/// the entry itself is unreachable (`false` under the preconditions). An
/// over-approximation (a user `-> !` leaf beside the panic) only adds an
/// obligation — completeness cost, never soundness.
pub(crate) fn body_entry_diverges_via_panic<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    block_diverges_via_panic(tcx, body, rustc_middle::mir::START_BLOCK)
}

/// Return true when a block reachable from the entry along normal (non-unwind)
/// edges ends in a call that never returns and is NOT a trusted inert spin
/// ([`trusted_inert_spin_callee`]).
///
/// This is Creusot's `Terminator::Abort` site set minus the MIR `Unreachable`
/// terminator: a `panic!`, an `assert!`'s failing arm, an `unreachable!`,
/// `abort`/`exit`, or any `-> !` callee whose body is not a provable spin.
/// Every such arm is charged "prove this arm unreachable" by the switch lanes,
/// and a body with no reachable `Return` is charged by
/// [`body_entry_diverges_via_panic`]. A function that reaches one therefore
/// owes a goal whether or not it carries a contract of its own — which is what
/// makes this the discovery predicate for a contract-free verification target.
///
/// The MIR `Unreachable` terminator is deliberately NOT a site here. Creusot
/// emits an `Abort` for it too, but in post-borrowck MIR rustc emits it only
/// for an edge its own exhaustiveness check proved dead (the otherwise arm of
/// a discriminant switch, an uninhabited scrutinee, an exhausted slice-length
/// switch), so trust-wp discharges it from the type system and states no goal.
/// Counting it here would make a body a verification target for an obligation
/// no lane emits: credit without a statement.
pub(crate) fn body_reaches_diverging_call<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    let mut visited = HashSet::new();
    let mut worklist = vec![rustc_middle::mir::START_BLOCK];
    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        let data = &body.basic_blocks[bb];
        if data.is_cleanup {
            continue;
        }
        let terminator = data.terminator();
        if let TerminatorKind::Call {
            func, target: None, ..
        } = &terminator.kind
        {
            if trusted_inert_spin_callee(tcx, body, func).is_none() {
                return true;
            }
        }
        for successor in terminator.successors() {
            if !body.basic_blocks[successor].is_cleanup {
                worklist.push(successor);
            }
        }
    }
    false
}

/// Return true when a block reachable from the entry along normal (non-unwind)
/// edges ends in an `Assert` terminator: a runtime check rustc inserted — an
/// index bounds check on an array or slice, a machine-integer overflow,
/// negation, shift, division or remainder check, or any other kind.
///
/// Creusot states every such check as a goal of the program function it sits
/// in (`index in bounds`; the integer operation's program-function
/// precondition), contract or no contract, and the extraction lanes charge
/// the bounds and arithmetic kinds (`bounds_check_obligation`,
/// `arithmetic_panic_obligation`). Every kind counts here, not only those two:
/// a kind no lane charges still makes the body a target, where
/// `unchecked_panic_sites` keeps its verdict below `verified`. Making a body a
/// target only adds obligations; reading "no charged kind" as "no goal owed"
/// would be the under-approximation that left
/// contract_free_index_bounds_uncharged.rs examined by nobody.
pub(crate) fn body_reaches_runtime_check(body: &Body<'_>) -> bool {
    let mut visited = HashSet::new();
    let mut worklist = vec![rustc_middle::mir::START_BLOCK];
    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        let data = &body.basic_blocks[bb];
        if data.is_cleanup {
            continue;
        }
        let terminator = data.terminator();
        if matches!(terminator.kind, TerminatorKind::Assert { .. }) {
            return true;
        }
        for successor in terminator.successors() {
            if !body.basic_blocks[successor].is_cleanup {
                worklist.push(successor);
            }
        }
    }
    false
}

/// Return true when a block reachable from the entry along normal (non-unwind)
/// edges ends in an `Assert` or a `Call` terminator: a place where the body
/// can carry a proof obligation (an overflow / bounds / `assert!` check, a
/// callee precondition, a panic entry point).
///
/// Used to fail closed when context extraction gave up part-way: if the body
/// has such a site, an obligation may never have been walked, so a `Verified`
/// verdict for the function contract cannot be trusted.
pub(crate) fn body_has_reachable_obligation_source(body: &Body<'_>) -> bool {
    let mut visited = HashSet::new();
    let mut worklist = vec![rustc_middle::mir::START_BLOCK];
    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        let data = &body.basic_blocks[bb];
        if data.is_cleanup {
            continue;
        }
        match &data.terminator().kind {
            TerminatorKind::Assert { .. } | TerminatorKind::Call { .. } => return true,
            TerminatorKind::Goto { target, .. } | TerminatorKind::Drop { target, .. } => {
                worklist.push(*target);
            }
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => worklist.push(*real_target),
            TerminatorKind::SwitchInt { targets, .. } => {
                worklist.extend(targets.all_targets().iter().copied());
            }
            _ => {}
        }
    }
    false
}

/// Return true when every path from `bb` diverges AND at least one diverging
/// leaf reachable along non-unwind edges is a call to a panic entry point
/// ([`is_panic_entry_point`]).
///
/// Over-approximating "panic" only ever turns an assumption into an
/// obligation, so a mixed arm (panic on one path, user `-> !` on another) is
/// classified as a panic arm: that costs completeness, never soundness.
pub(super) fn block_diverges_via_panic<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
) -> bool {
    block_must_diverge(body, bb, &mut HashSet::new())
        && block_reaches_panic_call(tcx, body, bb, &mut HashSet::new())
}

fn block_reaches_panic_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        return false;
    }
    match &body.basic_blocks[bb].terminator().kind {
        TerminatorKind::Call { func, target, .. } => {
            let Some(next) = target else {
                // A call that never returns (`target: None` — a `-> !` callee,
                // or any callee whose return type is uninhabited: an empty
                // enum, `Infallible`, ...) is a panic leaf unless it is a
                // trusted inert spin (see `trusted_inert_spin_callee`). A fn
                // pointer, `dyn Fn`, unresolved trait dispatch, foreign or
                // non-inert callee may panic, so its arm must be PROVED
                // unreachable.
                return trusted_inert_spin_callee(tcx, body, func).is_none();
            };
            if crate::mir_analysis::call_resolve::extract_call_def_id(func)
                .is_some_and(|def_id| is_panic_entry_point(tcx, def_id))
            {
                return true;
            }
            block_reaches_panic_call(tcx, body, *next, visited)
        }
        TerminatorKind::Goto { target, .. }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => {
            block_reaches_panic_call(tcx, body, *target, visited)
        }
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => {
            block_reaches_panic_call(tcx, body, *real_target, visited)
        }
        TerminatorKind::SwitchInt { targets, .. } => targets
            .all_targets()
            .iter()
            .any(|target| block_reaches_panic_call(tcx, body, *target, visited)),
        _ => false,
    }
}

/// Return true when every path from `bb` eventually reaches a `Return`
/// terminator (without diverging).
///
/// This detects early-return branches in try-operator (`?`) desugaring.
/// When MIR desugars `x?`, one branch of the `SwitchInt` on the
/// `ControlFlow` discriminant leads to `FromResidual::from_residual()`
/// followed by `Return`. Body extraction fails on that branch because
/// the early return doesn't contribute to the function's final return
/// expression. This helper identifies such branches so the non-boolean
/// `SwitchInt` handler can skip them and keep the surviving branch.
pub(super) fn block_must_early_return<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    visited: &mut HashSet<BasicBlock>,
) -> bool {
    if !visited.insert(bb) {
        return false;
    }

    let term = body.basic_blocks[bb].terminator();
    match &term.kind {
        TerminatorKind::Return => true,
        // Divergent terminators are NOT early returns.
        TerminatorKind::Call { target: None, .. }
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable
        | TerminatorKind::CoroutineDrop => false,
        TerminatorKind::Goto { target, .. }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Assert { target, .. } => block_must_early_return(body, *target, visited),
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => {
            block_must_early_return(body, *real_target, visited)
        }
        TerminatorKind::SwitchInt { targets, .. } => targets
            .all_targets()
            .iter()
            .copied()
            .all(|target| block_must_early_return(body, target, visited)),
        TerminatorKind::Call {
            target: Some(next), ..
        } => block_must_early_return(body, *next, visited),
        TerminatorKind::TailCall { .. }
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. } => false,
    }
}

/// Check whether an rvalue reads from a specific local (possibly through projection).
pub(super) fn rvalue_reads_from_local(rvalue: &Rvalue<'_>, local: Local) -> bool {
    match rvalue {
        // WithRetag does not change which local the operand reads.
        Rvalue::Use(operand, _) | Rvalue::Cast(_, operand, _) => operand_uses_local(operand, local),
        Rvalue::Ref(_, _, place) | Rvalue::Reborrow(_, _, place) | Rvalue::Discriminant(place) => {
            place.local == local
        }
        Rvalue::Aggregate(_, operands) => operands.iter().any(|op| operand_uses_local(op, local)),
        _ => false,
    }
}

/// Check whether an operand references a specific local.
pub(super) fn operand_uses_local(operand: &Operand<'_>, local: Local) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.local == local,
        Operand::Constant(_) | Operand::RuntimeChecks(_) => false,
    }
}
