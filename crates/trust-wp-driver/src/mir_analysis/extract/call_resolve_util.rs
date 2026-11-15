// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-site resolution utilities for MIR extraction.
//!
//! Low-level helpers for resolving function call targets, array `.len()`
//! folding, const-generic argument translation, and call-site side-effect
//! isolation. Used by `call_spec`, `spanned_extract`, and
//! `substitution::call_resolution`.

use std::sync::Arc;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, ProjectionElem, Rvalue, StatementKind},
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::{
    call_resolve::extract_call_def_id,
    diagnostics::{record_extraction_diag, ExtractionDiagKind, ExtractionDiagnosticSink},
    effects::CallEffects,
    spec_apply::TranslatedArg,
};

// ── Constants ───────────────────────────────────────────────────────

const MAX_ARRAY_LEN_BACKTRACK_DEPTH: usize = 8;
const MAX_CALL_DEF_BACKTRACK_DEPTH: usize = 8;

// ── Box::new path detection ─────────────────────────────────────────

pub(super) fn is_box_new_call_path(path: &str) -> bool {
    path.ends_with("::new") && path.contains("boxed::Box")
}

// ── Type-level const and array length translation ───────────────────

/// Translate a type-level array length const to a pure expression.
///
/// Supports concrete evaluable constants (`[T; 5]`) and const params
/// (`[T; N]`), returning either `Int(5)` or `Var("N")`.
fn translate_ty_const_len_expr(len_const: rustc_middle::ty::Const<'_>) -> Option<PureExpr> {
    if let Some(value) = len_const.try_to_value() {
        // The Trust toolchain exposes `try_to_scalar` on `ty::Value`, not on `ValTree`.
        let scalar = value
            .try_to_scalar()
            .and_then(|s| s.try_to_scalar_int().ok())?;
        let n = scalar.to_uint(scalar.size());
        return i64::try_from(n).ok().map(PureExpr::Int);
    }
    match len_const.kind() {
        rustc_middle::ty::ConstKind::Param(param) => Some(PureExpr::Var(
            param.name.as_str().to_string(),
            Some(ExprSort::Int),
        )),
        _ => None,
    }
}

fn array_len_from_ty(ty: rustc_middle::ty::Ty<'_>) -> Option<PureExpr> {
    match ty.peel_refs().kind() {
        rustc_middle::ty::TyKind::Array(_, len_const) => translate_ty_const_len_expr(*len_const),
        _ => None,
    }
}

pub(super) fn translate_const_generic_arg_expr(c: rustc_middle::ty::Const<'_>) -> Option<PureExpr> {
    use rustc_middle::ty::TyKind;
    if let Some(value) = c.try_to_value() {
        match value.ty.kind() {
            TyKind::Int(_) => {
                // The Trust toolchain exposes `try_to_scalar` on `ty::Value`, not on `ValTree`.
                let scalar = value
                    .try_to_scalar()
                    .and_then(|s| s.try_to_scalar_int().ok())?;
                let bits = scalar.to_int(scalar.size());
                return i64::try_from(bits).ok().map(PureExpr::Int);
            }
            TyKind::Uint(_) => {
                // The Trust toolchain exposes `try_to_scalar` on `ty::Value`, not on `ValTree`.
                let scalar = value
                    .try_to_scalar()
                    .and_then(|s| s.try_to_scalar_int().ok())?;
                let bits = scalar.to_uint(scalar.size());
                return i64::try_from(bits).ok().map(PureExpr::Int);
            }
            TyKind::Bool => {
                // The Trust toolchain exposes `try_to_scalar` on `ty::Value`, not on `ValTree`.
                let scalar = value
                    .try_to_scalar()
                    .and_then(|s| s.try_to_scalar_int().ok())?;
                return Some(PureExpr::Bool(scalar.to_uint(scalar.size()) != 0));
            }
            _ => {}
        }
    }
    match c.kind() {
        rustc_middle::ty::ConstKind::Param(param) => {
            // Const generic params are typically integral (Int/Uint) or Bool.
            // Int is correct for the vast majority (array lengths, counts).
            // Bool const generics would need the type from GenericParamDef
            // to get ExprSort::Bool — a known limitation.
            Some(PureExpr::Var(
                param.name.as_str().to_string(),
                Some(ExprSort::Int),
            ))
        }
        _ => None,
    }
}

pub(super) fn extend_call_with_const_generic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    func: &Operand<'tcx>,
    translated_args: &mut Vec<TranslatedArg>,
    param_names: &mut Vec<String>,
) {
    use rustc_middle::ty::TyKind;
    let Operand::Constant(deref!(constant)) = func else {
        return;
    };
    let TyKind::FnDef(_, substs) = constant.ty().kind() else {
        return;
    };
    let substs = substs.skip_binder();

    let generics = tcx.generics_of(callee_def_id);
    // Skip parent generic args — `substs` contains ALL args (parent + own),
    // but `own_params` only lists this function's own parameters. Without the
    // skip, own_params[i] is paired with the parent's substs[i], causing const
    // generics on methods of generic types to be silently dropped. (#2356)
    for (param_def, generic_arg) in generics
        .own_params
        .iter()
        .zip(substs.iter().skip(generics.parent_count))
    {
        if !matches!(
            param_def.kind,
            rustc_middle::ty::GenericParamDefKind::Const { .. }
        ) {
            continue;
        }
        let Some(actual_const) = generic_arg.as_const() else {
            continue;
        };
        let Some(actual_expr) = translate_const_generic_arg_expr(actual_const) else {
            continue;
        };
        param_names.push(param_def.name.as_str().to_string());
        translated_args.push(TranslatedArg::new(actual_expr));
    }
}

// ── Array length resolution with backtracking ───────────────────────

fn array_len_from_place<'tcx>(
    body: &Body<'tcx>,
    place: rustc_middle::mir::Place<'tcx>,
) -> Option<PureExpr> {
    array_len_from_ty(body.local_decls[place.local].ty)
}

/// Extract `[T; N]::len()` result directly from receiver type information.
fn array_len_from_operand<'tcx>(body: &Body<'tcx>, operand: &Operand<'tcx>) -> Option<PureExpr> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => array_len_from_place(body, *place),
        Operand::Constant(constant) => array_len_from_ty(constant.ty()),
        Operand::RuntimeChecks(_) => None,
    }
}

fn find_local_assignment_rvalue<'a, 'tcx>(
    body: &'a Body<'tcx>,
    bb: BasicBlock,
    local: Local,
) -> Option<&'a Rvalue<'tcx>> {
    body.basic_blocks[bb]
        .statements
        .iter()
        .rev()
        .find_map(|stmt| {
            let StatementKind::Assign((lhs, rvalue)) = &stmt.kind else {
                return None;
            };
            (lhs.local == local && lhs.projection.is_empty()).then_some(rvalue)
        })
}

// ── Loop-body call-target classification ────────────────────────────

/// Paths of the `Fn*` trait call methods. A call to one of these with a
/// GENERIC self type is Creusot's `precondition_F f args` goal, which neither
/// loop lane can state.
const FN_TRAIT_CALL_PATHS: &[&str] = &[
    "core::ops::Fn::call",
    "std::ops::Fn::call",
    "core::ops::FnMut::call_mut",
    "std::ops::FnMut::call_mut",
    "core::ops::FnOnce::call_once",
    "std::ops::FnOnce::call_once",
];

/// What a call terminator inside a LOOP BODY resolves to.
///
/// Both loop lanes — `loop_body.rs` (a loop carrying `#[invariant]`/
/// `#[variant]`) and `unannotated_loops.rs` (every other loop, which is the
/// DEFAULT lane) — must agree about which call sites owe an undischargeable
/// obligation, so the decision lives here and not in either lane. Two copies
/// drift: an unannotated lane that drops every non-`FnDef` callee silently
/// lets a violated precondition behind a fn pointer verify
/// (`s62_fnptr_unannotated_loop`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LoopCallTarget {
    /// The call site can hold exactly one callee, whose contract applies here.
    Resolved(DefId),
    /// A call through a generic `Fn*` bound (`F: Fn(..)`, self type is a type
    /// parameter). The callee's precondition is `precondition_F f args`, a
    /// goal no lane can state: it is OWED and no proof discharges it.
    GenericFnTrait,
    /// No unique callee: a fn-pointer parameter or reassigned local, a `dyn`
    /// vtable dispatch, an indirect call. Its precondition is unknown, and an
    /// unknown precondition is owed, never dropped.
    Unresolved,
}

/// Classify a loop-body call terminator's target.
///
/// A direct `FnDef` constant resolves to itself; a call through a local
/// resolves only when [`resolve_unique_call_fn_def`] proves the local can hold
/// nothing else. Anything else is [`LoopCallTarget::Unresolved`].
///
/// ONE DECISION, ONE IMPLEMENTATION. `Resolved` is what buys a callee its
/// credit here — the lane assumes its postcondition — so it is granted only
/// when the OBLIGATION side ([`resolve_obligation_callee`], which is what
/// `assertion::call_type_obligation` resolves through) reaches the SAME callee
/// at the SAME site. Credit and obligation therefore quantify over one set by
/// construction, and narrowing either side narrows both.
///
/// This is not hypothetical bookkeeping: a grant side that searches the whole
/// body beside an obligation side that scans only `body.basic_blocks[bb]
/// .statements` credits a fn pointer assigned BEFORE a loop and called inside
/// it while owing nothing, and `fn evil(n: u32) { let f: fn(D) -> u32 =
/// make::<D>; while i < n { need7(f(D)) } }` verifies with `D::drop`
/// panicking on every iteration (`s62v2_preloop_fnptr_credit_no_owe`).
pub(super) fn classify_loop_call_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
) -> LoopCallTarget {
    if is_generic_fn_trait_call(tcx, func) {
        return LoopCallTarget::GenericFnTrait;
    }
    let Some(def_id) = extract_call_def_id(func)
        .or_else(|| resolve_unique_call_fn_def(body, func).map(|(def_id, _)| def_id))
    else {
        return LoopCallTarget::Unresolved;
    };
    match resolve_obligation_callee(tcx, body, bb, func) {
        Some((owing_def_id, _)) if owing_def_id == def_id => LoopCallTarget::Resolved(def_id),
        // The obligation side cannot see this callee (or sees a different
        // one): crediting here would assume a contract at a site owing
        // nothing. Fail closed — the caller emits `false`.
        _ => LoopCallTarget::Unresolved,
    }
}

/// The callee the type-driven call OBLIGATIONS resolve through — the UNION of
/// every chain any lane credits a contract from, so that a credit anywhere
/// implies the obligation here.
///
/// 1. the `FnDef` the operand's own type carries (a direct call, and a call
///    through a local holding a zero-sized fn ITEM);
/// 2. the `FnDef` constant the BLOCK-LOCAL backtracker reaches
///    ([`resolve_call_fn_def`]) — what the primary extractor's `resolve_call`
///    credits from;
/// 3. the `FnDef` constant the WHOLE-BODY backtracker reaches
///    ([`resolve_unique_call_fn_def`]) — what the loop lanes'
///    [`classify_loop_call_target`] credits from.
///
/// (3) never guesses: every local on the way must have exactly one assignment
/// in the whole body and must never be mutably or raw-borrowed, so widening
/// the union with it only ever resolves MORE sites, and a resolved site can
/// only gain a `false` obligation. The widening is monotone in the safe
/// direction.
///
/// `None` means no chain pins the target down (a fn-pointer parameter, a `dyn`
/// vtable, a reassigned local). Every lane reaches `None` too and credits no
/// contract there, so no obligation is owed for a credit that is not granted.
pub(super) fn resolve_obligation_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgs<'tcx>)> {
    if let rustc_middle::ty::TyKind::FnDef(def_id, generic_args) =
        func.ty(&body.local_decls, tcx).kind()
    {
        return Some((*def_id, generic_args.skip_binder()));
    }
    resolve_call_fn_def(body, bb, func, None).or_else(|| resolve_unique_call_fn_def(body, func))
}

/// `true` for `<F as Fn*>::call*` where the self type is a type PARAMETER —
/// the callee is whatever the caller passed, so its precondition is opaque.
/// A concrete closure or fn item as self type is NOT this case: those resolve
/// to a `DefId` whose contract can be looked up.
pub(super) fn is_generic_fn_trait_call<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    let Operand::Constant(deref!(constant)) = func else {
        return false;
    };
    let rustc_middle::ty::TyKind::FnDef(callee, generic_args) = constant.const_.ty().kind() else {
        return false;
    };
    FN_TRAIT_CALL_PATHS.contains(&tcx.def_path_str(*callee).as_str())
        && generic_args
            .skip_binder()
            .first()
            .and_then(|arg| arg.as_type())
            .is_some_and(|self_ty| {
                matches!(
                    self_ty.peel_refs().kind(),
                    rustc_middle::ty::TyKind::Param(_)
                )
            })
}

/// The `FnDef` (with its generic arguments) a call's `func` operand denotes,
/// following fn-pointer locals back to the constant they were initialised
/// from: `let f: fn(u8, u8) -> u8 = <u8 as Add>::add; f(x, 1)`.
///
/// Unlike [`resolve_call_def_id`] this never guesses: every local on the way
/// must have exactly ONE assignment in the whole body and must never be
/// borrowed mutably or through a raw pointer, so the resolved target is the
/// only value the operand can hold at the call. `None` means the target is
/// unknown (a fn-pointer parameter, a reassigned local, a `dyn` vtable, ...).
pub(super) fn resolve_unique_call_fn_def<'tcx>(
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgs<'tcx>)> {
    if let Some(def) = func.const_fn_def() {
        return Some(def);
    }
    let base_local = |place: &rustc_middle::mir::Place<'tcx>| match place.projection.as_slice() {
        [] | [ProjectionElem::Deref] => Some(place.local),
        _ => None,
    };
    let mut current = match func {
        Operand::Copy(place) | Operand::Move(place) => base_local(place)?,
        _ => return None,
    };
    for _ in 0..MAX_CALL_DEF_BACKTRACK_DEPTH {
        let mut assignment = None;
        let mut count = 0usize;
        for bb_data in body.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                match &stmt.kind {
                    StatementKind::Assign((lhs, rvalue)) => {
                        if lhs.local == current {
                            count += 1;
                            if lhs.projection.is_empty() {
                                assignment = Some(rvalue);
                            } else {
                                return None;
                            }
                        }
                        if let Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Mut { .. }, place)
                        | Rvalue::RawPtr(_, place) = rvalue
                        {
                            if place.local == current {
                                return None;
                            }
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } if place.local == current => {
                        return None;
                    }
                    _ => {}
                }
            }
            if let Some(terminator) = &bb_data.terminator {
                if let rustc_middle::mir::TerminatorKind::Call { destination, .. } =
                    &terminator.kind
                {
                    if destination.local == current {
                        return None;
                    }
                }
            }
        }
        if count != 1 || current.as_usize() <= body.arg_count {
            return None;
        }
        match assignment? {
            Rvalue::Use(Operand::Constant(deref!(constant)), _)
            | Rvalue::Cast(_, Operand::Constant(deref!(constant)), _) => {
                let ty = constant.const_.ty();
                let inner = match ty.kind() {
                    rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
                    _ => ty,
                };
                return match inner.kind() {
                    rustc_middle::ty::TyKind::FnDef(def_id, args) => {
                        Some((*def_id, args.skip_binder()))
                    }
                    _ => None,
                };
            }
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
            | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
            | Rvalue::Ref(_, _, place)
            | Rvalue::CopyForDeref(place) => {
                current = base_local(place)?;
            }
            _ => return None,
        }
    }
    None
}

pub(super) fn resolve_call_def_id<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    diagnostics: Option<&ExtractionDiagnosticSink>,
) -> Option<DefId> {
    resolve_call_fn_def(body, bb, func, diagnostics).map(|(def_id, _)| def_id)
}

/// [`resolve_call_def_id`] carrying the callee's generic arguments.
///
/// The `DefId`-only wrapper above is what `resolve_call` uses to look up the
/// contract it credits at a call site; the type-driven call obligations in
/// `extract::assertion` need the same callee's INSTANTIATION as well (which
/// types a generic parameter was substituted with), so both read this one
/// function. Keeping them on one resolver is what makes the rule hold: if a
/// callee's postcondition is credited at a call site, every obligation that
/// callee's instantiation owes is owed at that same site. While the
/// obligations keyed on `TyKind::FnDef` alone and this chain followed
/// fn-pointer locals, one `let f: fn(&Cell<u8>) -> bool =
/// conflate::<Cell<u8>>; f(c)` coercion credited a postcondition and owed
/// nothing.
pub(super) fn resolve_call_fn_def<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    diagnostics: Option<&ExtractionDiagnosticSink>,
) -> Option<(DefId, rustc_middle::ty::GenericArgs<'tcx>)> {
    if let Operand::Constant(deref!(constant)) = func {
        if let rustc_middle::ty::TyKind::FnDef(def_id, generic_args) = constant.const_.ty().kind() {
            return Some((*def_id, generic_args.skip_binder()));
        }
    }

    let mut current_local = match func {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        // Function pointer calls through references: `(*_1)()` where _1 is
        // a `&fn()` reference. The func operand has a Deref projection; start
        // backtracking from the base local so we can resolve through the
        // reference chain to the underlying FnDef. (#1588)
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.len() == 1
                && matches!(place.projection[0], ProjectionElem::Deref) =>
        {
            Some(place.local)
        }
        _ => None,
    };

    for _ in 0..MAX_CALL_DEF_BACKTRACK_DEPTH {
        let Some(local) = current_local else {
            record_extraction_diag(
                diagnostics,
                "extract/call_resolve_util.rs",
                ExtractionDiagKind::CallResolutionBacktrackFailed,
                "call target backtracking lost the current local",
                None,
            );
            return None;
        };
        let Some(rvalue) = find_local_assignment_rvalue(body, bb, local) else {
            record_extraction_diag(
                diagnostics,
                "extract/call_resolve_util.rs",
                ExtractionDiagKind::CallResolutionBacktrackFailed,
                format!("no assignment found while backtracking call target local {local:?}"),
                None,
            );
            return None;
        };
        match rvalue {
            Rvalue::Use(Operand::Constant(deref!(constant)), _)
            | Rvalue::Cast(_, Operand::Constant(deref!(constant)), _) => {
                // Check for FnDef directly, or peel a reference layer for
                // promoted constants like `&some_fn`. Promoted `&fn_item`
                // has type `&fn() {fn_item}` where the inner type is FnDef. (#1636)
                let ty = constant.const_.ty();
                let inner_ty = match ty.kind() {
                    rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
                    _ => ty,
                };
                let rustc_middle::ty::TyKind::FnDef(def_id, generic_args) = inner_ty.kind() else {
                    record_extraction_diag(
                        diagnostics,
                        "extract/call_resolve_util.rs",
                        ExtractionDiagKind::CallResolutionBacktrackFailed,
                        "backtracked call target did not resolve to an FnDef constant",
                        None,
                    );
                    return None;
                };
                return Some((*def_id, generic_args.skip_binder()));
            }
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
            | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                if place.projection.is_empty() =>
            {
                current_local = Some(place.local);
            }
            // Handle deref-through-reference in call backtracking: `_4 = copy *_1`
            // where _1 is a `&fn()` reference. Follow to the base local. (#1588)
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref) =>
            {
                current_local = Some(place.local);
            }
            Rvalue::Ref(_, _, place) | Rvalue::CopyForDeref(place)
                if place.projection.is_empty() =>
            {
                current_local = Some(place.local);
            }
            // Handle `_1 = &(*_8)` — reference to a dereferenced promoted constant.
            // MIR generates this for `&some_fn_item`: the fn item is promoted to a
            // constant, and the reference is formed via `&(*promoted)`. Follow the
            // base local through the Deref projection. (#1636)
            Rvalue::Ref(_, _, place)
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref) =>
            {
                current_local = Some(place.local);
            }
            _ => {
                record_extraction_diag(
                    diagnostics,
                    "extract/call_resolve_util.rs",
                    ExtractionDiagKind::CallResolutionBacktrackFailed,
                    format!("unsupported backtracking rvalue for call target: {rvalue:?}"),
                    None,
                );
                return None;
            }
        }
    }

    record_extraction_diag(
        diagnostics,
        "extract/call_resolve_util.rs",
        ExtractionDiagKind::CallResolutionBacktrackFailed,
        format!("call target backtracking exceeded depth limit ({MAX_CALL_DEF_BACKTRACK_DEPTH})"),
        None,
    );
    None
}

fn array_len_from_place_with_backtrack<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    place: rustc_middle::mir::Place<'tcx>,
    depth: usize,
) -> Option<PureExpr> {
    if depth >= MAX_ARRAY_LEN_BACKTRACK_DEPTH {
        return None;
    }
    if let Some(expr) = array_len_from_place(body, place) {
        return Some(expr);
    }
    if !place.projection.is_empty() {
        return None;
    }
    let rvalue = find_local_assignment_rvalue(body, bb, place.local)?;
    match rvalue {
        Rvalue::Use(operand, _) | Rvalue::Cast(_, operand, _) => {
            array_len_from_operand_with_backtrack(body, bb, operand, depth + 1)
        }
        Rvalue::Ref(_, _, inner_place) | Rvalue::CopyForDeref(inner_place) => {
            array_len_from_place_with_backtrack(body, bb, *inner_place, depth + 1)
        }
        _ => None,
    }
}

fn array_len_from_operand_with_backtrack<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    operand: &Operand<'tcx>,
    depth: usize,
) -> Option<PureExpr> {
    if depth >= MAX_ARRAY_LEN_BACKTRACK_DEPTH {
        return None;
    }
    if let Some(expr) = array_len_from_operand(body, operand) {
        return Some(expr);
    }
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            array_len_from_place_with_backtrack(body, bb, *place, depth + 1)
        }
        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
    }
}

pub(super) fn call_receiver_array_len_expr<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    args: &[Spanned<Operand<'tcx>>],
) -> Option<PureExpr> {
    let receiver = args.first()?;
    array_len_from_operand_with_backtrack(body, bb, &receiver.node, 0)
}

/// Drain call-site assumptions and obligations from `CallEffects` and wrap the
/// continuation expression in `LetAssume`/`LetObligation` nodes.
///
/// This scopes call-site postcondition assumptions and precondition obligations
/// to the branch they were created in; an assumption that outlived its branch
/// would premise goals on every other path.
///
/// Effects are passed explicitly (`session.effects`); there is no thread-local
/// fallback.
pub(super) fn wrap_call_context(
    continuation: Option<PureExpr>,
    enabled: bool,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    if !enabled {
        return continuation;
    }
    let Some(mut expr) = continuation else {
        // Keep effects on the side channel when there is no expression to wrap,
        // so proof_assert cutoff snapshots can still consume them.
        return None;
    };
    let assumptions = std::mem::take(&mut effects.assumptions);
    let obligations = std::mem::take(&mut effects.obligations);

    if assumptions.is_empty() && obligations.is_empty() {
        return Some(expr);
    }

    for assumption in assumptions.into_iter().rev() {
        expr = PureExpr::LetAssume {
            assumption: Arc::new(assumption),
            body: Arc::new(expr),
        };
    }
    for obligation in obligations.into_iter().rev() {
        expr = PureExpr::LetObligation {
            obligation: Arc::new(obligation),
            body: Arc::new(expr),
        };
    }
    Some(expr)
}
