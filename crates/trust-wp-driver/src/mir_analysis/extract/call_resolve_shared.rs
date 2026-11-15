// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared call-resolution helpers used by multiple extraction pipelines.
//!
//! Functions in this module are shared between the primary (`call_spec`),
//! spanned (`spanned_extract`), and substitution (`substitution::call_resolution`)
//! pipelines. Moving them here eliminates cross-pipeline duplication.
//!
//! Contains:
//! - `resolve_call`: unified spec lookup chain returning `ResolvedCall`
//! - `try_int_passthrough`: Int arithmetic translation
//! - `is_trust_wp_int_type`: Int type detection
//!
//! Phase 1 of #2066 (extract block visitor unification).

use std::{collections::HashMap, fmt::Write as _, sync::Arc};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand},
    ty::{TyCtxt, TypeVisitableExt},
};
use rustc_span::Spanned;
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        call_resolve::{resolve_trait_method_def_id, ufcs_path_for_call},
        diagnostics::ExtractionDiagnosticSink,
        translate::{translate_operand, ExprLookup},
    },
    call_resolve_util::{
        call_receiver_array_len_expr, is_box_new_call_path, resolve_call_def_id,
        translate_const_generic_arg_expr,
    },
    try_operator::is_try_branch_call,
};
// ── Int type detection ──────────────────────────────────────────────

/// Check if a type is `trust_wp_std::logic::Int` (the unbounded integer newtype).
///
/// Matches both direct paths (`trust_wp_std::logic::int::Int`) and re-export
/// paths through the Creusot compatibility shim (`creusot_std::Int`).
pub(super) fn is_trust_wp_int_type(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = ty.kind() {
        // Provenance: a local `mod trust_wp_std { struct Int }` prints alike.
        if !crate::provenance::is_spec_library_item(tcx, adt_def.did()) {
            return false;
        }
        let path = tcx.def_path_str(adt_def.did());
        path == "trust_wp_std::logic::int::Int"
            || path == "trust_wp_std::logic::Int"
            || path == "trust_wp_std::Int"
            || path == "trust_wp::logic::int::Int"
            || path == "trust_wp::logic::Int"
            || path == "trust_wp::Int"
            || path == "creusot_std::Int"
    } else {
        false
    }
}

// ── Int arithmetic passthrough ──────────────────────────────────────

/// Translate `trust_wp_std::logic::Int` arithmetic calls to `PureExpr` nodes.
///
/// Recognizes `From::from`, binary arithmetic (`Add::add`, `Sub::sub`,
/// `Mul::mul`, `Div::div`, `Rem::rem`), and unary negation (`Neg::neg`).
///
/// This is the single shared implementation used by all three extraction
/// pipelines. Previously duplicated as `try_int_passthrough` in `call_spec/dispatch.rs`
/// and `try_int_call_passthrough` in `substitution/call_resolution.rs`. (#2066)
///
/// # Arguments
/// * `call_path` - The resolved def path string of the callee
/// * `args` - The call arguments
/// * `local_exprs` - Current local-to-expression map (any `ExprLookup` impl)
pub(super) fn try_int_passthrough(
    call_path: &str,
    args: &[Spanned<Operand<'_>>],
    local_exprs: &impl ExprLookup,
) -> Option<PureExpr> {
    // From::from(value) → passthrough (newtype identity)
    if call_path.ends_with("::from") && args.len() == 1 {
        return translate_operand(&args[0].node, local_exprs);
    }

    // Binary arithmetic operators: Add, Sub, Mul, Div, Rem
    let binop = if call_path.ends_with("::add") {
        Some(BinOp::Add)
    } else if call_path.ends_with("::sub") {
        Some(BinOp::Sub)
    } else if call_path.ends_with("::mul") {
        Some(BinOp::Mul)
    } else if call_path.ends_with("::div") {
        // `Div::div` truncates toward zero: trust-wp-std `Int` divides its
        // i128 with Rust `/`, and Creusot's Int `/` is
        // `int.ComputerDivision.div`. Euclidean `BinOp::Div` would model
        // `(-7).div(2)` as -4 instead of -3; `div_euclid` stays Euclidean.
        Some(BinOp::DivTrunc)
    } else if call_path.ends_with("::rem") {
        // `Rem::rem` on primitives (and trust-wp-std `Int`) truncates.
        Some(BinOp::RemTrunc)
    } else {
        None
    };
    if let Some(op) = binop {
        if args.len() == 2 {
            let lhs = translate_operand(&args[0].node, local_exprs)?;
            let rhs = translate_operand(&args[1].node, local_exprs)?;
            return Some(PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs)));
        }
    }

    // Unary: Neg::neg
    if call_path.ends_with("::neg") && args.len() == 1 {
        let operand = translate_operand(&args[0].node, local_exprs)?;
        return Some(PureExpr::UnOp(UnOp::Neg, Arc::new(operand)));
    }

    // Model functions → identity passthrough for Int (#2245)
    // `deep_model(self) -> Int { self }` and `view(x) -> Int { x }` are
    // identity for `trust_wp_std::logic::Int`. The type guard in
    // `try_int_passthrough_if_int_type` ensures the destination is Int,
    // so this only fires for the identity case.
    if (call_path.ends_with("::deep_model")
        || call_path.ends_with("::view")
        || call_path.ends_with("::shallow_model"))
        && args.len() == 1
    {
        return translate_operand(&args[0].node, local_exprs);
    }

    None
}

/// Guarded version of [`try_int_passthrough`] that first checks whether the
/// destination type is `trust_wp_std::logic::Int`. Used when the caller has
/// access to the MIR body and destination local.
pub(super) fn try_int_passthrough_if_int_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    destination: Local,
    call_path: &str,
    args: &[Spanned<Operand<'tcx>>],
    local_exprs: &impl ExprLookup,
) -> Option<PureExpr> {
    if !is_trust_wp_int_type(tcx, body.local_decls[destination].ty) {
        return None;
    }
    try_int_passthrough(call_path, args, local_exprs)
}

// ── Unified call resolution ─────────────────────────────────────────

/// Result of resolving a function call against all spec tables.
///
/// Returned by [`resolve_call`] and consumed by each pipeline's call handler.
/// The pipeline-specific logic (precondition/postcondition application, effect
/// threading, closure mutation propagation) remains in the caller.
pub(super) struct ResolvedCall {
    /// The resolved DefId of the callee, if available.
    pub def_id: Option<DefId>,
    /// What kind of call this resolved to.
    pub kind: ResolvedCallKind,
}

/// Classification of a resolved call site.
#[derive(Debug, Clone)]
pub(super) enum ResolvedCallKind {
    /// Array `.len()` call resolved to a length expression.
    ArrayLen(PureExpr),
    /// Direct user/trait spec found via `user_specs` or `trait_specs` tables.
    DirectSpec(StdSpec),
    /// Spec found via UFCS, extern_specs, std_specs, or trait method fallback.
    ExternSpec(StdSpec),
    /// Try-operator (`?`) branch call detected.
    TryBranch,
    /// `Box::new` call — pass through the argument.
    BoxNew,
    /// `trust_wp_std::logic::Int` arithmetic resolved to a concrete expression.
    IntPassthrough(PureExpr),
    /// `core::mem::size_of` / `core::mem::align_of` resolved to a `size_of_logic__<T>()`
    /// or `align_of_logic__<T>()` logic function call expression. Bridges the runtime
    /// intrinsic to the layout axiom system. (#2693)
    LayoutIntrinsic(PureExpr),
    /// `Mapping::from_closure(closure)` — extract closure body as mapping axiom (#2316).
    MappingFromClosure,
    /// `IteratorSpec::map_inv(iter, closure)` — connect the closure's per-element
    /// `#[ensures]` to the produced `MapInv` view and assert length preservation. (#2170)
    MapInvFromClosure,
    /// No spec found — opaque call.
    Opaque,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CellBuiltin {
    PredCellNew,
    PredCellGet,
    PredCellSet,
    PredCellSwap,
    PredCellReplace,
    PredCellIntoInner,
    PredCellUpdate,
    PredCellFromMut,
    PredCellAsSliceOfCells,
    PermCellNew,
    PermCellSet,
    PermCellGet,
    PermCellBorrow,
    PermCellBorrowMut,
    PermCellReplace,
    PermCellIntoInner,
    PredCellTake,
    PermCellTake,
    PermCellFromMut,
    PermWard,
}

/// Whether a `Box::new(arg)` call wraps a closure environment, possibly behind
/// `&`/`&mut`/nested `Box` layers.
///
/// `Box<Closure>` / `Box<&mut Closure>` (and nested boxes thereof) is a
/// transparent wrapper over the closure env — the boxed value's `FnMut`/`FnOnce`
/// impl delegates to the inner closure, so logically `Box::new(env) == env`.
/// Used to gate the `Box::new` identity treatment (`ResolvedCallKind::BoxNew`) so
/// it applies to closure-env boxes (whose receiver identity the closure
/// enrichment must see) without touching value boxes (`Box<i32>`, …), which keep
/// their `*result == value` extern spec.
fn box_new_wraps_closure_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg: &Operand<'tcx>,
) -> bool {
    let mut ty = arg.ty(body, tcx);
    // Peel &/&mut and Box layers down to the ultimate payload type.
    loop {
        match ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner, _) => ty = *inner,
            rustc_middle::ty::TyKind::Adt(adt_def, substs) if adt_def.is_box() => {
                match substs.types().next() {
                    Some(inner) => ty = inner,
                    None => return false,
                }
            }
            _ => break,
        }
    }
    matches!(ty.kind(), rustc_middle::ty::TyKind::Closure(..))
}

/// Extract the array length `N` from a `box_assume_init_into_vec_unsafe::<T, N>`
/// call's const generic arguments.
///
/// The `vec![e1, ..., eN]` macro lowers to this intrinsic with the element
/// count carried as a const generic, so the length is available directly on the
/// call (no MIR backtracking through the intermediate `Box<MaybeUninit<[T; N]>>`
/// needed). Returns the first const-generic argument that resolves to a concrete
/// integer. (syntax/13_vec_macro)
fn box_assume_init_into_vec_array_len<'tcx>(func: &Operand<'tcx>) -> Option<PureExpr> {
    let Operand::Constant(deref!(constant)) = func else {
        return None;
    };
    let rustc_middle::ty::TyKind::FnDef(_, substs) = constant.ty().kind() else {
        return None;
    };
    substs.skip_binder().iter().find_map(|arg| {
        match translate_const_generic_arg_expr(arg.as_const()?) {
            Some(PureExpr::Int(n)) => Some(PureExpr::Int(n)),
            _ => None,
        }
    })
}

/// True when `def_id` is `core::iter::Extend::extend` (or an impl of it) called
/// with a `&mut Vec<T>` receiver and a `Vec<T>` argument of the SAME element
/// type `T`. This is the only shape for which Creusot's `Vec::extend` contract
/// collapses to `(^self)@ == self@.concat(iter@)` (see the call site).
fn vec_extend_with_same_element_vec<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    def_id: DefId,
    args: &[Spanned<Operand<'tcx>>],
) -> bool {
    if args.len() != 2 {
        return false;
    }
    let trait_item = resolve_trait_method_def_id(tcx, def_id).unwrap_or(def_id);
    if tcx.crate_name(trait_item.krate).as_str() != "core"
        || tcx.item_name(trait_item).as_str() != "extend"
    {
        return false;
    }
    let trait_def = tcx.parent(trait_item);
    if tcx.def_kind(trait_def) != rustc_hir::def::DefKind::Trait
        || tcx.item_name(trait_def).as_str() != "Extend"
    {
        return false;
    }
    let receiver_ty = args[0].node.ty(&body.local_decls, tcx);
    let rustc_middle::ty::TyKind::Ref(_, receiver_inner, rustc_middle::ty::Mutability::Mut) =
        receiver_ty.kind()
    else {
        return false;
    };
    let (Some(self_elem), Some(arg_elem)) = (
        vec_element_ty(tcx, *receiver_inner),
        vec_element_ty(tcx, args[1].node.ty(&body.local_decls, tcx)),
    ) else {
        return false;
    };
    self_elem == arg_elem
}

/// Element type `T` of `alloc::vec::Vec<T, A>`, or `None` for any other type.
fn vec_element_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<rustc_middle::ty::Ty<'tcx>> {
    let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
        return None;
    };
    if !tcx.is_diagnostic_item(rustc_span::sym::Vec, adt_def.did()) {
        return None;
    }
    substs.types().next()
}

/// Recover the element VALUES of a `vec![c0, .., cN-1]` literal from the MIR
/// that feeds `box_assume_init_into_vec_unsafe::<T, N>(move a)`.
///
/// The macro lowers to `x = Box::<[T; N]>::new_uninit()`,
/// `((*x).1.0) = [c0, .., cN-1]` (`MaybeUninit`'s `ManuallyDrop` value field and
/// its value; borrowck MIR; after box-deref elaboration the write goes through
/// `p = copy (x.0) as *const _ (BoxDerefTransmute)`, `x.0` the `BoxRaw`),
/// `a = move x`, then the call. Returns the rendered constants only when:
/// * `a` is assigned exactly once, from `move x` (or `a` is `x`);
/// * exactly one statement writes the payload `(*x|*p).1.0`, and it is an
///   array aggregate of exactly `n` operands, each a scalar integer/bool
///   constant;
/// * every other mention of `x`, `p` and `a` in the body is one of: the
///   defining call, the move, the pointer definition, pointer-to-`*const ()`
///   casts (address-only reads), drops, storage/no-op markers, or the vec call
///   itself — i.e. no borrow, raw-pointer escape, or second write can alter the
///   payload between initialization and the call.
///
/// Any other shape returns `None` (the caller then keeps only the length fact).
fn vec_macro_constant_elements<'tcx>(
    body: &Body<'tcx>,
    call_bb: BasicBlock,
    arg: &Operand<'tcx>,
    n: i64,
) -> Option<Vec<String>> {
    use rustc_middle::mir::{
        visit::{PlaceContext, Visitor},
        AggregateKind, CastKind, Location, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    };

    // Borrowck MIR passes the box by `move`; after optimization the same
    // single use can appear as `copy`. Either is accepted only because the
    // alias guard below rejects every other mention of the local.
    let (Operand::Move(arg_place) | Operand::Copy(arg_place)) = arg else {
        return None;
    };
    if !arg_place.projection.is_empty() {
        return None;
    }
    let a = arg_place.local;

    let is_payload_write = |place: &Place<'tcx>, base: Local| {
        place.local == base
            && matches!(
                place.projection.as_slice(),
                [
                    ProjectionElem::Deref,
                    ProjectionElem::Field(f1, _),
                    ProjectionElem::Field(f2, _),
                ] if f1.as_u32() == 1 && f2.as_u32() == 0
            )
    };

    // (1) `a = move x`, exactly once.
    let mut a_defs = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (idx, stmt) in data.statements.iter().enumerate() {
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                if place.local == a && place.projection.is_empty() {
                    a_defs.push((
                        Location {
                            block: bb,
                            statement_index: idx,
                        },
                        rvalue,
                    ));
                }
            }
        }
    }
    let (x, a_def_loc) = match a_defs.as_slice() {
        [] => (a, None),
        [(loc, Rvalue::Use(Operand::Move(src) | Operand::Copy(src), ..))]
            if src.projection.is_empty() =>
        {
            (src.local, Some(*loc))
        }
        _ => return None,
    };

    // (2) optional elaborated pointer `p = copy (x.0) as _ (BoxDerefTransmute)`,
    //     and (3) the single payload write.
    let mut pointer_defs = Vec::new();
    let mut payload_writes = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (idx, stmt) in data.statements.iter().enumerate() {
            let StatementKind::Assign((place, rvalue)) = &stmt.kind else {
                continue;
            };
            let loc = Location {
                block: bb,
                statement_index: idx,
            };
            if place.projection.is_empty() {
                if let Rvalue::Cast(CastKind::BoxDerefTransmute, Operand::Copy(src), _) = rvalue {
                    if src.local == x
                        && matches!(
                            src.projection.as_slice(),
                            [ProjectionElem::Field(f, _)] if f.as_u32() == 0
                        )
                    {
                        pointer_defs.push((place.local, loc));
                    }
                }
            }
            if !place.projection.is_empty() {
                payload_writes.push((place.local, *place, rvalue, loc));
            }
        }
    }
    let pointer = match pointer_defs.as_slice() {
        [] => None,
        [(p, loc)] => Some((*p, *loc)),
        _ => return None,
    };
    let bases: Vec<Local> = std::iter::once(x).chain(pointer.map(|(p, _)| p)).collect();
    let mut matching = payload_writes.iter().filter(|(local, place, _, _)| {
        bases
            .iter()
            .any(|b| is_payload_write(place, *b) && local == b)
    });
    let (_, _, payload_rvalue, payload_loc) = matching.next()?;
    if matching.next().is_some() {
        return None;
    }
    // No other projected write may target `x`/`p` (e.g. a second partial write).
    if payload_writes
        .iter()
        .filter(|(local, ..)| bases.contains(local))
        .count()
        != 1
    {
        return None;
    }
    let Rvalue::Aggregate(AggregateKind::Array(_), operands) = payload_rvalue else {
        return None;
    };
    if i64::try_from(operands.len()).ok()? != n {
        return None;
    }
    let mut rendered = Vec::with_capacity(operands.len());
    for operand in operands {
        if !matches!(operand, Operand::Constant(_)) {
            return None;
        }
        match translate_operand(operand, &HashMap::<Local, PureExpr>::new())? {
            PureExpr::Int(v) => rendered.push(v.to_string()),
            PureExpr::Bool(b) => rendered.push(b.to_string()),
            _ => return None,
        }
    }

    // (4) alias guard: every mention of x / p / a must be a whitelisted one.
    struct Mentions {
        tracked: Vec<Local>,
        seen: Vec<(Local, PlaceContext, Location)>,
    }
    impl<'tcx> Visitor<'tcx> for Mentions {
        fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
            if self.tracked.contains(&local) {
                self.seen.push((local, context, location));
            }
        }
    }
    let mut mentions = Mentions {
        tracked: bases.iter().copied().chain(std::iter::once(a)).collect(),
        seen: Vec::new(),
    };
    mentions.visit_body(body);
    let call_loc = body.terminator_loc(call_bb);
    for (_local, context, location) in &mentions.seen {
        if matches!(context, PlaceContext::NonUse(_)) {
            continue;
        }
        if *location == call_loc || Some(*location) == a_def_loc || location == payload_loc {
            continue;
        }
        if pointer.is_some_and(|(_, loc)| loc == *location) {
            continue;
        }
        let block = &body.basic_blocks[location.block];
        if location.statement_index == block.statements.len() {
            // Terminator: the defining `new_uninit()` call of `x`, or a drop.
            match &block.terminator().kind {
                TerminatorKind::Drop { place, .. } if place.projection.is_empty() => continue,
                TerminatorKind::Call {
                    destination,
                    args: call_args,
                    ..
                } if destination.local == x
                    && destination.projection.is_empty()
                    && call_args.is_empty() =>
                {
                    continue
                }
                _ => return None,
            }
        }
        let stmt = &block.statements[location.statement_index];
        match &stmt.kind {
            StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..) => continue,
            // Address-only reads of the elaborated pointer (alignment / null
            // checks): `q = copy p as *const () (PtrToPtr)`. A `*const ()`
            // cannot be written through to alter the payload.
            StatementKind::Assign((
                _,
                Rvalue::Cast(CastKind::PtrToPtr, Operand::Copy(src), ty),
            )) if src.projection.is_empty()
                && pointer.is_some_and(|(p, _)| p == src.local)
                && matches!(
                    ty.kind(),
                    rustc_middle::ty::TyKind::RawPtr(pointee, _) if pointee.is_unit()
                ) =>
            {
                continue
            }
            _ => return None,
        }
    }
    Some(rendered)
}

/// Resolve a function call against all spec tables.
///
/// This is the single shared spec lookup chain used by all three extraction
/// pipelines, eliminating the 3x duplication of the lookup sequence. (#2066)
///
/// The resolution order is:
/// 1. Array `.len()` folding by receiver type
/// 2. Direct user/trait spec lookup
/// 3. `trust_wp_std::logic::Int` arithmetic passthrough (#2694)
/// 4. UFCS-qualified path → extern/std_specs
/// 5. Plain def_path → extern/std_specs
/// 6. Trait method fallback → extern/std_specs
/// 7. Try-operator (`?`) branch detection
/// 8. `Box::new` alias-preserving detection
/// 9. Opaque fallback
#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: Local,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    diagnostics: Option<&ExtractionDiagnosticSink>,
    local_exprs: &impl ExprLookup,
) -> ResolvedCall {
    // Step 1: Array receiver `.len()` by arity
    if args.len() == 1 {
        if let Some(len_expr) = call_receiver_array_len_expr(body, bb, args) {
            return ResolvedCall {
                def_id: None,
                kind: ResolvedCallKind::ArrayLen(len_expr),
            };
        }
    }

    let call_def_id = resolve_call_def_id(body, bb, func, diagnostics);

    // Multi-arg len call shapes
    if args.len() > 1
        && call_def_id.is_some_and(|def_id| {
            crate::provenance::builtin_def_path_str(tcx, def_id)
                .is_some_and(|path| path.ends_with("::len"))
        })
    {
        if let Some(len_expr) = call_receiver_array_len_expr(body, bb, args) {
            return ResolvedCall {
                def_id: call_def_id,
                kind: ResolvedCallKind::ArrayLen(len_expr),
            };
        }
    }

    let Some(def_id) = call_def_id else {
        return ResolvedCall {
            def_id: None,
            kind: ResolvedCallKind::Opaque,
        };
    };

    // Step 2: Direct user/trait spec lookup
    let direct_spec = crate::trait_credit::lookup_user_or_trait_spec(
        user_specs,
        trait_specs,
        def_id,
        crate::trait_credit::GrantSite { tcx, body, func },
    );
    if let Some(spec) = direct_spec {
        // Logic-function identity: generic markers in the callee contract
        // denote the impl selected by THIS call's generic arguments.
        let spec = crate::logic::identity_typed::instantiate_generic_markers_for_call(
            tcx,
            body,
            func,
            def_id,
            spec.clone(),
        );
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::DirectSpec(spec),
        };
    }

    let path = tcx.def_path_str(def_id);
    let extern_opt = (!extern_specs.is_empty()).then_some(extern_specs);
    // Provenance (spec-provenance front): every recogniser below that grants
    // semantics from the printed `path` applies only to callees DEFINED in a
    // std / spec-library crate. A local item prints like a library item
    // (`crate::core::cmp::max` prints `core::cmp::max`), so it must never
    // reach them. Table lookups (steps 4-6) are gated by DefId separately.
    let builtin_callee = crate::provenance::is_builtin_provider(tcx, def_id);

    // Step 2a: `vec![e1, ..., eN]` N-element literal length.
    //
    // The element-list form of the `vec!` macro lowers (on this toolchain) to
    // `box_assume_init_into_vec_unsafe::<T, N>(Box<MaybeUninit<[T; N]>>)`, where
    // the array length `N` is a *const generic* argument on the call. The
    // returned `Vec` has exactly `N` elements, so synthesize the length
    // postcondition `result@.len() == N` from that const generic. This mirrors
    // the `Vec::new` (`result@.len() == 0`) and `from_elem` (`result@.len() ==
    // count@`) length specs that already cover the `vec![]` and `vec![e; n]`
    // forms; without it the N-element form leaves `result@` unconstrained. The
    // fact is exactly the construct's semantics (SOUND). (syntax/13_vec_macro)
    if builtin_callee && path.ends_with("box_assume_init_into_vec_unsafe") {
        if let Some(PureExpr::Int(n)) = box_assume_init_into_vec_array_len(func) {
            let mut ensures = vec![format!("result@.len() == {n}")];
            // Element values (bug/874): when the boxed array is initialized by a
            // single, alias-free `[c0, .., cN-1]` aggregate of scalar constants,
            // the returned Vec's view is exactly that sequence. Any shape the
            // recognizer cannot prove exact keeps the length-only fact.
            if let Some(elements) = args
                .first()
                .and_then(|arg| vec_macro_constant_elements(body, bb, &arg.node, n))
            {
                for (i, value) in elements.iter().enumerate() {
                    ensures.push(format!("result@.index_logic({i}) == {value}"));
                }
            }
            let spec = StdSpec {
                inv_requires: Vec::new(),
                capture_inv_requires: Vec::new(),
                requires: Vec::new(),
                ensures,
                param_names: Some(vec!["self_".to_string()]),
            };
            return ResolvedCall {
                def_id: Some(def_id),
                kind: ResolvedCallKind::ExternSpec(spec),
            };
        }
    }

    // Step 2a': `<Vec<T> as Extend<T>>::extend::<Vec<T>>` — Creusot's exact
    // `Vec::extend` contract (`creusot-std/src/std/vec.rs:175-180`) is
    //   exists<start_, done, prod> I::into_iter.postcondition((iter,), start_)
    //     && done.completed() && start_.produces(prod, *done)
    //     && (^self)@ == self@.concat(prod).
    // For an argument of type `Vec<T>` (and ONLY that type) every piece is
    // determined: `Vec::into_iter` ensures `result@ == self@`, `vec::IntoIter`
    // `produces(visited, o)` is `self@ == visited.concat(o@)`, and `completed`
    // forces `o@ == Seq::empty()`, so `prod == iter@`. The instantiated
    // theorem is therefore `(^self)@ == self@.concat(iter@)`. Every other
    // argument type keeps the generic prefix-preservation spec below.
    if vec_extend_with_same_element_vec(tcx, body, def_id, args) {
        let spec = StdSpec {
            inv_requires: Vec::new(),
            capture_inv_requires: Vec::new(),
            requires: Vec::new(),
            ensures: vec![
                "(^self)@ == self@.concat(iter@)".to_string(),
                "(^self)@.len() == self@.len() + iter@.len()".to_string(),
            ],
            param_names: Some(vec!["self".to_string(), "iter".to_string()]),
        };
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::ExternSpec(spec),
        };
    }

    // Step 2b: `Box::new` of a closure environment is a transparent wrapper.
    //
    // `Box<Closure>` / `Box<&mut Closure>` (or nested boxes thereof) forwards its
    // `FnMut`/`FnOnce` impl to the inner closure, so logically `Box::new(env) ==
    // env`. Resolving such a call to the alias-preserving `BoxNew` identity (dest
    // := inner) INSTEAD of the `*result == value` extern spec keeps the boxed
    // closure env flowing to call-obligation receivers (e.g. `f.postcondition_mut`
    // in `call_fnmut`'s `#[requires]`) as the concrete tuple env, rather than an
    // opaque `call_N` result var that the closure-enrichment receiver-identity
    // hooks can't recognize. Mirrors the reborrow-chain transparency of #2318 into
    // the call-obligation receiver path so closures/07's Box pair
    // (`test_fnmut2box` / `test_fnmut3box`) reduce to the already-verified non-Box
    // shape. Narrowly gated to a *closure-typed* payload — value boxes (`Box<i32>`
    // etc.) keep their `*result == value` extern spec, so this is not general Box
    // deref-transparency. (closures/07 Box pair)
    if builtin_callee
        && is_box_new_call_path(&path)
        && args.len() == 1
        && box_new_wraps_closure_env(tcx, body, &args[0].node)
    {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::BoxNew,
        };
    }

    // Step 3: Int arithmetic passthrough (#1581, #2694)
    //
    // Checked before UFCS/plain-path/trait-method spec lookups so that
    // `Int::from(x)`, `Int::add(a, b)`, etc. resolve to direct expression
    // passthroughs. Without this priority, `Int::from(1)` matches the
    // generic `core::convert::From::from` spec (via UFCS path
    // `<creusot_std::Int as std::convert::From>::from` or the plain path
    // `std::convert::From::from`), producing an unconstrained
    // `T::from.postcondition(...)` instead of the identity passthrough.
    if let Some(int_expr) = builtin_callee
        .then(|| try_int_passthrough_if_int_type(tcx, body, destination, &path, args, local_exprs))
        .flatten()
    {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::IntPassthrough(int_expr),
        };
    }

    // Step 3a: primitive integer bit-count methods.
    //
    // Creusot specs use `x.leading_zeros_logic()` while MIR for executable
    // code calls `core::num::<impl usize>::leading_zeros(x)`. Preserve the
    // relationship by translating the runtime call to the corresponding logic
    // method expression during body extraction.
    if let Some(expr) = builtin_callee
        .then(|| try_primitive_numeric_logic_call(&path, args, local_exprs))
        .flatten()
    {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::IntPassthrough(expr),
        };
    }

    if let Some(expr) = builtin_callee
        .then(|| try_int_partial_eq_call(tcx, body, &path, args, local_exprs))
        .flatten()
    {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::IntPassthrough(expr),
        };
    }

    // Step 3b: Layout intrinsic passthrough (#2693)
    //
    // Intercepts `core::mem::size_of::<T>()` and `core::mem::align_of::<T>()`
    // calls and produces a `size_of_logic__<T>()` / `align_of_logic__<T>()`
    // LogicFnCall expression. This bridges the runtime layout intrinsics to
    // the layout axiom system in trust-wp-ay, allowing `proof_assert!(t2@ ==
    // 2 * size_of_logic::<T>())` to connect with `let t2 = size_of::<[T; 2]>()`.
    if let Some(layout_expr) = builtin_callee
        .then(|| try_layout_intrinsic_passthrough(tcx, func, &path))
        .flatten()
    {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::LayoutIntrinsic(layout_expr),
        };
    }

    // Builtin-table contracts describe library behaviour only: admitted when
    // the call resolves to library code whose trait bounds are discharged by
    // library types (never a local impl of a std trait). User extern specs are
    // unaffected.
    let admission = crate::provenance::builtin_spec_admission_for_operand(
        tcx,
        func,
        Some(body.source.def_id()),
    );
    // The call whose generic arguments size the element type of an
    // allocation-sizing std spec.
    let site = crate::provenance::CallSite::of_operand(func, Some(body.source.def_id()));
    // Step 4: UFCS-qualified lookup (#967)
    let spec = ufcs_path_for_call(tcx, func).and_then(|ufcs_path| {
        crate::provenance::lookup_spec_for_def(tcx, def_id, admission, extern_opt, &ufcs_path, site)
    });
    // Step 5: Plain path lookup
    let spec = spec.or_else(|| {
        crate::provenance::lookup_spec_for_def(tcx, def_id, admission, extern_opt, &path, site)
    });
    if let Some(spec) = spec {
        // `Iterator::collect`: the table entry is intentionally empty; append
        // the roundtrip only for a whitelisted monomorphized `(Self, B)` pair.
        let spec = super::collect_gate::refine_collect_spec(tcx, func, spec);
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::ExternSpec(spec),
        };
    }

    // Step 6: Trait method fallback (#352)
    let spec = {
        let trait_method_id = resolve_trait_method_def_id(tcx, def_id);
        trait_method_id.and_then(|tmid| {
            let trait_path = tcx.def_path_str(tmid);
            crate::provenance::lookup_spec_for_def(
                tcx,
                tmid,
                admission,
                extern_opt,
                &trait_path,
                site,
            )
        })
    };
    if let Some(spec) = spec {
        let spec = super::collect_gate::refine_collect_spec(tcx, func, spec);
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::ExternSpec(spec),
        };
    }

    // Step 7: Try-operator pattern (#1266)
    if builtin_callee && is_try_branch_call(tcx, def_id) {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::TryBranch,
        };
    }

    // Step 8: Box::new alias-preserving fallback (#1277)
    if builtin_callee && is_box_new_call_path(&path) && args.len() == 1 {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::BoxNew,
        };
    }
    // Step 8b: Mapping::from_closure — connect closure body to Mapping value (#2316)
    if builtin_callee && is_mapping_from_closure_path(&path) {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::MappingFromClosure,
        };
    }

    // Step 8b': IteratorSpec::map_inv — connect the mapping closure's per-element
    // `#[ensures]` to the produced MapInv view, plus the length-preservation
    // fact `result@.len() == iter@.len()`. Both are sound theorems of the
    // `map_inv` contract; the per-element fact is gated in the handler to fire
    // only when substituting `result := mapinv@[i]` leaves no dangling closure
    // formals (see `handle_map_inv_from_closure`). (#2170 "Slice 3")
    if builtin_callee
        && is_map_inv_path(&path)
        && args.len() == 2
        && is_trust_wp_std_item(tcx, def_id)
    {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::MapInvFromClosure,
        };
    }

    // Step 8c: Local bodyful trait-default methods (#2315, #2670)
    //
    // If the callee is a local trait method with a provided body, use the
    // trait's contract spec (if any) rather than falling to Opaque. This
    // prevents OpaqueCallTrueAssumption demotion for user-defined provided
    // trait defaults like `fn default(&self) -> u32 { 0 }`.
    //
    // Also handles local impl methods that override trait methods (#2670):
    // when the DefId points to an impl method, check the trait method's
    // DefId in trait_specs for inherited contracts.
    if def_id.as_local().is_some() {
        if let Some(assoc) = tcx.opt_associated_item(def_id) {
            let is_trait_method =
                matches!(assoc.container, rustc_middle::ty::AssocContainer::Trait);
            let is_impl_of_trait = !is_trait_method && assoc.trait_item_def_id().is_some();

            if (is_trait_method || is_impl_of_trait) && tcx.is_mir_available(def_id) {
                // Check if the trait method has contracts in the trait_specs table.
                // This was already attempted in step 2 (direct lookup), but reaching
                // here means step 2 didn't match — either because the def_id was an
                // impl copy, or the trait had no contracts. Try both the current
                // def_id and the trait method's def_id.
                let spec = trait_specs
                    .get(&def_id)
                    .cloned()
                    .or_else(|| {
                        // For impl methods, also check the trait method's DefId.
                        let trait_method_id = assoc.trait_item_def_id()?;
                        trait_specs.get(&trait_method_id).cloned()
                    })
                    .unwrap_or_else(|| StdSpec {
                        inv_requires: Vec::new(),
                        capture_inv_requires: Vec::new(),
                        requires: Vec::new(),
                        ensures: Vec::new(),
                        param_names: None,
                    });
                return ResolvedCall {
                    def_id: Some(def_id),
                    kind: ResolvedCallKind::ExternSpec(spec),
                };
            }
        }
    }

    // Step 9: Opaque fallback
    ResolvedCall {
        def_id: Some(def_id),
        kind: ResolvedCallKind::Opaque,
    }
}

fn try_primitive_numeric_logic_call(
    call_path: &str,
    args: &[Spanned<Operand<'_>>],
    local_exprs: &impl ExprLookup,
) -> Option<PureExpr> {
    if args.len() != 1 {
        return None;
    }

    let logic_method = if call_path.ends_with("::leading_zeros") {
        Some("leading_zeros_logic")
    } else if call_path.ends_with("::trailing_zeros") {
        Some("trailing_zeros_logic")
    } else if call_path.ends_with("::leading_ones") {
        Some("leading_ones_logic")
    } else if call_path.ends_with("::trailing_ones") {
        Some("trailing_ones_logic")
    } else {
        None
    }?;

    let receiver = translate_operand(&args[0].node, local_exprs)?;
    Some(PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: logic_method.to_string(),
        args: vec![],
    })
}

/// True when `PartialEq::eq` on `ty` (with `Rhs = ty`) IS logical equality of
/// values:
/// - integers, `bool`, `char` (library impls);
/// - tuples and arrays of such types (library impls compare componentwise);
/// - `Option` / `Result` (library structural impls) over such types;
/// - a LOCAL struct or enum whose `PartialEq` impl, as resolved for `ty`, is
///   `#[automatically_derived]` and whose field types (instantiated) are
///   themselves such types. A derived `eq` is "same variant and every field
///   `eq`" by the definition of `#[derive(PartialEq)]`, which is logical
///   equality once every field comparison is.
///
/// Anything else (a hand-written impl, a generic parameter, floats, `dyn`,
/// pointers, other library containers) is `false`.
fn partial_eq_is_logical_equality<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    depth: usize,
) -> bool {
    use rustc_middle::ty::TyKind;
    if depth > 8 {
        return false;
    }
    match ty.kind() {
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Bool | TyKind::Char => true,
        TyKind::Tuple(fields) => fields
            .iter()
            .all(|field| partial_eq_is_logical_equality(tcx, field, depth + 1)),
        TyKind::Array(elem, _) => partial_eq_is_logical_equality(tcx, *elem, depth + 1),
        TyKind::Adt(adt, args) => {
            if adt.is_union() {
                return false;
            }
            let did = adt.did();
            let field_types_ok = || {
                adt.all_fields().all(|field| {
                    let field_ty = field.ty(tcx, *args).skip_norm_wip();
                    partial_eq_is_logical_equality(tcx, field_ty, depth + 1)
                })
            };
            if crate::provenance::is_std_item(tcx, did) {
                let lang = tcx.lang_items();
                let structural = lang.option_type() == Some(did)
                    || tcx.is_diagnostic_item(rustc_span::sym::Result, did);
                return structural && field_types_ok();
            }
            if !did.is_local() {
                return false;
            }
            let Some(partial_eq) = tcx.lang_items().eq_trait() else {
                return false;
            };
            let Some(eq_method) = tcx
                .associated_items(partial_eq)
                .in_definition_order()
                .find(|item| item.name().as_str() == "eq")
                .map(|item| item.def_id)
            else {
                return false;
            };
            if args.has_non_region_param() || args.has_aliases() {
                return false;
            }
            let call_args = tcx.mk_args(&[ty.into(), ty.into()]);
            let Ok(Some(instance)) = rustc_middle::ty::Instance::try_resolve(
                tcx,
                rustc_middle::ty::TypingEnv::fully_monomorphized(),
                eq_method,
                call_args,
            ) else {
                return false;
            };
            let rustc_middle::ty::InstanceKind::Item(impl_method) = instance.def else {
                return false;
            };
            let Some(impl_def_id) = tcx.impl_of_assoc(impl_method) else {
                return false;
            };
            impl_method.is_local() && tcx.is_automatically_derived(impl_def_id) && field_types_ok()
        }
        _ => false,
    }
}

/// `PartialEq::eq` / `ne` as logical `==` / `!=`.
///
/// SOUND only where `PartialEq` IS logical equality
/// ([`partial_eq_is_logical_equality`]) for both operands (through
/// references), and both operands have the same type. Any other operand type
/// may run a user `eq` (a hand-written local impl, a generic `T`, `Option<S>`
/// delegating to `S::eq`) or a non-reflexive one (floats), so it is left to
/// the admitted table contract or treated opaque.
fn try_int_partial_eq_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    call_path: &str,
    args: &[Spanned<Operand<'tcx>>],
    local_exprs: &impl ExprLookup,
) -> Option<PureExpr> {
    if args.len() != 2 || !call_path.contains("PartialEq") {
        return None;
    }
    let lhs_ty = args[0].node.ty(&body.local_decls, tcx).peel_refs();
    let rhs_ty = args[1].node.ty(&body.local_decls, tcx).peel_refs();
    if lhs_ty != rhs_ty || !partial_eq_is_logical_equality(tcx, lhs_ty, 0) {
        return None;
    }
    let op = if call_path.ends_with("::eq") {
        BinOp::Eq
    } else if call_path.ends_with("::ne") {
        BinOp::Ne
    } else {
        return None;
    };
    let lhs = translate_operand(&args[0].node, local_exprs)?;
    let rhs = translate_operand(&args[1].node, local_exprs)?;
    Some(PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs)))
}

pub(super) fn classify_cell_builtin_path(path: &str) -> Option<CellBuiltin> {
    let normalized = strip_path_generics(path);

    if matches_cell_builtin(&normalized, "PredCell", "new") {
        Some(CellBuiltin::PredCellNew)
    } else if matches_cell_builtin(&normalized, "PredCell", "get") {
        Some(CellBuiltin::PredCellGet)
    } else if matches_cell_builtin(&normalized, "PredCell", "set") {
        Some(CellBuiltin::PredCellSet)
    } else if matches_cell_builtin(&normalized, "PredCell", "swap") {
        Some(CellBuiltin::PredCellSwap)
    } else if matches_cell_builtin(&normalized, "PredCell", "replace") {
        Some(CellBuiltin::PredCellReplace)
    } else if matches_cell_builtin(&normalized, "PredCell", "into_inner") {
        Some(CellBuiltin::PredCellIntoInner)
    } else if matches_cell_builtin(&normalized, "PredCell", "update") {
        Some(CellBuiltin::PredCellUpdate)
    } else if matches_cell_builtin(&normalized, "PredCell", "from_mut") {
        Some(CellBuiltin::PredCellFromMut)
    } else if matches_cell_builtin(&normalized, "PredCell", "as_slice_of_cells") {
        Some(CellBuiltin::PredCellAsSliceOfCells)
    } else if matches_cell_builtin(&normalized, "PermCell", "new") {
        Some(CellBuiltin::PermCellNew)
    } else if matches_cell_builtin(&normalized, "PermCell", "set") {
        Some(CellBuiltin::PermCellSet)
    } else if matches_cell_builtin(&normalized, "PermCell", "get") {
        Some(CellBuiltin::PermCellGet)
    } else if matches_cell_builtin(&normalized, "PermCell", "borrow") {
        Some(CellBuiltin::PermCellBorrow)
    } else if matches_cell_builtin(&normalized, "PermCell", "borrow_mut") {
        Some(CellBuiltin::PermCellBorrowMut)
    } else if matches_cell_builtin(&normalized, "PermCell", "replace") {
        Some(CellBuiltin::PermCellReplace)
    } else if matches_cell_builtin(&normalized, "PermCell", "into_inner") {
        Some(CellBuiltin::PermCellIntoInner)
    } else if matches_cell_builtin(&normalized, "PredCell", "take") {
        Some(CellBuiltin::PredCellTake)
    } else if matches_cell_builtin(&normalized, "PermCell", "take") {
        Some(CellBuiltin::PermCellTake)
    } else if matches_cell_builtin(&normalized, "PermCell", "from_mut") {
        Some(CellBuiltin::PermCellFromMut)
    } else if matches_perm_builtin(&normalized, "ward") {
        Some(CellBuiltin::PermWard)
    } else {
        None
    }
}

fn matches_cell_builtin(path: &str, type_name: &str, method: &str) -> bool {
    const CELL_PREFIXES: [&str; 3] = [
        "trust_wp_std::std::cell::",
        "trust_wp_std::cell::",
        "creusot_std::cell::",
    ];
    let suffix = format!("::{type_name}::{method}");
    CELL_PREFIXES
        .iter()
        .any(|prefix| path.starts_with(prefix) && path.ends_with(&suffix))
}

fn matches_perm_builtin(path: &str, method: &str) -> bool {
    const PERM_PREFIXES: [&str; 5] = [
        "trust_wp_std::ghost::perm::",
        "trust_wp_std::ghost::",
        "trust_wp_std::",
        "creusot_std::ghost::perm::",
        "creusot_std::",
    ];
    let suffix = format!("::Perm::{method}");
    PERM_PREFIXES
        .iter()
        .any(|prefix| path.starts_with(prefix) && path.ends_with(&suffix))
}

fn strip_path_generics(path: &str) -> String {
    let mut result = String::with_capacity(path.len());
    let mut generic_depth = 0u32;
    let chars: Vec<char> = path.chars().collect();
    let mut index = 0usize;

    while index < chars.len() {
        let ch = chars[index];
        match ch {
            ':' if index + 2 < chars.len()
                && chars[index + 1] == ':'
                && chars[index + 2] == '<' =>
            {
                index += 2;
            }
            '<' => {
                generic_depth += 1;
                index += 1;
            }
            '>' => {
                generic_depth = generic_depth.saturating_sub(1);
                index += 1;
            }
            _ if generic_depth > 0 => {
                index += 1;
            }
            _ => {
                result.push(ch);
                index += 1;
            }
        }
    }

    result
}

/// Check if a def path corresponds to `Mapping::from_closure` or `<Mapping as From>::from`.
///
/// Paths from `tcx.def_path_str()` may include generic parameters (e.g.,
/// `creusot_std::Mapping::<A, B>::from_closure`), so we use substring matching
/// rather than exact equality.
fn is_mapping_from_closure_path(path: &str) -> bool {
    // Direct `Mapping::from_closure` or `Mapping::<A,B>::from_closure`
    (path.contains("Mapping") && path.ends_with("::from_closure"))
        // `<Mapping as From>::from` trait call
        || (path.contains("Mapping") && path.contains("From>::from"))
}

/// Check if a def path corresponds to `IteratorSpec::map_inv`.
///
/// Paths from `tcx.def_path_str()` may be the trait-default form
/// `creusot_std::prelude::IteratorSpec::map_inv` or a UFCS-qualified
/// `<I as ...IteratorSpec>::map_inv`, so match the trailing method segment
/// together with the `IteratorSpec` carrier to avoid colliding with any
/// unrelated user method literally named `map_inv`.
fn is_map_inv_path(path: &str) -> bool {
    path.ends_with("::map_inv") && path.contains("IteratorSpec")
}

/// True when `def_id` is defined in the (non-local) `trust_wp_std` crate,
/// which owns `IteratorSpec`. `def_path_str` omits the crate for local items,
/// so a local `trait IteratorSpec { fn map_inv(..) }` prints a matching path;
/// the per-element closure facts must never be granted to it.
fn is_trust_wp_std_item(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    !def_id.is_local() && tcx.crate_name(def_id.krate).as_str() == "trust_wp_std"
}

// ── Layout intrinsic passthrough (#2693) ───────────────────────────

/// Recognized runtime layout intrinsic paths and their logic-level function
/// name prefixes.
const LAYOUT_INTRINSIC_PATHS: &[(&str, &str)] = &[
    ("core::mem::size_of", "size_of_logic"),
    ("std::mem::size_of", "size_of_logic"),
    ("core::mem::align_of", "align_of_logic"),
    ("std::mem::align_of", "align_of_logic"),
];

/// Attempt to resolve a `core::mem::size_of::<T>()` or `core::mem::align_of::<T>()`
/// call to a `size_of_logic__<T>()` / `align_of_logic__<T>()` `LogicFnCall`.
///
/// Extracts the type argument `T` from the MIR FnDef's generic substitutions
/// and formats it as the turbofish-normalized logic function name that the
/// layout axiom module in trust-wp-ay recognizes. (#2693)
fn try_layout_intrinsic_passthrough<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    path: &str,
) -> Option<PureExpr> {
    // Strip generic args from path for matching (path may contain `<T>` suffix).
    let base_path = path
        .split('<')
        .next()
        .unwrap_or(path)
        .trim_end_matches("::");

    let logic_prefix = LAYOUT_INTRINSIC_PATHS
        .iter()
        .find(|(intrinsic_path, _)| base_path == *intrinsic_path)
        .map(|(_, prefix)| *prefix)?;

    // Extract the type argument from the FnDef's generic substitutions.
    let Operand::Constant(deref!(constant)) = func else {
        return None;
    };
    let rustc_middle::ty::TyKind::FnDef(_, substs) = constant.ty().kind() else {
        return None;
    };

    // `size_of::<T>()` has exactly one type parameter `T` as its first subst.
    let type_arg = substs.skip_binder().types().next()?;
    let type_name = format_ty_for_layout_logic(tcx, type_arg);

    // Produce `size_of_logic__<type_name>()` as a zero-argument LogicFnCall.
    // This matches the turbofish normalization that the contract parser
    // produces for `size_of_logic::<T>()` expressions in contracts.
    let logic_fn_name = format!("{logic_prefix}__{type_name}");
    Some(PureExpr::LogicFnCall {
        name: logic_fn_name,
        args: Vec::new(),
    })
}

/// Format a MIR `Ty` for use as a layout logic function name suffix.
///
/// Produces the same string representation that the contract parser generates
/// when normalizing `size_of_logic::<T>()` turbofish expressions, so that the
/// SMT-level layout axiom matching works correctly.
///
/// Examples:
/// - `u32` -> `"u32"`
/// - `[T; 2]` -> `"[T; 2]"`
/// - `Option<T>` -> `"Option<T>"`
/// - `(A, B)` -> `"(A, B)"`
fn format_ty_for_layout_logic<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty<'tcx>) -> String {
    use rustc_middle::ty::TyKind;

    match ty.kind() {
        // Primitive types: use their canonical Rust names.
        TyKind::Bool => "bool".to_string(),
        TyKind::Char => "char".to_string(),
        TyKind::Int(int_ty) => int_ty.name_str().to_string(),
        TyKind::Uint(uint_ty) => uint_ty.name_str().to_string(),
        TyKind::Float(float_ty) => float_ty.name_str().to_string(),

        // Array type: `[T; N]`
        TyKind::Array(elem_ty, len_const) => {
            let elem_str = format_ty_for_layout_logic(tcx, *elem_ty);
            let len_str = if let Some(value) = len_const.try_to_value() {
                // Trust: ValTree::try_to_scalar removed; use ty::Value::try_to_scalar.
                if let Some(scalar) = value
                    .try_to_scalar()
                    .and_then(|s| s.try_to_scalar_int().ok())
                {
                    format!("{}", scalar.to_uint(scalar.size()))
                } else {
                    format!("{len_const}")
                }
            } else if let rustc_middle::ty::ConstKind::Param(param) = len_const.kind() {
                param.name.as_str().to_string()
            } else {
                format!("{len_const}")
            };
            format!("[{elem_str}; {len_str}]")
        }

        // Slice type: `[T]`
        TyKind::Slice(elem_ty) => {
            let elem_str = format_ty_for_layout_logic(tcx, *elem_ty);
            format!("[{elem_str}]")
        }

        // Tuple type: `(A, B, C)`
        TyKind::Tuple(fields) => {
            if fields.is_empty() {
                return "()".to_string();
            }
            let mut result = String::from("(");
            for (i, field_ty) in fields.iter().enumerate() {
                if i > 0 {
                    result.push_str(", ");
                }
                write!(result, "{}", format_ty_for_layout_logic(tcx, field_ty))
                    .expect("write to String cannot fail");
            }
            result.push(')');
            result
        }

        // Reference types: `&T`, `&mut T`
        TyKind::Ref(_, inner, mutability) => {
            let inner_str = format_ty_for_layout_logic(tcx, *inner);
            match mutability {
                rustc_middle::ty::Mutability::Not => format!("&{inner_str}"),
                rustc_middle::ty::Mutability::Mut => format!("&mut {inner_str}"),
            }
        }

        // Raw pointer types: `*const T`, `*mut T`
        TyKind::RawPtr(inner, mutability) => {
            let inner_str = format_ty_for_layout_logic(tcx, *inner);
            match mutability {
                rustc_middle::ty::Mutability::Not => format!("*const {inner_str}"),
                rustc_middle::ty::Mutability::Mut => format!("*mut {inner_str}"),
            }
        }

        // ADT types (structs, enums): use short name with generics.
        // e.g., `Option<T>`, `Result<T, E>`, `Vec<T>`, `NonZero<u32>`
        TyKind::Adt(adt_def, substs) => {
            let base_name = tcx.item_name(adt_def.did()).to_string();
            if substs.is_empty() {
                return base_name;
            }
            let type_args: Vec<String> = substs
                .types()
                .map(|t| format_ty_for_layout_logic(tcx, t))
                .collect();
            if type_args.is_empty() {
                // Only const or lifetime args — use base name only.
                base_name
            } else {
                format!("{base_name}<{}>", type_args.join(", "))
            }
        }

        // Type parameters: `T`, `U`, etc.
        TyKind::Param(param) => param.name.as_str().to_string(),

        // Never type
        TyKind::Never => "!".to_string(),

        // Fallback: use Rust's Display impl.
        _ => format!("{ty}"),
    }
}

/// Recover the current dereferenced value for a `Snapshot::capture(&(*mutref))`
/// whose `result == value` binding collapsed to a mut-ref reference identity.
///
/// `snapshot!(*a)` for `a: &mut T` lowers to a shared reborrow chain
/// `_t = &(*a); _u = &(*_t); capture(_u)`. Reborrow cancellation in the rvalue
/// translator collapses the chain to the bare mut-ref identity
/// `Var("a", MutRef(_))`, so `Snapshot::capture`'s `result == value`
/// postcondition would bind the snapshot to the REFERENCE rather than freezing
/// the current dereferenced value at the capture point. Because `a`'s own
/// substitution is later advanced to its prophecy/final after an intervening
/// `&mut` call, `*a_p` would then incorrectly follow `^a`.
///
/// This recovery fires ONLY when:
/// - the call is `Snapshot::capture`,
/// - the captured target type `T` (the deref of the `&T` argument) is NOT a
///   reference (so the snapshot stores a value, not a borrow — the
///   reference-capturing case `snapshot!(&mut **x)` must keep its identity),
///   and
/// - the bound `result` expression is a `MutRef`-sorted `Var` (the over-erased
///   reborrow).
///
/// In that case we wrap the reference in a single `Deref` to freeze the current
/// pointee (`name_current`). All other shapes are returned unchanged. (#682)
pub(super) fn recover_snapshot_capture_current_pointee<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    def_id: DefId,
    args: &[Spanned<Operand<'tcx>>],
    result_expr: PureExpr,
) -> PureExpr {
    // Provenance: only the spec library's capture freezes the pointee.
    if !crate::provenance::is_spec_library_item(tcx, def_id) {
        return result_expr;
    }
    let path = tcx.def_path_str(def_id);
    // Fires for the two capture-reading calls that carry the inline `&expr`:
    // a direct `Snapshot::capture(&expr)` and the type-directed
    // `snapshot_capture_select(&(expr))` dispatch. It must NOT fire for the
    // dispatch's argument-less `.capture()` identity tail (a
    // `SnapshotCaptureSelect`/`SnapshotCaptureFallback` method with no `&expr`
    // arg) — that would double-recover the already-frozen pointee. (bug/869)
    let is_direct_capture = path.ends_with("::capture")
        && path.contains("Snapshot")
        && !path.contains("SnapshotCaptureSelect")
        && !path.contains("SnapshotCaptureFallback");
    let is_dispatch_select = path.ends_with("::snapshot_capture_select");
    if !is_direct_capture && !is_dispatch_select {
        return result_expr;
    }
    let PureExpr::Var(_, Some(trust_wp_core::formula::ExprSort::MutRef(_))) = &result_expr else {
        return result_expr;
    };
    // The captured reference is the sole inline `&expr` argument. (bug/869)
    let Some(arg) = args.last() else {
        return result_expr;
    };
    let arg_ty = arg.node.ty(body, tcx);
    // The snapshot target `T` is the pointee of the `&T` argument. Only recover
    // when `T` is a non-reference value; reference captures keep their identity.
    let captures_reference = match arg_ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, inner, _) => inner.is_ref() || inner.is_mutable_ptr(),
        _ => arg_ty.is_ref() || arg_ty.is_mutable_ptr(),
    };
    if captures_reference {
        return result_expr;
    }
    PureExpr::Deref(Arc::new(result_expr))
}
