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
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};
use trust_wp_driver::{lookup_spec_with_extern, StdSpec};

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
        Some(BinOp::Div)
    } else if call_path.ends_with("::rem") {
        Some(BinOp::Mod)
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
    let Operand::Constant(box constant) = func else {
        return None;
    };
    let rustc_middle::ty::TyKind::FnDef(_, substs) = constant.ty().kind() else {
        return None;
    };
    substs.iter().find_map(
        |arg| match translate_const_generic_arg_expr(arg.as_const()?) {
            Some(PureExpr::Int(n)) => Some(PureExpr::Int(n)),
            _ => None,
        },
    )
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
        && call_def_id.is_some_and(|def_id| tcx.def_path_str(def_id).ends_with("::len"))
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
    let direct_spec = user_specs.get(&def_id).or_else(|| trait_specs.get(&def_id));
    if let Some(spec) = direct_spec {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::DirectSpec(spec.clone()),
        };
    }

    let path = tcx.def_path_str(def_id);
    let extern_opt = (!extern_specs.is_empty()).then_some(extern_specs);

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
    if path.ends_with("box_assume_init_into_vec_unsafe") {
        if let Some(PureExpr::Int(n)) = box_assume_init_into_vec_array_len(func) {
            let spec = StdSpec {
                requires: Vec::new(),
                ensures: vec![format!("result@.len() == {n}")],
                param_names: Some(vec!["self_".to_string()]),
            };
            return ResolvedCall {
                def_id: Some(def_id),
                kind: ResolvedCallKind::ExternSpec(spec),
            };
        }
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
    if is_box_new_call_path(&path)
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
    if let Some(int_expr) =
        try_int_passthrough_if_int_type(tcx, body, destination, &path, args, local_exprs)
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
    if let Some(expr) = try_primitive_numeric_logic_call(&path, args, local_exprs) {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::IntPassthrough(expr),
        };
    }

    if let Some(expr) = try_int_partial_eq_call(&path, args, local_exprs) {
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
    if let Some(layout_expr) = try_layout_intrinsic_passthrough(tcx, func, &path) {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::LayoutIntrinsic(layout_expr),
        };
    }

    // Step 4: UFCS-qualified lookup (#967)
    let spec = ufcs_path_for_call(tcx, func)
        .and_then(|ufcs_path| lookup_spec_with_extern(extern_opt, &ufcs_path));
    // Step 5: Plain path lookup
    let spec = spec.or_else(|| lookup_spec_with_extern(extern_opt, &path));
    if let Some(spec) = spec {
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
            lookup_spec_with_extern(extern_opt, &trait_path)
        })
    };
    if let Some(spec) = spec {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::ExternSpec(spec),
        };
    }

    // Step 7: Try-operator pattern (#1266)
    if is_try_branch_call(tcx, def_id) {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::TryBranch,
        };
    }

    // Step 8: Box::new alias-preserving fallback (#1277)
    if is_box_new_call_path(&path) && args.len() == 1 {
        return ResolvedCall {
            def_id: Some(def_id),
            kind: ResolvedCallKind::BoxNew,
        };
    }
    // Step 8b: Mapping::from_closure — connect closure body to Mapping value (#2316)
    if is_mapping_from_closure_path(&path) {
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
    if is_map_inv_path(&path) && args.len() == 2 {
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

fn try_int_partial_eq_call(
    call_path: &str,
    args: &[Spanned<Operand<'_>>],
    local_exprs: &impl ExprLookup,
) -> Option<PureExpr> {
    if args.len() != 2 || !call_path.contains("PartialEq") {
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
    let Operand::Constant(box constant) = func else {
        return None;
    };
    let rustc_middle::ty::TyKind::FnDef(_, substs) = constant.ty().kind() else {
        return None;
    };

    // `size_of::<T>()` has exactly one type parameter `T` as its first subst.
    let type_arg = substs.types().next()?;
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
