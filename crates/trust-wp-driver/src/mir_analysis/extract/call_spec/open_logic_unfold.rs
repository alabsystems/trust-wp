// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Monomorphization-aware unfolding of OPEN trait-logic methods at call sites.
//!
//! # Problem
//!
//! A callee's contract may reference a trait logic method through a generic
//! bound, e.g. `MutexGuard::<T, I>::set` (where `I: Inv<T>`) carries
//! `#[requires(self.1.inv(v))]`. The `inv` method is abstract on the trait
//! `Inv` (no body), while a concrete `impl Inv<u32> for Even` provides an
//! OPEN body `#[logic(open(self))] fn inv(&self, x) { x.view() % 2 == 0 }`.
//!
//! When the abstract `Inv::inv` and the open `Even::inv` both derive the same
//! SMT symbol `logic_inv`, the abstract (opaque, first-writer-wins) declaration
//! drops the open body. The solver then sees `inv` as an UNINTERPRETED function
//! with no defining axiom and cannot relate `inv(t, val)` to `inv(t, val + 2)`,
//! yielding a spurious counterexample (e.g. the `mutex.rs` `AddsTwo::call`
//! obligation `val % 2 == 0 ⊢ (val + 2) % 2 == 0`).
//!
//! # Fix (faithful, sound — mirrors Creusot's transparent open-logic unfolding)
//!
//! At the call site we have the callee's FnDef substs (monomorphized): for
//! `set` on a `Mutex<u32, Even>` guard, the trait bound `I: Inv<T>` is
//! instantiated to `Even: Inv<u32>`. We resolve `<Even as Inv<u32>>::inv` to
//! the concrete in-crate impl method, confirm it is an OPEN logic method, and
//! UNFOLD `recv.inv(args)` to its body `[self := recv, params := args]` in the
//! freshly generated obligations / assumptions for THIS call. The opaque UF
//! never participates, so the obligation reduces to `(val + 2) % 2 == 0` under
//! `val % 2 == 0` — provable.
//!
//! # Soundness gates (every one is non-negotiable)
//!
//! 1. ONLY OPEN bodies (`#[logic(open)]` / `#[logic(open(self))]`). Never an
//!    abstract / opaque / `Default`-mode / `#[trusted]` method — those have no
//!    visible body and must remain uninterpreted.
//! 2. UNAMBIGUOUS resolution only. We require the callee to expose EXACTLY ONE
//!    in-scope trait bound that declares a logic method of the given name, AND
//!    that the monomorphized receiver type resolves to EXACTLY ONE concrete
//!    in-crate impl. If a name is reachable via two different bounds (or two
//!    impls), we DROP it — never unfold — so we can never bind a different
//!    impl's receiver (no universal-over-receiver).
//! 3. In-crate only. We only unfold bodies we can read from the local crate's
//!    HIR/doc markers; external impls fall back to current (opaque) behavior.
//! 4. Fail-closed. Any resolution uncertainty → no unfolding, identical to the
//!    pre-existing behavior. Mis-resolution would be a false-accept, so every
//!    branch that cannot prove unambiguity returns without rewriting.

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::Operand,
    ty::{self, GenericArgs, TyCtxt},
};
use trust_wp_core::{
    formula::{CaptureAvoidingSubstOptions, PureExpr},
    logic::LogicMode,
};

use crate::{
    attr_utils::get_contract_attrs_from_doc,
    logic::discovery::{extract_logic_mode, has_logic_marker},
};

/// A resolved open-logic unfolding: the concrete impl method's parameter names
/// (first is the receiver, conventionally `self`) and its body expression.
struct OpenLogicResolution {
    params: Vec<String>,
    body: PureExpr,
}

/// Build the set of open trait-logic methods that can be UNAMBIGUOUSLY unfolded
/// for a call to `callee_def_id` with monomorphized `substs`.
///
/// The returned map is keyed by the (short) method name. A name is present ONLY
/// when exactly one in-scope trait bound declares a logic method of that name
/// and the monomorphized receiver type resolves to exactly one open in-crate
/// impl method. Names that are ambiguous (multiple bounds / impls / partial
/// resolution) are intentionally absent.
fn build_open_logic_unfold_map<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    substs: GenericArgs<'tcx>,
) -> HashMap<String, OpenLogicResolution> {
    // For each trait predicate in the callee's where-clauses, instantiate it
    // with the call substs to get a concrete (monomorphized) trait reference,
    // then collect any OPEN logic methods of that trait resolved against the
    // concrete Self type. We track, per method name, the DISTINCT resolved impl
    // method DefIds so we can drop ambiguous names.
    let mut per_name: HashMap<String, Vec<(DefId, OpenLogicResolution)>> = HashMap::new();

    // Collect the callee's trait predicates AND those of its enclosing impl /
    // ancestors. A trait bound like `I: Inv<T>` is attached to the IMPL block,
    // not the method, so `clauses_of(method)` alone misses it; we follow the
    // `parent` chain (method -> impl -> ...) to gather every in-scope bound.
    let mut all_predicates: Vec<_> = Vec::new();
    let mut cur = Some(callee_def_id);
    while let Some(did) = cur {
        let preds = tcx.clauses_of(did);
        all_predicates.extend(preds.clauses.iter().copied());
        cur = preds.parent;
    }
    for &(clause, _span) in &all_predicates {
        let Some(trait_pred) = clause.as_trait_clause() else {
            continue;
        };
        // Instantiate the (possibly generic) trait predicate with the call's
        // substs. The binder is skipped; the substs monomorphize the type
        // parameters (e.g. `I -> Even`, `T -> u32`).
        let trait_ref = trait_pred.skip_binder().trait_ref;
        let trait_ref = ty::EarlyBinder::bind(tcx, trait_ref)
            .instantiate(tcx, substs)
            .skip_norm_wip();
        let trait_def_id = trait_ref.def_id;

        // Skip auto/marker traits (Send, Sync, Sized, ...) — they declare no
        // logic methods.
        if tcx.trait_is_auto(trait_def_id) {
            continue;
        }

        let self_ty = trait_ref.self_ty();
        // We can only resolve an in-crate impl for a concrete nominal ADT Self.
        // A still-generic Self (TypeParam) means the surrounding function was
        // itself generic and the receiver type is unknown — fail closed.
        if !matches!(self_ty.kind(), ty::TyKind::Adt(..)) {
            continue;
        }

        for assoc in tcx.associated_items(trait_def_id).in_definition_order() {
            if !matches!(assoc.kind, ty::AssocKind::Fn { .. }) {
                continue;
            }
            let trait_method_def_id = assoc.def_id;
            // The TRAIT method must itself be a logic method (so a contract
            // calling it really is a logic-fn call, not a runtime method).
            if !has_logic_marker(tcx.get_all_attrs(trait_method_def_id)) {
                continue;
            }
            let method_name = assoc.name().to_string();

            // Resolve the concrete impl method for this trait method against the
            // monomorphized substs. `Instance::try_resolve` performs the same
            // monomorphization-faithful resolution codegen uses.
            let Some(resolution) = resolve_open_impl_body(tcx, trait_method_def_id, trait_ref.args)
            else {
                continue;
            };
            per_name.entry(method_name).or_default().push(resolution);
        }
    }

    // Keep only unambiguous names: exactly one resolved impl method DefId.
    let mut out = HashMap::new();
    for (name, mut resolutions) in per_name {
        // Distinct by impl-method DefId.
        let first_did = resolutions[0].0;
        let all_same = resolutions.iter().all(|(did, _)| *did == first_did);
        if all_same {
            // Safe: vector is non-empty and all entries share the impl DefId.
            let (_, resolution) = resolutions.swap_remove(0);
            out.insert(name, resolution);
        }
        // else: ambiguous — DROP (never unfold), preserving opaque behavior.
    }
    out
}

/// Resolve a trait logic method to its concrete in-crate OPEN impl body.
///
/// Returns `Some` only when:
/// - `Instance::try_resolve` yields a concrete user-defined impl method,
/// - that method is local (in-crate) and an OPEN logic method, and
/// - its body text parses into a `PureExpr`.
///
/// Any failure → `None` (fail closed; caller keeps opaque behavior).
fn resolve_open_impl_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_method_def_id: DefId,
    trait_args: GenericArgs<'tcx>,
) -> Option<(DefId, OpenLogicResolution)> {
    let instance = ty::Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        trait_method_def_id,
        trait_args,
    )
    .ok()
    .flatten()?;

    let impl_method_def_id = match instance.def {
        ty::InstanceKind::Item(did) => did,
        _ => return None,
    };

    // Must NOT be the bare trait method (i.e. resolution actually found a
    // concrete impl override). If `try_resolve` returned the trait method
    // itself, there is no in-crate body to unfold.
    if impl_method_def_id == trait_method_def_id {
        return None;
    }

    // In-crate only: we read the body from the local crate's doc markers / HIR.
    impl_method_def_id.as_local()?;

    let attrs = tcx.get_all_attrs(impl_method_def_id);
    // The impl method must carry the logic marker and be OPEN. An open mode is
    // the ONLY case where the body is semantically visible to callers; Default
    // (opaque) / Prophetic / non-logic must NOT be unfolded.
    if !has_logic_marker(attrs) {
        return None;
    }
    let mode = extract_logic_mode(attrs);
    if !matches!(mode, LogicMode::Open | LogicMode::OpenSelf) {
        return None;
    }

    // `#[trusted]` open methods (ghost stubs) have no semantic body — never
    // unfold them.
    if attrs
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .any(|v| v.as_str().starts_with("trust-wp:trusted:"))
    {
        return None;
    }

    // Extract the open body text the proc macro embedded, then parse it.
    let body_text = get_contract_attrs_from_doc(attrs, "logic_body")
        .into_iter()
        .next()?;
    let body = trust_wp_core::contract_parser::parse_contract(&body_text).ok()?;

    // Parameter names (first is the receiver — conventionally `self`). Use the
    // impl method's own HIR parameter names so substitution binds correctly.
    let params = impl_method_param_names(tcx, impl_method_def_id)?;
    if params.is_empty() {
        return None;
    }
    // D-177: a name a parameter pattern binds is that parameter's projection.
    // Substituting the parameters alone would leave it free, to be read in the
    // caller's scope; a body that mentions one without a projection is not
    // unfolded at all.
    let bindings =
        crate::param_patterns::param_pattern_bindings(tcx, impl_method_def_id.as_local()?);
    let body = match crate::param_patterns::destructure_expr(&body, &bindings) {
        Ok(destructured) => destructured.unwrap_or(body),
        Err(_) => return None,
    };

    Some((impl_method_def_id, OpenLogicResolution { params, body }))
}

/// Parameter names for an impl logic method, in declaration order (receiver
/// first). Returns `None` if the method has no HIR body to read names from.
fn impl_method_param_names(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Vec<String>> {
    let local = def_id.as_local()?;
    let body_id = tcx.hir_node_by_def_id(local).body_id()?;
    let hir_body = tcx.hir_body(body_id);
    // Unnamed parameters get collision-free fallback names: a positional name
    // equal to a real parameter name would make the later binding win in the
    // substitution map and unfold the body against the wrong argument.
    let raw: Vec<Option<String>> = hir_body
        .params
        .iter()
        .map(|param| match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, ident, _) => Some(ident.as_str().to_string()),
            _ => None,
        })
        .collect();
    Some(crate::mir_analysis::name_unnamed_params(raw))
}

/// Unfold open trait-logic method calls inside `expr` according to `unfold_map`.
///
/// Replaces every `recv.m(args)` (a `MethodCall`) and every `LogicFnCall { name:
/// m, args: [recv, rest..] }` whose `m` is an unambiguously resolved open method
/// with the impl body, substituting `[params := [recv, args..]]`. Substitution
/// is capture-avoiding. Calls whose arity does not match the resolved body's
/// parameter list are left untouched (defensive; should not happen for a
/// correctly resolved trait method).
fn unfold_expr(expr: &PureExpr, unfold_map: &HashMap<String, OpenLogicResolution>) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::MethodCall {
            ref receiver,
            ref method,
            ref args,
        } => {
            if let Some(resolution) = unfold_map.get(method) {
                // Actual args: receiver + explicit args.
                let mut actuals: Vec<PureExpr> = Vec::with_capacity(1 + args.len());
                actuals.push((**receiver).clone());
                actuals.extend(args.iter().cloned());
                if actuals.len() == resolution.params.len() {
                    let subst: HashMap<String, PureExpr> =
                        resolution.params.iter().cloned().zip(actuals).collect();
                    return resolution.body.substitute_capture_avoiding(
                        &subst,
                        &CaptureAvoidingSubstOptions::default(),
                    );
                }
            }
            node
        }
        PureExpr::LogicFnCall { ref name, ref args } => {
            if let Some(resolution) = unfold_map.get(name) {
                if args.len() == resolution.params.len() {
                    let subst: HashMap<String, PureExpr> = resolution
                        .params
                        .iter()
                        .cloned()
                        .zip(args.iter().cloned())
                        .collect();
                    return resolution.body.substitute_capture_avoiding(
                        &subst,
                        &CaptureAvoidingSubstOptions::default(),
                    );
                }
            }
            node
        }
        other => other,
    })
}

/// Extract the callee `DefId` and monomorphized substs from a call's `func`
/// operand. Returns `None` for indirect calls (non-`FnDef` operand).
fn callee_fn_def<'tcx>(func: &Operand<'tcx>) -> Option<(DefId, GenericArgs<'tcx>)> {
    let Operand::Constant(deref!(constant)) = func else {
        return None;
    };
    match constant.const_.ty().kind() {
        ty::TyKind::FnDef(def_id, substs) => Some((*def_id, substs.skip_binder())),
        _ => None,
    }
}

/// Unfold open trait-logic methods in the obligation and assumption expressions
/// that the just-applied callee contract appended to `effects`.
///
/// `obligations_before` / `assumptions_before` mark the lengths of the
/// respective effect vectors BEFORE the callee's `#[requires]` / `#[ensures]`
/// were applied, so only the freshly generated clauses for THIS call are
/// rewritten. No-op (early return) unless an unambiguous open-logic resolution
/// exists for the call, so the common path costs only the cheap FnDef/substs
/// inspection plus a predicate scan.
pub(super) fn unfold_open_logic_in_effects<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    effects: &mut crate::mir_analysis::effects::CallEffects,
    obligations_before: usize,
    assumptions_before: usize,
) {
    let Some((callee_def_id, substs)) = callee_fn_def(func) else {
        return;
    };
    // Substs must be concrete enough to resolve an impl. If they still mention
    // type/region params from a generic surrounding function we will simply fail
    // to resolve a concrete impl below and emit nothing — but skip cheaply when
    // there are no type args at all.
    if substs.is_empty() {
        return;
    }
    let unfold_map = build_open_logic_unfold_map(tcx, callee_def_id, substs);
    if unfold_map.is_empty() {
        return;
    }
    for obligation in effects.obligations.iter_mut().skip(obligations_before) {
        *obligation = unfold_expr(obligation, &unfold_map);
    }
    for assumption in effects.assumptions.iter_mut().skip(assumptions_before) {
        *assumption = unfold_expr(assumption, &unfold_map);
    }
}
