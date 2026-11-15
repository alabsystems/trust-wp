// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-site DefId resolution and parameter name lookup.
//!
//! Bridges MIR operands to DefId-level function identity and resolves
//! parameter names for user-defined functions, enabling spec substitution
//! with actual parameter names. Local functions use HIR; cross-crate
//! functions fall back to MIR `var_debug_info`. (#2215)

use rustc_hir::{def_id::DefId, Node, TraitFn, TraitItemKind};
use rustc_middle::{
    mir::Operand,
    ty::{TyCtxt, TyKind},
};
use tracing::debug;

/// Extract the `DefId` from a function call operand.
pub(super) fn extract_call_def_id(func: &Operand<'_>) -> Option<DefId> {
    if let Operand::Constant(deref!(constant)) = func {
        if let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() {
            return Some(*def_id);
        }
    }
    None
}

/// Resolve an impl method `DefId` to its trait method `DefId`.
///
/// When MIR calls a trait impl method (e.g., `<Closure as Fn>::call`),
/// the DefId points to the specific impl. `tcx.def_path_str()` then
/// returns a path like `<closure as Fn<(usize,)>>::call` which doesn't
/// match the std_specs table entries like `core::ops::Fn::call`.
///
/// This function resolves back to the trait method DefId so that
/// `tcx.def_path_str()` returns the generic trait path. (#352)
pub(super) fn resolve_trait_method_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    let assoc_item = tcx.opt_associated_item(def_id)?;
    assoc_item.trait_item_def_id()
}

/// For a `Fn::call` / `FnOnce::call_once` / `FnMut::call_mut` call,
/// extract the concrete closure `DefId` from the FnDef's generic args.
///
/// When MIR compiles `c(2)` where `c` is a closure, it generates a call
/// to `<closure as Fn<(i32,)>>::call`. The `FnDef` type carries generic
/// args where `substs[0]` is the Self type — for concrete closures this
/// is `TyKind::Closure(closure_def_id, ...)`.
///
/// Returns `None` for non-closure Self types (e.g., generic `F: Fn(i32)`)
/// or non-FnDef operands.
pub(super) fn extract_closure_def_id_from_fn_call(func: &Operand<'_>) -> Option<DefId> {
    if let Operand::Constant(deref!(constant)) = func {
        if let TyKind::FnDef(_, substs) = constant.const_.ty().kind() {
            // substs[0] is the Self type for trait methods
            if let Some(self_ty) = substs.skip_binder().first().and_then(|arg| arg.as_type()) {
                if let TyKind::Closure(closure_def_id, _) = self_ty.kind() {
                    return Some(*closure_def_id);
                }
            }
        }
    }
    None
}

/// For a `Fn::call` / `FnOnce::call_once` / `FnMut::call_mut` call,
/// extract the concrete function item `DefId` from the FnDef's generic args.
///
/// When MIR compiles `let f = &some_fn; f(1)`, it generates a call to
/// `<fn(i32) -> i32 as Fn<(i32,)>>::call`. The `FnDef` type carries generic
/// args where `substs[0]` is the Self type — for function items this is
/// `TyKind::FnDef(fn_def_id, ...)`.
///
/// This complements [`extract_closure_def_id_from_fn_call`] which handles
/// closures. Together they enable spec resolution for any concrete callable
/// dispatched through the `Fn` trait family. (#1636)
///
/// Returns `None` for closures, generic `F: Fn(i32)` bounds, or non-FnDef operands.
pub(super) fn extract_fn_item_def_id_from_fn_trait_call(func: &Operand<'_>) -> Option<DefId> {
    if let Operand::Constant(deref!(constant)) = func {
        if let TyKind::FnDef(_, substs) = constant.const_.ty().kind() {
            if let Some(self_ty) = substs.skip_binder().first().and_then(|arg| arg.as_type()) {
                if let TyKind::FnDef(fn_def_id, _) = self_ty.kind() {
                    return Some(*fn_def_id);
                }
            }
        }
    }
    None
}

/// Resolve parameter names from a function's `DefId`.
///
/// For local functions, extracts names from HIR. For cross-crate functions,
/// falls back to MIR `var_debug_info` which preserves source-level parameter
/// names for compiled crates. Non-binding patterns fall back to positional
/// names ([`name_unnamed_params`]). (#2215)
pub(super) fn arg_names_for_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Vec<String>> {
    // Local functions: use HIR (source-level parameter names).
    if let Some(local_def_id) = def_id.as_local() {
        if let Some(hir_body_id) = tcx.hir_node_by_def_id(local_def_id).body_id() {
            let hir_body = tcx.hir_body(hir_body_id);
            let names = hir_body
                .params
                .iter()
                .map(|param| match param.pat.kind {
                    rustc_hir::PatKind::Binding(_, _, ident, _) => Some(ident.as_str().to_string()),
                    _ => None,
                })
                .collect();
            return Some(name_unnamed_params(names));
        }

        // Trait method declarations without default bodies have no HIR body.
        // Pull parameter names from the trait signature so generic call-site
        // postconditions can still substitute named parameters like `x` and `y`.
        if let Node::TraitItem(trait_item) = tcx.hir_node_by_def_id(local_def_id) {
            if let TraitItemKind::Fn(_, TraitFn::Required(param_names)) = trait_item.kind {
                let names = param_names
                    .iter()
                    .map(|ident| {
                        ident
                            .map(|ident| ident.as_str().to_string())
                            .filter(|name| !name.is_empty() && name != "_")
                    })
                    .collect();
                return Some(name_unnamed_params(names));
            }
        }
    }

    // Cross-crate: extract names from MIR var_debug_info. (#2215)
    arg_names_from_cross_crate_mir(tcx, def_id)
}

/// Extract parameter names from cross-crate MIR `var_debug_info`.
/// Arguments are locals `_1`..`_N` (where N = `arg_count`); `_1` is `self` for methods.
fn arg_names_from_cross_crate_mir(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Vec<String>> {
    if !tcx.is_mir_available(def_id) {
        return None;
    }
    let body = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tcx.optimized_mir(def_id)))
        .ok()?;
    let arg_count = body.arg_count;
    if arg_count == 0 {
        return Some(Vec::new());
    }
    // Map MIR local index → debug name. Local 0 is return place; args are 1..=arg_count.
    use rustc_middle::mir::VarDebugInfoContents;
    let mut arg_names: Vec<Option<String>> = vec![None; arg_count];
    for debug_info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = &debug_info.value {
            let local_idx = place.local.as_usize();
            if local_idx >= 1 && local_idx <= arg_count {
                arg_names[local_idx - 1] = Some(debug_info.name.as_str().to_string());
            }
        }
    }
    Some(name_unnamed_params(arg_names))
}

/// Prefix of the positional name a parameter with no usable source name is
/// registered under (`_`, a destructuring pattern, missing debug info).
///
/// It lies in the `__twp` namespace, which no source identifier of a verified
/// crate may use (`creusot_frontend_checks::validate_reserved_binding_names`
/// refuses items, bindings, paths and specification identifiers there), so no
/// module item, static, closure capture or clause name can be spelled like a
/// positional parameter and be read as one. `arg{idx}` could: a module `const
/// arg0` was substituted into the projection `(arg0.0)` a pattern binding is
/// stated as (param_pattern_projection_read_as_module_const), and a closure's
/// captured `arg0` was read as its destructured parameter
/// (closure_fallback_param_name_captures_upvar).
pub(crate) const POSITIONAL_PARAM_PREFIX: &str = "__twp_arg";

/// Reserved prefix of the name given to a parameter with no usable source
/// name when its positional name is taken by another parameter.
pub(crate) const ANON_PARAM_PREFIX: &str = "$anon_arg";

/// Prefix of the placeholder variables standing for a call argument the MIR
/// translator could not express.
pub(crate) const FALLBACK_ARG_PREFIX: &str = "$fallback_arg";

static FALLBACK_ARG_COUNTER: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// A FRESH placeholder variable for an untranslatable call argument at
/// position `idx`.
///
/// The placeholder used to be `Var("arg{idx}")`. That name (a) collides with a
/// caller variable literally named `arg{idx}`, so a callee contract such as
/// `result == v` became a fact about the caller's own `arg0`, and (b) is shared
/// by every call site with the same argument position, so `id(K1)` and
/// `id(K2)` were both equated with the same symbol. The placeholder is
/// therefore drawn from the reserved `__trust_wp_` namespace and numbered per
/// creation, so it denotes an unconstrained value distinct from every other
/// placeholder and every source variable.
pub(crate) fn fresh_fallback_arg_var(
    idx: usize,
    sort: Option<trust_wp_core::formula::ExprSort>,
) -> trust_wp_core::formula::PureExpr {
    let n = FALLBACK_ARG_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    trust_wp_core::formula::PureExpr::Var(format!("{FALLBACK_ARG_PREFIX}{idx}_{n}"), sort)
}

/// True for a placeholder produced by [`fresh_fallback_arg_var`].
pub(crate) fn is_fallback_arg_placeholder(name: &str) -> bool {
    name.starts_with(FALLBACK_ARG_PREFIX)
}

/// Name every parameter, keeping source names and giving each unnamed one
/// (`_`, a destructuring pattern, missing debug info) the positional name
/// [`POSITIONAL_PARAM_PREFIX`]`{idx}`, unless another parameter of the same
/// signature is literally named that (only a crate trust-wp does not check
/// can spell it). The result is injective: call sites bind clause names to
/// arguments by these names (later names win), so a fallback that collided
/// with a real parameter of that spelling would bind the real parameter's
/// clause occurrences to the wrong argument. A colliding fallback gets a name
/// in the `$anon_arg` namespace instead, disambiguated further if even that
/// is taken.
pub(crate) fn name_unnamed_params(names: Vec<Option<String>>) -> Vec<String> {
    let real: std::collections::HashSet<String> = names.iter().flatten().cloned().collect();
    let mut used: std::collections::HashSet<String> = real.clone();
    names
        .into_iter()
        .enumerate()
        .map(|(idx, name)| match name {
            Some(name) => name,
            None => {
                let mut candidate = format!("{POSITIONAL_PARAM_PREFIX}{idx}");
                let mut attempt = 0usize;
                while used.contains(&candidate) {
                    candidate = if attempt == 0 {
                        format!("{ANON_PARAM_PREFIX}{idx}")
                    } else {
                        format!("{ANON_PARAM_PREFIX}{idx}_{attempt}")
                    };
                    attempt += 1;
                }
                used.insert(candidate.clone());
                candidate
            }
        })
        .collect()
}

/// Resolve argument names with fallback chain and diagnostic.
///
/// Tries (in order): spec-provided parameter names → HIR/MIR parameter names →
/// empty default. Emits a warning when all sources are unavailable, since the
/// resulting empty name vector causes named contract parameters to remain
/// unsubstituted (#1653).
///
/// Spec-provided names take precedence over the callee's HIR/MIR parameter
/// names because a std/extern spec's clause text is authored against the
/// `params:` line declared in the spec string — not against the real
/// function's source-level parameter identifiers. These usually coincide
/// (and for most std functions `arg_names_for_def_id` returns `None`, so the
/// distinction is moot), but they diverge when the spec deliberately renames
/// a parameter. For example, the generic `<[T]>::get` / `Vec::get` spec uses
/// `ix` (so its clauses can call the `ix.in_bounds(self@)` / `ix.has_value`
/// `SliceIndexSpec` surface), while rustc reports the real parameter name as
/// `index`. Preferring the MIR name `index` left the spec's `ix` unsubstituted
/// — a free variable — which silently dropped the in-bounds/`Some` postcondition
/// and made `addr.get(left/8)`'s `None`-arm unreachability undischargeable.
/// This only re-binds the spec's own parameter name to the (unchanged) actual
/// call argument; it introduces no new assumption.
pub(crate) fn resolve_arg_names_or_warn(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    spec_param_names: Option<&Vec<String>>,
) -> Vec<String> {
    if let Some(names) = resolve_spec_or_mir_arg_names(tcx, def_id, spec_param_names) {
        return names;
    }
    let path = tcx.def_path_str(def_id);
    debug!(
        "trust-wp: warning: no parameter names for `{path}` ({def_id:?}), \
         using positional fallback — named contract parameters will not be substituted"
    );
    Vec::new()
}

/// Resolve parameter names for spec substitution, preferring the spec's own
/// declared `params:` names over the callee's HIR/MIR parameter identifiers.
///
/// Returns `None` only when neither source is available.
///
/// A std/extern spec's clause text is authored against the parameter names on
/// its `params:` line, not against the real function's source-level parameter
/// identifiers. These usually coincide (and for most std functions
/// `arg_names_for_def_id` returns `None`, so the distinction never matters),
/// but they diverge when a spec deliberately renames a parameter. The generic
/// `<[T]>::get` / `Vec::get` spec, for instance, names its index `ix` so its
/// clauses can use the `ix.in_bounds(self@)` / `ix.has_value(...)`
/// `SliceIndexSpec` surface, while rustc reports the real parameter name as
/// `index`. Preferring the MIR name left the spec's `ix` unsubstituted — a
/// free variable — silently dropping the in-bounds/`Some` postcondition. The
/// spec names win only when they are positionally consistent with the callee's
/// real parameters (same arity); an arity mismatch means the spec models a
/// different surface (const-generic / implicit-receiver shapes handled
/// elsewhere), so the MIR names are used there. This only re-binds the spec's
/// own parameter name to the (unchanged) actual call argument; it introduces no
/// new assumption.
pub(crate) fn resolve_spec_or_mir_arg_names(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    spec_param_names: Option<&Vec<String>>,
) -> Option<Vec<String>> {
    let mir_names = arg_names_for_def_id(tcx, def_id);
    match (spec_param_names, mir_names) {
        (Some(spec_names), Some(mir_names)) => {
            if mir_names.len() == spec_names.len() {
                Some(spec_names.clone())
            } else {
                Some(mir_names)
            }
        }
        (Some(spec_names), None) => Some(spec_names.clone()),
        (None, mir_names) => mir_names,
    }
}

/// Build a UFCS-qualified path for a trait method call using the Self type.
///
/// For a call like `<Snapshot<T> as Deref>::deref`, the MIR may carry the
/// trait method DefId (`core::ops::Deref::deref`) rather than the impl
/// method. This function extracts the concrete Self type from the FnDef's
/// generic args and constructs the UFCS path `<SelfType as Trait>::method`
/// so that impl-specific specs (e.g., Snapshot::deref) can be found.
///
/// Returns `None` if the operand is not a trait method call or the Self type
/// is not an ADT.
pub(super) fn ufcs_path_for_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<String> {
    let Operand::Constant(deref!(constant)) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, substs) = constant.const_.ty().kind() else {
        return None;
    };
    let assoc_item = tcx.opt_associated_item(*def_id)?;
    // Accept both trait methods (container=Trait) and impl methods that
    // override a trait method (trait_item_def_id is Some).
    let is_trait_method = matches!(
        assoc_item.container,
        rustc_middle::ty::AssocContainer::Trait
    ) || assoc_item.trait_item_def_id().is_some();
    if !is_trait_method {
        return None;
    }
    // Get the Self type from substs[0].
    // Peel references: MIR trait method calls may carry the reference-wrapped
    // Self type (e.g., `&[T]` for `<[T] as Index<usize>>::index`) rather than
    // the bare implementing type. Without peeling, `&[T]` falls through to the
    // default `return None` branch and the call becomes opaque. (#2004)
    let self_ty = substs.skip_binder().first()?.as_type()?;
    let self_ty_inner = self_ty.peel_refs();
    // Provenance (spec-provenance front): a UFCS path is only as trustworthy
    // as every printed path inside it. A local (or foreign lookalike) Self
    // type or trait prints like a library one, so refuse to build the path
    // unless each named item comes from a builtin provider crate. Callers then
    // fall back to the DefId-gated plain/trait-method lookups.
    let named_items_are_library = |ty: rustc_middle::ty::Ty<'_>| {
        ty.walk().all(|arg| match arg.as_type().map(|t| t.kind()) {
            Some(TyKind::Adt(adt_def, _)) => {
                crate::provenance::is_builtin_provider(tcx, adt_def.did())
            }
            Some(TyKind::Foreign(did)) => crate::provenance::is_builtin_provider(tcx, *did),
            _ => true,
        })
    };
    if !named_items_are_library(self_ty_inner) {
        return None;
    }
    let self_type_name = match self_ty_inner.kind() {
        TyKind::Adt(adt_def, _) => tcx.def_path_str(adt_def.did()),
        // Slice ([T]) and Array ([T; N]) implement Index/IndexMut traits.
        // MIR calls show the concrete Self type, but spec table entries use
        // generic "[T]" form. Produce "[T]" for both so UFCS paths match
        // specs like "<[T] as core::ops::IndexMut>::index_mut". (#1374)
        TyKind::Slice(_) => "[T]".to_string(),
        TyKind::Array(_, _) => "[T]".to_string(),
        TyKind::Str => "str".to_string(),
        // Primitive types implement Clone, Default, PartialEq, etc.
        // Without this, monomorphized calls like `<i32 as Default>::default`
        // fall through to the generic trait fallback instead of matching
        // the type-specific spec (e.g., `result == 0`). (#2256)
        TyKind::Bool => "bool".to_string(),
        TyKind::Int(int_ty) => int_ty.name_str().to_string(),
        TyKind::Uint(uint_ty) => uint_ty.name_str().to_string(),
        TyKind::Float(float_ty) => float_ty.name_str().to_string(),
        TyKind::Char => "char".to_string(),
        // Tuple types implement Default, PartialEq, Clone, etc.
        // Produce the Rust-syntax tuple type name so UFCS paths match
        // potential spec entries like `<(i32, i64) as Default>::default`.
        // Note: the spec table is unlikely to have tuple-specific entries,
        // but this enables the fallback to the generic trait method spec
        // (step 5) via `resolve_trait_method_def_id`. (#2670)
        TyKind::Tuple(tys) => {
            let inner: Vec<String> = tys
                .iter()
                .map(|ty| match ty.kind() {
                    TyKind::Bool => "bool".to_string(),
                    TyKind::Int(int_ty) => int_ty.name_str().to_string(),
                    TyKind::Uint(uint_ty) => uint_ty.name_str().to_string(),
                    TyKind::Float(float_ty) => float_ty.name_str().to_string(),
                    TyKind::Char => "char".to_string(),
                    TyKind::Adt(adt_def, _) => tcx.def_path_str(adt_def.did()),
                    _ => "_".to_string(),
                })
                .collect();
            if tys.is_empty() {
                "()".to_string()
            } else {
                format!("({})", inner.join(", "))
            }
        }
        // Never type: required for some trait impls in std.
        TyKind::Never => "!".to_string(),
        // Type parameters: `T: Trait` dispatched calls carry the type param name
        // as the Self type. Produce `<T as Trait>::method` so that UFCS path
        // lookup can try to match (step 4). While no concrete spec will match
        // `<T as Trait>::method`, the fallback to the generic trait method spec
        // (steps 5 and 6) handles these. Returning None here causes the UFCS
        // path to be skipped entirely, which is equivalent — but providing the
        // path enables diagnostic logging and future spec-table entries for
        // generic dispatch patterns. (#2670)
        TyKind::Param(param_ty) => param_ty.name.as_str().to_string(),
        _ => return None,
    };
    // Get the canonical trait path.
    // For impl-associated methods, use `trait_item_def_id` + `parent` to avoid
    // impl-container paths and keep UFCS lookup stable for trait specs.
    let trait_def_id = if matches!(
        assoc_item.container,
        rustc_middle::ty::AssocContainer::Trait
    ) {
        assoc_item.container_id(tcx)
    } else {
        let trait_method_id = assoc_item.trait_item_def_id()?;
        tcx.parent(trait_method_id)
    };
    if !crate::provenance::is_builtin_provider(tcx, trait_def_id) {
        return None;
    }
    let trait_path = tcx.def_path_str(trait_def_id);
    // Get the method name
    let method_name = assoc_item.name();
    Some(format!("<{self_type_name} as {trait_path}>::{method_name}"))
}

#[cfg(test)]
mod tests;
