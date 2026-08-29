// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function discovery and parsing.
//!
//! Finds `#[logic]`/`#[predicate]` functions in a crate, extracts their
//! metadata (params, contracts, body text), and parses bodies into
//! [`LogicFnDef`] structures.

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    Attribute, Node, TraitFn, TraitItemKind,
};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    contract_parser::{parse_contract, parse_contract_body_with_leading_exprs},
    formula::{internal::tuple_lowering::tuple_logic_fn_name, ExprSort, PureExpr},
    logic::{LogicFnDef, LogicMode},
};

use super::attrs::{
    append_opaque_guard_if_needed, extract_ensures, extract_requires, extract_variants,
};

/// A logic function found in the crate.
#[derive(Debug)]
pub(crate) struct LogicFunction {
    /// Function name
    pub(crate) name: String,
    /// Full path (e.g., "crate::specs::max")
    pub(crate) full_path: String,
    /// Parameter names
    pub(crate) params: Vec<String>,
    /// Preconditions (from #[requires(...)])
    pub(crate) requires: Vec<String>,
    /// Postconditions (from #[ensures(...)]).
    /// When non-empty, the logic function's body is verified against these.
    pub(crate) ensures: Vec<String>,
    /// Decreasing variants (from `#[variant(...)]`) for recursion checks.
    pub(crate) variants: Vec<String>,
    /// Whether this logic function is marked with `#[opaque]`.
    pub(crate) is_opaque: bool,
    /// Whether this logic function is marked with `#[trusted]`.
    ///
    /// Trusted logic functions have their ensures clauses treated as axioms
    /// rather than verification targets. (#2700)
    pub(crate) is_trusted: bool,
    /// Whether this logic function is marked as a Creusot compatibility law.
    pub(crate) is_law: bool,
    /// Openness mode from the `#[logic(...)]` attribute argument.
    pub(crate) mode: LogicMode,
    /// Whether this is an associated function declared in a trait.
    pub(crate) is_trait_method: bool,
    /// Sort annotations for parameters (parallel to `params`).
    /// Extracted from `tcx` function signatures. `None` = default (Int).
    pub(crate) param_sort_hints: Vec<Option<ExprSort>>,
    /// Sort annotation for the return type. Extracted from the function signature.
    pub(crate) return_sort_hint: Option<ExprSort>,
    /// Function body as source text (to be parsed)
    pub(crate) body_text: Option<String>,
    /// For a `DeepModel::deep_model` trait-impl method, the set of in-crate
    /// `<C as DeepModel>::deep_model` full-paths that this impl's body can
    /// actually dispatch into, resolved from the implementing ADT's field
    /// types (descending through every type-constructor generic argument,
    /// e.g. `Box`/`Option`/`Vec`/references). Used by recursion detection to
    /// replace the text-scan blanket edge — text scanning cannot tell whether
    /// `field.deep_model()` recurses into a sibling concrete type or just a
    /// primitive/generic, so it fabricated a fully-connected SCC.
    ///
    /// Semantics:
    /// - `Some(set)` — resolved typed dispatch targets (may be empty, meaning
    ///   the body only recurses into primitives/generics → genuinely
    ///   non-recursive, like `#[derive(DeepModel)]` on a flat struct).
    /// - `None` — not a resolvable in-crate `deep_model` impl, OR the typed
    ///   resolution could not run; callers DEFAULT-REJECT (fall back to the
    ///   conservative text-scan behavior) on `None`.
    pub(crate) deep_model_dispatch_targets: Option<std::collections::HashSet<String>>,
}

/// Find all functions marked with `#[logic]` attribute.
///
/// This searches for functions that have the `#[doc = "trust-wp:logic:"]` attribute
/// which is added by the `#[logic]` proc macro. Using doc markers because proc
/// macro attributes are consumed during expansion.
pub(crate) fn find_logic_functions(tcx: TyCtxt<'_>) -> Vec<LogicFunction> {
    let mut logic_fns = Vec::new();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();

        // Only consider functions
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }

        // Check for #[doc = "trust-wp:logic:"] marker
        let attrs = tcx.get_all_attrs(def_id);
        if !has_logic_marker(attrs) {
            continue;
        }

        // Extract function information.
        // Qualify with crate name since tcx.def_path_str() omits it for local items.
        // scope_logic_fn_modes compares caller/function parent modules on these
        // crate-qualified paths, so local items need the prefix as well.
        let local_path = tcx.def_path_str(def_id);
        let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
        let full_path = format!("{crate_name}::{local_path}");
        let name = extract_function_name(&full_path);
        let const_param_names = get_const_generic_param_names(tcx, def_id);
        let mut params = const_param_names.clone();
        params.extend(get_param_names_from_hir(tcx, local_def_id));
        let mut param_sort_hints = vec![Some(ExprSort::Int); const_param_names.len()];
        param_sort_hints.extend(get_param_sort_hints(tcx, def_id));
        let return_sort_hint = get_return_sort_hint(tcx, def_id);
        let mut requires = extract_requires(attrs);
        let ensures = extract_ensures(attrs);
        // Recover the erased `>= 0` invariant of unsigned-integer parameters
        // (ExprSort collapses signedness), but ONLY for logic fns whose contract
        // contains a genuine multiplication — the sole case the nonneg bound is
        // needed (to discharge the antecedent of the nonlinear product-bound
        // completeness pass, e.g. `a@*a@ <= 1_000_000` over `a: usize`). Gating
        // on multiplication avoids polluting bitwise/bitvector logic fns (e.g.
        // `count8_log`: `n & 0x..`), where injecting `n@ >= 0` on a BV-modeled
        // param breaks the BV proof (regressed bitvectors/{bits,popcount}).
        // SOUND: the nonneg fact is always-true for unsigned values; the gate
        // only narrows WHERE it is added, never admits a false model.
        if requires
            .iter()
            .chain(ensures.iter())
            .any(|c| contract_has_multiplication(c))
        {
            requires.extend(unsigned_nonneg_requires(
                tcx,
                def_id,
                &params,
                const_param_names.len(),
            ));
        }
        let variants = extract_variants(attrs);
        let is_opaque = has_opaque_marker(attrs);
        // An impl logic method inherits trusted from its trait declaration so
        // that Creusot-style "theorem" trait methods (e.g.,
        // `WellFounded::no_infinite_decreasing_sequence`) are axiomatized
        // crate-wide. Without this, impls override the default with bodies
        // (often containing parameterized closures, #985) whose postconditions
        // would otherwise be marked unverified. (#985)
        let is_trusted = has_trusted_doc_marker(attrs) || inherits_trusted_from_trait(tcx, def_id);
        let is_law = has_law_doc_marker(attrs);
        let mode = extract_logic_mode(attrs);
        let is_trait_method = tcx.opt_associated_item(def_id).is_some_and(|assoc| {
            matches!(assoc.container, rustc_middle::ty::AssocContainer::Trait)
        });

        // Try to extract body text from doc marker first (reliable),
        // then fall back to HIR extraction (may get erased body).
        let body_text =
            extract_body_text_from_doc(attrs).or_else(|| extract_body_text(tcx, local_def_id));

        let deep_model_dispatch_targets = compute_deep_model_dispatch_targets(tcx, def_id, &name);

        logic_fns.push(LogicFunction {
            name,
            full_path,
            params,
            requires,
            ensures,
            variants,
            is_opaque,
            is_trusted,
            is_law,
            mode,
            is_trait_method,
            param_sort_hints,
            return_sort_hint,
            body_text,
            deep_model_dispatch_targets,
        });
    }

    logic_fns
}

/// Heuristic: does a contract clause contain a binary multiplication `*`?
///
/// A multiplication `*` is preceded — ignoring one optional space — by an
/// operand-ending char (`@`, alphanumeric, `_`, `)`, `]`). A dereference `*`
/// is preceded by `(`, an operator, a comma, or start-of-expression, so it is
/// NOT matched. This distinguishes `a@ * b` / `x*y` (multiplication) from
/// `*x` / `(*x)` (dereference) without a full parse, which is all the
/// nonneg-injection gate needs (#knights-tour).
fn contract_has_multiplication(contract: &str) -> bool {
    let bytes = contract.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        if b != b'*' {
            continue;
        }
        // Walk back to the previous non-space byte.
        let mut j = i;
        while j > 0 {
            j -= 1;
            if bytes[j] != b' ' {
                let prev = bytes[j];
                if prev == b'@'
                    || prev == b')'
                    || prev == b']'
                    || prev == b'_'
                    || prev.is_ascii_alphanumeric()
                {
                    return true;
                }
                break;
            }
        }
    }
    false
}

/// Build synthetic `requires` clauses asserting non-negativity of unsigned
/// integer parameters of a logic function.
///
/// Rust's unsigned integer types (`usize`, `u8`..`u128`) have an implicit
/// `>= 0` invariant on their `@` view. trust-wp's `ExprSort` collapses all
/// integers to `ExprSort::Int`, erasing signedness, so the SMT solver is
/// otherwise free to pick a negative model value for an unsigned parameter in
/// an isolated logic-function postcondition VC. That produces spurious
/// counterexamples — e.g. `#[requires(a@ <= 1000)] #[ensures(a@*a@ <= 1_000_000)]`
/// over `a: usize` is a theorem only because `a@ >= 0`.
///
/// Recovers the erased fact from the real MIR signature (`TyKind::Uint`) and
/// emits a `"<param>@ >= 0"` source clause per unsigned parameter. SOUND: the
/// fact is always true for an unsigned value, so it can only constrain (never
/// admit) models. Signed and non-integer parameters are skipped.
fn unsigned_nonneg_requires(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    params: &[String],
    param_offset: usize,
) -> Vec<String> {
    use rustc_middle::ty::TyKind;

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();

    sig.inputs()
        .iter()
        .enumerate()
        .filter_map(|(i, ty)| {
            if !matches!(ty.kind(), TyKind::Uint(_)) {
                return None;
            }
            let name = params.get(param_offset + i)?;
            Some(format!("{name}@ >= 0"))
        })
        .collect()
}

/// Check if the attributes include `#[doc = "trust-wp:logic:"]`.
///
/// The `#[logic]` proc macro embeds this doc marker because proc macro attributes
/// are consumed during expansion and not visible to tcx.get_all_attrs().
pub(crate) fn has_logic_marker(attrs: &[Attribute]) -> bool {
    for attr in attrs {
        if let Some(value) = crate::attr_utils::doc_marker_str(attr) {
            if value.as_str().starts_with("trust-wp:logic:") {
                return true;
            }
        }
    }
    false
}

/// Extract the `LogicMode` from the `trust-wp:logic:{suffix}` doc marker.
///
/// Parses the suffix after `"trust-wp:logic:"` to determine the openness mode.
pub(crate) fn extract_logic_mode(attrs: &[Attribute]) -> LogicMode {
    for attr in attrs {
        if let Some(value) = crate::attr_utils::doc_marker_str(attr) {
            let s = value.as_str();
            if let Some(suffix) = s.strip_prefix("trust-wp:logic:") {
                return LogicMode::from_marker_suffix(suffix);
            }
        }
    }
    LogicMode::Default
}

/// Check if the attributes include `#[doc = "trust-wp:opaque:"]`.
fn has_opaque_marker(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .any(|value| value.as_str().starts_with("trust-wp:opaque:"))
}

/// Check if the attributes include `#[doc = "trust-wp:trusted:"]`.
///
/// This is a lightweight check for the trusted doc marker emitted by the
/// `#[trusted]` proc macro. Unlike the full `has_trusted_marker` in
/// `callbacks::discovery::trusted`, this does NOT check for ancestor module
/// propagation. For logic function discovery, the proc macro always emits
/// the marker directly on the function item, so direct attribute checking
/// is sufficient. (#2700)
fn has_trusted_doc_marker(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .any(|value| value.as_str().starts_with("trust-wp:trusted:"))
}

/// Whether an impl logic method inherits its `#[trusted]` from its trait
/// declaration.
///
/// Creusot-style "theorem" trait methods (e.g.,
/// `WellFounded::no_infinite_decreasing_sequence`) are axioms in disguise:
/// each implementor provides a witness body, but the postcondition is
/// supposed to hold by virtue of the type implementing the trait at all.
/// Marking the trait declaration `#[trusted]` should therefore axiomatize
/// every implementor's override too, otherwise impl bodies containing
/// parameterized closures (#985) get flagged unverified.
fn inherits_trusted_from_trait(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(assoc) = tcx.opt_associated_item(def_id) else {
        return false;
    };
    let Some(trait_method_id) = assoc.trait_item_def_id() else {
        return false;
    };
    if trait_method_id == def_id {
        return false;
    }
    has_trusted_doc_marker(tcx.get_all_attrs(trait_method_id))
}

/// Resolve, for a `DeepModel::deep_model` trait-impl method, the set of in-crate
/// `<C as DeepModel>::deep_model` full-paths reachable from the implementing
/// ADT's field types.
///
/// The `deep_model` logic body is erased to `unreachable!()` (the real
/// expression survives only as text), so the receiver types of the
/// `field.deep_model()` calls cannot be read from this fn's own HIR/MIR.
/// Instead we reconstruct them from the implementing ADT: a derived
/// `deep_model` recurses by calling `.deep_model()` on each field, so the set
/// of receiver types is exactly the set of field types. We over-approximate by
/// collecting EVERY nominal ADT reachable anywhere inside those field types
/// (recursing through all generic arguments of every type constructor — `Box`,
/// `Option`, `Vec`, references, tuples, ...). Over-approximation is sound here:
/// it can only keep a recursion edge that already exists, never invent a false
/// "non-recursive" verdict (which would be a false-accept).
///
/// Returns:
/// - `Some(set)` when `def_id` is an in-crate `impl DeepModel for <Adt>`'s
///   `deep_model` method whose Self type is a struct/enum we can walk. The set
///   holds the crate-qualified full-paths of every reachable in-crate
///   `deep_model` impl. An empty set means the body only recurses into
///   primitive/generic fields → genuinely non-recursive.
/// - `None` otherwise (the caller falls back to the conservative text scan).
fn compute_deep_model_dispatch_targets(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    name: &str,
) -> Option<std::collections::HashSet<String>> {
    use rustc_middle::ty::TyKind;

    if name != "deep_model" {
        return None;
    }

    // The method must be an associated fn inside a trait impl (`impl DeepModel
    // for <Adt>`). Its parent def is that impl.
    let impl_def_id = tcx.parent(def_id);
    if !matches!(
        tcx.def_kind(impl_def_id),
        rustc_hir::def::DefKind::Impl { of_trait: true }
    ) {
        return None;
    }
    let impl_trait_ref = tcx.impl_trait_ref(impl_def_id).skip_binder();
    let deep_model_trait_def_id = impl_trait_ref.def_id;
    // Sanity-gate on the trait name so we only ever act on `DeepModel` impls.
    if !tcx
        .def_path_str(deep_model_trait_def_id)
        .ends_with("DeepModel")
    {
        return None;
    }

    let self_ty = impl_trait_ref.self_ty();
    let TyKind::Adt(self_adt, self_substs) = self_ty.kind() else {
        // Non-ADT Self (primitive, slice, ...): no in-crate ADT fields to walk.
        return Some(std::collections::HashSet::new());
    };

    // Collect every nominal ADT DefId reachable through the Self ADT's field
    // types, recursing through all generic arguments of every type constructor.
    let mut reachable_adts: std::collections::HashSet<DefId> = std::collections::HashSet::new();
    let mut field_types: Vec<rustc_middle::ty::Ty<'_>> = Vec::new();
    for variant in self_adt.variants() {
        for field in &variant.fields {
            field_types.push(field.ty(tcx, self_substs).skip_norm_wip());
        }
    }
    for field_ty in field_types {
        collect_reachable_adts(tcx, field_ty, &mut reachable_adts, &mut 0);
    }

    // For each reachable in-crate ADT, find its in-crate `impl DeepModel` and
    // record the crate-qualified full-path of that impl's `deep_model` method.
    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
    let mut targets = std::collections::HashSet::new();
    for adt_did in reachable_adts {
        let Some(method_did) =
            find_in_crate_deep_model_method(tcx, adt_did, deep_model_trait_def_id)
        else {
            continue;
        };
        let path = format!("{crate_name}::{}", tcx.def_path_str(method_did));
        targets.insert(path);
    }

    Some(targets)
}

/// Recursively collect all nominal ADT `DefId`s appearing in `ty`, descending
/// through every generic argument of every ADT (`Box`/`Option`/`Vec`/...),
/// references, tuples, slices, and arrays. Bounded by a depth cap to avoid
/// pathological deep types; the cap is generous and only a defensive guard.
fn collect_reachable_adts<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    out: &mut std::collections::HashSet<DefId>,
    depth: &mut u32,
) {
    use rustc_middle::ty::TyKind;
    if *depth > 64 {
        return;
    }
    *depth += 1;
    match ty.kind() {
        TyKind::Adt(adt_def, substs) => {
            out.insert(adt_def.did());
            for arg in substs.types() {
                collect_reachable_adts(tcx, arg, out, depth);
            }
        }
        TyKind::Ref(_, inner, _) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            collect_reachable_adts(tcx, *inner, out, depth);
        }
        TyKind::Tuple(elems) => {
            for elem in elems.iter() {
                collect_reachable_adts(tcx, elem, out, depth);
            }
        }
        _ => {}
    }
    *depth -= 1;
}

/// Find the in-crate `impl DeepModel for <adt_did>`'s `deep_model` method
/// `DefId`, if one exists locally. Returns `None` for ADTs whose `DeepModel`
/// impl is external (primitives, std types) — those are not nodes in the
/// recursion graph and so cannot participate in an in-crate cycle.
fn find_in_crate_deep_model_method(
    tcx: TyCtxt<'_>,
    adt_did: DefId,
    deep_model_trait_def_id: DefId,
) -> Option<DefId> {
    for scan_local in tcx.iter_local_def_id() {
        let impl_def_id = scan_local.to_def_id();
        if !matches!(
            tcx.def_kind(impl_def_id),
            rustc_hir::def::DefKind::Impl { of_trait: true }
        ) {
            continue;
        }
        let impl_trait_ref = tcx.impl_trait_ref(impl_def_id).skip_binder();
        if impl_trait_ref.def_id != deep_model_trait_def_id {
            continue;
        }
        let rustc_middle::ty::TyKind::Adt(self_adt, _) = impl_trait_ref.self_ty().kind() else {
            continue;
        };
        if self_adt.did() != adt_did {
            continue;
        }
        for assoc in tcx.associated_items(impl_def_id).in_definition_order() {
            if assoc.name().as_str() == "deep_model"
                && matches!(tcx.def_kind(assoc.def_id), rustc_hir::def::DefKind::AssocFn)
                && assoc.def_id.as_local().is_some()
            {
                return Some(assoc.def_id);
            }
        }
    }
    None
}

/// Check if the attributes include `#[doc = "trust-wp:logic_law:"]`.
pub(crate) fn has_law_doc_marker(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .any(|value| value.as_str().starts_with("trust-wp:logic_law:"))
}

/// Extract function name from full path.
pub(super) fn extract_function_name(full_path: &str) -> String {
    full_path
        .rsplit("::")
        .next()
        .unwrap_or(full_path)
        .to_string()
}

/// Get parameter names from HIR.
fn get_param_names_from_hir(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Vec<String> {
    let mut names = Vec::new();

    if let Some(hir_body_id) = tcx.hir_node_by_def_id(def_id).body_id() {
        let hir_body = tcx.hir_body(hir_body_id);
        for param in hir_body.params {
            if let rustc_hir::PatKind::Binding(_, _, ident, _) = param.pat.kind {
                names.push(ident.as_str().to_string());
            } else {
                names.push(format!("arg{}", names.len()));
            }
        }
    }

    if !names.is_empty() {
        return names;
    }

    // Trait method declarations without default bodies have no HIR body. Reuse
    // the signature-level parameter names so declaration-only logic methods keep
    // the correct arity and receiver name for later dispatch.
    if let Node::TraitItem(trait_item) = tcx.hir_node_by_def_id(def_id) {
        if let TraitItemKind::Fn(_, TraitFn::Required(param_names)) = trait_item.kind {
            return param_names
                .iter()
                .enumerate()
                .map(|(idx, ident)| match ident {
                    Some(ident) => {
                        let name = ident.as_str();
                        if name.is_empty() || name == "_" {
                            format!("arg{idx}")
                        } else {
                            name.to_string()
                        }
                    }
                    None => format!("arg{idx}"),
                })
                .collect();
        }
    }

    names
}

fn get_const_generic_param_names(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<String> {
    tcx.generics_of(def_id)
        .own_params
        .iter()
        .filter(|param_def| {
            matches!(
                param_def.kind,
                rustc_middle::ty::GenericParamDefKind::Const { .. }
            )
        })
        .map(|param_def| param_def.name.as_str().to_string())
        .collect()
}

pub(super) fn looks_like_seq_type_name(ty_name: &str) -> bool {
    ty_name.starts_with("Seq<")
        || ty_name.ends_with("::logic::seq::Seq")
        || ty_name.contains("::Seq<")
        || ty_name.contains("::logic::seq::Seq<")
}

/// Extract sort annotations for function parameters from the `tcx` type system.
///
/// Uses `fn_sig` to get parameter types and maps them to `ExprSort` via
/// `sort_for_ty`. Carries full sort information (Bool, Seq, Int, TypeParam,
/// Datatype, etc.) instead of the former two-variant ParamSortHint.
fn get_param_sort_hints(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<Option<ExprSort>> {
    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();

    sig.inputs()
        .iter()
        .map(|ty| sort_for_ty(tcx, *ty))
        .collect()
}

fn get_return_sort_hint(tcx: TyCtxt<'_>, def_id: DefId) -> Option<ExprSort> {
    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    sort_for_ty(tcx, sig.output())
}

/// Map a Rust type to an `ExprSort` for logic function parameter/return sorts.
///
/// Uses `ty_to_expr_sort_enriched` (which resolves ADT names via `TyCtxt`) so
/// that logic functions returning Option, Result, FMap, Mapping, user-defined
/// enums, etc. get `ExprSort::Datatype(name)` instead of `None`. This enables
/// the encoder's `preseed_logic_fn_return_sort_hint` and declaration-based sort
/// resolution to use the correct return sort. (#994, #2231)
///
/// Seq types are checked first because `ty_to_expr_sort_enriched` maps them to
/// `Datatype("Seq<...>")` rather than the preferred `ExprSort::Seq`.
fn sort_for_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty<'tcx>) -> Option<ExprSort> {
    use rustc_middle::ty::TyKind;

    // Check for Seq types first (requires tcx for ADT path resolution).
    // Must precede ty_to_expr_sort_enriched because that maps Seq ADTs to
    // Datatype("Seq<...>") rather than the canonical ExprSort::Seq.
    let is_seq_type = |ty: rustc_middle::ty::Ty<'_>| -> bool {
        if let TyKind::Adt(adt_def, _) = ty.kind() {
            let path = tcx.def_path_str(adt_def.did());
            looks_like_seq_type_name(&path)
        } else {
            let ty_str = ty.to_string();
            looks_like_seq_type_name(&ty_str)
        }
    };

    if is_seq_type(ty) {
        return Some(ExprSort::Seq);
    }

    // Use enriched conversion to capture ADT names (Option, FMap, etc.) as
    // ExprSort::Datatype(name). Falls through to ty_to_expr_sort for
    // non-ADT types (Bool, Int, TypeParam, Tuple, etc.).
    crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, ty)
}

/// Extract logic function body text from doc marker.
///
/// The `#[logic]` proc macro embeds the original body text as
/// `#[doc = "trust-wp:logic_body:..."]` before erasing the body. This is more
/// reliable than HIR extraction because the erased body (`unreachable!()`) is
/// not parseable as a contract expression.
fn extract_body_text_from_doc(attrs: &[Attribute]) -> Option<String> {
    use crate::attr_utils::get_contract_attrs_from_doc;
    let bodies = get_contract_attrs_from_doc(attrs, "logic_body");
    bodies.into_iter().next()
}

/// Extract body text from HIR for parsing (fallback).
///
/// This extracts the source text of the function body to be parsed
/// as a contract expression. Falls back to HIR when no doc marker is present
/// (e.g., for logic functions from external crates or older macro versions).
fn extract_body_text(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<String> {
    use rustc_hir::ExprKind;

    let hir_body_id = tcx.hir_node_by_def_id(def_id).body_id()?;
    let hir_body = tcx.hir_body(hir_body_id);

    // The body value is the expression to extract
    let body_expr = hir_body.value;

    // For simple expressions, get the source text
    let source_map = tcx.sess.source_map();

    // Handle block expressions by extracting the inner expression
    let expr_to_extract = match &body_expr.kind {
        ExprKind::Block(block, _) => {
            // If block has a trailing expression, use that
            if let Some(expr) = block.expr {
                expr
            } else {
                body_expr
            }
        }
        _ => body_expr,
    };

    // Get the source span and extract text
    let span = expr_to_extract.span;
    source_map.span_to_snippet(span).ok()
}

/// Convert a `LogicFunction` to a `LogicFnDef` by parsing its body.
///
/// Returns `None` if the body cannot be parsed as a contract expression.
pub(crate) fn to_logic_fn_def(logic_fn: &LogicFunction) -> Option<LogicFnDef> {
    let declaration_only_trait_body = logic_fn.body_text.is_none() && logic_fn.is_trait_method;
    let mut force_opaque = false;
    let body = if logic_fn.is_trusted && logic_fn.body_text.is_some() {
        // Trusted methods supply a body only as a runtime stub (e.g.
        // `panic!("ghost code only")`). Skip body parsing; the symbol is
        // declared opaque so no defining axiom is emitted.
        force_opaque = true;
        declaration_only_trait_logic_body_for_trusted(logic_fn)
    } else {
        match logic_fn.body_text.as_ref() {
            Some(body_text) => {
                match parse_logic_body(body_text, logic_fn.return_sort_hint.as_ref()) {
                    Ok(body) => body,
                    Err(e) => {
                        // Bodies that are intentionally unparseable ghost stubs
                        // (e.g. `panic!(...)`) appear in Creusot-style trait impls
                        // — see crates/trust-wp-std/src/logic/ra. Fall back to a
                        // placeholder body and mark opaque so no defining axiom
                        // is emitted.
                        if is_ghost_stub_body(body_text) {
                            force_opaque = true;
                            declaration_only_trait_logic_body_for_trusted(logic_fn)
                        } else {
                            crate::result_protocol_state::record_parse_error();
                            eprintln!(
                                "trust-wp: error: failed to parse logic function body for {}: {}",
                                logic_fn.full_path, e
                            );
                            return None;
                        }
                    }
                }
            }
            None => declaration_only_trait_logic_body(logic_fn)?,
        }
    };

    let is_opaque = logic_fn.is_opaque || force_opaque;
    let mut requires = parse_contract_clauses(logic_fn.requires.iter(), logic_fn, "requires")?;
    // `#[opaque]` means callers should not get a defining axiom. We preserve
    // declaration/sort inference while forcing the generated axiom guard to
    // be unsatisfiable (`false => body_eq`), which is semantically inert.
    append_opaque_guard_if_needed(&mut requires, is_opaque);

    let ensures = parse_contract_clauses(logic_fn.ensures.iter(), logic_fn, "ensures")?;

    // Parse `#[variant(...)]` measures leniently. A variant is OPTIONAL metadata
    // used only to gate sound recursive-induction-hypothesis injection; an
    // unparseable variant must never abort logic-fn discovery (it just means no
    // IH will be injected — incompleteness, never a soundness change). (#ri)
    let parsed_variants: Vec<PureExpr> = logic_fn
        .variants
        .iter()
        .filter_map(|v| parse_contract(v).ok())
        .collect();

    let mut def = LogicFnDef::new_with_requires(
        logic_fn.name.clone(),
        logic_fn.full_path.clone(),
        logic_fn.params.clone(),
        requires,
        body,
    )
    .with_param_sorts(logic_fn.param_sort_hints.clone())
    .with_return_sort(logic_fn.return_sort_hint.clone())
    .with_variants(parsed_variants)
    .with_opaque(is_opaque || declaration_only_trait_body)
    .with_trusted(logic_fn.is_trusted || force_opaque)
    .with_law(logic_fn.is_law)
    .with_mode(logic_fn.mode)
    .detect_recursion();
    def.set_ensures(ensures);
    Some(def)
}

/// Detect bodies that are ghost-only stubs whose source intentionally uses
/// `panic!(...)` (or `unimplemented!(...)`/`todo!(...)`) because the function
/// is a specification placeholder. Matching is conservative: a single
/// statement-like macro invocation with a string literal payload.
fn is_ghost_stub_body(body_text: &str) -> bool {
    // `quote!` may emit whitespace around tokens (e.g. `panic ! ( ".." )`),
    // so normalize whitespace out before matching macro-call prefixes.
    let normalized: String = body_text.chars().filter(|c| !c.is_whitespace()).collect();
    let core = normalized
        .strip_prefix('{')
        .and_then(|s| s.strip_suffix('}'))
        .unwrap_or(&normalized);
    ["panic!(", "unimplemented!(", "todo!("]
        .iter()
        .any(|prefix| core.starts_with(prefix))
}

/// Parse a logic function body, preserving leading expression statements.
///
/// Logic bodies like `{ lemma_a(x); lemma_b(x); body_expr }` must retain the
/// leading semicolon-terminated calls. The plain `parse_contract` parser drops
/// them. This function uses `parse_contract_body_with_leading_exprs` and wraps
/// leading expressions into nested `PureExpr::Let` carriers (`__stmt0`, `__stmt1`,
/// ...) matching the shape expected by the manual verification tests.
///
/// Falls back to `parse_contract` when the input is not a block (no braces).
fn parse_logic_body(
    body_text: &str,
    return_sort_hint: Option<&ExprSort>,
) -> Result<PureExpr, trust_wp_core::contract_parser::ParseError> {
    // Try the block-body parser first. If the body is not a block (e.g., a
    // simple expression like `x + 1`), it may fail — fall back to parse_contract.
    match parse_contract_body_with_leading_exprs(body_text) {
        Ok((mut leading, tail)) if !leading.is_empty() => {
            if matches!(return_sort_hint, Some(ExprSort::Unit)) {
                leading.push(tail);
                Ok(wrap_leading_exprs_as_lets(leading, unit_expr()))
            } else {
                Ok(wrap_leading_exprs_as_lets(leading, tail))
            }
        }
        Ok((_, tail)) => Ok(tail),
        Err(_) => parse_contract(body_text),
    }
}

/// Wrap leading expression statements into nested `PureExpr::Let` carriers.
///
/// Produces `let __stmt0 = expr0 in let __stmt1 = expr1 in ... in tail`.
fn wrap_leading_exprs_as_lets(leading: Vec<PureExpr>, tail: PureExpr) -> PureExpr {
    leading
        .into_iter()
        .enumerate()
        .rev()
        .fold(tail, |body, (idx, expr)| PureExpr::Let {
            var: format!("__stmt{idx}"),
            value: std::sync::Arc::new(expr),
            body: std::sync::Arc::new(body),
        })
}

fn unit_expr() -> PureExpr {
    PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(0),
        args: vec![],
    }
}

fn parse_contract_clauses<'a>(
    clauses: impl IntoIterator<Item = &'a String>,
    logic_fn: &LogicFunction,
    clause_kind: &str,
) -> Option<Vec<trust_wp_core::formula::PureExpr>> {
    let mut parsed = Vec::new();
    for clause in clauses {
        match parse_contract(clause) {
            Ok(expr) => parsed.push(expr),
            Err(e) => {
                crate::result_protocol_state::record_parse_error();
                eprintln!(
                    "trust-wp: error: failed to parse logic function {clause_kind} '{}' for {}: {}",
                    clause, logic_fn.full_path, e
                );
                return None;
            }
        }
    }
    Some(parsed)
}

fn declaration_only_trait_logic_body(
    logic_fn: &LogicFunction,
) -> Option<trust_wp_core::formula::PureExpr> {
    if !logic_fn.is_trait_method || logic_fn.body_text.is_some() {
        return None;
    }
    if !logic_fn.is_opaque && logic_fn.mode != LogicMode::Default {
        return None;
    }

    // Declaration-only trait logic methods exist to publish the SMT symbol and
    // its signature. Default/opaque modes suppress the defining axiom, so this
    // literal is a transport placeholder rather than executable semantics.
    Some(trust_wp_core::formula::PureExpr::Int(0))
}

/// Placeholder body for trusted trait-method logic functions whose source
/// body is an unparseable ghost stub (typically `panic!("ghost code only")`).
/// `with_trusted(true)` later in `to_logic_fn_def` suppresses the defining
/// axiom; this value is a transport placeholder, never consulted semantically.
fn declaration_only_trait_logic_body_for_trusted(
    _logic_fn: &LogicFunction,
) -> trust_wp_core::formula::PureExpr {
    trust_wp_core::formula::PureExpr::Int(0)
}
