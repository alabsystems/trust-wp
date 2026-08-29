// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort resolution: `impl AYEncoder` methods for querying, conversion, and
//! variable sort resolution.

use ay_dpll::api::Sort;
use tracing::debug;
use trust_wp_core::{
    formula::{ExprSort, PureExpr},
    logic::logic_fn_smt_name,
};

use super::{derived_names::classify_var_name, resolve_registered_non_int_sort, DerivedKind};
use crate::encoder::{unsoundness, AYEncoder};

/// Peel concrete `MutRef` wrappers for variable declaration sort resolution.
///
/// The RustHorn encoding represents `&mut T` as (current, final) pairs of the
/// **inner** sort T, not as a composite MutRef SMT sort. When a MIR annotation
/// says `MutRef(Int)`, the variable should be declared as `Int`, not as
/// `Uninterpreted("MutRef_Int")`. The composite sort is only needed by
/// `bind_whole_borrow_aliases` for whole-borrow UF structure. (#2673)
///
/// Generic `MutRef(TypeParam(_))` is different: closure-spec precondition
/// triggers use the whole-borrow placeholder carrier, and peeling it to `Int`
/// splits quantified and ground UF signatures. Preserve that carrier. (#717)
fn peel_mutref_for_decl(sort: &ExprSort) -> ExprSort {
    match sort {
        ExprSort::MutRef(inner) if annotation_contains_type_param(inner) => sort.clone(),
        ExprSort::MutRef(inner) => peel_mutref_for_decl(inner),
        other => other.clone(),
    }
}

fn annotation_contains_type_param(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::TypeParam(_) => true,
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => annotation_contains_type_param(inner),
        _ => false,
    }
}

impl AYEncoder {
    fn project_reference_like_base_sort(&self, name: &str, base_sort: &Sort) -> Option<Sort> {
        super::project_reference_like_sort_for_requested_name(name, base_sort, self.seq_carrier())
    }

    pub(crate) fn is_bool_var(&self, name: &str) -> bool {
        matches!(self.sort_resolver.get_sort_hint(name), Some(s) if *s == ExprSort::Bool)
            || matches!(self.var_sort(name), Some(Sort::Bool))
    }

    /// Resolve the sort for a variable from all available sources. (#1319)
    pub(crate) fn resolve_var_sort(&mut self, name: &str) -> Option<Sort> {
        if let Some(sort) = self.var_sort(name) {
            return Some(sort.clone());
        }
        if let Some(hint) = self.sort_resolver.get_sort_hint(name).cloned() {
            return Some(self.sort_from_expr_sort(hint));
        }
        None
    }

    fn resolve_var_sort_candidate(&mut self, name: &str) -> Option<Sort> {
        if let Some(sort) = resolve_registered_non_int_sort(self, name) {
            return Some(sort);
        }
        if let Some(sort) = self.resolve_var_sort(name) {
            return Some(sort);
        }
        if let Some(derived_view) = DerivedKind::peel_final_view_prefix(name) {
            if let Some(sort) = self.resolve_derived_var_sort_candidate(&derived_view) {
                return Some(sort);
            }
        }
        if let Some((DerivedKind::View, base)) = DerivedKind::strip_from(name) {
            if let Some(sort) = self.resolve_var_sort_candidate(base) {
                return Some(sort);
            }
        }
        let mut base = name;
        while let Some((DerivedKind::Current | DerivedKind::Final | DerivedKind::Prime, stripped)) =
            DerivedKind::strip_from(base)
        {
            base = stripped;
            if let Some(sort) = self.var_sort(base).cloned() {
                if let Some(projected) = self.project_reference_like_base_sort(name, &sort) {
                    return Some(projected);
                }
                if sort != Sort::Int {
                    return Some(sort);
                }
                if let Some(hint) = self.sort_resolver.get_sort_hint(base).cloned() {
                    return Some(self.sort_from_expr_sort(hint));
                }
                return Some(sort);
            }
            if let Some(hint) = self.sort_resolver.get_sort_hint(base).cloned() {
                return Some(self.sort_from_expr_sort(hint));
            }
        }
        None
    }

    fn resolve_derived_var_sort_candidate(&mut self, name: &str) -> Option<Sort> {
        if let Some(sort) = self.resolve_var_sort_candidate(name) {
            return Some(sort);
        }
        for stripped in DerivedKind::peel_old_prefixes(name) {
            if let Some(sort) = self.resolve_var_sort_candidate(stripped) {
                return Some(sort);
            }
        }
        None
    }

    /// Resolve the sort for a variable, falling back to `Sort::Int`. (#1608)
    pub(crate) fn resolve_var_sort_or_int(&mut self, name: &str) -> Sort {
        self.resolve_var_sort_or_int_with_annotation(name, None)
    }

    /// Resolve the sort for a variable, with an optional ExprSort annotation
    /// from MIR type information. (#2039, #994, #2078)
    ///
    /// Phase 2 of #1965: When a non-Int `ExprSort` annotation is present, it
    /// is **authoritative** — the annotation was derived from MIR types in the
    /// driver and bypasses the entire heuristic hint cascade. Only `Int`
    /// annotations (a weak signal, since Int is also the default fallback) fall
    /// through to the cascade for backwards compatibility.
    ///
    /// Phase 3 (#2020 Slice 3): Distinguishes source names from derived names.
    /// Source names without a declaration or hint indicate a plan gap and emit
    /// a debug trace (`TRUST_WP_DEBUG`). Derived names (`_view`, `_current`,
    /// `_final`, `_prime`, `old_`, `final_*_view`) continue using the full
    /// suffix/prefix stripping cascade.
    #[track_caller]
    pub(crate) fn resolve_var_sort_or_int_with_annotation(
        &mut self,
        name: &str,
        annotation: Option<&trust_wp_core::formula::ExprSort>,
    ) -> Sort {
        // Phase 2 (#1965): ExprSort annotation from MIR is authoritative.
        // Any non-Int annotation bypasses the hint cascade entirely. Ref
        // layers are peeled to check the inner sort — if the innermost
        // sort is non-Int, the full annotation (including Ref wrapping)
        // is used directly.
        //
        // MutRef annotations are peeled to the inner sort before conversion
        // because the RustHorn encoding represents &mut T variables as
        // (current, final) pairs of the **inner** sort, not as a composite
        // MutRef SMT sort. Without this peeling, MutRef(Int) would produce
        // Uninterpreted("MutRef_Int") which is non-Int, causing the variable
        // to be declared with the wrong sort and triggering sort mismatches
        // in postcondition equality encoding. The composite MutRef sort is
        // only used by bind_whole_borrow_aliases for whole-borrow UF binding,
        // not for variable declarations. (#2673)
        if let Some(sort) = annotation {
            let peeled = peel_mutref_for_decl(sort);
            let ay_sort = self.sort_from_expr_sort(peeled);
            if ay_sort != Sort::Int {
                return ay_sort;
            }
        }
        // Direct lookup: declarations and hints for the exact name.
        if let Some(sort) = self.resolve_var_sort_candidate(name) {
            if sort != Sort::Int {
                return sort;
            }
            if self.var_sort(name).is_some() || self.sort_resolver.get_sort_hint(name).is_some() {
                return Sort::Int;
            }
        }
        // Derived-name cascade vs source-name plan gap. (#2020 Slice 3)
        // Source names skip fallback entirely and emit a plan gap diagnostic.
        // Derived names try old_ prefix stripping as a secondary resolution
        // path (for suffix-only names the while-loop is a no-op since they
        // have no old_ prefix to strip).
        if classify_var_name(name).is_some() {
            // Derived name: try old_ prefix stripping. For DerivedKind::Old,
            // this is the primary resolution path. For suffix+prefix names
            // like `old_x_current`, this strips old_ and re-resolves through
            // the suffix cascade (old_x_current -> x_current -> x). For
            // suffix-only names (x_current), the loop is a no-op.
            for stripped in DerivedKind::peel_old_prefixes(name) {
                if let Some(sort) = self.resolve_var_sort_candidate(stripped) {
                    if sort != Sort::Int {
                        return sort;
                    }
                }
            }
            unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromVar);
            Sort::Int
        } else {
            // Source name: not predeclared by the sort plan — a plan gap.
            // Keep Int for compatibility; emit a debug trace for observability.
            let loc = std::panic::Location::caller();
            debug!(
                "[TRUST_WP_DEBUG] sort plan gap: source name {name:?} resolved to Int \
                 at {}:{}:{}",
                loc.file(),
                loc.line(),
                loc.column()
            );
            unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromVar);
            Sort::Int
        }
    }

    /// Convert an `ExprSort` annotation to a ay `Sort`. (#717, #2059, #2062)
    ///
    /// Delegates to `expr_sort_to_ay_sort` for the pure structural mapping,
    /// then layers solver-state-dependent behavior for `Seq` (sort
    /// registration only) and `Datatype` (declared DatatypeSort lookup). (#2059)
    pub(crate) fn sort_from_expr_sort(&mut self, sort: trust_wp_core::formula::ExprSort) -> Sort {
        use trust_wp_core::formula::ExprSort as ES;
        match sort {
            ES::Seq => self.get_seq_sort(),
            ES::Datatype(id) => {
                use super::sort_inference::{
                    canonical_sort, fmap_sort, mapping_sort, CanonicalSort,
                };
                let name = trust_wp_core::formula::resolve_sort_name(id);
                // #prophecy-slots (Fix B M1): an instantiation-suffixed
                // `Option<&mut T>` annotation resolves to the specialized
                // carrier Option family, with the `Some` payload field at the
                // mutref record sort. Declared eagerly for the same reason as
                // the OptionInt/ResultIntInt block below (#2706): returning
                // an uninterpreted sort here and declaring the datatype later
                // creates two incompatible declarations of the same name.
                if let Some(payload) = super::sort_mapping::parse_mutref_instantiated_option(&name)
                {
                    let payload_sort = self.sort_from_expr_sort(payload);
                    let datatype =
                        crate::encoder::match_enc::stdlib_option_datatype_for_payload(payload_sort);
                    self.ensure_datatype_declared(&datatype);
                    return Sort::Datatype(datatype);
                }
                // #prophecy-slots (Fix B M2): the carrier tuple sort stays
                // UNINTERPRETED (like the mutref record sort) and keeps its
                // full instantiation name — `canonical_sort` below would strip
                // the `::`-qualified prefix and conflate distinct
                // instantiations.
                if super::sort_mapping::parse_mutref_carrier_tuple(&name).is_some() {
                    return Sort::Uninterpreted(name);
                }
                let bare = name.rsplit("::").next().unwrap_or(&name);
                let canonical = canonical_sort(&name);
                // For non-primary model names (e.g. "LinkedList"),
                // registered user ADTs win over the canonical sort alias.
                // Primary model names (Seq, Vec, VecDeque, FMap, HashMap,
                // GhostMap, Mapping) always use canonical sorts even when
                // a same-named native datatype has been registered, to
                // prevent ADT sort collision. (#2652, #2673, compat bug/1562)
                let is_primary_model_name = matches!(
                    bare,
                    "Seq" | "Vec" | "VecDeque" | "FMap" | "HashMap" | "GhostMap" | "Mapping"
                );
                // Fail-safe against the same disease from the OTHER direction:
                // a registered decl must NEVER override a canonical-**Int**
                // model name (`Rc`/`Arc`/`Box`/`Ghost`/`Snapshot`/`Int`/…,
                // `is_int_model_type`). Those are transparent wrappers whose
                // view IS the payload; reinterpreting `Datatype("Rc")` as a
                // registered `Rc {rc_ptr, …}` carrier makes `rc@ == 1` an
                // eq(Datatype, Int), and `coerce_ite_sorts` then replaces the
                // literal with a fresh unconstrained constant — the premise is
                // fabricated away (adtpa: the arc_and_rc regression). User ADTs
                // are canonically `Uninterpreted`, so the #2652/#2673 rule
                // "registered user ADTs win over the canonical alias" is
                // untouched. The driver already declines to emit such decls
                // (adt_analysis.rs peels Box/Rc/Arc); this is the encoder-side
                // backstop for any other producer. (adtpa)
                let is_canonical_int_model = matches!(canonical, CanonicalSort::Int);
                // Standard Option/Result annotations carry enough information
                // to declare their native datatypes immediately. Returning an
                // uninterpreted sort here and declaring the datatype later
                // when `Some`/`Ok` is encoded creates two incompatible
                // declarations with the same name; AY 0.4 correctly rejects
                // that stale-sort upgrade. (#2706)
                if !is_primary_model_name
                    && matches!(bare, "OptionInt" | "ResultIntInt")
                    && self
                        .get_datatype_decl(&name)
                        .or_else(|| self.get_datatype_decl(bare))
                        .is_none()
                {
                    let datatype = match bare {
                        "OptionInt" => {
                            crate::encoder::match_enc::SwitchTarget::OptionInt.datatype()
                        }
                        "ResultIntInt" => {
                            crate::encoder::match_enc::SwitchTarget::ResultIntInt.datatype()
                        }
                        _ => unreachable!("guarded standard datatype name"),
                    };
                    self.ensure_datatype_declared(&datatype);
                    return Sort::Datatype(datatype);
                }
                if !is_primary_model_name {
                    if let Some(dt) = self
                        .get_datatype_decl(&name)
                        .or_else(|| self.get_datatype_decl(bare))
                    {
                        // The canonical-Int carve-out (adtpa) applies HERE, on
                        // the result, rather than by skipping the lookup: the
                        // lookup itself is a pure read, and keeping the control
                        // flow byte-identical on the (overwhelmingly common)
                        // no-decl path keeps this a strictly local change.
                        if !is_canonical_int_model {
                            return Sort::Datatype(dt.clone());
                        }
                        debug!(
                            sort_name = %name,
                            decl = %dt.name,
                            "canonical-Int model name keeps Sort::Int; registered decl does \
                             NOT override (adtpa)"
                        );
                    }
                }
                match canonical {
                    CanonicalSort::Int => Sort::Int,
                    CanonicalSort::Seq => self.get_seq_sort(),
                    CanonicalSort::FMap => fmap_sort(),
                    CanonicalSort::Mapping => mapping_sort(),
                    CanonicalSort::Uninterpreted(bare) => {
                        // Use native DatatypeSort when declared. (#2002)
                        if let Some(dt) = self
                            .get_datatype_decl(&name)
                            .or_else(|| self.get_datatype_decl(&bare))
                        {
                            Sort::Datatype(dt.clone())
                        } else {
                            Sort::Uninterpreted(bare)
                        }
                    }
                }
            }
            // Ref peels the reference layer and recurses through this
            // match, so that Ref(Seq) hits the ES::Seq arm (calling
            // get_seq_sort) and Ref(Datatype) hits the ES::Datatype arm
            // (looking up declared DatatypeSorts). Delegating to the pure
            // expr_sort_to_ay_sort would skip these stateful behaviors.
            // (#1965 Phase 2 audit)
            ES::Ref(inner) => self.sort_from_expr_sort(*inner),
            // MutRef deliberately delegates to the pure mapping (which
            // produces Uninterpreted("MutRef_T")) rather than peeling.
            // bind_whole_borrow_aliases (bindings.rs) calls
            // sort_from_expr_sort(MutRef(inner)) and compares the result
            // against the predeclared base-variable sort to decide
            // whether whole-borrow UF binding is needed. Peeling here
            // would collapse MutRef(Int) → Int, breaking that gate.
            // Callers that need the peeled inner sort for variable
            // declaration peel MutRef at their own callsite. (#2673)
            ES::MutRef(_) => super::sort_inference::expr_sort_to_ay_sort(&sort),
            // All other variants: delegate to the pure mapping function.
            // This ensures sort_from_expr_sort and infer_expr_sort always
            // agree for Int, Bool, Unit, FMap, and Tuple.
            other => super::sort_inference::expr_sort_to_ay_sort(&other),
        }
    }

    /// Convert an `ExprSort` parameter/return sort to a ay `Sort`.
    ///
    /// For Seq, ensures the Seq sort exists without forcing theory setup.
    /// Delegates to `sort_from_expr_sort` for most variants.
    pub(crate) fn sort_from_param_sort(&mut self, sort: ExprSort) -> Sort {
        match sort {
            ExprSort::Seq => self.get_seq_sort(),
            other => self.sort_from_expr_sort(other),
        }
    }

    pub(crate) fn resolve_logic_param_sort(
        &mut self,
        logic_fn: &trust_wp_core::logic::LogicFnDef,
        i: usize,
    ) -> Sort {
        if let Some(sort) = logic_fn.param_sorts().get(i).cloned().flatten() {
            // TypeParam sorts (from generic type parameters like `T`) resolve to
            // Int at the logic-function declaration level. In monomorphic verification,
            // call sites pass concrete sorts (Int, Bool, etc.) for generic params.
            // Declaring with Uninterpreted("T") causes sort mismatches at call sites,
            // triggering __apply_coerce fresh constants that disconnect arguments from
            // the function body — and fire the SortFallbackToInt demotion counter.
            // Int is the universal sort in trust-wp's encoding and works for all
            // concrete instantiations.
            if matches!(sort, trust_wp_core::formula::ExprSort::TypeParam(_)) {
                return Sort::Int;
            }
            return self.sort_from_param_sort(sort);
        }
        if let Some(param_name) = logic_fn.params().get(i) {
            if let Some(sort) = self.var_sort(param_name).cloned() {
                if sort != Sort::Int {
                    return sort;
                }
            }
            if let Some(hint) = self.sort_resolver.get_sort_hint(param_name).cloned() {
                return self.sort_from_expr_sort(hint);
            }
        }
        // No param_sorts, no preseeded var_sorts, and no sort hints —
        // declaration-side logic-function fallback. (#2002, #2352)
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromLogicFn);
        Sort::Int
    }

    /// Resolve declaration sort for a symbolic name. (#1608, #1805)
    ///
    /// Callers pass `base_name` when `declared_name` is derived (e.g.,
    /// `x_current` with base `x`). When `base_name` is `None` and the
    /// function falls through to the `fallback` return, this is a plan
    /// gap for a source-like name. (#2020 Slice 3)
    #[track_caller]
    pub(in crate::encoder) fn resolve_decl_sort(
        &mut self,
        declared_name: &str,
        base_name: Option<&str>,
        fallback: Sort,
    ) -> Sort {
        if let Some(sort) = self.var_sort(declared_name).cloned() {
            if sort != Sort::Int {
                return sort;
            }
            if let Some(hint) = self.sort_resolver.get_sort_hint(declared_name).cloned() {
                return self.sort_from_expr_sort(hint);
            }
            if let Some(base) = base_name {
                if let Some(base_sort) = self.var_sort(base).cloned() {
                    if let Some(projected) =
                        self.project_reference_like_base_sort(declared_name, &base_sort)
                    {
                        return projected;
                    }
                    if base_sort != Sort::Int {
                        return base_sort;
                    }
                }
                if let Some(hint) = self.sort_resolver.get_sort_hint(base).cloned() {
                    return self.sort_from_expr_sort(hint);
                }
            }
            if fallback != Sort::Int {
                return fallback;
            }
            return sort;
        }
        if let Some(base) = base_name {
            if let Some(base_sort) = self.var_sort(base).cloned() {
                if let Some(projected) =
                    self.project_reference_like_base_sort(declared_name, &base_sort)
                {
                    return projected;
                }
                // Authoritative base_sort (from prior encoding) wins over hints
                // when non-Int. Hints are heuristic; base_sort is ground truth.
                if base_sort != Sort::Int {
                    return base_sort;
                }
                if let Some(hint) = self.sort_resolver.get_sort_hint(declared_name).cloned() {
                    return self.sort_from_expr_sort(hint);
                }
                if fallback != Sort::Int {
                    return fallback;
                }
                if let Some(hint) = self.sort_resolver.get_sort_hint(base).cloned() {
                    return self.sort_from_expr_sort(hint);
                }
                return base_sort;
            }
        }
        if let Some(hint) = self.sort_resolver.get_sort_hint(declared_name).cloned() {
            return self.sort_from_expr_sort(hint);
        }
        if let Some(base) = base_name {
            if let Some(hint) = self.sort_resolver.get_sort_hint(base).cloned() {
                return self.sort_from_expr_sort(hint);
            }
        }
        // Diagnostic: when a source-like name (no base_name, not a derived
        // suffix pattern) falls through to the fallback, log the gap. (#2020)
        if base_name.is_none()
            && fallback == Sort::Int
            && classify_var_name(declared_name).is_none()
        {
            let loc = std::panic::Location::caller();
            debug!(
                "[TRUST_WP_DEBUG] decl sort plan gap: {declared_name:?} fell back to Int at {}:{}:{}",
                loc.file(),
                loc.line(),
                loc.column()
            );
        }
        fallback
    }

    /// Reconcile sort hints for Eq/Ne operands. (#585)
    pub(in crate::encoder) fn reconcile_eq_sort_hints(&mut self, l: &PureExpr, r: &PureExpr) {
        // Use context-aware inference so declared LogicFnCall return sorts
        // are checked before clearing hints. (#1965)
        if let PureExpr::LogicFnCall { name, .. } = r {
            if !matches!(l, PureExpr::LogicFnCall { .. }) {
                let l_sort = self.infer_expr_sort_with_context(l, None);
                if l_sort != Sort::Bool {
                    self.clear_stale_bool_hint(name);
                }
            }
        }
        if let PureExpr::LogicFnCall { name, .. } = l {
            if !matches!(r, PureExpr::LogicFnCall { .. }) {
                let r_sort = self.infer_expr_sort_with_context(r, None);
                if r_sort != Sort::Bool {
                    self.clear_stale_bool_hint(name);
                }
            }
        }
    }

    fn clear_stale_bool_hint(&mut self, fn_name: &str) {
        let smt_name = logic_fn_smt_name(fn_name);
        if !self.has_logic_func_decl(&smt_name)
            && self.sort_resolver.get_sort_hint(&smt_name) == Some(&ExprSort::Bool)
        {
            self.sort_resolver.remove_sort_hint(&smt_name);
        }
    }
}
