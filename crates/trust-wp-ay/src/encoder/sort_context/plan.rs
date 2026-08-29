// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{hash_map::Entry, HashMap, HashSet};

use ay_dpll::api::Sort;
use trust_wp_core::formula::{resolve_sort_name, ExprSort, PureExpr};

use super::{
    hint_collection::{collect_names_as_bool, SortHintAccumulator},
    hint_registration::collect_registered_sort_hints as collect_expr_sort_hints,
    is_collection_expr_sort,
    sort_mapping::{canonical_sort, retarget_seq_carrier, CanonicalSort, SeqCarrier},
    var_collection::{determine_sort, VarUsage},
};
use crate::{
    encoder::{state::DeclarationState, AYEncoder},
    error::EncodingError,
};

/// Pure declaration plan for names discovered during verification setup. (#2020)
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SortPlan {
    pub(crate) source_var_sorts: HashMap<String, Sort>,
    sort_hints: HashMap<String, ExprSort>,
}

impl SortPlan {
    /// Apply the planned source-name declarations in one explicit phase. (#2020)
    ///
    /// This is where the plan — built by pure functions with no encoder in
    /// scope — meets the encoder that will hold the declarations. Seq sorts
    /// are retargeted to that encoder's carrier here, so a plan minted with
    /// the default native spelling still declares its variables on the
    /// uninterpreted carrier in the lanes that chose one. Without this the
    /// variables and `ensure_seq_theory`'s projectors end up on different
    /// sorts and `Solver::apply` fails its domain-sort check.
    pub(crate) fn apply(&self, encoder: &mut AYEncoder) -> Result<(), EncodingError> {
        let carrier = encoder.seq_carrier();
        let mut planned_names: Vec<_> = self.source_var_sorts.iter().collect();
        planned_names.sort_by_key(|(left, _)| *left);
        for (name, sort) in planned_names {
            let sort = retarget_seq_carrier(sort.clone(), carrier);
            if sort == Sort::Int || encoder.var_sort(name).is_some() {
                continue;
            }
            encoder.get_or_declare_var(name, sort)?;
        }

        let mut hint_names: Vec<_> = self.sort_hints.iter().collect();
        hint_names.sort_by_key(|(left, _)| *left);
        for (name, hint) in hint_names {
            encoder.record_sort_hint(name.clone(), hint.clone());
        }
        if !self.sort_hints.is_empty() {
            encoder.mark_sort_hints_registered();
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn source_sort(&self, name: &str) -> Option<&Sort> {
        self.source_var_sorts.get(name)
    }

    #[cfg(test)]
    pub(crate) fn sort_hint(&self, name: &str) -> Option<&ExprSort> {
        self.sort_hints.get(name)
    }
}

/// Builder for the setup-time sort declaration plan. (#2020)
#[derive(Debug, Default)]
pub(crate) struct SortPlanBuilder {
    usage: HashMap<String, VarUsage>,
    explicit_source_sorts: HashMap<String, Sort>,
    sort_hints: HashMap<String, ExprSort>,
}

impl SortPlanBuilder {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn collect_registered_sort_hints(&mut self, exprs: &[PureExpr]) {
        self.merge_sort_hint_accumulator(collect_expr_sort_hints(exprs.iter()));
    }

    pub(crate) fn collect_registered_sort_hints_from_refs(&mut self, exprs: &[&PureExpr]) {
        self.merge_sort_hint_accumulator(collect_expr_sort_hints(exprs.iter().copied()));
    }

    pub(crate) fn merge_variable_usage(&mut self, batch: HashMap<String, VarUsage>) {
        for (name, usage) in batch {
            if let Some(annotation) = usage.annotation.as_ref() {
                // Peel MutRef/Ref layers for sort hints: the RustHorn encoding
                // uses (current, final) pairs for &mut parameters, so the
                // variable's SMT sort is the inner sort, not MutRef. Recording
                // MutRef as a sort hint causes cascading sort mismatches when
                // the variable is later declared with its inner sort. (#2673)
                let peeled = peel_ref_annotation(annotation);
                let hinted_sort = super::expr_sort_to_ay_sort(peeled);
                if hinted_sort != Sort::Int
                    || matches!(peeled, ExprSort::Ref(_) | ExprSort::MutRef(_))
                {
                    self.record_sort_hint(name.clone(), peeled.clone());
                }
            }
            self.usage.entry(name).or_default().merge(usage);
        }
    }

    pub(crate) fn record_source_sort(&mut self, name: String, sort: Sort) {
        if sort == Sort::Int {
            return;
        }
        // Filter out MutRef composite sorts: the RustHorn encoding represents
        // &mut T variables as (current, final) pairs of the inner sort T, not
        // as a dedicated MutRef SMT sort. When closure captures or domain sort
        // collection emits `Uninterpreted("__trust_wp_mutref::...")`, recording
        // it as a source sort would predeclare the variable with the wrong
        // carrier, causing sort mismatches during encoding. (#2673)
        if let Sort::Uninterpreted(ref name_str) = sort {
            if name_str.starts_with("__trust_wp_mutref::") {
                return;
            }
        }
        // Filter out dotted-projection names (e.g. `self.0`, `self.1.0`).
        // These are structural projections that must be routed through
        // `try_encode_projected_var` so they map to the right native
        // selectors (tuple field logic-fns or closure-capture datatype
        // selectors). Pre-declaring `self.0` as a free SMT variable creates
        // a term disconnected from `closure_capture_<suffix>_0(self)`,
        // breaking closure-body verification of `proof_assert!` clauses
        // that reference outer captures (Wave 17A/18A, #2257).
        if is_dotted_projection_name(&name) {
            return;
        }
        match self.explicit_source_sorts.entry(name) {
            Entry::Occupied(mut existing) => {
                if should_replace_sort(existing.get(), &sort) {
                    existing.insert(sort);
                }
            }
            Entry::Vacant(vacant) => {
                vacant.insert(sort);
            }
        }
    }

    pub(crate) fn extend_source_sorts(&mut self, sorts: impl IntoIterator<Item = (String, Sort)>) {
        for (name, sort) in sorts {
            self.record_source_sort(name, sort);
        }
    }

    pub(crate) fn collect_formula_logic_fn_return_hints(&mut self, formulas: &[PureExpr]) {
        let mut bool_var_names = HashSet::new();
        let mut bool_fn_names = HashSet::new();
        for expr in formulas {
            collect_names_as_bool(expr, &mut bool_var_names, &mut bool_fn_names);
        }
        for name in bool_fn_names {
            self.record_sort_hint(name, ExprSort::Bool);
        }
    }

    #[must_use]
    pub(crate) fn build(self, decls: &DeclarationState) -> SortPlan {
        let Self {
            usage,
            explicit_source_sorts,
            mut sort_hints,
        } = self;
        // Evidence-complete Bool-hint hygiene sweep (arc_and_rc sort-plan
        // flake). The builder is the single chokepoint holding both the
        // merged usage evidence and the accumulated hints, so heuristic
        // `ExprSort::Bool` VAR hints are dropped here when the complete
        // evidence proves the variable cannot be Bool:
        //
        // (a1) int-literal-equality veto: the variable appears in Eq/Ne with
        //      an integer literal outside {0,1} (`rc3@ == 2`). Freezing it
        //      Bool would force `bool_vs_out_of_range_int_literal_eq` to
        //      fabricate the premise away, weakening the assumption base and
        //      manufacturing model-validated false counterexamples.
        // (a2) annotation veto: the variable carries an authoritative
        //      non-Bool MIR annotation (Datatype/Seq/FMap/..., including
        //      canonical-Int model types like Rc/Arc whose annotation is
        //      inert at encode time by design). A heuristic Bool hint can
        //      only contradict MIR ground truth. Weak annotations (Int,
        //      TypeParam, and Ref/MutRef layers peeled to them) do NOT veto.
        //
        // Both rules only remove heuristic hints minted from the same
        // premise set — the surviving encoding is byte-wise the one today's
        // passing (hint-free) runs produce, independent of hash-iteration
        // order of the driver ghost maps.
        for (name, usage) in &usage {
            if sort_hints.get(name) != Some(&ExprSort::Bool) {
                continue;
            }
            let annotation_veto = usage
                .annotation
                .as_ref()
                .is_some_and(annotation_vetoes_heuristic_bool_hint);
            if usage.int_literal_eq || annotation_veto {
                sort_hints.remove(name);
            }
        }
        let mut source_var_sorts = HashMap::new();
        for (name, usage) in usage {
            let sort = resolve_usage_sort(decls, &usage);
            if sort != Sort::Int {
                source_var_sorts.insert(name, sort);
            }
        }
        for (name, sort) in explicit_source_sorts {
            match source_var_sorts.entry(name) {
                Entry::Occupied(mut existing) => {
                    if should_replace_sort(existing.get(), &sort) {
                        existing.insert(sort);
                    }
                }
                Entry::Vacant(vacant) => {
                    vacant.insert(sort);
                }
            }
        }
        SortPlan {
            source_var_sorts,
            sort_hints,
        }
    }

    fn merge_sort_hint_accumulator(&mut self, acc: SortHintAccumulator) {
        for name in acc.seqs {
            self.record_sort_hint(name, ExprSort::Seq);
        }
        for name in acc.bool_vars {
            self.record_sort_hint(name, ExprSort::Bool);
        }
        for name in acc.bool_fns {
            self.record_sort_hint(name, ExprSort::Bool);
        }
        for name in acc.fmaps {
            self.record_sort_hint(name, ExprSort::FMap);
        }
        for name in acc.mappings {
            self.record_sort_hint(name, super::mapping_expr_sort());
        }
    }

    fn record_sort_hint(&mut self, name: String, hint: ExprSort) {
        match self.sort_hints.entry(name) {
            Entry::Occupied(existing)
                if is_collection_expr_sort(existing.get()) && hint == ExprSort::Bool =>
            {
                // Collection hints are more specific than Bool.
            }
            Entry::Occupied(existing)
                if *existing.get() == ExprSort::FMap && hint == ExprSort::Seq =>
            {
                // FMap is more specific than Seq.
            }
            Entry::Occupied(mut existing) => {
                existing.insert(hint);
            }
            Entry::Vacant(vacant) => {
                vacant.insert(hint);
            }
        }
    }
}

/// `true` when a MIR `ExprSort` annotation is authoritative evidence that a
/// heuristic `Bool` VAR hint is wrong. (a2 of the arc_and_rc sort-plan fix)
///
/// Ref/MutRef layers are peeled first (the RustHorn encoding gives the
/// variable the inner sort), then:
/// - `Bool` obviously does not veto;
/// - `Int` is the weak/default annotation (the resolution cascade already
///   treats it as fall-through), so it does not veto;
/// - `TypeParam` resolves to Int and is equally weak;
/// - everything else (Datatype — including canonical-Int model types like
///   Rc/Arc — Seq, FMap, Tuple, Unit, Float) is MIR ground truth that the
///   variable is not Bool.
fn annotation_vetoes_heuristic_bool_hint(ann: &ExprSort) -> bool {
    let peeled = peel_ref_annotation(ann);
    !matches!(
        peeled,
        ExprSort::Bool | ExprSort::Int | ExprSort::TypeParam(_)
    )
}

fn resolve_usage_sort(decls: &DeclarationState, usage: &VarUsage) -> Sort {
    if let Some(quantifier_sort) = usage.quantifier_sort.as_ref() {
        let sort = expr_sort_to_plan_sort(decls, quantifier_sort);
        if sort != Sort::Int {
            return sort;
        }
    }
    // A direct `Datatype`-annotated variable outranks tuple-projection
    // evidence collected from a non-view projection.
    //
    // Closure-captured ADTs like `y: Zero<T>` flow into the proof_assert
    // expression as `tuple_get_0(y)` (positional ADT field access). Without
    // this guard the bootstrap sort plan would pre-declare `y` as
    // `Uninterpreted("Tuple1")` from `usage.tuple_arity`, even though the
    // MIR-derived annotation is `Datatype("Zero")`. Once `y` is locked in
    // as `Tuple1`, the assertion's annotation-driven `Zero` request raises a
    // sort conflict (closures/10_tyinv). The encoder already routes
    // `tuple_get_N(adt_var)` through `native_field_projection_return_sort`
    // when the receiver is a Datatype, so preferring the annotation is the
    // semantically correct choice.
    //
    // Gate on `tuple_arity_from_direct_projection`: view-derived names like
    // `frag_view: Datatype("Authority")` with `tuple_get_0(View(frag))`
    // intentionally describe a tuple model and still want the `TupleN` sort.
    // Only direct projections on the same variable are reinterpreted as
    // ADT field accessors here. (Part of #5; closures/10_tyinv)
    //
    // Extended Tuple1 lock-out for user-defined single-field ADTs (Wave 19B):
    // user types like `Cloned<I>` / `Copied<I>` carry one `iter` field whose
    // MIR projection emits `tuple_get_0(self)`. When the receiver `self`
    // travels through a `View` wrapper (e.g. via `*self`), the projection is
    // not classified as "direct" and the original guard above does not fire,
    // so `self` collapsed to `Uninterpreted("Tuple1")` and the apply layer
    // panicked with "sort mismatch in apply: expected matching domain sort,
    // got Tuple1" once an annotation-driven `Datatype("Cloned")` accessor
    // re-entered the encoder (examples/iterators/13_cloned, 14_copied).
    //
    // The encoder already registers user ADT shapes via
    // `ensure_datatype_declared` during driver setup, so we can detect this
    // case by checking whether the annotated Datatype name is registered in
    // `decls`. When it is, the annotation describes a real ADT and the
    // tuple-projection evidence is just the positional accessor for its sole
    // field — prefer the Datatype. Synthetic view-derived names like
    // `frag_view: Datatype("Authority")` keep the TupleN behaviour because
    // their inner type is not registered as a Datatype declaration.
    if let Some(annotation) = usage.annotation.as_ref() {
        if matches!(annotation, ExprSort::Datatype(_)) {
            let direct = usage.tuple_arity_from_direct_projection;
            // Tuple1-only registered-datatype extension: user-defined
            // single-field ADTs (Cloned/Copied) trigger `tuple_arity = 1`
            // from view-wrapped projections of their sole field. Multi-field
            // user types like `Zip<A, B>` retain their TupleN model so we
            // keep the lock-out scoped to arity 1.
            let registered_tuple1 = usage.tuple_arity == Some(1)
                && datatype_annotation_is_registered(decls, annotation);
            if direct || registered_tuple1 {
                let sort = expr_sort_to_plan_sort(decls, annotation);
                // For the original direct-projection path, accept any non-Int
                // sort (matches pre-Wave-19B semantics). For the registered-
                // datatype extension, require the planner to produce a real
                // `Sort::Datatype(_)` shape — otherwise the annotation only
                // resolved to an unregistered `Sort::Uninterpreted(name)` and
                // the Tuple1 fallback is still the safer choice.
                let accept = if direct {
                    sort != Sort::Int
                } else {
                    matches!(sort, Sort::Datatype(_))
                };
                if accept {
                    return sort;
                }
            }
        }
        // Wave 22A extension: `Ref(...Datatype)` / `MutRef(...Datatype)`
        // wrappers around a registered single-field ADT.
        //
        // A `&mut self` receiver on a user-defined single-field ADT like
        // `Cloned<I>` carries annotation `MutRef(Datatype(Cloned))`. The
        // RustHorn encoding represents this variable in SMT as the inner
        // Datatype sort (the &mut layer becomes the (current, final) pair),
        // so the variable's SMT sort is `Sort::Datatype(Cloned)`.
        //
        // Without this extension, view-wrapped projections of the sole field
        // (`tuple_get_0(View(*self))`) accumulate `tuple_arity = 1` with
        // `tuple_arity_from_direct_projection = false`. The Wave 19B block
        // above only fires when the outer annotation is `ExprSort::Datatype(_)`
        // directly, so a reference-wrapped annotation falls through to the
        // `Sort::Uninterpreted("Tuple1")` branch on line 301. The variable
        // then gets predeclared with the wrong carrier and the apply layer
        // panics with "sort mismatch in apply: expected matching domain
        // sort, got Tuple1" once the assertion's annotation-driven `Cloned`
        // accessor re-enters the encoder.
        //
        // Scope (same as Wave 19B):
        // - `tuple_arity == Some(1)` only: multi-field user types like
        //   `Zip<A, B>` keep their TupleN model.
        // - The inner Datatype must be registered in `decls`. Synthetic
        //   reference-wrapped names whose inner type is not declared keep
        //   the Tuple1 fallback (mirrors the unregistered-Datatype gate
        //   used by the bare-Datatype case).
        // - At least one `Ref`/`MutRef` layer must be present so we don't
        //   re-handle the bare-Datatype case (already covered above).
        //
        // Soundness:
        // - `expr_sort_to_plan_sort` recurses through `Ref`/`MutRef` and
        //   returns the inner Datatype's `Sort::Datatype(_)` shape — the
        //   exact sort RustHorn-encoded references-to-ADT variables get at
        //   binding time. We only return when the planner produces a real
        //   `Sort::Datatype(_)`; if the lookup falls back to
        //   `Sort::Uninterpreted(name)` we keep the Tuple1 path.
        //
        // Wave 22B extension (this commit): the direct-projection branch.
        // Wave 19B accepts ANY arity (not just 1) when the projection is
        // `tuple_arity_from_direct_projection == true` and the annotation is
        // a bare `Datatype`. The analogous direct branch was missing for
        // `Ref`/`MutRef`-wrapped registered Datatypes: a `&mut Zip<A, B>`
        // receiver with direct projections (`tuple_get_0(self)`,
        // `tuple_get_1(self)`) would land on the `Tuple2` fallback at
        // line 348 even though the SMT sort under RustHorn is the inner
        // `Sort::Datatype(Zip)`. Mirror the Wave 19B accept gate:
        // - require `tuple_arity_from_direct_projection == true`,
        // - allow any arity (not restricted to `Some(1)`),
        // - require the inner Datatype to be registered, and
        // - require the planner to produce a real `Sort::Datatype(_)`
        //   (gracefully fall through to TupleN otherwise, same as the
        //   tuple_arity == Some(1) case above).
        let registered_direct_ref =
            usage.tuple_arity_from_direct_projection && usage.tuple_arity.is_some();
        if usage.tuple_arity == Some(1) || registered_direct_ref {
            if let Some(inner_dt) = peel_ref_layers_to_datatype(annotation) {
                if datatype_annotation_is_registered(decls, inner_dt) {
                    let sort = expr_sort_to_plan_sort(decls, annotation);
                    if matches!(sort, Sort::Datatype(_)) {
                        return sort;
                    }
                }
            }
        }
    }
    if let Some(arity) = usage.tuple_arity {
        return Sort::Uninterpreted(format!("Tuple{arity}"));
    }
    if let Some(annotation) = usage.annotation.as_ref() {
        let sort = expr_sort_to_plan_sort(decls, annotation);
        if sort != Sort::Int {
            return sort;
        }
        // When MutRef wraps a polymorphic inner sort (TypeParam) that
        // resolves to Int, determine_sort would convert the raw annotation
        // via expr_sort_to_ay_sort, producing a polymorphic MutRef sort
        // like Uninterpreted("__trust_wp_mutref::typeparam_*"). This differs
        // from the canonical Uninterpreted("__trust_wp_mutref::int") that
        // bind_whole_borrow_aliases produces for the same variable, causing
        // the whole-borrow sort gate to fail.
        //
        // Return Int so the variable is NOT predeclared with a MutRef sort.
        // The RustHorn encoding represents &mut variables as (current, final)
        // pairs of the inner sort; predeclaring with MutRef sort causes
        // first-declaration-wins to lock the variable to the wrong carrier.
        // bind_result_expr and bind_single_final_value will declare the
        // variable with the correct sort at binding time. (#2673)
        //
        // Strip outer `Ref` layers before checking the MutRef gate so that
        // annotations like `Ref(MutRef(TypeParam(T)))` (i.e., `&&mut T`) also
        // route through the Int-fallback. Without the peel step, only direct
        // `MutRef(TypeParam(T))` matched the gate and any extra reference
        // wrapping caused `determine_sort` to return the polymorphic carrier
        // (`Uninterpreted("__trust_wp_mutref::typeparam_*")`) via
        // `expr_sort_to_ay_sort`'s Ref-peeling recursion, surfacing as
        // "seq_index_term: index argument has wrong sort" when the variable
        // was later used as a Seq index (iterators/15_enumerate, #2673).
        let inner = strip_outer_refs(annotation);
        if matches!(inner, ExprSort::MutRef(_)) && annotation_contains_type_param(inner) {
            return Sort::Int;
        }
    }
    determine_sort(usage)
}

fn expr_sort_to_plan_sort(decls: &DeclarationState, sort: &ExprSort) -> Sort {
    match sort {
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            match canonical_sort(&name) {
                // Keep logical model types on their canonical encoding sorts even
                // when the driver also registered a same-named datatype. The
                // rest of the Seq/FMap/Mapping/Int pipelines operate on the
                // encoding sorts, so predeclaring these names as Datatype
                // creates false sort conflicts later in verification. (#2116)
                CanonicalSort::Seq
                | CanonicalSort::FMap
                | CanonicalSort::Mapping
                | CanonicalSort::Int => super::expr_sort_to_ay_sort(sort),
                CanonicalSort::Uninterpreted(_) => {
                    let bare = name.rsplit("::").next().unwrap_or(&name);
                    decls
                        .get_datatype(&name)
                        .or_else(|| decls.get_datatype(bare))
                        .cloned()
                        .map_or_else(|| super::expr_sort_to_ay_sort(sort), Sort::Datatype)
                }
            }
        }
        ExprSort::Ref(inner) => expr_sort_to_plan_sort(decls, inner),
        // MutRef peels the reference layer like Ref: the RustHorn encoding
        // represents &mut T variables as (current, final) pairs of the inner
        // sort, not as a dedicated MutRef sort. Predeclaring "result" as
        // MutRef_T causes a sort mismatch when bind_result_expr declares it
        // with the inner sort, producing spurious counterexamples. (#2673)
        ExprSort::MutRef(inner) => expr_sort_to_plan_sort(decls, inner),
        _ => super::expr_sort_to_ay_sort(sort),
    }
}

fn should_replace_sort(existing: &Sort, incoming: &Sort) -> bool {
    if let (Some(existing_arity), Some(incoming_arity)) =
        (tuple_sort_arity(existing), tuple_sort_arity(incoming))
    {
        return incoming_arity > existing_arity;
    }
    sort_specificity(incoming) > sort_specificity(existing)
}

fn tuple_sort_arity(sort: &Sort) -> Option<usize> {
    match sort {
        Sort::Uninterpreted(name) => name.strip_prefix("Tuple")?.parse().ok(),
        _ => None,
    }
}

fn sort_specificity(sort: &Sort) -> u8 {
    // Both Seq carriers rank identically. Which spelling an encoder uses is a
    // proof-surface decision, not evidence about the variable, so it must not
    // change which of two competing sorts wins. Without this the uninterpreted
    // carrier would fall through to the generic `Uninterpreted(_) => 4` arm
    // and start outranking FMap. (See `SeqCarrier`.)
    if SeqCarrier::classify(sort).is_some() {
        return 2;
    }
    match sort {
        Sort::Int => 0,
        Sort::Bool => 1,
        Sort::Seq(_) => 2,
        Sort::Uninterpreted(name) if name == "Mapping" => 2,
        Sort::Uninterpreted(name) if name == "FMap" => 3,
        Sort::Uninterpreted(_) => 4,
        // Datatype carries full constructor information and enables native
        // constructor encoding. It must win over Uninterpreted (bare name)
        // so that constructor-equality evidence from bootstrap Pass 3
        // (collect_constructor_eq_dt_vars) overrides annotation-derived
        // Uninterpreted sorts like "Result" or "Option". Without this,
        // variables like `call_3` get declared as Uninterpreted("Result")
        // instead of Datatype(ResultIntInt), causing sort coercion to
        // disconnect constraints. (#2675)
        Sort::Datatype(_) => 5,
        _ => 2,
    }
}

/// Return `true` when a `Datatype` annotation names an ADT that has already
/// been declared in `decls`.
///
/// Used by `resolve_usage_sort` to distinguish user-defined single-field ADTs
/// (registered, real Datatype shapes) from synthetic view-derived names that
/// merely carry a `Datatype` annotation as a placeholder. Without this gate,
/// the `tuple_arity == 1` lock-out would also fire for view-derived names
/// like `frag_view: Datatype("Authority")` and lose the tuple model. (#5; Wave 19B)
fn datatype_annotation_is_registered(decls: &DeclarationState, ann: &ExprSort) -> bool {
    let ExprSort::Datatype(id) = ann else {
        return false;
    };
    let name = resolve_sort_name(*id);
    if decls.get_datatype(&name).is_some() {
        return true;
    }
    let bare = name.rsplit("::").next().unwrap_or(&name);
    decls.get_datatype(bare).is_some()
}

/// Check whether an `ExprSort` annotation contains a `TypeParam` anywhere.
///
/// Used by `resolve_usage_sort` to detect polymorphic `MutRef(TypeParam(T))`
/// annotations that need normalization to canonical `MutRef(Int)`. Without
/// this, `determine_sort` converts the raw annotation via `expr_sort_to_ay_sort`,
/// producing a polymorphic `Uninterpreted("__trust_wp_mutref::typeparam_*")` that
/// differs from the canonical `Uninterpreted("__trust_wp_mutref::int")` used by
/// `bind_whole_borrow_aliases`, causing the whole-borrow sort gate to fail. (#2673)
fn annotation_contains_type_param(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::TypeParam(_) => true,
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => annotation_contains_type_param(inner),
        _ => false,
    }
}

/// Strip only outermost `Ref` layers from an `ExprSort` annotation, leaving
/// any inner `MutRef` wrapper intact.
///
/// Used to detect polymorphic `MutRef(TypeParam(T))` patterns that may appear
/// nested inside extra reference layers like `Ref(MutRef(TypeParam(T)))`
/// (i.e., `&&mut T`). The Int-fallback in `resolve_usage_sort` must fire for
/// these patterns so the variable is not predeclared with the polymorphic
/// `Uninterpreted("__trust_wp_mutref::typeparam_*")` carrier sort.
///
/// Unlike `peel_ref_annotation`, this helper deliberately stops at the first
/// `MutRef` wrapper: the MutRef-vs-Int distinction is what the gate at line 323
/// keys on, so peeling through MutRef too would lose the signal. (#2673)
fn strip_outer_refs(ann: &ExprSort) -> &ExprSort {
    match ann {
        ExprSort::Ref(inner) => strip_outer_refs(inner),
        other => other,
    }
}

/// Strip outermost `Ref` and `MutRef` layers from an `ExprSort` annotation.
///
/// The RustHorn encoding maps `&mut T` variables to `(current, final)` pairs
/// of the inner sort `T`, not to a dedicated `MutRef<T>` SMT sort. When the
/// driver emits `Var("result", MutRef(TypeParam(T)))`, the annotation signals
/// reference semantics but the variable's SMT sort should be the inner sort.
/// Without peeling, sort hints and predeclarations use the MutRef wrapper sort
/// (`Uninterpreted("MutRef_Int")`), causing cascading sort mismatches. (#2673)
fn peel_ref_annotation(ann: &ExprSort) -> &ExprSort {
    match ann {
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => peel_ref_annotation(inner),
        other => other,
    }
}

/// Walk through outer `Ref`/`MutRef` wrappers and return the inner annotation
/// when it is an `ExprSort::Datatype(_)`. Requires at least one `Ref`/`MutRef`
/// layer — a bare `Datatype` returns `None` so the caller does not re-handle
/// the case already covered by the Wave 19B branch in `resolve_usage_sort`.
///
/// Used by the Wave 22A `Ref(...Datatype)` / `MutRef(...Datatype)` extension
/// in `resolve_usage_sort` to detect reference-wrapped registered ADT
/// annotations whose RustHorn-encoded variable sort is the inner Datatype,
/// not `Tuple{arity}`.
fn peel_ref_layers_to_datatype(ann: &ExprSort) -> Option<&ExprSort> {
    fn walk(ann: &ExprSort, peeled_any: bool) -> Option<&ExprSort> {
        match ann {
            ExprSort::Ref(inner) | ExprSort::MutRef(inner) => walk(inner, true),
            ExprSort::Datatype(_) if peeled_any => Some(ann),
            _ => None,
        }
    }
    walk(ann, false)
}

/// Returns `true` for dotted-projection variable names such as `self.0`,
/// `self.1.0`, `x.2`, where the base is a non-empty identifier and every
/// component after the first `.` is a non-negative integer.
///
/// Names that match this shape MUST be routed through
/// `try_encode_projected_var` so they resolve to native datatype selectors
/// (tuple-field logic-fns or `closure_capture_<suffix>_N` selectors). Pre-
/// declaring such a name as a free SMT variable creates a term disconnected
/// from the projection result, breaking closure-body verification when
/// `proof_assert!` clauses reference outer captures via `self.N`
/// (Wave 17A/18A, #2257).
fn is_dotted_projection_name(name: &str) -> bool {
    let Some((base, rest)) = name.split_once('.') else {
        return false;
    };
    if base.is_empty() || rest.is_empty() {
        return false;
    }
    rest.split('.')
        .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use ntest::timeout;
    use trust_wp_core::formula::{intern_sort_name, BinOp};

    use super::{super::var_collection::collect_variable_usage_as_formula, *};
    use crate::encoder::AYEncoder;

    // ── Evidence-complete Bool-hint veto (arc_and_rc sort-plan flake) ──

    /// `rc3@` with the authoritative MIR annotation `Datatype("Rc")` — the
    /// canonical-Int model type shape from the arc_and_rc false reject.
    fn rc_view(name: &str) -> Arc<PureExpr> {
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            name.to_string(),
            Some(ExprSort::Datatype(intern_sort_name("Rc"))),
        ))))
    }

    fn build_plan_for(exprs: &[PureExpr]) -> SortPlan {
        let mut builder = SortPlanBuilder::new();
        builder.collect_registered_sort_hints(exprs);
        builder.merge_variable_usage(collect_variable_usage_as_formula(exprs));
        builder.build(&AYEncoder::new().decls)
    }

    /// Regression pin for the arc_and_rc rc3 shape: a DT-view var carrying a
    /// canonical-Int `Datatype("Rc")` annotation, hit by BOTH a heuristic
    /// Bool-mint premise (`b == rc3@`, the ptr_eq-bridge shape) and an
    /// out-of-range int-literal equality (`rc3@ == 2`). The planned outcome
    /// must be identical in BOTH premise orders: no Bool hint, no Bool
    /// source sort — the var falls to the Int plan-gap fallback exactly as
    /// today's passing runs do. Before the fix, hash-iteration order decided
    /// whether the Bool hint survived, and when it did the `== 2` premise was
    /// fabricated away (`__trust_wp_unencodable_eq_*`) producing a
    /// model-validated false counterexample.
    #[test]
    #[timeout(30000)]
    fn dt_view_var_with_int_literal_eq_plans_int_in_both_orders() {
        let poison = PureExpr::BinOp(
            Arc::new(PureExpr::Var("b".to_string(), Some(ExprSort::Bool))),
            BinOp::Eq,
            rc_view("rc3"),
        );
        let literal = PureExpr::BinOp(rc_view("rc3"), BinOp::Eq, Arc::new(PureExpr::Int(2)));
        for exprs in [
            [poison.clone(), literal.clone()],
            [literal.clone(), poison.clone()],
        ] {
            let plan = build_plan_for(&exprs);
            assert_ne!(
                plan.sort_hint("rc3"),
                Some(&ExprSort::Bool),
                "rc3 must not carry a Bool hint (order-independent)"
            );
            assert_ne!(
                plan.source_sort("rc3"),
                Some(&Sort::Bool),
                "rc3 must not be predeclared Bool (order-independent)"
            );
            assert_ne!(
                plan.sort_hint("rc3_view"),
                Some(&ExprSort::Bool),
                "rc3_view must not carry a Bool hint (order-independent)"
            );
        }
    }

    /// a1 in isolation: even WITHOUT any MIR annotation, an out-of-range
    /// int-literal equality vetoes the heuristic Bool hint in both orders.
    #[test]
    #[timeout(30000)]
    fn unannotated_var_with_int_literal_eq_loses_bool_hint_in_both_orders() {
        let x_view = || {
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            ))))
        };
        let poison = PureExpr::BinOp(
            Arc::new(PureExpr::Var("b".to_string(), Some(ExprSort::Bool))),
            BinOp::Eq,
            x_view(),
        );
        let literal = PureExpr::BinOp(x_view(), BinOp::Eq, Arc::new(PureExpr::Int(2)));
        for exprs in [
            [poison.clone(), literal.clone()],
            [literal.clone(), poison.clone()],
        ] {
            let plan = build_plan_for(&exprs);
            assert_ne!(
                plan.sort_hint("x"),
                Some(&ExprSort::Bool),
                "x@ == 2 must strip the heuristic Bool hint for x"
            );
            assert_ne!(plan.source_sort("x"), Some(&Sort::Bool));
        }
    }

    /// a2 in isolation: an authoritative non-Bool MIR annotation (the
    /// canonical-Int model type `Datatype("Rc")`) vetoes a heuristic Bool
    /// hint even without literal evidence.
    #[test]
    #[timeout(30000)]
    fn non_bool_annotation_vetoes_heuristic_bool_hint() {
        let poison = PureExpr::BinOp(
            Arc::new(PureExpr::Var("b".to_string(), Some(ExprSort::Bool))),
            BinOp::Eq,
            rc_view("rc3"),
        );
        let plan = build_plan_for(std::slice::from_ref(&poison));
        assert_ne!(
            plan.sort_hint("rc3"),
            Some(&ExprSort::Bool),
            "Datatype(Rc) annotation must veto the heuristic Bool hint"
        );
    }

    /// a2 negative: a weak `Int` annotation must NOT veto — the resolution
    /// cascade treats Int annotations as fall-through, so a Bool hint on an
    /// Int-annotated var is preserved (pre-fix behavior pinned).
    #[test]
    #[timeout(30000)]
    fn weak_int_annotation_does_not_veto_bool_hint() {
        let poison = PureExpr::BinOp(
            Arc::new(PureExpr::Var("b".to_string(), Some(ExprSort::Bool))),
            BinOp::Eq,
            Arc::new(PureExpr::Var("y".to_string(), Some(ExprSort::Int))),
        );
        let plan = build_plan_for(std::slice::from_ref(&poison));
        assert_eq!(
            plan.sort_hint("y"),
            Some(&ExprSort::Bool),
            "weak Int annotation must not veto the heuristic Bool hint"
        );
    }

    #[test]
    #[timeout(30000)]
    fn annotation_veto_classifier() {
        use trust_wp_core::formula::ExprSort as ES;
        assert!(annotation_vetoes_heuristic_bool_hint(&ES::Datatype(
            intern_sort_name("Rc")
        )));
        assert!(annotation_vetoes_heuristic_bool_hint(&ES::Seq));
        assert!(annotation_vetoes_heuristic_bool_hint(&ES::MutRef(
            Box::new(ES::Datatype(intern_sort_name("Rc")))
        )));
        assert!(!annotation_vetoes_heuristic_bool_hint(&ES::Bool));
        assert!(!annotation_vetoes_heuristic_bool_hint(&ES::Int));
        assert!(!annotation_vetoes_heuristic_bool_hint(&ES::TypeParam(
            intern_sort_name("T")
        )));
        assert!(!annotation_vetoes_heuristic_bool_hint(&ES::Ref(Box::new(
            ES::Bool
        ))));
    }

    #[test]
    #[timeout(30000)]
    fn formula_logic_fn_hint_collection_is_bool_only() {
        let mut builder = SortPlanBuilder::new();
        builder.collect_formula_logic_fn_return_hints(&[PureExpr::LogicFnCall {
            name: "is_valid".to_string(),
            args: vec![],
        }]);

        let plan = builder.build(&AYEncoder::new().decls);
        let smt_name = trust_wp_core::logic::logic_fn_smt_name("is_valid");
        assert_eq!(plan.sort_hint(&smt_name), Some(&ExprSort::Bool));
    }

    #[test]
    #[timeout(30000)]
    fn dotted_projection_names_are_filtered_from_source_sorts() {
        let mut builder = SortPlanBuilder::new();
        let dt = ay_dpll::api::DatatypeSort {
            name: "ClosureEnv_test".to_string(),
            constructors: vec![],
        };
        // self.0, self.1, self.1.0 — all dotted projections, must not be
        // recorded as predeclared source variables (Wave 18A).
        builder.record_source_sort("self.0".to_string(), Sort::Datatype(dt.clone()));
        builder.record_source_sort("self.1".to_string(), Sort::Bool);
        builder.record_source_sort("self.1.0".to_string(), Sort::seq(Sort::Int));
        // Non-dotted names continue to be recorded.
        builder.record_source_sort("x".to_string(), Sort::Bool);
        // Dotted with non-integer tail (e.g. method-call residue) is NOT a
        // projection — but we don't expect such names from bootstrap, so
        // ensure the filter only matches integer tails.
        builder.record_source_sort("foo.bar".to_string(), Sort::Bool);

        let plan = builder.build(&AYEncoder::new().decls);
        assert!(
            plan.source_sort("self.0").is_none(),
            "dotted self.0 must be filtered"
        );
        assert!(
            plan.source_sort("self.1").is_none(),
            "dotted self.1 must be filtered"
        );
        assert!(
            plan.source_sort("self.1.0").is_none(),
            "nested dotted self.1.0 must be filtered"
        );
        assert_eq!(plan.source_sort("x"), Some(&Sort::Bool));
        assert_eq!(plan.source_sort("foo.bar"), Some(&Sort::Bool));
    }

    #[test]
    #[timeout(30000)]
    fn is_dotted_projection_name_classifier() {
        assert!(is_dotted_projection_name("self.0"));
        assert!(is_dotted_projection_name("self.1"));
        assert!(is_dotted_projection_name("self.1.0"));
        assert!(is_dotted_projection_name("x.2.3.4"));
        assert!(!is_dotted_projection_name("self"));
        assert!(!is_dotted_projection_name("foo.bar"));
        assert!(!is_dotted_projection_name(".0"));
        assert!(!is_dotted_projection_name("x."));
        assert!(!is_dotted_projection_name("x.0.y"));
        // Leading dot followed by an integer is still rejected because base
        // must be non-empty.
        assert!(!is_dotted_projection_name(".0.1"));
    }

    #[test]
    #[timeout(30000)]
    fn explicit_sorts_override_usage_defaults() {
        let mut builder = SortPlanBuilder::new();
        let mut usage = HashMap::new();
        usage.insert("v".to_string(), VarUsage::default());
        builder.merge_variable_usage(usage);
        builder.record_source_sort("v".to_string(), Sort::seq(Sort::Int));

        let plan = builder.build(&AYEncoder::new().decls);
        assert_eq!(plan.source_sort("v"), Some(&Sort::seq(Sort::Int)));
    }

    #[test]
    #[timeout(30000)]
    fn registered_sort_hints_preserve_view_aliases() {
        let mut builder = SortPlanBuilder::new();
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "v".to_string(),
                None,
            )))),
            method: "len".to_string(),
            args: vec![],
        };

        builder.collect_registered_sort_hints(std::slice::from_ref(&expr));

        let plan = builder.build(&AYEncoder::new().decls);
        assert_eq!(plan.sort_hint("v_view"), Some(&ExprSort::Seq));
    }

    #[test]
    #[timeout(30000)]
    fn registered_seq_datatype_annotation_stays_on_seq_encoding_sort() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "result".to_string(),
            VarUsage {
                annotation: Some(ExprSort::Datatype(intern_sort_name("creusot_std::Seq"))),
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "Seq".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Seq".to_string(),
                fields: vec![DatatypeField {
                    name: "seq_elements".to_string(),
                    sort: Sort::seq(Sort::Int),
                }],
            }],
        });

        let plan = builder.build(encoder.decls());
        assert_eq!(
            plan.source_sort("result"),
            Some(&Sort::seq(Sort::Int)),
            "registered Seq datatype annotations must preserve the canonical Seq encoding sort"
        );
    }

    #[test]
    #[timeout(30000)]
    fn registered_fmap_datatype_annotation_stays_on_fmap_encoding_sort() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "m".to_string(),
            VarUsage {
                annotation: Some(ExprSort::Datatype(intern_sort_name("creusot_std::FMap"))),
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "FMap".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "FMap".to_string(),
                fields: vec![DatatypeField {
                    name: "fmap_entries".to_string(),
                    sort: Sort::Uninterpreted("FMap".to_string()),
                }],
            }],
        });

        let plan = builder.build(encoder.decls());
        assert_eq!(
            plan.source_sort("m"),
            Some(&Sort::Uninterpreted("FMap".to_string())),
            "registered FMap datatype annotations must preserve the canonical FMap encoding sort"
        );
    }

    /// User-defined single-field ADTs like `Cloned<I>` / `Copied<I>` carry a
    /// `Datatype` annotation and accumulate `tuple_arity = 1` evidence from
    /// view-wrapped projections such as `tuple_get_0(View(self))`. The original
    /// guard required a direct projection and would let `Tuple1` win, which
    /// later panicked at the apply layer with "sort mismatch in apply:
    /// expected matching domain sort, got Tuple1" once the assertion's
    /// annotation-driven `Cloned` accessor re-entered the encoder
    /// (examples/iterators/13_cloned, 14_copied). Wave 19B extends the lock-out
    /// so a registered `Datatype` annotation outranks the `Tuple1` fallback
    /// even when the projection is not classified as direct.
    #[test]
    #[timeout(30000)]
    fn registered_single_field_datatype_outranks_tuple1_from_view_projection() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "self".to_string(),
            VarUsage {
                annotation: Some(ExprSort::Datatype(intern_sort_name("Cloned"))),
                tuple_arity: Some(1),
                // View-wrapped projection: NOT direct.
                tuple_arity_from_direct_projection: false,
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "Cloned".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Cloned".to_string(),
                fields: vec![DatatypeField {
                    name: "iter".to_string(),
                    sort: Sort::Int,
                }],
            }],
        });

        let plan = builder.build(encoder.decls());
        match plan.source_sort("self") {
            Some(Sort::Datatype(dt)) => assert_eq!(dt.name, "Cloned"),
            other => panic!("expected Sort::Datatype(Cloned), got {other:?}"),
        }
    }

    /// View-derived synthetic names like `frag_view: Datatype("Authority")`
    /// describe a tuple model on the inner type and must keep the
    /// `Tuple1` predeclaration when the underlying Datatype is not
    /// registered. This guards against regressing the case that motivated
    /// the original `tuple_arity_from_direct_projection` gate.
    #[test]
    #[timeout(30000)]
    fn unregistered_view_datatype_keeps_tuple1_fallback() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "frag_view".to_string(),
            VarUsage {
                annotation: Some(ExprSort::Datatype(intern_sort_name("Authority"))),
                tuple_arity: Some(1),
                tuple_arity_from_direct_projection: false,
                ..VarUsage::default()
            },
        )]));

        // No Authority datatype is declared on the encoder.
        let plan = builder.build(&AYEncoder::new().decls);
        assert_eq!(
            plan.source_sort("frag_view"),
            Some(&Sort::Uninterpreted("Tuple1".to_string())),
            "unregistered Datatype annotations on view-derived names must keep Tuple1"
        );
    }

    /// Regression guard: `MutRef(TypeParam(T))` annotations must route to the
    /// Int-fallback so the polymorphic MutRef carrier sort
    /// (`Uninterpreted("__trust_wp_mutref::typeparam_*")`) does not leak into
    /// variable predeclarations. The Int return means `source_var_sorts`
    /// omits the variable, letting `bind_result_expr` declare it with the
    /// correct sort at binding time. (#2673)
    #[test]
    #[timeout(30000)]
    fn mutref_typeparam_annotation_routes_to_int_fallback() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "result".to_string(),
            VarUsage {
                annotation: Some(ExprSort::MutRef(Box::new(ExprSort::TypeParam(
                    intern_sort_name("T"),
                )))),
                ..VarUsage::default()
            },
        )]));

        let plan = builder.build(&AYEncoder::new().decls);
        assert!(
            plan.source_sort("result").is_none(),
            "direct MutRef(TypeParam) must fall through to Int (omitted from \
             source_var_sorts), got {:?}",
            plan.source_sort("result")
        );
    }

    /// Extended Int-fallback gate (this commit): annotations like
    /// `Ref(MutRef(TypeParam(T)))` (i.e., `&&mut T`) must also route to the
    /// Int-fallback. Without the outer-Ref strip, `determine_sort` would
    /// return the polymorphic carrier
    /// `Uninterpreted("__trust_wp_mutref::typeparam_*")` via
    /// `expr_sort_to_ay_sort`'s Ref-peeling recursion, surfacing as
    /// "seq_index_term: index argument has wrong sort" when the variable
    /// later appeared as a Seq index (iterators/15_enumerate, #2673).
    #[test]
    #[timeout(30000)]
    fn ref_mutref_typeparam_annotation_routes_to_int_fallback() {
        let mut builder = SortPlanBuilder::new();
        let inner = ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "result".to_string(),
            VarUsage {
                annotation: Some(ExprSort::Ref(Box::new(inner))),
                ..VarUsage::default()
            },
        )]));

        let plan = builder.build(&AYEncoder::new().decls);
        assert!(
            plan.source_sort("result").is_none(),
            "Ref(MutRef(TypeParam)) must fall through to Int (omitted from \
             source_var_sorts) — leaking the polymorphic MutRef carrier here \
             breaks Seq indexing of values bound through &&mut T, got {:?}",
            plan.source_sort("result")
        );
    }

    /// Nested outer Refs (e.g., `Ref(Ref(MutRef(TypeParam(T))))`) must also
    /// strip cleanly so the Int-fallback fires. Guards against the gate
    /// regressing to handle only a single Ref layer.
    #[test]
    #[timeout(30000)]
    fn nested_ref_mutref_typeparam_annotation_routes_to_int_fallback() {
        let mut builder = SortPlanBuilder::new();
        let typaram = ExprSort::TypeParam(intern_sort_name("T"));
        let annotation = ExprSort::Ref(Box::new(ExprSort::Ref(Box::new(ExprSort::MutRef(
            Box::new(typaram),
        )))));
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "v".to_string(),
            VarUsage {
                annotation: Some(annotation),
                ..VarUsage::default()
            },
        )]));

        let plan = builder.build(&AYEncoder::new().decls);
        assert!(
            plan.source_sort("v").is_none(),
            "Ref(Ref(MutRef(TypeParam))) must fall through to Int, got {:?}",
            plan.source_sort("v")
        );
    }

    /// Negative case: `Ref(MutRef(Int))` (i.e., `&&mut i32`) must NOT route
    /// to the Int-fallback gate — it should preserve its concrete inner sort
    /// through `expr_sort_to_plan_sort`. The MutRef-TypeParam Int-fallback
    /// is strictly for the polymorphic case where the carrier name would
    /// embed an interned TypeParam id and break sort equality. Concrete
    /// `MutRef(Int)` annotations are handled by the standard non-Int return
    /// path or by the `__trust_wp_mutref::` filter in `record_source_sort`.
    #[test]
    #[timeout(30000)]
    fn ref_mutref_concrete_int_does_not_trigger_typeparam_fallback() {
        let inner = ExprSort::Ref(Box::new(ExprSort::MutRef(Box::new(ExprSort::Int))));
        // strip_outer_refs strips the outer Ref → MutRef(Int).
        let stripped = strip_outer_refs(&inner);
        assert!(matches!(stripped, ExprSort::MutRef(_)));
        // `annotation_contains_type_param` is the second gate — it must be
        // false for concrete Int payloads so the Int-fallback does NOT fire.
        assert!(
            !annotation_contains_type_param(stripped),
            "concrete MutRef(Int) must NOT match the TypeParam fallback gate"
        );
    }

    /// Wave 22A: `MutRef(Datatype(D))` where `D` is a registered single-field
    /// ADT and `tuple_arity = 1` from a view-wrapped projection must resolve
    /// to `Sort::Datatype(D)`, not `Tuple1`.
    ///
    /// A `&mut self` receiver on `Cloned<I>` carries this exact annotation
    /// shape: `MutRef(Datatype("Cloned"))`. Without the extension the
    /// reference-wrapped annotation fell through Wave 19B's
    /// `matches!(annotation, ExprSort::Datatype(_))` guard and `Tuple1`
    /// hijacked the predeclaration, breaking the apply layer once the
    /// assertion's annotation-driven `Cloned` accessor re-entered the
    /// encoder.
    #[test]
    #[timeout(30000)]
    fn mutref_wrapped_registered_single_field_datatype_outranks_tuple1() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "self".to_string(),
            VarUsage {
                annotation: Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name("Cloned"),
                )))),
                tuple_arity: Some(1),
                tuple_arity_from_direct_projection: false,
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "Cloned".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Cloned".to_string(),
                fields: vec![DatatypeField {
                    name: "iter".to_string(),
                    sort: Sort::Int,
                }],
            }],
        });

        let plan = builder.build(encoder.decls());
        match plan.source_sort("self") {
            Some(Sort::Datatype(dt)) => assert_eq!(dt.name, "Cloned"),
            other => panic!(
                "expected Sort::Datatype(Cloned) for MutRef(Datatype(Cloned)) with tuple_arity=1, \
                 got {other:?}"
            ),
        }
    }

    /// Wave 22A: deeper wrapper `Ref(MutRef(Datatype(D)))` (i.e., `&&mut D`)
    /// must also resolve to the inner registered Datatype, not `Tuple1`.
    /// Guards the recursive `Ref`/`MutRef` walk in
    /// `peel_ref_layers_to_datatype`.
    #[test]
    #[timeout(30000)]
    fn nested_ref_mutref_wrapped_registered_datatype_outranks_tuple1() {
        let mut builder = SortPlanBuilder::new();
        let inner = ExprSort::MutRef(Box::new(ExprSort::Datatype(intern_sort_name("Copied"))));
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "self".to_string(),
            VarUsage {
                annotation: Some(ExprSort::Ref(Box::new(inner))),
                tuple_arity: Some(1),
                tuple_arity_from_direct_projection: false,
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "Copied".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Copied".to_string(),
                fields: vec![DatatypeField {
                    name: "iter".to_string(),
                    sort: Sort::Int,
                }],
            }],
        });

        let plan = builder.build(encoder.decls());
        match plan.source_sort("self") {
            Some(Sort::Datatype(dt)) => assert_eq!(dt.name, "Copied"),
            other => panic!(
                "expected Sort::Datatype(Copied) for Ref(MutRef(Datatype(Copied))) with \
                 tuple_arity=1, got {other:?}"
            ),
        }
    }

    /// Wave 22A negative: `MutRef(Datatype(D))` where `D` is NOT registered
    /// must keep the `Tuple1` fallback. Mirrors the
    /// `unregistered_view_datatype_keeps_tuple1_fallback` guard for the bare
    /// `Datatype` case — unregistered names lack the constructor information
    /// the planner needs to produce a real `Sort::Datatype(_)`, so the safer
    /// choice is the tuple model.
    #[test]
    #[timeout(30000)]
    fn unregistered_mutref_wrapped_datatype_keeps_tuple1_fallback() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "frag_view".to_string(),
            VarUsage {
                annotation: Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name("Authority"),
                )))),
                tuple_arity: Some(1),
                tuple_arity_from_direct_projection: false,
                ..VarUsage::default()
            },
        )]));

        // No Authority datatype is declared on the encoder.
        let plan = builder.build(&AYEncoder::new().decls);
        assert_eq!(
            plan.source_sort("frag_view"),
            Some(&Sort::Uninterpreted("Tuple1".to_string())),
            "unregistered Datatype inside MutRef wrapper must keep Tuple1 fallback"
        );
    }

    /// Wave 22A negative: multi-field user ADT (arity ≥ 2) must keep its
    /// `TupleN` model even when reference-wrapped and registered. The
    /// extension is scoped to `tuple_arity == Some(1)` because only
    /// single-field ADTs share the `tuple_get_0` projection shape with
    /// `Tuple1`; multi-field types like `Zip<A, B>` legitimately need the
    /// tuple model for the encoder's positional field access.
    #[test]
    #[timeout(30000)]
    fn multi_field_mutref_wrapped_datatype_keeps_tuple_n_fallback() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "self".to_string(),
            VarUsage {
                annotation: Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name("Zip"),
                )))),
                tuple_arity: Some(2),
                tuple_arity_from_direct_projection: false,
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "Zip".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Zip".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "a".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "b".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        });

        let plan = builder.build(encoder.decls());
        assert_eq!(
            plan.source_sort("self"),
            Some(&Sort::Uninterpreted("Tuple2".to_string())),
            "multi-field reference-wrapped Datatype must keep TupleN even when registered"
        );
    }

    /// Wave 22B: `MutRef(Datatype(D))` where `D` is a registered multi-field
    /// ADT and `tuple_arity_from_direct_projection == true` must resolve to
    /// `Sort::Datatype(D)`, not `TupleN`.
    ///
    /// Mirrors Wave 19B's direct-projection branch for `Ref`/`MutRef`-wrapped
    /// annotations: a `&mut self` receiver on a multi-field struct like
    /// `Zip<A, B>` with positional field access (`tuple_get_0(self)`,
    /// `tuple_get_1(self)`) accumulates direct-projection evidence for the
    /// ADT's fields. The RustHorn-encoded SMT sort is `Sort::Datatype(Zip)`;
    /// the `Tuple2` fallback at line 348 would be wrong because the
    /// annotation already pins the variable to a registered ADT shape.
    #[test]
    #[timeout(30000)]
    fn mutref_wrapped_multi_field_registered_datatype_direct_projection_outranks_tuple_n() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "self".to_string(),
            VarUsage {
                annotation: Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name("Zip"),
                )))),
                tuple_arity: Some(2),
                // Direct projection (NOT view-wrapped): positional field
                // access on the ADT, not a logical tuple model.
                tuple_arity_from_direct_projection: true,
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "Zip".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Zip".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "a".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "b".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        });

        let plan = builder.build(encoder.decls());
        match plan.source_sort("self") {
            Some(Sort::Datatype(dt)) => assert_eq!(dt.name, "Zip"),
            other => panic!(
                "expected Sort::Datatype(Zip) for MutRef(Datatype(Zip)) with direct \
                 tuple_arity=2, got {other:?}"
            ),
        }
    }

    /// Wave 22B nested: `Ref(MutRef(Datatype(D)))` (i.e., `&&mut D`) with
    /// direct multi-field projection must also resolve to the inner
    /// registered Datatype. Guards the recursive `peel_ref_layers_to_datatype`
    /// walk when combined with the direct-projection extension.
    #[test]
    #[timeout(30000)]
    fn nested_ref_mutref_multi_field_datatype_direct_projection_outranks_tuple_n() {
        let mut builder = SortPlanBuilder::new();
        let inner = ExprSort::MutRef(Box::new(ExprSort::Datatype(intern_sort_name("Pair"))));
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "self".to_string(),
            VarUsage {
                annotation: Some(ExprSort::Ref(Box::new(inner))),
                tuple_arity: Some(2),
                tuple_arity_from_direct_projection: true,
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "Pair".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Pair".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "fst".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "snd".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        });

        let plan = builder.build(encoder.decls());
        match plan.source_sort("self") {
            Some(Sort::Datatype(dt)) => assert_eq!(dt.name, "Pair"),
            other => panic!(
                "expected Sort::Datatype(Pair) for Ref(MutRef(Datatype(Pair))) with direct \
                 tuple_arity=2, got {other:?}"
            ),
        }
    }

    /// Wave 22B negative: view-wrapped multi-field projection
    /// (`tuple_arity_from_direct_projection == false`) keeps the `TupleN`
    /// fallback even when the inner Datatype is registered. The Wave 19B
    /// direct-projection rationale only applies to direct projections;
    /// view-wrapped names like `frag_view: Datatype("Authority")` describe
    /// a tuple model on the inner type and must not be hijacked. This guards
    /// against the new branch leaking into the view-wrapped case.
    #[test]
    #[timeout(30000)]
    fn view_wrapped_multi_field_mutref_datatype_keeps_tuple_n() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "self".to_string(),
            VarUsage {
                annotation: Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name("Zip"),
                )))),
                tuple_arity: Some(2),
                // View-wrapped projection: NOT direct.
                tuple_arity_from_direct_projection: false,
                ..VarUsage::default()
            },
        )]));

        let mut encoder = AYEncoder::new();
        encoder.ensure_datatype_declared(&DatatypeSort {
            name: "Zip".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Zip".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "a".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "b".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        });

        let plan = builder.build(encoder.decls());
        assert_eq!(
            plan.source_sort("self"),
            Some(&Sort::Uninterpreted("Tuple2".to_string())),
            "view-wrapped multi-field MutRef(Datatype) must keep TupleN — the \
             Wave 22B direct-projection extension must NOT fire here"
        );
    }

    /// Wave 22B negative: unregistered multi-field Datatype inside
    /// `MutRef`/`Ref` with direct projection keeps the `TupleN` fallback.
    /// Mirrors the `unregistered_view_datatype_keeps_tuple1_fallback` guard:
    /// without a registered declaration, the planner cannot produce a real
    /// `Sort::Datatype(_)` and the tuple model is the safer choice.
    #[test]
    #[timeout(30000)]
    fn unregistered_multi_field_mutref_datatype_direct_projection_keeps_tuple_n() {
        let mut builder = SortPlanBuilder::new();
        builder.merge_variable_usage(std::collections::HashMap::from([(
            "self".to_string(),
            VarUsage {
                annotation: Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                    intern_sort_name("Authority"),
                )))),
                tuple_arity: Some(2),
                tuple_arity_from_direct_projection: true,
                ..VarUsage::default()
            },
        )]));

        // No Authority datatype is declared on the encoder.
        let plan = builder.build(&AYEncoder::new().decls);
        assert_eq!(
            plan.source_sort("self"),
            Some(&Sort::Uninterpreted("Tuple2".to_string())),
            "unregistered multi-field Datatype inside MutRef must keep TupleN even with direct projection"
        );
    }

    /// `peel_ref_layers_to_datatype` returns `None` for a bare `Datatype`
    /// because the Wave 19B branch already handles the bare case. Returning
    /// `Some` here would re-fire the Wave 22A branch and short-circuit the
    /// existing `direct`/`registered_tuple1` accept gate.
    #[test]
    #[timeout(30000)]
    fn peel_ref_layers_to_datatype_requires_at_least_one_layer() {
        let bare = ExprSort::Datatype(intern_sort_name("Cloned"));
        assert!(
            peel_ref_layers_to_datatype(&bare).is_none(),
            "bare Datatype must return None — Wave 19B handles this case"
        );

        let one_layer = ExprSort::MutRef(Box::new(ExprSort::Datatype(intern_sort_name("Cloned"))));
        assert!(
            matches!(
                peel_ref_layers_to_datatype(&one_layer),
                Some(ExprSort::Datatype(_))
            ),
            "single MutRef layer over Datatype must return the inner Datatype"
        );

        let two_layers = ExprSort::Ref(Box::new(ExprSort::MutRef(Box::new(ExprSort::Datatype(
            intern_sort_name("Cloned"),
        )))));
        assert!(
            matches!(
                peel_ref_layers_to_datatype(&two_layers),
                Some(ExprSort::Datatype(_))
            ),
            "nested Ref(MutRef(Datatype)) must return the inner Datatype"
        );

        // Non-Datatype payloads return None even when wrapped.
        let int_payload = ExprSort::MutRef(Box::new(ExprSort::Int));
        assert!(
            peel_ref_layers_to_datatype(&int_payload).is_none(),
            "reference wrapper around non-Datatype payload returns None"
        );

        let typeparam_payload =
            ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
        assert!(
            peel_ref_layers_to_datatype(&typeparam_payload).is_none(),
            "reference wrapper around TypeParam returns None — leaves Wave 21C MutRef-TypeParam \
             Int-fallback intact"
        );
    }

    /// `strip_outer_refs` must stop at the first MutRef wrapper. Peeling
    /// past MutRef would erase the MutRef-vs-Int distinction the
    /// resolve_usage_sort gate relies on.
    #[test]
    #[timeout(30000)]
    fn strip_outer_refs_stops_at_mutref() {
        let typaram = ExprSort::TypeParam(intern_sort_name("T"));
        let inner = ExprSort::MutRef(Box::new(typaram));
        let wrapped = ExprSort::Ref(Box::new(ExprSort::Ref(Box::new(inner.clone()))));
        let stripped = strip_outer_refs(&wrapped);
        assert_eq!(stripped, &inner, "outer Refs strip; inner MutRef preserved");

        // Direct MutRef is returned unchanged.
        let direct = ExprSort::MutRef(Box::new(ExprSort::Int));
        let stripped = strip_outer_refs(&direct);
        assert_eq!(stripped, &direct, "MutRef at outer position is preserved");

        // Bare TypeParam (no Ref/MutRef) is returned unchanged.
        let bare = ExprSort::TypeParam(intern_sort_name("U"));
        let stripped = strip_outer_refs(&bare);
        assert_eq!(stripped, &bare, "non-Ref ExprSorts are returned unchanged");
    }
}
