// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::borrow::Cow;

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, ExprSort, PureExpr,
};

use super::super::{
    sort_context::{DerivedKind, MutRefVarNames},
    type_resolve::resolve_qualified_int_constant,
    AYEncoder,
};
use crate::error::EncodingError;

fn parse_projected_var_path(name: &str) -> Option<(&str, Vec<usize>)> {
    let (base, rest) = name.split_once('.')?;
    if base.is_empty() || rest.is_empty() {
        return None;
    }

    let indices = rest
        .split('.')
        .map(str::parse::<usize>)
        .collect::<Result<Vec<_>, _>>()
        .ok()?;

    Some((base, indices))
}

/// Classification of a projection base sort for structural encoding.
///
/// - `Tuple`: tuple lowering via `tuple_field_logic_fn_name` (non-ClosureEnv
///   datatypes or `TupleN` uninterpreted sorts produced by tuple lowering).
/// - `ClosureEnv`: native datatype selectors via `closure_capture_<suffix>_<i>`,
///   bridging `self.N` references inside closure-body verification to the
///   registered closure environment datatype's native selectors. Without this
///   bridge, `self.N` decays to a free SMT variable disconnected from the
///   closure-capture datatype (#2257, Wave 16A).
enum ProjectedBaseKind {
    Tuple,
    ClosureEnv,
}

fn classify_projected_base(sort: &Sort) -> Option<ProjectedBaseKind> {
    match sort {
        Sort::Datatype(dt) if dt.name.starts_with("ClosureEnv_") => {
            Some(ProjectedBaseKind::ClosureEnv)
        }
        Sort::Datatype(_) => Some(ProjectedBaseKind::Tuple),
        Sort::Uninterpreted(name) if name.starts_with("Tuple") => Some(ProjectedBaseKind::Tuple),
        _ => None,
    }
}

impl AYEncoder {
    fn try_encode_projected_var(
        &mut self,
        name: &str,
        prefix: Option<DerivedKind>,
    ) -> Option<Result<Term, EncodingError>> {
        let (base, field_indices) = parse_projected_var_path(name)?;
        let lookup = prefix.map_or_else(|| base.to_string(), |kind| kind.format_name(base));
        let base_sort = self.resolve_var_sort(&lookup)?;
        let kind = classify_projected_base(&base_sort)?;

        match kind {
            ProjectedBaseKind::Tuple => {
                let projected = field_indices.into_iter().fold(
                    PureExpr::Var(base.to_string(), None),
                    |receiver, field_index| PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(field_index),
                        args: vec![receiver],
                    },
                );
                Some(self.encode_pure_impl(&projected, prefix))
            }
            ProjectedBaseKind::ClosureEnv => {
                Some(self.encode_closure_env_projection(base, prefix, &base_sort, &field_indices))
            }
        }
    }

    /// Encode a `self.N` projection where the base resolves to a registered
    /// closure-environment datatype.
    ///
    /// Applies the registered `closure_capture_<suffix>_N` native selector via
    /// `try_datatype_selector`, bridging `self.N` to the closure-capture
    /// datatype's first constructor field. Without this bridge, the standard
    /// projection path treats `self.N` as a free uninterpreted variable
    /// disconnected from the closure-capture sort, breaking `proof_assert!`
    /// clauses that reference outer captures inside closure bodies (#2257,
    /// Wave 16A).
    ///
    /// Subsequent indices (e.g., `self.0.1`) chain via tuple-field logic-fn
    /// calls. The intermediate selector term is bound to a fresh helper
    /// variable so the standard structural projection path can re-resolve the
    /// receiver from a `PureExpr::Var`.
    fn encode_closure_env_projection(
        &mut self,
        base: &str,
        prefix: Option<DerivedKind>,
        base_sort: &Sort,
        field_indices: &[usize],
    ) -> Result<Term, EncodingError> {
        // `base_sort` comes from `resolve_var_sort`, which prefers hint-based
        // datatype evidence over any prior `Uninterpreted("ClosureEnv_*")`
        // declaration that may have been emitted by a fallback path. ay maps
        // `Sort::Datatype` and `Sort::Uninterpreted` with the same ClosureEnv
        // name as term-sort equivalent (see `get_or_declare_var` ClosureEnv
        // equivalence suppression), so the selector application succeeds even
        // if the existing solver declaration uses the Uninterpreted form.
        let lookup_name = prefix.map_or_else(|| base.to_string(), |kind| kind.format_name(base));
        let mut current_term = self.get_or_declare_var(&lookup_name, base_sort.clone())?;
        let dt = match base_sort {
            Sort::Datatype(dt) if dt.name.starts_with("ClosureEnv_") => dt.clone(),
            other => {
                return Err(EncodingError::unsupported(format!(
                    "closure capture projection requires a closure-env datatype, \
                     got: {other:?}"
                )));
            }
        };

        let (first_index, rest_indices) = field_indices
            .split_first()
            .ok_or_else(|| EncodingError::unsupported("closure projection with empty indices"))?;

        let constructor = dt.constructors.first().ok_or_else(|| {
            EncodingError::unsupported(format!(
                "closure env datatype '{}' has no constructors",
                dt.name
            ))
        })?;
        let field = constructor.fields.get(*first_index).ok_or_else(|| {
            EncodingError::unsupported(format!(
                "closure capture index {first_index} out of bounds for '{}' with {} fields",
                dt.name,
                constructor.fields.len()
            ))
        })?;
        let field_sort = field.sort.clone();
        let selector_name = field.name.clone();
        current_term = self.safe_datatype_selector(
            "closure_capture_projection",
            &selector_name,
            current_term,
            field_sort,
        )?;

        for (step, &nested_index) in rest_indices.iter().enumerate() {
            let helper_name =
                format!("__trust_wp_closure_proj__{lookup_name}__{step}_{nested_index}");
            let helper_sort = self.solver.get_sort(current_term);
            let helper_term = self.get_or_declare_var(&helper_name, helper_sort)?;
            let eq = self.eq_term(helper_term, current_term);
            self.assert_solver_term("closure_capture_projection_step", eq);
            let nested = PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(nested_index),
                args: vec![PureExpr::Var(helper_name, None)],
            };
            current_term = self.encode_pure_impl(&nested, prefix)?;
        }

        Ok(current_term)
    }

    /// Encodes a variable reference (`Var`).
    ///
    /// Resolves type-level constants, qualified int constants, nullary
    /// constructors, quantifier-bound variable collapse, annotation-aware
    /// sort resolution, and existing-sort fallback.
    pub(super) fn encode_var(
        &mut self,
        name: &str,
        sort_ann: Option<&ExprSort>,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let Some(projected) = self.try_encode_projected_var(name, prefix) {
            return projected;
        }

        // Type-level constant resolution: Self::MIN, Self::MAX, etc.
        // These resolve to exact PureExpr values when type_constants
        // have been set by the driver. (#688, #2315)
        if let Some(value) = self.type_constant_cloned(name) {
            return self.encode_pure_impl(&value, prefix);
        }
        // Qualified integer constants: u32::MAX, i32::MIN, etc.
        // These appear directly in user contracts (not via Self::).
        // Returns exact symbolic expressions for types wider than i64.
        if let Some(value) = resolve_qualified_int_constant(name) {
            return self.encode_pure_impl(&value, prefix);
        }
        // Nullary constructor resolution: the contract parser produces bare Vars
        // for zero-field variants like `None` and user-defined enum cases such as
        // `On`. Redirect them to the LogicFnCall path so registered ADTs use
        // native constructors instead of free SMT variables. (#1277, #1982)
        if name == "None" || self.nullary_constructor_datatype(name).is_some() {
            return self.encode_logic_fn_call_impl(name, &[], prefix);
        }
        // Qualified enum constructors (e.g., `Peano::Z`, `Color::Red`) appear as
        // Var nodes from the constant translator (no trailing parens → Var not
        // LogicFnCall). When the name follows the Rust enum variant convention
        // (`Type::UpperCamelCase`), redirect to the LogicFnCall path so the
        // postcondition uses the same Uninterpreted sort as the body, preventing
        // sort mismatches between body result and postcondition.
        if !self.has_var(name) {
            if let Some((_, short)) = name.rsplit_once("::") {
                let is_likely_variant = short.starts_with(char::is_uppercase)
                    && (short.len() == 1 || short.chars().any(|c| c.is_lowercase()));
                if is_likely_variant {
                    return self.encode_logic_fn_call_impl(name, &[], prefix);
                }
            }
        }
        // Quantifier-bound variable collapse: when a prefix (e.g., "old_")
        // would create a different name, but the variable is quantifier-bound,
        // collapse to the bound variable. Quantifier-bound variables are pure
        // logical values without temporal state, so `old(i)` for bound `i`
        // is just `i`. Without this, `old_i` creates a free variable
        // disconnected from the quantifier binding, making the quantified
        // formula vacuously satisfiable. (#1122)
        let prefixed_name = prefix.map(|kind| kind.format_name(name));
        let var_name: Cow<'_, str> = match prefixed_name.as_ref() {
            Some(prefixed)
                if self.is_quantifier_bound(name) && !self.has_var(prefixed.as_str()) =>
            {
                Cow::Borrowed(name)
            }
            Some(prefixed) => Cow::Owned(prefixed.clone()),
            None => Cow::Borrowed(name),
        };
        // Sort authority cutover (#1965): pre-declared variables use their
        // existing sort directly, bypassing the hint cascade entirely.
        // `predeclare_collected_vars` determines sorts from complete evidence
        // across ALL expression sources; the cascade can only disagree, never
        // improve. The cascade remains as fallback for synthesized variables
        // not present in input expressions (_current, _final, _view, etc.).
        //
        // See: designs/2026-03-08-1965-sort-authority-cutover.md Step 1.
        let sort = if let Some(existing_sort) = self.var_sort(var_name.as_ref()) {
            // Variable was pre-declared by predeclare_collected_vars,
            // predeclare_datatype_vars, or a prior encoding step.
            // Use its sort as-is — no cascade consultation.
            existing_sort.clone()
        } else {
            // Variable was NOT pre-declared (synthesized name, _current/_final
            // suffix, or other non-input variable). Fall back to old cascade.
            self.resolve_var_sort_or_int_with_annotation(&var_name, sort_ann)
        };
        // Track unit-sorted variables for singleton axiom generation.
        // When `assert_unit_singleton_axioms()` runs, each tracked variable
        // will be constrained to equal `tuple0()`. (#1271)
        if matches!(sort_ann, Some(ExprSort::Unit)) {
            self.mark_unit_sorted_var(var_name.to_string());
        }
        let term = self.get_or_declare_var(&var_name, sort.clone())?;

        if prefix.is_none() {
            if let Some(ExprSort::MutRef(inner)) = sort_ann {
                let names = MutRefVarNames::new(var_name.as_ref());
                if let (Some(current_term), Some(final_term), Some(id_term)) = (
                    self.var_term(&names.current),
                    self.var_term(&names.final_val),
                    self.var_term(&names.id),
                ) {
                    let inner_sort = self.sort_from_expr_sort((**inner).clone());
                    if self.solver.get_sort(current_term) == inner_sort
                        && self.solver.get_sort(final_term) == inner_sort
                    {
                        self.bind_whole_mut_ref(
                            &sort,
                            &inner_sort,
                            term,
                            current_term,
                            final_term,
                            id_term,
                        )?;
                    }
                }
            }
        }

        Ok(term)
    }
}
