// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pattern binding and condition encoding for match expressions.
//!
//! Handles extracting variable bindings from patterns (e.g., `Some(x)` -> `x = payload`)
//! and encoding pattern conditions for the ITE chain (e.g., `Some(_)` -> `is_some(scrutinee)`).

mod bindings;
mod constructors;

#[cfg(test)]
mod tests;

use std::borrow::Cow;

use ay_dpll::api::{DatatypeSort, Sort, Term};
use tracing::debug;
use trust_wp_core::formula::{internal::tuple_lowering::tuple_field_logic_fn_name, Pattern};

use super::{datatype_constructor_matches, datatype_constructor_name, short_constructor_name};
use crate::{
    encoder::{
        infer_expr_sort, select_structural_sort_target, sort_context::DerivedKind, unsoundness,
        AYEncoder,
    },
    error::EncodingError,
};

impl AYEncoder {
    /// Internal implementation for pattern condition encoding with optional prefix.
    ///
    /// Automatically derives the scrutinee sort from the solver term so that
    /// recursive pattern condition encoding uses the correct sort for equality
    /// comparisons (e.g., Datatype-sorted scrutinees use `eq` instead of
    /// falling back to `SortFallbackToInt`). (#994, #2155)
    pub(in crate::encoder) fn encode_pattern_condition_impl(
        &mut self,
        scrutinee: Term,
        pattern: &Pattern,
        datatype: Option<&DatatypeSort>,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let scrutinee_sort = self.solver.get_sort(scrutinee);
        self.encode_pattern_condition_with_sort(
            scrutinee,
            pattern,
            datatype,
            Some(&scrutinee_sort),
            prefix,
        )
    }

    pub(super) fn pattern_accessor_domain_sort(
        &self,
        scrutinee: Term,
        scrutinee_sort: Option<&Sort>,
    ) -> Sort {
        // Accessor applications must use the solver term's actual sort. A stale
        // hint can still guide recursive payload sorts, but using it as the UF
        // domain makes ay reject the application before verification can
        // produce the real residual.
        let actual = self.solver.get_sort(scrutinee).as_term_sort();
        match scrutinee_sort.map(Sort::as_term_sort) {
            Some(hinted) if hinted == actual => hinted,
            _ => actual,
        }
    }

    /// Pattern condition encoding with explicit scrutinee sort tracking.
    ///
    /// `scrutinee_sort` tracks the sort of the scrutinee term through recursion
    /// into constructor payloads. When a datatype selector extracts a payload
    /// with `Sort::Int` but the inner pattern is `Literal(Bool(true))`, the
    /// Bool literal must be coerced to Int via `ite(lit, 1, 0)` to avoid a
    /// ay `mk_eq` sort mismatch panic. (#1055)
    #[allow(clippy::too_many_lines)]
    fn encode_pattern_condition_with_sort(
        &mut self,
        scrutinee: Term,
        pattern: &Pattern,
        datatype: Option<&DatatypeSort>,
        scrutinee_sort: Option<&Sort>,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        match pattern {
            // Wildcard and binding always match
            Pattern::Wildcard | Pattern::Binding(_) => Ok(self.solver.bool_const(true)),

            Pattern::Alias { pattern, .. } => self.encode_pattern_condition_with_sort(
                scrutinee,
                pattern,
                datatype,
                scrutinee_sort,
                prefix,
            ),

            // Literal: scrutinee == literal
            Pattern::Literal(lit) => {
                let l = self.encode_pure_impl(lit, prefix)?;
                // When the literal sort differs from the scrutinee sort (e.g.,
                // Bool literal `true` compared against an Int-sorted datatype
                // payload from OptionInt), coerce via ite(lit, 1, 0). (#1055)
                let lit_sort = infer_expr_sort(lit);
                let l = if lit_sort == Sort::Bool && scrutinee_sort == Some(&Sort::Int) {
                    let one = self.solver.int_const(1);
                    let zero = self.solver.int_const(0);
                    self.solver.ite(l, one, zero)
                } else {
                    l
                };
                let _eq_sort = scrutinee_sort.cloned().unwrap_or(lit_sort);
                Ok(self.eq_term(scrutinee, l))
            }

            // Constructor: check against constructor term when possible
            Pattern::Constructor { name, inner } => {
                let declared_datatype = datatype.map(|dt| self.canonical_declared_datatype(dt));
                let selector_datatype = declared_datatype
                    .as_ref()
                    .map(|dt| self.selector_datatype_for_scrutinee(scrutinee, dt, name));
                let datatype = selector_datatype.as_ref().or(declared_datatype.as_ref());
                // When the inner pattern is a literal and we have a native datatype,
                // encode as equality against the full constructor term:
                //   scrutinee == Ctor(lit_value)
                // This avoids ay's incomplete tester/selector axiom propagation
                // in non-DT logics (UFLIA, QF_AUFLIA). (#1055)
                if let Some(dt) = datatype {
                    if let Some(inner_pat) = inner.as_deref() {
                        if let Some(ctor_term) =
                            self.try_encode_constructor_equality(name, inner_pat, dt, prefix)?
                        {
                            let _eq_sort = scrutinee_sort
                                .cloned()
                                .or_else(|| {
                                    let actual_sort = self.solver.get_sort(scrutinee);
                                    let ctor_sort = self.solver.get_sort(ctor_term);
                                    select_structural_sort_target(&actual_sort, &ctor_sort)
                                })
                                .unwrap_or_else(|| {
                                    // Structural sort mismatch in pattern condition —
                                    // both sorts are known but incompatible. Conservative
                                    // bridge, not an inference failure. (#2231)
                                    unsoundness::increment(
                                        unsoundness::UnsoundnessCategory::SortCoercionBridge,
                                    );
                                    Sort::Int
                                });
                            return Ok(self.eq_term(scrutinee, ctor_term));
                        }
                    } else {
                        // No inner pattern: either a truly nullary constructor
                        // (e.g., None) or a non-nullary one used as a wildcard
                        // (e.g., Some with inner pattern omitted = Some(_)).
                        let is_nullary = dt
                            .constructors
                            .iter()
                            .find(|c| datatype_constructor_matches(dt, &c.name, name))
                            .is_some_and(|c| c.fields.is_empty());
                        if is_nullary {
                            let actual_ctor = datatype_constructor_name(dt, name);
                            if let Some(ctor_term) = self.axiom_datatype_constructor(
                                "pattern nullary constructor",
                                dt,
                                &actual_ctor,
                                &[],
                            ) {
                                let _eq_sort = scrutinee_sort
                                    .cloned()
                                    .or_else(|| {
                                        let actual_sort = self.solver.get_sort(scrutinee);
                                        let ctor_sort = self.solver.get_sort(ctor_term);
                                        select_structural_sort_target(&actual_sort, &ctor_sort)
                                    })
                                    .unwrap_or_else(|| {
                                        unsoundness::increment(
                                            unsoundness::UnsoundnessCategory::SortCoercionBridge,
                                        );
                                        Sort::Int
                                    });
                                return Ok(self.eq_term(scrutinee, ctor_term));
                            }
                            // Fall through to tester approach on sort mismatch
                        }
                        // Non-nullary constructor without inner pattern (e.g.,
                        // Some without binding): fall through to tester approach
                    }
                }

                // Fallback: tester + selector approach (used for UF path and
                // complex inner patterns like nested constructors or tuples)
                let ctor_cond = self.encode_constructor_test(name, scrutinee, datatype)?;
                let Some(inner_pat) = inner.as_deref() else {
                    return Ok(ctor_cond);
                };

                // Multi-field constructor with native datatype: use per-field
                // selectors to check inner pattern conditions. Only when the
                // scrutinee actually has the expected Datatype sort at the ay
                // level - otherwise fall through to UF path. (#1965, #2002)
                if let Some(dt) = datatype {
                    let selector_datatype =
                        self.selector_datatype_for_scrutinee(scrutinee, dt, name);
                    let dt_sort_ok = {
                        let expected = Sort::Datatype(selector_datatype.clone()).as_term_sort();
                        self.solver.get_sort(scrutinee) == expected
                    };
                    if dt_sort_ok {
                        if let Some(fields) =
                            Self::constructor_multi_field_selectors(&selector_datatype, name)
                        {
                            if let Pattern::Tuple(elements) = inner_pat {
                                let mut cond = ctor_cond;
                                for (i, sub_pattern) in elements.iter().enumerate() {
                                    if i >= fields.len() {
                                        break;
                                    }
                                    let field = &fields[i];
                                    if let Ok(field_term) = self.solver.try_datatype_selector(
                                        &field.name,
                                        scrutinee,
                                        field.sort.clone(),
                                    ) {
                                        let sub_cond = self.encode_pattern_condition_with_sort(
                                            field_term,
                                            sub_pattern,
                                            None,
                                            Some(&field.sort),
                                            prefix,
                                        )?;
                                        cond = self.solver.and(cond, sub_cond);
                                    }
                                }
                                return Ok(cond);
                            }
                        }
                    }
                }

                // Extract the payload to check inner conditions (e.g., Some(42))
                let (payload_term, payload_sort) = if let Some(dt) = datatype {
                    if let Some((sel_name, sel_sort)) = Self::constructor_payload_selector(dt, name)
                    {
                        match self.solver.try_datatype_selector(
                            sel_name,
                            scrutinee,
                            sel_sort.clone(),
                        ) {
                            Ok(term) => (term, Some(sel_sort.clone())),
                            Err(err) => {
                                debug!(
                                    "[DEBUG-MATCH] datatype_selector fallback for {name}: {err}"
                                );

                                let short = short_constructor_name(name);
                                let accessor_name = match short {
                                    "Some" | "Ok" => "spec_unwrap",
                                    "Err" => "result_err_error",
                                    _ => {
                                        // Generic accessor for custom constructors (#1681).
                                        // Declare payload_<name> : Int -> Int to extract
                                        // the constructor payload rather than silently
                                        // dropping the inner pattern constraint.
                                        let generic_name =
                                            format!("payload_{}", short.to_lowercase());
                                        let domain_sort = self.pattern_accessor_domain_sort(
                                            scrutinee,
                                            scrutinee_sort,
                                        );
                                        let accessor = self.get_or_declare_accessor_for_sorts(
                                            &generic_name,
                                            &domain_sort,
                                            &Sort::Int,
                                        );
                                        let payload = self.safe_apply(
                                            "pattern_accessor",
                                            &accessor,
                                            &[scrutinee],
                                        )?;
                                        let inner_cond = self.encode_pattern_condition_with_sort(
                                            payload,
                                            inner_pat,
                                            None,
                                            Some(&Sort::Int),
                                            prefix,
                                        )?;
                                        return Ok(self.solver.and(ctor_cond, inner_cond));
                                    }
                                };
                                let domain_sort =
                                    self.pattern_accessor_domain_sort(scrutinee, scrutinee_sort);
                                let accessor = self.get_or_declare_accessor_for_sorts(
                                    accessor_name,
                                    &domain_sort,
                                    &Sort::Int,
                                );
                                (
                                    self.safe_apply("pattern_accessor", &accessor, &[scrutinee])?,
                                    Some(Sort::Int),
                                )
                            }
                        }
                    } else {
                        // No selector: constructor has 0 or 2+ fields.
                        // Multi-field was already handled above; if the constructor
                        // is nullary, an inner pattern like Tag(x) is invalid — fail
                        // closed rather than synthesizing a phantom payload (#2300).
                        let short = short_constructor_name(name);
                        if dt
                            .constructors
                            .iter()
                            .any(|c| c.name == short && c.fields.is_empty())
                        {
                            return Err(EncodingError::solver_error(format!(
                                "encode_pattern_condition: constructor pattern {name} has no payload \
                                 (zero-field constructor) but pattern expects a binding"
                            )));
                        }
                        let generic_name = format!("payload_{}", short.to_lowercase());
                        let domain_sort =
                            self.pattern_accessor_domain_sort(scrutinee, scrutinee_sort);
                        let accessor = self.get_or_declare_accessor_for_sorts(
                            &generic_name,
                            &domain_sort,
                            &Sort::Int,
                        );
                        (
                            self.safe_apply("pattern_accessor", &accessor, &[scrutinee])?,
                            Some(Sort::Int),
                        )
                    }
                } else {
                    let short = short_constructor_name(name);
                    let accessor_name: Cow<'_, str> = match short {
                        "Some" | "Ok" => Cow::Borrowed("spec_unwrap"),
                        "Err" => Cow::Borrowed("result_err_error"),
                        _ => {
                            // Generic accessor for custom constructors without
                            // datatype info - pure UF path (#1681, #1787).
                            Cow::Owned(format!("payload_{}", short.to_lowercase()))
                        }
                    };
                    let domain_sort = self.pattern_accessor_domain_sort(scrutinee, scrutinee_sort);
                    let accessor = self.get_or_declare_accessor_for_sorts(
                        &accessor_name,
                        &domain_sort,
                        &Sort::Int,
                    );
                    // UF accessors are Int -> Int (#2155: safe_apply prevents panics
                    // when scrutinee has non-Int sort, e.g., Datatype or Uninterpreted)
                    (
                        self.safe_apply("pattern_accessor", &accessor, &[scrutinee])?,
                        Some(Sort::Int),
                    )
                };
                // When the payload sort is a known datatype, pass that
                // datatype context to the inner recursion so nested
                // constructor patterns use native testers/selectors
                // instead of UF accessors. (#1296)
                let inner_datatype = payload_sort.as_ref().and_then(|sort| match sort {
                    Sort::Datatype(dt) => Some(dt.clone()),
                    Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
                    _ => None,
                });
                let inner_cond = self.encode_pattern_condition_with_sort(
                    payload_term,
                    inner_pat,
                    inner_datatype.as_ref(),
                    payload_sort.as_ref(),
                    prefix,
                )?;
                Ok(self.solver.and(ctor_cond, inner_cond))
            }

            // Tuple: conjoin conditions for each element pattern
            Pattern::Tuple(elements) => {
                let mut cond = self.solver.bool_const(true);
                let domain_sort = scrutinee_sort
                    .cloned()
                    .unwrap_or_else(|| self.solver.get_sort(scrutinee));
                for (i, sub_pattern) in elements.iter().enumerate() {
                    let getter_name = tuple_field_logic_fn_name(i);
                    let elem_sort = self.infer_tuple_element_sort_with_context(
                        sub_pattern,
                        prefix,
                        &getter_name,
                        &domain_sort,
                    );
                    let elem_datatype = match &elem_sort {
                        Sort::Datatype(dt) => Some(dt),
                        _ => None,
                    };
                    let getter =
                        self.get_or_declare_tuple_getter(&getter_name, &domain_sort, &elem_sort);
                    let elem_term = self.safe_apply("tuple_getter", &getter, &[scrutinee])?;
                    let sub_cond = self.encode_pattern_condition_with_sort(
                        elem_term,
                        sub_pattern,
                        elem_datatype,
                        Some(&elem_sort),
                        prefix,
                    )?;
                    cond = self.solver.and(cond, sub_cond);
                }
                Ok(cond)
            }
            // Pattern is #[non_exhaustive]; future variants fail closed here.
            #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
            _ => Ok(self.solver.bool_const(false)),
        }
    }
}
