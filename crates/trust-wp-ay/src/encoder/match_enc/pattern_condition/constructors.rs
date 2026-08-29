// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{DatatypeSort, Sort, Term};
use tracing::debug;
use trust_wp_core::formula::Pattern;

use super::super::{datatype_constructor_name, short_constructor_name};
use crate::{
    encoder::{infer_expr_sort, sort_context::DerivedKind, AYEncoder},
    error::EncodingError,
};

impl AYEncoder {
    /// Try to encode a constructor pattern as a full constructor term for
    /// equality comparison: `scrutinee == Ctor(value)`.
    ///
    /// Only activates when the inner pattern literal has a Bool->Int sort
    /// mismatch with the datatype field sort. In this case, the tester/selector
    /// approach fails because ay's non-DT solver paths (UFLIA, QF_AUFLIA) do
    /// not propagate `is-C(x)` from `x = C(args)`. Constructor equality
    /// (`scrutinee == Some(ite(true,1,0))`) works because ay's EUF theory
    /// handles term equality directly. (#1055)
    ///
    /// For same-sort literals (e.g., `Some(42)` where Int matches Int),
    /// the tester/selector approach works correctly and also supports the
    /// negative case (mismatched values) via LIA reasoning on the selector.
    pub(super) fn try_encode_constructor_equality(
        &mut self,
        ctor_name: &str,
        inner_pattern: &Pattern,
        datatype: &DatatypeSort,
        prefix: Option<DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        let short = short_constructor_name(ctor_name);
        match inner_pattern {
            Pattern::Literal(lit) => {
                // Only use constructor equality when there's a sort mismatch
                // (Bool literal in Int-sorted field). For same-sort cases, the
                // tester/selector approach is more complete (supports negative
                // cases via LIA on selector values).
                if let Some((_, field_sort)) = Self::constructor_payload_selector(datatype, short) {
                    let lit_sort = infer_expr_sort(lit);
                    if lit_sort == Sort::Bool && *field_sort == Sort::Int {
                        let lit_term = self.encode_pure_impl(lit, prefix)?;
                        let one = self.solver.int_const(1);
                        let zero = self.solver.int_const(0);
                        let coerced = self.solver.ite(lit_term, one, zero);
                        // Use try_ variant to avoid ICE on sort mismatch (#1532)
                        if let Some(ctor_term) = self.axiom_datatype_constructor(
                            "pattern constructor equality",
                            datatype,
                            short,
                            &[coerced],
                        ) {
                            return Ok(Some(ctor_term));
                        }
                        // Fall through to None on sort mismatch
                        return Ok(None);
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// Encode a constructor test (e.g., `is_some(scrutinee)`).
    ///
    /// Returns `Err` when the UF tester application panics due to a sort
    /// mismatch (e.g., scrutinee has Datatype sort but tester expects Int).
    /// (#2155)
    pub(in crate::encoder) fn encode_constructor_test(
        &mut self,
        name: &str,
        scrutinee: Term,
        datatype: Option<&DatatypeSort>,
    ) -> Result<Term, EncodingError> {
        let short = short_constructor_name(name);
        // Try native datatype tester: works for Datatype-sorted scrutinees
        // regardless of whether the DatatypeSort metadata is available.
        // For non-Int scrutinees, the Int->Bool UF fallback would panic, so
        // the native tester is the only viable path. (#2207)
        if datatype.is_some() || self.solver.get_sort(scrutinee) != Sort::Int {
            let actual_ctor = datatype
                .map(|dt| datatype_constructor_name(dt, name))
                .unwrap_or_else(|| short.to_string());
            if let Ok(term) = self.solver.try_datatype_tester(&actual_ctor, scrutinee) {
                return Ok(term);
            }

            debug!(
                    "[DEBUG-MATCH] datatype_tester fallback for constructor {name} on non-datatype scrutinee"
                );
        }

        match short {
            "Some" => {
                self.assert_is_option(scrutinee)?;
                let domain_sort = self.solver.get_sort(scrutinee);
                let tester =
                    self.get_or_declare_constructor_tester_for_sort("is_some", &domain_sort);
                self.safe_apply("constructor_test", &tester, &[scrutinee])
            }
            "None" => {
                self.assert_is_option(scrutinee)?;
                // None is the negation of Some
                let domain_sort = self.solver.get_sort(scrutinee);
                let tester =
                    self.get_or_declare_constructor_tester_for_sort("is_some", &domain_sort);
                let is_some = self.safe_apply("constructor_test", &tester, &[scrutinee])?;
                Ok(self.solver.not(is_some))
            }
            _ => {
                // Generic constructor: is_<name>
                let tester_name = format!("is_{}", short.to_lowercase());
                let domain_sort = self.solver.get_sort(scrutinee);
                let tester =
                    self.get_or_declare_constructor_tester_for_sort(&tester_name, &domain_sort);
                self.safe_apply("constructor_test", &tester, &[scrutinee])
            }
        }
    }
}
