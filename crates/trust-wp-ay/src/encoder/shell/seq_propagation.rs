// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SeqValue propagation helpers for `AYEncoder`.
//!
//! These methods bridge `SeqValue` entries across variable bindings so that
//! the Array+Length encoding remains usable after variable aliasing (e.g.,
//! `source = target` equality assertions, `View(return_expr)` → `result_view`
//! linkage).
//!
//! Extracted from `encoder/mod.rs` (#2655).

use std::sync::Arc;

use trust_wp_core::formula::PureExpr;

use crate::{encoder::AYEncoder, error::EncodingError};

impl AYEncoder {
    /// Build an equality term that respects trust-wp's SeqValue decomposition.
    pub(in crate::encoder) fn seq_aware_equality_term(
        &mut self,
        lhs: ay_dpll::api::Term,
        rhs: ay_dpll::api::Term,
    ) -> ay_dpll::api::Term {
        self.try_decompose_seq_equality(lhs, rhs)
            .ok()
            .flatten()
            .unwrap_or_else(|| self.eq_term(lhs, rhs))
    }

    #[cfg(test)]
    pub(crate) fn test_seq_aware_equality_term(
        &mut self,
        lhs: ay_dpll::api::Term,
        rhs: ay_dpll::api::Term,
    ) -> ay_dpll::api::Term {
        self.seq_aware_equality_term(lhs, rhs)
    }

    /// Assert an unconditional ground equality and propagate SeqValue metadata.
    pub(in crate::encoder) fn assert_ground_equality_with_seq_propagation(
        &mut self,
        label: &str,
        lhs: ay_dpll::api::Term,
        rhs: ay_dpll::api::Term,
    ) {
        let equality = self.seq_aware_equality_term(lhs, rhs);
        self.assert_solver_term(label, equality);

        if self.has_seq_value(lhs) {
            self.propagate_seq_value(lhs, rhs);
        }
        if self.has_seq_value(rhs) {
            self.propagate_seq_value(rhs, lhs);
        }
    }

    /// Propagate SeqValue from `source` to `target` if `source` has one (#1317).
    ///
    /// When `source = target` is asserted as an SMT equality but the variable
    /// map still points `target` at a fresh constant (not rebound), the
    /// `SeqValue` registry has an entry for `source` but not `target`. This
    /// makes `seq_len_term(target)` / `seq_index_term(target, i)` fall back
    /// to UF projectors, defeating the Array+Length encoding.
    ///
    /// Call this after asserting `source = target` when `target` is a declared
    /// variable that may later be used in view/postcondition encoding.
    pub(crate) fn propagate_seq_value(
        &mut self,
        source: ay_dpll::api::Term,
        target: ay_dpll::api::Term,
    ) {
        if source == target {
            return;
        }
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&source) {
            // If target already has a SeqValue, assert component-wise equality
            // between the existing and new SeqValues. This makes contradictory
            // flat call-site assumptions (multiple push_back results equated to
            // the same variable) UNSAT in Array theory. (#1317)
            if let Some(existing) = self.seq_state.get_seq_value_cloned(&target) {
                if existing.arr != sv.arr {
                    let _array_sort =
                        ay_dpll::api::Sort::array(ay_dpll::api::Sort::Int, ay_dpll::api::Sort::Int);
                    let arr_eq = self.eq_term(existing.arr, sv.arr);
                    self.assert_solver_term("propagate_seq_value/arr", arr_eq);
                }
                if existing.len != sv.len {
                    let len_eq = self.eq_term(existing.len, sv.len);
                    self.assert_solver_term("propagate_seq_value/len", len_eq);
                }
                if existing.offset != sv.offset {
                    let off_eq = self.eq_term(existing.offset, sv.offset);
                    self.assert_solver_term("propagate_seq_value/off", off_eq);
                }
            } else {
                self.insert_seq_value(target, sv);
            }
        }
    }

    /// Bridge SeqValue from a return_expr's view variable to `result_view` (#1317).
    ///
    /// The push_back chain builds SeqValues on view terms (e.g.,
    /// `final_call_1_final_final_final_final_view`). When the return_expr is
    /// `Final(Final(...(Var("call_1"))))`, the body encoding produces the
    /// non-view variable (`call_1_final_..._final`), which has no SeqValue.
    /// Postconditions reference `View(Var("result"))` = `result_view`, which
    /// also has no SeqValue. This method bridges the gap by looking up the
    /// return_expr's View form's SeqValue and propagating it to `result_view`.
    pub(crate) fn propagate_body_view_seq_value_to_result(&mut self, return_expr: &PureExpr) {
        use super::super::sort_context::resolve_view_var_name;

        // Compute the view var name for View(return_expr).
        let body_view_expr = PureExpr::View(Arc::new(return_expr.clone()));
        let Some(body_view_name) = resolve_view_var_name(&body_view_expr, None) else {
            return;
        };

        let Some(body_view_term) = self.var_term(&body_view_name) else {
            return;
        };

        let Some(sv) = self.seq_state.get_seq_value_cloned(&body_view_term) else {
            return;
        };

        // Declare result_view with Seq sort if it doesn't exist yet, then propagate.
        let seq_sort = self.get_seq_sort();
        let Ok(result_view_term) = self.get_or_declare_var("result_view", seq_sort) else {
            return;
        };

        self.insert_seq_value(result_view_term, sv);
    }

    /// Compute the inner term for a transparent adapter return expression
    /// (`Copied(...)` / `Cloned(...)`).
    ///
    /// The caller can use this to seed `result` from the adapter's inner
    /// logical model instead of the raw wrapper.
    pub(crate) fn body_inner_term_for_transparent_adapter(
        &mut self,
        return_expr: &PureExpr,
    ) -> Result<Option<ay_dpll::api::Term>, EncodingError> {
        use super::super::logic_fn::transparent_adapter_inner;

        let Some(inner) = transparent_adapter_inner(return_expr) else {
            return Ok(None);
        };
        Ok(Some(self.encode_pure(inner)?))
    }
}
