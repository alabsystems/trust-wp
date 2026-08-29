// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Transparent `produces` decomposition for logical `FMapIter`. (#2116)
//!
//! The generic `produces` fallback is intentionally abstract: reflexivity and
//! transitivity are sound, but the solver cannot learn what a concrete
//! `produces(iter, visited, next)` fact means for the iterator views.
//!
//! For logical `FMapIter`, assert one additional quantified axiom:
//!
//! ```text
//! produces(self, visited, o) ==> fmap_partition_body(self, visited, o)
//! ```
//!
//! The body mirrors the earlier driver-side FMap partition rewrite, but it is
//! attached once to the `produces` predicate instead of being inlined into
//! every caller. A small logical view projector bridges quantified iterator
//! states to the existing ground `it@` terms used elsewhere in the encoder.
//!
//! Submodules:
//! - [`body_builder`]: PureExpr body construction and FMapIter sort detection

mod body_builder;
pub(crate) mod completed_delegation;
pub(crate) mod iter_mut;

use std::sync::Arc;

use ay_dpll::api::FuncDecl;
use trust_wp_core::formula::{ExprSort, PureExpr};

pub(crate) use self::body_builder::is_logical_fmap_iter_receiver;
use self::body_builder::{
    build_logical_fmap_iter_body, logical_fmap_iter_expr_sort, FMAP_ITER_VIEW_LOGIC_FN,
};
use super::{resolve_view_var_name, sort_context::DerivedKind, AYEncoder};
use crate::error::EncodingError;

impl AYEncoder {
    pub(crate) fn assert_logical_fmap_iter_produces_decomposition(
        &mut self,
        receiver: &PureExpr,
        produces_func: &FuncDecl,
    ) -> Result<(), EncodingError> {
        let Some(iter_sort) = logical_fmap_iter_expr_sort(receiver) else {
            return Ok(());
        };

        let dedup_key = format!(
            "logical_fmap_iter_produces_decomposition::{}",
            produces_func.name()
        );
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return Ok(());
        }

        let param_sorts = produces_func.domain();
        if param_sorts.len() != 3 || param_sorts[0] != param_sorts[2] {
            return Ok(());
        }

        let self_name = "__logical_fmap_iter_self";
        let visited_name = "__logical_fmap_iter_visited";
        let next_name = "__logical_fmap_iter_next";
        let self_term = self.solver.fresh_var(self_name, param_sorts[0].clone());
        let visited_term = self.solver.fresh_var(visited_name, param_sorts[1].clone());
        let next_term = self.solver.fresh_var(next_name, param_sorts[2].clone());

        let projector_smt = trust_wp_core::logic::logic_fn_smt_name(FMAP_ITER_VIEW_LOGIC_FN);
        self.record_sort_hint(projector_smt, ExprSort::FMap);

        let mut old_bindings = Vec::with_capacity(3);
        for (name, term, sort) in [
            (self_name, self_term, param_sorts[0].clone()),
            (visited_name, visited_term, param_sorts[1].clone()),
            (next_name, next_term, param_sorts[2].clone()),
        ] {
            old_bindings.push((name.to_string(), self.insert_var(name.to_string(), term)));
            self.bind_quantifier_var(name.to_string());
            self.insert_var_sort(name.to_string(), sort);
        }

        self.quantifier_state.inc_quantifier_depth();
        let encoded = (|| -> Result<(ay_dpll::api::Term, ay_dpll::api::Term), EncodingError> {
            let premise_expr = PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var(
                    self_name.to_string(),
                    Some(iter_sort.clone()),
                )),
                method: "produces".to_string(),
                args: vec![
                    PureExpr::Var(visited_name.to_string(), Some(ExprSort::Seq)),
                    PureExpr::Var(next_name.to_string(), Some(iter_sort.clone())),
                ],
            };
            let premise = self.encode_pure(&premise_expr)?;
            let body_expr =
                build_logical_fmap_iter_body(iter_sort.clone(), self_name, visited_name, next_name);
            let body = self.encode_pure(&body_expr)?;
            Ok((premise, body))
        })();
        self.quantifier_state.dec_quantifier_depth();

        for (name, old) in old_bindings.into_iter().rev() {
            self.unbind_quantifier_var(&name);
            if let Some(term) = old {
                self.insert_var(name, term);
            }
        }

        let (premise, body) = encoded?;
        let implication = self.solver.implies(premise, body);
        let axiom = self.solver.forall_with_triggers(
            &[self_term, visited_term, next_term],
            implication,
            &[&[premise]],
        );
        self.solver.assert_term(axiom);
        Ok(())
    }

    /// Assert ground-level length partition for a logical FMapIter `produces` call.
    ///
    /// When `produces(it, visited, next)` is asserted at ground level and `it` is
    /// a logical FMapIter, assert the ground implication:
    ///
    /// ```text
    /// produces(it, visited, next) ==> fmap_len(view(it)) == seq_len(visited) + fmap_len(view(next))
    /// ```
    ///
    /// This bypasses the full transparent predicate decomposition axiom (which
    /// contains nested quantifiers that ay-dpll struggles to instantiate) and gives
    /// the solver the length partition directly. The full decomposition axiom is
    /// still asserted for the other 4 clauses (visited membership, next membership,
    /// receiver coverage, key uniqueness), but the length partition is by far the
    /// most commonly needed and the cheapest to assert at ground level. (#2116)
    pub(crate) fn assert_logical_fmap_iter_ground_length_partition(
        &mut self,
        receiver: &PureExpr,
        produces_term: ay_dpll::api::Term,
        visited: &PureExpr,
        successor: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Result<Option<ay_dpll::api::Term>, EncodingError> {
        if self.quantifier_state.quantifier_depth() > 0 || !is_logical_fmap_iter_receiver(receiver)
        {
            return Ok(None);
        }

        let dedup_key = format!("logical_fmap_iter_ground_length::{produces_term:?}");
        let should_assert_implication = self.mark_logic_fn_axiom_asserted(dedup_key);

        // Encode len(view(receiver)) — this will be an fmap_len(it_view) term
        let receiver_view = match receiver {
            PureExpr::View(_) => receiver.clone(),
            _ => PureExpr::View(Arc::new(receiver.clone())),
        };
        let receiver_len = PureExpr::MethodCall {
            receiver: Arc::new(receiver_view),
            method: "len".to_string(),
            args: vec![],
        };

        // Encode len(visited) — this will be a seq_len(visited) term
        let visited_len = PureExpr::MethodCall {
            receiver: Arc::new(visited.clone()),
            method: "len".to_string(),
            args: vec![],
        };

        // Encode len(view(successor)) — this will be an fmap_len(next_view) term
        let successor_view = match successor {
            PureExpr::View(_) => successor.clone(),
            _ => PureExpr::View(Arc::new(successor.clone())),
        };
        let successor_len = PureExpr::MethodCall {
            receiver: Arc::new(successor_view),
            method: "len".to_string(),
            args: vec![],
        };

        let receiver_len_term = self.encode_pure_impl(&receiver_len, prefix)?;
        let visited_len_term = self.encode_pure_impl(&visited_len, prefix)?;
        let successor_len_term = self.encode_pure_impl(&successor_len, prefix)?;

        // produces(it, v, next) ==> len(view(it)) == len(v) + len(view(next))
        let sum = self.solver.add(visited_len_term, successor_len_term);
        let len_eq = self.eq_term(receiver_len_term, sum);
        if should_assert_implication {
            let implication = self.solver.implies(produces_term, len_eq);
            self.assert_solver_term("fmap_iter_ground_length_partition", implication);
        }

        // Return the exact ground consequence as well as asserting the
        // implication.  A positive use of `produces` can then carry this
        // consequence directly into its caller's formula instead of requiring
        // the solver to rediscover ground modus ponens in the presence of the
        // full quantified decomposition axiom.  This is logically equivalent
        // to the raw predicate because the implication above remains asserted.
        Ok(Some(len_eq))
    }

    pub(crate) fn assert_logical_fmap_iter_view_bridge(
        &mut self,
        expr: &PureExpr,
        expr_term: ay_dpll::api::Term,
        prefix: Option<DerivedKind>,
    ) -> Result<(), EncodingError> {
        if self.quantifier_state.quantifier_depth() > 0 || !is_logical_fmap_iter_receiver(expr) {
            return Ok(());
        }

        let dedup_key = format!("logical_fmap_iter_view_bridge::{expr_term:?}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return Ok(());
        }

        let projector_smt = trust_wp_core::logic::logic_fn_smt_name(FMAP_ITER_VIEW_LOGIC_FN);
        self.record_sort_hint(projector_smt, ExprSort::FMap);

        // Preserve an existing view wrapper so we record the FMap hint against
        // the actual ground-view name (`it_view`) rather than a synthetic
        // nested view (`View(View(it))`), which resolve_view_var_name cannot
        // name. Without this normalization the already-viewed path can fall
        // back to the iterator carrier sort instead of FMap. (#2116)
        let view_expr = match expr {
            PureExpr::View(_) => expr.clone(),
            _ => PureExpr::View(Arc::new(expr.clone())),
        };
        if let Some(view_name) = resolve_view_var_name(&view_expr, prefix) {
            self.record_sort_hint(view_name, ExprSort::FMap);
        }

        let arg_exprs = [expr.clone()];
        let projected = self.apply_logic_fn(
            FMAP_ITER_VIEW_LOGIC_FN,
            &[expr_term],
            Some(&arg_exprs),
            prefix,
        )?;
        let ground_view = self.encode_pure_impl(&view_expr, prefix)?;
        let bridge = self.eq_term(projected, ground_view);
        self.assert_solver_term("logical_fmap_iter_view_bridge", bridge);
        Ok(())
    }
}
