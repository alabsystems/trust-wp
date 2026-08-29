// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier encoding for pure expressions and formulas.
//!
//! This module handles encoding `forall`/`exists` quantifiers into ay terms,
//! including:
//! - Pure expression quantifiers with trigger support and multi-variable collapsing
//! - Formula-level quantifiers
//! - Bool quantifier expansion (finite domain case splitting)
//! - Multi-variable Bool cartesian product expansion
//! - `resolve(x)` built-in encoding (`x_current == x_final`)
//!
//! Constructor equality elimination logic is in [`super::quantifier_ctor_elim`].
//!
//! Extracted from `logic_fn.rs` as Phase 2 of the logic-fn decomposition
//! (designs/2026-02-13-logic-fn-decomposition.md, #907).
//! Decomposed into directory module as part of #1988.

#[cfg(any(test, feature = "sep-logic"))]
mod formula_quantifier;
pub(crate) mod pure_quantifier;

use std::sync::Arc;

use ay_dpll::api::{SolverError, Term};
use trust_wp_core::formula::PureExpr;

use super::AYEncoder;
use crate::error::EncodingError;

impl AYEncoder {
    /// Encode `resolve(x)` as `x_current == x_final`.
    ///
    /// For mutable references, resolve asserts that the current value equals
    /// the final/prophecy value, meaning the mutable borrow has ended.
    ///
    /// For by-value parameters (no mutable borrow), `resolve(x)` is trivially
    /// `true` because there is no prophecy variable to constrain. This matches
    /// Creusot semantics where resolve on non-reference types is vacuously true.
    /// (#2683)
    ///
    /// The argument can be:
    /// - `Var("x")` -> generates `x_current == x_final` (if x is &mut)
    /// - `Deref(Var("x"))` -> strips Deref, generates `x_current == x_final`
    /// - `Deref(Deref(Var("x")))` -> strips all Deref layers, same result
    /// - Non-variable expressions (e.g., field access `x.a`) -> delegates to
    ///   encoding Deref and Final forms of the expression
    ///
    /// All `Deref` layers are stripped to reach the base expression. Without
    /// this, `Deref(Deref(Var("x")))` would produce `x_current_current`
    /// instead of the intended `x_current`. See #508.
    pub(super) fn encode_resolve(
        &mut self,
        arg: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Strip all Deref layers to get the base variable -- resolve(*x),
        // resolve(**x), etc. should all produce x_current == x_final.
        // A single-layer strip would leave nested derefs broken (#508).
        let mut base = arg;
        while let PureExpr::Deref(inner) = base {
            base = inner.as_ref();
        }

        // For simple variable references, check if the variable has a _final
        // counterpart in the environment. If not, this is a by-value parameter
        // (no mutable borrow) and resolve is trivially true. (#2683)
        if let PureExpr::Var(name, _) = base {
            let final_name = super::sort_context::DerivedKind::Final
                .format_name(&super::sort_context::apply_name_prefix(name, prefix));
            if self.var_term(&final_name).is_none() {
                // No _final variable declared — this is a by-value parameter.
                // resolve(x) for by-value types is trivially true (no borrow to resolve).
                return Ok(self.solver.bool_const(true));
            }
        }

        // Build the Deref and Final forms of the base to get _current and _final names
        let current_expr = PureExpr::Deref(Arc::new(base.clone()));
        let final_expr = PureExpr::Final(Arc::new(base.clone()));
        let _base_sort = self.infer_expr_sort_with_context(base, prefix);

        let current_term = self.encode_pure_impl(&current_expr, prefix)?;
        let final_term = self.encode_pure_impl(&final_expr, prefix)?;

        Ok(self.eq_term(current_term, final_term))
    }

    /// Universal quantifier in pure expressions — delegates to shared implementation.
    pub(super) fn encode_pure_forall_impl(
        &mut self,
        var: &str,
        var_sort: Option<trust_wp_core::formula::ExprSort>,
        body: &PureExpr,
        triggers: &[Vec<PureExpr>],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        self.encode_pure_quantifier_impl(
            QuantifierKind::Forall,
            var,
            var_sort,
            body,
            triggers,
            prefix,
        )
    }

    /// Existential quantifier in pure expressions — delegates to shared implementation.
    pub(super) fn encode_pure_exists_impl(
        &mut self,
        var: &str,
        var_sort: Option<trust_wp_core::formula::ExprSort>,
        body: &PureExpr,
        triggers: &[Vec<PureExpr>],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        self.encode_pure_quantifier_impl(
            QuantifierKind::Exists,
            var,
            var_sort,
            body,
            triggers,
            prefix,
        )
    }

    /// Encode an existential quantifier: exists x. body — delegates to shared implementation.
    #[cfg(any(test, feature = "sep-logic"))]
    pub(super) fn encode_exists(
        &mut self,
        var: &str,
        var_sort: Option<trust_wp_core::formula::ExprSort>,
        body: &trust_wp_core::formula::Formula,
        triggers: &[Vec<trust_wp_core::formula::Formula>],
    ) -> Result<Term, EncodingError> {
        self.encode_formula_quantifier(QuantifierKind::Exists, var, var_sort, body, triggers)
    }

    /// Encode a universal quantifier: forall x. body — delegates to shared implementation.
    #[cfg(any(test, feature = "sep-logic"))]
    pub(super) fn encode_forall(
        &mut self,
        var: &str,
        var_sort: Option<trust_wp_core::formula::ExprSort>,
        body: &trust_wp_core::formula::Formula,
        triggers: &[Vec<trust_wp_core::formula::Formula>],
    ) -> Result<Term, EncodingError> {
        self.encode_formula_quantifier(QuantifierKind::Forall, var, var_sort, body, triggers)
    }

    /// Expand N Bool-sorted quantifier variables via cartesian product of
    /// Bool valuations (#1027, #1134).
    ///
    /// Single variable: `∀b. φ(b)` → `φ(true) ∧ φ(false)`
    /// Multi-variable:  `∀a,b. φ(a,b)` → `φ(T,T) ∧ φ(T,F) ∧ φ(F,T) ∧ φ(F,F)`
    /// For `∃`, branches are OR'd instead of AND'd.
    ///
    /// The caller caps `vars` at 4 elements (16 branches) to bound the
    /// cartesian product expansion.
    fn encode_pure_multi_bool_expansion(
        &mut self,
        kind: QuantifierKind,
        vars: &[&str],
        body: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let n = vars.len();
        debug_assert!(n > 0 && n <= 4, "Bool expansion capped at 4 variables");

        // Save old bindings for all variables (both bare and prefixed).
        // Stored as parallel arrays to avoid clippy::type_complexity.
        let mut bare_names: Vec<String> = Vec::with_capacity(n);
        let mut bare_old: Vec<Option<Term>> = Vec::with_capacity(n);
        let mut pref_names: Vec<Option<String>> = Vec::with_capacity(n);
        let mut pref_old: Vec<Option<Term>> = Vec::with_capacity(n);
        for &v in vars {
            bare_names.push(v.to_string());
            bare_old.push(self.var_term(v));
            let prefixed = prefix.map(|kind| kind.format_name(v));
            let old_pref = prefixed.as_ref().and_then(|pn| self.var_term(pn.as_str()));
            pref_names.push(prefixed);
            pref_old.push(old_pref);
        }

        let true_const = self.solver.bool_const(true);
        let false_const = self.solver.bool_const(false);

        // Iterate over all 2^N valuations using a bitmask.
        let num_branches = 1u32 << n;
        let mut branch_results: Vec<Result<Term, EncodingError>> =
            Vec::with_capacity(num_branches as usize);

        for mask in 0..num_branches {
            // Bind each variable to true/false based on bitmask.
            for (i, &v) in vars.iter().enumerate() {
                let val = if (mask >> i) & 1 == 1 {
                    true_const
                } else {
                    false_const
                };
                self.insert_var(v.to_string(), val);
                if let Some(ref pn) = pref_names[i] {
                    if pn.as_str() != v {
                        self.insert_var(pn.clone(), val);
                    }
                }
            }
            branch_results.push(self.encode_pure_impl(body, prefix));
        }

        // Restore original bindings — always, even on error.
        for i in 0..n {
            self.restore_var(&bare_names[i], bare_old[i]);
            if let Some(ref pn) = pref_names[i] {
                if pn.as_str() != bare_names[i].as_str() {
                    self.restore_var(pn, pref_old[i]);
                }
            }
        }

        // Propagate any encoding errors, then combine all branches.
        let mut terms: Vec<Term> = Vec::with_capacity(branch_results.len());
        for r in branch_results {
            terms.push(r?);
        }

        // Combine: forall → AND of all branches, exists → OR of all branches.
        let mut combined = terms[0];
        for &t in &terms[1..] {
            combined = match kind {
                QuantifierKind::Forall => self.solver.and(combined, t),
                QuantifierKind::Exists => self.solver.or(combined, t),
            };
        }
        Ok(combined)
    }
}

/// Distinguishes universal vs existential quantifier for shared encoding logic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum QuantifierKind {
    Forall,
    Exists,
}

impl QuantifierKind {
    /// Apply quantifier without triggers.
    pub(crate) fn apply_simple(
        self,
        solver: &mut ay_dpll::api::Solver,
        vars: &[Term],
        body: Term,
    ) -> Result<Term, SolverError> {
        match self {
            Self::Forall => solver.try_forall(vars, body),
            Self::Exists => solver.try_exists(vars, body),
        }
    }

    /// Apply quantifier with trigger patterns.
    pub(crate) fn apply_with_triggers(
        self,
        solver: &mut ay_dpll::api::Solver,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Result<Term, SolverError> {
        match self {
            Self::Forall => solver.try_forall_with_triggers(vars, body, triggers),
            Self::Exists => solver.try_exists_with_triggers(vars, body, triggers),
        }
    }

    /// Apply a triggered quantifier, optionally falling back to the triggerless
    /// form when synthesized patterns are rejected as invalid.
    pub(crate) fn apply_with_optional_invalid_trigger_fallback(
        self,
        solver: &mut ay_dpll::api::Solver,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
        allow_invalid_trigger_fallback: bool,
    ) -> Result<(Term, bool), SolverError> {
        match self.apply_with_triggers(solver, vars, body, triggers) {
            Ok(term) => Ok((term, false)),
            Err(SolverError::InvalidTrigger { .. }) if allow_invalid_trigger_fallback => self
                .apply_simple(solver, vars, body)
                .map(|term| (term, true)),
            Err(err) => Err(err),
        }
    }
}

#[cfg(any(test, feature = "sep-logic"))]
const TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT: usize = 2;

#[cfg(any(test, feature = "sep-logic"))]
fn push_single_pattern(out: &mut Vec<Vec<Term>>, term: Term) {
    push_pattern(out, vec![term]);
}

#[cfg(any(test, feature = "sep-logic"))]
fn push_pattern(out: &mut Vec<Vec<Term>>, pattern: Vec<Term>) {
    if out.len() >= TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT {
        return;
    }
    if out.contains(&pattern) {
        return;
    }
    out.push(pattern);
}
