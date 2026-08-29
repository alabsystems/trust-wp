// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Formula-level quantifier encoding.
//!
//! Handles `forall`/`exists` over `Formula` with:
//! - Bool quantifier expansion (finite domain case splitting)
//! - Sep-logic trigger synthesis (`PointsTo`/`MutBorrow` atoms)
//! - PureExpr-based trigger synthesis fallback
//!
//! Extracted from `quantifier.rs` as part of #1988.

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::formula::{ExprSort, Formula, PureExpr, Value};

use super::{
    super::{
        trigger::{expr_mentions_any_var, synthesize_triggers},
        AYEncoder,
    },
    pure_quantifier::peel_quantifier_ref_annotation,
    push_pattern, push_single_pattern, QuantifierKind, TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT,
};
use crate::error::EncodingError;

impl AYEncoder {
    /// Encode a formula-level quantifier (forall or exists).
    ///
    /// Unified from the previously separate `encode_forall` and `encode_exists`
    /// methods which had identical structure. (#626)
    ///
    /// When explicit triggers are provided (non-empty `triggers`), they are
    /// encoded and passed to `apply_with_triggers()`. When triggers are empty,
    /// automatic formula trigger synthesis is attempted (#1726). If synthesis
    /// finds triggers, those are used; otherwise falls back to `apply_simple()`.
    pub(in crate::encoder) fn encode_formula_quantifier(
        &mut self,
        kind: QuantifierKind,
        var: &str,
        var_sort: Option<ExprSort>,
        body: &Formula,
        triggers: &[Vec<Formula>],
    ) -> Result<Term, EncodingError> {
        // Reflexive equality elimination (#2696): if the formula body is
        // `Pure(lhs == rhs)` with structurally identical sides (or implies
        // leading to such), the quantifier is trivially true.
        if is_formula_reflexive_equality(body) {
            return Ok(self.solver.bool_const(true));
        }

        // Infer sort hints from the body before resolving the bound variable's sort.
        // Without this, bound variables default to Int even when used in Bool contexts
        // (e.g., `forall b. !b` or `exists b. !b`). (#544)
        self.register_formula_body_sort_hints(body);

        let qvar_sort = if let Some(es) = var_sort {
            let explicit = self.sort_from_expr_sort(peel_quantifier_ref_annotation(&es));
            if explicit == Sort::Int {
                let hint_sort = self.resolve_decl_sort(var, None, Sort::Int);
                if hint_sort == Sort::Int {
                    explicit
                } else {
                    hint_sort
                }
            } else {
                explicit
            }
        } else {
            self.resolve_decl_sort(var, None, Sort::Int)
        };

        // Bool quantifier expansion (#1027): ay's quantifier engine does not
        // enumerate the finite Bool domain, causing `∀b. b ∨ ¬b` and
        // `∃b. b == true` to return Unknown. Expand Bool quantifiers into
        // case splits: ∀b. φ(b) → φ(true) ∧ φ(false),
        //              ∃b. φ(b) → φ(true) ∨ φ(false).
        if qvar_sort == Sort::Bool {
            return self.encode_formula_bool_expansion(kind, var, body);
        }

        let qvar_id = self.next_quantifier_var_id();
        let bound_var = self
            .solver
            .fresh_var(&format!("qvar_{var}_{qvar_id}"), qvar_sort);

        // Store the variable mapping temporarily
        let old_binding = self.insert_var(var.to_string(), bound_var);
        self.bind_quantifier_var(var.to_string());

        // Encode the body with the bound variable in scope.
        // Increment quantifier_depth so that inner LogicFnCall applications
        // are NOT registered with the ground pool — their arguments are bound
        // variables, not ground terms. (#1965, Lane 5)
        self.quantifier_state.inc_quantifier_depth();
        let body_result = self.encode(body);

        // Trigger synthesis should inspect the full chain of nested same-kind
        // quantifiers so it can see the innermost body and all bound vars.
        let (quantified_var_names, trigger_body) =
            collect_nested_formula_quantifier_vars(kind, var, body);

        // If the triggerless chain collapses to multiple binders, encode the
        // innermost body under a single multi-variable quantifier. This keeps
        // the quantifier structure aligned with the synthesized trigger scope.
        if triggers.is_empty()
            && quantified_var_names.len() > 1
            && quantified_var_names
                .iter()
                .all(|v| self.resolve_decl_sort(v, None, Sort::Int) != Sort::Bool)
        {
            return self.encode_formula_quantifier_multi_var(
                kind,
                &quantified_var_names,
                trigger_body,
            );
        }

        // Encode trigger patterns (Formula → Term) with bound vars in scope.
        // If no explicit triggers are present, synthesize term-level triggers
        // from sep-logic and pure subterms in the nested quantifier body. (#1742, #1726)
        let trigger_patterns_result: Result<Vec<Vec<Term>>, EncodingError> = if triggers.is_empty()
        {
            let synthesized =
                self.synthesize_formula_trigger_terms_for_vars(&quantified_var_names, trigger_body);

            if let Ok(ref patterns) = synthesized {
                if !patterns.is_empty() {
                    debug!(
                        "[trust-wp-ay] synthesized {} formula trigger pattern(s) for ∀/∃{}",
                        patterns.len(),
                        quantified_var_names.join(", "),
                    );
                }
            }

            synthesized
        } else {
            triggers
                .iter()
                .map(|pattern| {
                    pattern
                        .iter()
                        .map(|f| self.encode(f))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect()
        };
        self.quantifier_state.dec_quantifier_depth();

        // Restore the old binding (or remove if there was none) - always, even on error.
        // Use expect() instead of ? — cleanup must complete unconditionally.
        // The variable was inserted just above, so absence is a logic bug. (#1649)
        self.unbind_quantifier_var(var);
        self.restore_var(var, old_binding);

        let body_term = body_result?;
        let trigger_patterns = trigger_patterns_result?;
        let used_synthesized_triggers = triggers.is_empty() && !trigger_patterns.is_empty();

        // Create the quantifier with triggers if present
        if trigger_patterns.is_empty() {
            kind.apply_simple(&mut self.solver, &[bound_var], body_term)
                .map_err(|err| EncodingError::solver_error(err.to_string()))
        } else {
            let trigger_refs: Vec<&[Term]> = trigger_patterns.iter().map(Vec::as_slice).collect();
            let (term, fell_back) = kind
                .apply_with_optional_invalid_trigger_fallback(
                    &mut self.solver,
                    &[bound_var],
                    body_term,
                    &trigger_refs,
                    used_synthesized_triggers,
                )
                .map_err(|err| EncodingError::solver_error(err.to_string()))?;
            if fell_back {
                debug!(
                    "[trust-wp-ay] synthesized formula trigger rejected for {kind:?}<{var}>; \
                     falling back to triggerless quantifier",
                );
            }
            Ok(term)
        }
    }

    fn encode_formula_quantifier_multi_var(
        &mut self,
        kind: QuantifierKind,
        vars: &[String],
        body: &Formula,
    ) -> Result<Term, EncodingError> {
        let mut bound_vars = Vec::with_capacity(vars.len());
        let mut old_bindings: Vec<(String, Option<Term>)> = Vec::with_capacity(vars.len());
        let mut old_sort_bindings: Vec<(String, Option<Sort>)> = Vec::with_capacity(vars.len());

        for v in vars {
            let qvar_id = self.next_quantifier_var_id();
            let qvar_sort = self.resolve_decl_sort(v, None, Sort::Int);
            let bound_var = self
                .solver
                .fresh_var(&format!("qvar_{v}_{qvar_id}"), qvar_sort.clone());
            bound_vars.push(bound_var);

            let old_binding = self.insert_var(v.clone(), bound_var);
            old_bindings.push((v.clone(), old_binding));
            let old_sort = self.insert_var_sort(v.clone(), qvar_sort);
            old_sort_bindings.push((v.clone(), old_sort));
            self.bind_quantifier_var(v.clone());
        }

        self.quantifier_state.inc_quantifier_depth();
        let body_result = self.encode(body);
        let trigger_patterns_result = self.synthesize_formula_trigger_terms_for_vars(vars, body);
        self.quantifier_state.dec_quantifier_depth();

        for v in vars.iter().rev() {
            self.unbind_quantifier_var(v);
        }
        for (name, old_sort) in old_sort_bindings.into_iter().rev() {
            self.restore_var_sort(&name, old_sort);
        }
        for (name, old) in old_bindings.into_iter().rev() {
            self.restore_var(&name, old);
        }

        let body_term = body_result?;
        let trigger_patterns = trigger_patterns_result?;
        if trigger_patterns.is_empty() {
            return kind
                .apply_simple(&mut self.solver, &bound_vars, body_term)
                .map_err(|err| EncodingError::solver_error(err.to_string()));
        }

        let trigger_refs: Vec<&[Term]> = trigger_patterns.iter().map(Vec::as_slice).collect();
        let (term, fell_back) = kind
            .apply_with_optional_invalid_trigger_fallback(
                &mut self.solver,
                &bound_vars,
                body_term,
                &trigger_refs,
                true,
            )
            .map_err(|err| EncodingError::solver_error(err.to_string()))?;
        if fell_back {
            debug!(
                "[trust-wp-ay] synthesized formula trigger rejected for {kind:?}<{vars:?}>; \
                 falling back to triggerless quantifier",
            );
        }
        Ok(term)
    }

    /// Synthesize trigger terms for a formula-level quantifier.
    ///
    /// Priority order:
    /// 1. Sep-logic terms from `PointsTo` / `MutBorrow` atoms referencing `var` (#1742)
    /// 2. Existing PureExpr trigger synthesis fallback (#1726)
    pub(crate) fn synthesize_formula_trigger_terms(
        &mut self,
        var: &str,
        body: &Formula,
    ) -> Result<Vec<Vec<Term>>, EncodingError> {
        let vars = vec![var.to_string()];
        self.synthesize_formula_trigger_terms_for_vars(&vars, body)
    }

    /// Synthesize trigger terms for a collapsed formula-level quantifier.
    ///
    /// This path is used after nested same-kind quantifiers have been collapsed
    /// into a single multi-variable scope, so trigger synthesis sees the actual
    /// innermost body and the complete binder set at once.
    pub(crate) fn synthesize_formula_trigger_terms_for_vars(
        &mut self,
        vars: &[String],
        body: &Formula,
    ) -> Result<Vec<Vec<Term>>, EncodingError> {
        let mut patterns = Vec::new();

        // First try sep-logic trigger terms (domain/permission/value/current/final).
        // Scan once per binder so collapsed multi-variable formula quantifiers
        // can collect triggers tied to any of the bound names.
        for var in vars {
            self.collect_sep_logic_trigger_terms(body, var, vars, &mut patterns)?;
            if patterns.len() >= TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT {
                return Ok(patterns);
            }
        }

        // Fill remaining trigger budget with existing PureExpr-based synthesis.
        // This keeps sep-logic terms as highest priority while preserving
        // trigger coverage from pure formulas when sep synthesis is partial.
        if patterns.len() < TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT {
            let pure_patterns = self.synthesize_formula_pure_trigger_terms(vars, body)?;
            for pattern in pure_patterns {
                push_pattern(&mut patterns, pattern);
                if patterns.len() >= TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT {
                    break;
                }
            }
        }

        Ok(patterns)
    }

    fn synthesize_formula_pure_trigger_terms(
        &mut self,
        vars: &[String],
        body: &Formula,
    ) -> Result<Vec<Vec<Term>>, EncodingError> {
        // Existing PureExpr-based trigger synthesis fallback.
        let mut pure_exprs = Vec::new();
        collect_pure_exprs(body, &mut pure_exprs);
        for expr in &pure_exprs {
            let triggers = synthesize_triggers(vars, expr);
            if !triggers.is_empty() {
                return triggers
                    .into_iter()
                    .map(|pattern| {
                        pattern
                            .into_iter()
                            .map(|trigger_expr| self.encode_pure(&trigger_expr))
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .collect();
            }
        }

        Ok(Vec::new())
    }

    /// Collect sep-logic trigger terms from a formula body.
    ///
    /// Descends through conjunction/disjunction/connectives and stops at nested
    /// quantifier boundaries to avoid capturing inner binders.
    fn collect_sep_logic_trigger_terms(
        &mut self,
        formula: &Formula,
        var: &str,
        vars: &[String],
        out: &mut Vec<Vec<Term>>,
    ) -> Result<(), EncodingError> {
        if out.len() >= TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT {
            return Ok(());
        }

        match formula {
            Formula::PointsTo {
                location, value, ..
            } => {
                if location.0 == var {
                    let loc_term = if let Some(term) = self.var_term(var) {
                        term
                    } else {
                        self.get_or_declare_var(var, Sort::Int)?
                    };
                    let in_domain = self.solver.select(self.mem_state.domain, loc_term);
                    push_single_pattern(out, in_domain);

                    if out.len() < TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT {
                        let has_perm = self.solver.select(self.mem_state.permissions, loc_term);
                        push_single_pattern(out, has_perm);
                    }
                }

                if out.len() < TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT {
                    if let Value::Expr(expr) = value {
                        if expr_mentions_any_var(expr, vars) && is_sep_trigger_candidate_expr(expr)
                        {
                            let value_term = self.encode_pure(expr)?;
                            push_single_pattern(out, value_term);
                        }
                    }
                }
            }
            Formula::MutBorrow {
                var: borrow_var,
                current,
                final_val,
                id,
            } => {
                let mentions_current = expr_mentions_any_var(current, vars);
                let mentions_final = expr_mentions_any_var(final_val, vars);
                let mentions_id = expr_mentions_any_var(id, vars);

                if borrow_var == var || mentions_current || mentions_final || mentions_id {
                    if mentions_current
                        && out.len() < TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT
                        && is_sep_trigger_candidate_expr(current)
                    {
                        let current_term = self.encode_pure(current)?;
                        push_single_pattern(out, current_term);
                    }
                    if mentions_final
                        && out.len() < TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT
                        && is_sep_trigger_candidate_expr(final_val)
                    {
                        let final_term = self.encode_pure(final_val)?;
                        push_single_pattern(out, final_term);
                    }
                    if mentions_id
                        && out.len() < TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT
                        && is_sep_trigger_candidate_expr(id)
                    {
                        let id_term = self.encode_pure(id)?;
                        push_single_pattern(out, id_term);
                    }
                }
            }
            Formula::And(l, r)
            | Formula::Or(l, r)
            | Formula::Implies(l, r)
            | Formula::SepConj(l, r)
            | Formula::MagicWand(l, r) => {
                self.collect_sep_logic_trigger_terms(l, var, vars, out)?;
                if out.len() < TRUST_WP_FORMULA_TRIGGER_PATTERN_LIMIT {
                    self.collect_sep_logic_trigger_terms(r, var, vars, out)?;
                }
            }
            // Do not descend across nested quantifier boundaries.
            Formula::Forall { .. } | Formula::Exists { .. } => {}
            Formula::True | Formula::False | Formula::Pure(_) => {}
            // Formula is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns)]
            _ => {}
        }

        Ok(())
    }

    /// Expand a Bool-sorted formula quantifier into case splits. (#1027)
    ///
    /// `∀b. φ(b)` → `φ(true) ∧ φ(false)`
    /// `∃b. φ(b)` → `φ(true) ∨ φ(false)`
    fn encode_formula_bool_expansion(
        &mut self,
        kind: QuantifierKind,
        var: &str,
        body: &Formula,
    ) -> Result<Term, EncodingError> {
        let old_binding = self.var_term(var);

        // Encode body with var = true
        let true_const = self.solver.bool_const(true);
        self.insert_var(var.to_string(), true_const);
        let body_true_result = self.encode(body);

        // Encode body with var = false (even if true-case failed, to keep
        // this method's structure simple; the error propagates below).
        let false_const = self.solver.bool_const(false);
        self.insert_var(var.to_string(), false_const);
        let body_false_result = self.encode(body);

        // Restore original binding — always, even on error, to avoid
        // leaving stale bindings in the encoder state.
        self.restore_var(var, old_binding);

        // Now propagate any encoding errors.
        let body_true = body_true_result?;
        let body_false = body_false_result?;

        Ok(match kind {
            QuantifierKind::Forall => self.solver.and(body_true, body_false),
            QuantifierKind::Exists => self.solver.or(body_true, body_false),
        })
    }
}

/// Recursively collect `Pure(expr)` sub-expressions from a formula tree for
/// the PureExpr synthesis fallback.
///
/// Descends through And, Or, Implies, SepConj, MagicWand, and quantifier
/// bodies. Stops at PointsTo, MutBorrow, True, False (no Pure content).
fn collect_pure_exprs<'a>(formula: &'a Formula, out: &mut Vec<&'a PureExpr>) {
    match formula {
        Formula::Pure(expr) => out.push(expr),
        Formula::And(l, r)
        | Formula::Or(l, r)
        | Formula::Implies(l, r)
        | Formula::SepConj(l, r)
        | Formula::MagicWand(l, r) => {
            collect_pure_exprs(l, out);
            collect_pure_exprs(r, out);
        }
        // Don't descend into nested quantifier bodies — triggers should
        // reference variables from the current quantifier, not inner ones.
        Formula::Forall { .. } | Formula::Exists { .. } => {}
        Formula::True | Formula::False | Formula::PointsTo { .. } | Formula::MutBorrow { .. } => {}
        // Formula is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

/// Check whether a formula is a reflexive equality wrapped in Pure,
/// optionally behind implications and conjunctions.
fn is_formula_reflexive_equality(formula: &Formula) -> bool {
    use trust_wp_core::formula::BinOp;
    match formula {
        Formula::Pure(expr) => match expr {
            PureExpr::BinOp(lhs, BinOp::Eq, rhs) => lhs == rhs,
            PureExpr::BinOp(_, BinOp::Implies, consequent) => {
                is_formula_reflexive_equality(&Formula::Pure(consequent.as_ref().clone()))
            }
            PureExpr::BinOp(left, BinOp::And, right) => {
                is_formula_reflexive_equality(&Formula::Pure(left.as_ref().clone()))
                    && is_formula_reflexive_equality(&Formula::Pure(right.as_ref().clone()))
            }
            _ => false,
        },
        Formula::And(l, r) => is_formula_reflexive_equality(l) && is_formula_reflexive_equality(r),
        Formula::Implies(_, consequent) => is_formula_reflexive_equality(consequent),
        Formula::True => true,
        _ => false,
    }
}

fn is_sep_trigger_candidate_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall { .. } | PureExpr::LogicFnCall { .. } => true,
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => is_sep_trigger_candidate_expr(inner),
        _ => false,
    }
}

/// Collect all bound variable names from a chain of nested same-kind formula
/// quantifiers.
///
/// Used to synthesize triggers from the innermost body of nested formula
/// quantifiers like `forall<i> forall<x> ...` without changing the encoded
/// quantifier structure.
fn collect_nested_formula_quantifier_vars<'a>(
    kind: QuantifierKind,
    first_var: &str,
    outer_body: &'a Formula,
) -> (Vec<String>, &'a Formula) {
    let mut vars = vec![first_var.to_string()];
    let mut body = outer_body;
    loop {
        match body {
            Formula::Forall {
                var,
                body: inner,
                triggers,
                ..
            } if kind == QuantifierKind::Forall && triggers.is_empty() => {
                vars.push(var.clone());
                body = inner;
            }
            Formula::Exists {
                var,
                body: inner,
                triggers,
                ..
            } if kind == QuantifierKind::Exists && triggers.is_empty() => {
                vars.push(var.clone());
                body = inner;
            }
            _ => break,
        }
    }
    (vars, body)
}
