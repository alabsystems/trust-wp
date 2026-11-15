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

#[cfg(any(test, feature = "sep-logic"))]
mod formula_quantifier;
pub(crate) mod pure_quantifier;

use std::sync::Arc;

use ay_dpll::api::{SolverError, Term};
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::{final_collapse_guard::sort_holds_no_borrow, AYEncoder};
use crate::error::EncodingError;

/// Whether `expr` is one or more dereferences of a variable annotated as a
/// shared reference to a sort that holds no borrow (`&i32`, `&&bool`): every
/// value reached through it is part of that referent, so its resolve is
/// `true`. Nothing else is: the driver erases a `Box`, `Ghost` or `Snapshot`
/// layer from a sort, so `b: Box<&mut i32>` and `s: Snapshot<&mut i32>` are
/// annotated `&mut i32` like `x: &mut i32` (and a value-model snapshot `Int`),
/// and `*b` and `*s` are the borrow where `*x` is its integer.
fn dereferences_a_shared_value(expr: &PureExpr) -> bool {
    let PureExpr::Deref(first) = expr else {
        return false;
    };
    let mut base = first.as_ref();
    while let PureExpr::Deref(next) = base {
        base = next.as_ref();
    }
    matches!(base, PureExpr::Var(_, Some(sort @ ExprSort::Ref(_))) if sort_holds_no_borrow(sort))
}

impl AYEncoder {
    /// Encode `resolve(e)`: Creusot's resolve of `e` at `e`'s own type, `true`
    /// of a value holding no borrow and `*e == ^e` of a borrow.
    ///
    /// A value whose sort certainly holds no borrow
    /// ([`sort_holds_no_borrow`], asked of the sort's own shape) resolves
    /// trivially (#2683). That reading is taken of the variable itself,
    /// annotated, with no final value in the lane (D-126). An unannotated
    /// variable is not known to be a value (the closure postcondition `|r:
    /// &mut i32| resolve(r)` reads the returned borrow as an unannotated
    /// `result`); a `Datatype`, a value-model sort, a tuple or a type parameter
    /// may hold a borrow its sort does not show (`Vec<&mut i32>`, a struct
    /// with an `Option<&mut i32>` field declared at `Int`).
    ///
    /// Any other variable is the `*x == ^x` it denotes, through the lane's
    /// own final reading; a variable the lane names no final value of (a
    /// by-value parameter holding a borrow, a snapshot, a value bound by a
    /// `let`, a borrow at a loop head) has none to read and is refused,
    /// fail-closed. A quantifier's binder is read through the wrapper's binder
    /// arm, which refuses the final value of a binder not certified to hold no
    /// borrow.
    ///
    /// Every other operand is a value held through another or computed from
    /// one, and its resolve is its OWN: `true` of the integer `*x` of `x: &mut
    /// i32`, the inner borrow's `**x == ^*x` of `*x` of `x: &mut &mut i32`, the
    /// inner borrow's of a field `x.m` of `x: &mut M` that is one, `true` of
    /// `x@` and of `Some(*x)`. The #508 strip read `resolve(*x)` as the
    /// OUTER borrow's `*x == ^x`, and a projection, view or constructor as
    /// `*e == ^e` distributed into it (`(*x).f == (^x).f`, `(*x)@ ==
    /// (^x)@`): stronger than `true` of a value, so `!resolve(*x)` of a write
    /// verified, and blind to the borrow the operand may be, so
    /// `resolve(*x)` of an untouched `x: &mut &mut i32` and `resolve(x.m)` of
    /// an untouched `x: &mut M` holding the caller's borrow verified (D-127).
    /// A chain of dereferences of a shared reference to a value is `true`
    /// ([`dereferences_a_shared_value`]). Everything else is refused: `*x` of
    /// `x: &mut i32` too, whose sort cannot tell it from `*b` of `b: Box<&mut
    /// i32>`, and a literal, since at a call a borrow's argument may reach here
    /// as the constant its referent held (`resolve(3)`) and an existential
    /// witness probe substitutes one for a binder.
    pub(super) fn encode_resolve(
        &mut self,
        arg: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        use super::sort_context::{apply_name_prefix, DerivedKind};

        let PureExpr::Var(name, sort) = arg else {
            return if dereferences_a_shared_value(arg) {
                Ok(self.solver.bool_const(true))
            } else {
                Err(self.refuse_resolve_of_a_held_value(arg))
            };
        };
        let final_name = DerivedKind::Final.format_name(&apply_name_prefix(name, prefix));
        let lane_reads_a_final = self.var_term(&final_name).is_some();
        if sort.as_ref().is_some_and(sort_holds_no_borrow) && !lane_reads_a_final {
            return Ok(self.solver.bool_const(true));
        }
        if !lane_reads_a_final && !self.is_quantifier_bound(name) {
            return Err(self.refuse_resolve_without_a_final(name, sort.as_ref()));
        }
        // Inferring the variable's sort declares it first, and the naming path
        // reads a declared base's datatype sort for `x_current`/`x_final` (#967).
        let _ = self.infer_expr_sort_with_context(arg, prefix);
        let current_term =
            self.encode_pure_impl(&PureExpr::Deref(Arc::new(arg.clone())), prefix)?;
        let final_term = self.encode_pure_impl(&PureExpr::Final(Arc::new(arg.clone())), prefix)?;
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
