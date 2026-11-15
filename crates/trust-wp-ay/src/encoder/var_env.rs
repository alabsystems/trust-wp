// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Variable-environment ownership for `AYEncoder`.
//!
//! This shell state groups declared variable terms, tracked sorts, and
//! unit-sorted markers behind a single ownership boundary. `AYEncoder` keeps
//! the public helper surface, while `VarEnv` owns the underlying maps/sets.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::PureExpr;

use super::AYEncoder;

#[derive(Default)]
pub(in crate::encoder) struct VarEnv {
    vars: HashMap<String, Term>,
    /// Source-level expression aliases for variables rebound to encoded body
    /// terms. This lets later expression-level lowering, such as direct-view
    /// field beta, see the constructor shape behind `result`.
    expr_aliases: HashMap<String, PureExpr>,
    /// Declared variable sorts tracked separately from `vars` because some
    /// temporary quantifier/let bindings bypass `get_or_declare_var`. (#1584)
    var_sorts: HashMap<String, Sort>,
    /// Variables known to have `ExprSort::Unit` annotation from MIR type info.
    /// Used by `assert_tuple_axioms()` to emit singleton constraints. (#1271)
    unit_sorted_vars: HashSet<String>,
    /// Declared solver constants that are authenticated equal to an active
    /// source binding which has been rebound to a compound term.
    ///
    /// Compound terms have no model identity of their own.  Keeping the
    /// equality witness separately lets counterexample extraction recover the
    /// active value without falling back to an unconstrained stale declaration.
    counterexample_witnesses: HashMap<String, Term>,
    /// Solver constants a phantom sort upgrade left behind, each with the
    /// source name it was bound to. Facts asserted before the upgrade still
    /// constrain the old constant while every later read is of the new one,
    /// and nothing relates the two, so a model may give them values no single
    /// execution has. Read by the refutation gate only
    /// (`AYEncoder::split_source_read_by_assertions`).
    split_sources: Vec<(String, Term)>,
    /// Monotonic discriminator for source-derived solver identities.
    ///
    /// A source binding can be repaired more than once as stronger sort
    /// evidence arrives. Reusing a role-only identity (for example,
    /// `upgrade`) would either collide at a different sort or revive stale
    /// constraints if the sort later cycles back. Every derived declaration
    /// therefore receives a fresh, encoder-local serial.
    next_source_derived_id: u64,
}

impl VarEnv {
    pub(in crate::encoder) fn new() -> Self {
        Self::default()
    }

    pub(in crate::encoder) fn rebind_var(&mut self, name: &str, term: Term, sort: Sort) {
        self.vars.insert(name.to_string(), term);
        self.var_sorts.insert(name.to_string(), sort);
        self.expr_aliases.remove(name);
        self.counterexample_witnesses.remove(name);
    }

    pub(in crate::encoder) fn var_names(&self) -> Vec<String> {
        self.vars.keys().cloned().collect()
    }

    pub(in crate::encoder) fn var_count(&self) -> usize {
        self.vars.len()
    }

    pub(in crate::encoder) fn active_vars(&self) -> impl Iterator<Item = (&str, Term)> + '_ {
        self.vars.iter().map(|(name, term)| (name.as_str(), *term))
    }

    pub(in crate::encoder) fn counterexample_witness(&self, name: &str) -> Option<Term> {
        self.counterexample_witnesses.get(name).copied()
    }

    pub(in crate::encoder) fn record_counterexample_witness(&mut self, name: &str, term: Term) {
        self.counterexample_witnesses.insert(name.to_string(), term);
    }

    pub(in crate::encoder) fn record_split_source(&mut self, name: &str, abandoned: Term) {
        self.split_sources.push((name.to_string(), abandoned));
    }

    pub(in crate::encoder) fn split_sources(&self) -> &[(String, Term)] {
        &self.split_sources
    }

    pub(in crate::encoder) fn next_source_derived_id(&mut self) -> u64 {
        let id = self.next_source_derived_id;
        self.next_source_derived_id = self
            .next_source_derived_id
            .checked_add(1)
            .expect("source-derived identity counter exhausted");
        id
    }

    pub(in crate::encoder) fn var_term(&self, name: &str) -> Option<Term> {
        self.vars.get(name).copied()
    }

    #[cfg(test)]
    pub(in crate::encoder) fn vars_for_test(&self) -> &HashMap<String, Term> {
        &self.vars
    }

    #[cfg(test)]
    pub(in crate::encoder) fn vars_mut_for_test(&mut self) -> &mut HashMap<String, Term> {
        &mut self.vars
    }

    pub(in crate::encoder) fn var_sort(&self, name: &str) -> Option<&Sort> {
        self.var_sorts.get(name)
    }

    pub(in crate::encoder) fn record_expr_alias(&mut self, name: String, expr: PureExpr) {
        self.expr_aliases.insert(name, expr);
    }

    pub(in crate::encoder) fn expr_alias(&self, name: &str) -> Option<&PureExpr> {
        self.expr_aliases.get(name)
    }

    #[cfg(test)]
    pub(in crate::encoder) fn var_sorts_for_test(&self) -> &HashMap<String, Sort> {
        &self.var_sorts
    }

    #[cfg(test)]
    pub(in crate::encoder) fn var_sorts_mut_for_test(&mut self) -> &mut HashMap<String, Sort> {
        &mut self.var_sorts
    }

    pub(in crate::encoder) fn has_var(&self, name: &str) -> bool {
        self.vars.contains_key(name)
    }

    pub(in crate::encoder) fn insert_var(&mut self, name: String, term: Term) -> Option<Term> {
        self.vars.insert(name, term)
    }

    pub(in crate::encoder) fn remove_var(&mut self, name: &str) -> Option<Term> {
        self.counterexample_witnesses.remove(name);
        self.vars.remove(name)
    }

    pub(in crate::encoder) fn restore_var(&mut self, name: &str, old: Option<Term>) {
        match old {
            Some(term) => {
                self.insert_var(name.to_string(), term);
            }
            None => {
                self.remove_var(name);
            }
        }
    }

    pub(in crate::encoder) fn insert_var_sort(&mut self, name: String, sort: Sort) -> Option<Sort> {
        self.var_sorts.insert(name, sort)
    }

    pub(in crate::encoder) fn remove_var_sort(&mut self, name: &str) -> Option<Sort> {
        self.var_sorts.remove(name)
    }

    pub(in crate::encoder) fn restore_var_sort(&mut self, name: &str, old: Option<Sort>) {
        match old {
            Some(sort) => {
                self.insert_var_sort(name.to_string(), sort);
            }
            None => {
                self.remove_var_sort(name);
            }
        }
    }

    pub(in crate::encoder) fn has_var_sort(&self, name: &str) -> bool {
        self.var_sorts.contains_key(name)
    }

    pub(in crate::encoder) fn mark_unit_sorted_var(&mut self, name: String) {
        self.unit_sorted_vars.insert(name);
    }

    pub(in crate::encoder) fn has_unit_sorted_vars(&self) -> bool {
        !self.unit_sorted_vars.is_empty()
    }

    pub(in crate::encoder) fn unit_sorted_var_names(&self) -> Vec<String> {
        self.unit_sorted_vars.iter().cloned().collect()
    }

    #[cfg(test)]
    pub(in crate::encoder) fn unit_sorted_vars_for_test(&self) -> &HashSet<String> {
        &self.unit_sorted_vars
    }

    #[cfg(test)]
    pub(in crate::encoder) fn unit_sorted_vars_mut_for_test(&mut self) -> &mut HashSet<String> {
        &mut self.unit_sorted_vars
    }
}

impl AYEncoder {
    /// Rebind an existing variable name to a new term without declaring a new
    /// SMT constant. Updates both tracked terms and sorts atomically. (#1567)
    ///
    /// Keep this shell helper with the rest of the variable-environment API so
    /// production modules do not reach through `self.var_env` directly. (#1584)
    ///
    /// Ground field-range assumptions ride along with every datatype-sorted
    /// binding (#2097): asserted here, at the single chokepoint all production
    /// bindings flow through, instead of via the retired quantified
    /// per-datatype axiom (see `match_enc/field_range.rs` for why the
    /// datatype-binder `forall` had to go).
    pub(crate) fn rebind_var(&mut self, name: &str, term: Term, sort: Sort) {
        self.assert_field_range_assumptions_for_binding(term, &sort);
        self.var_env.rebind_var(name, term, sort);
    }

    /// Rebind a source after the caller has asserted `prior == term`, retaining
    /// a declared model identity across repeated compound-term rebindings.
    ///
    /// If `prior` is already compound, its previously authenticated witness is
    /// transitively authenticated by the new equality.  No witness is invented
    /// when neither source is a declared solver constant.
    pub(crate) fn rebind_var_with_authenticated_witness(
        &mut self,
        name: &str,
        term: Term,
        sort: Sort,
        prior: Term,
    ) {
        let witness = if self.solver.var_name(prior).is_some() {
            Some(prior)
        } else {
            self.var_env.counterexample_witness(name)
        };
        self.rebind_var(name, term, sort);
        if let Some(witness) = witness {
            self.record_counterexample_witness(name, witness);
        }
    }

    pub(crate) fn record_var_expr_alias(&mut self, name: &str, expr: PureExpr) {
        self.var_env.record_expr_alias(name.to_string(), expr);
    }

    pub(crate) fn var_expr_alias(&self, name: &str) -> Option<&PureExpr> {
        self.var_env.expr_alias(name)
    }

    /// Hidden bench/test helper for seeding a concrete variable binding.
    #[cfg(feature = "internal-bench-api")]
    #[doc(hidden)]
    pub fn bind_const_for_internal_bench(&mut self, name: &str, sort: Sort) {
        let term = self.declare_derived_source_var(name, "internal_bench", sort.clone());
        self.rebind_var(name, term, sort);
    }

    /// Return declared variable names (useful for debug logging).
    pub(crate) fn var_names(&self) -> Vec<String> {
        self.var_env.var_names()
    }

    /// Map each active solver declaration identity back to its source name.
    ///
    /// Sort upgrades deliberately leave old constants in the solver. Only the
    /// current shell binding belongs in a source-level counterexample; stale
    /// base/upgrade terms must remain hidden as encoding internals.
    pub(crate) fn active_source_projection(
        &self,
    ) -> (HashMap<String, Vec<String>>, HashSet<String>) {
        let mut active: HashMap<String, Vec<String>> = HashMap::new();
        let mut source_names = HashSet::new();
        for (source, term) in self.var_env.active_vars() {
            source_names.insert(source.to_string());
            let identity_term = self
                .solver
                .var_name(term)
                .map(|_| term)
                .or_else(|| self.var_env.counterexample_witness(source));
            let Some(identity) = identity_term.and_then(|term| self.solver.var_name(term)) else {
                continue;
            };
            active.entry(identity).or_default().push(source.to_string());
        }
        for sources in active.values_mut() {
            sources.sort();
            sources.dedup();
        }
        (active, source_names)
    }

    /// Retain a declared model identity after rebinding a source variable to a
    /// compound term.  Callers must first assert that `witness` equals the new
    /// active term; unauthenticated aliases deliberately remain invisible.
    pub(crate) fn record_counterexample_witness(&mut self, name: &str, witness: Term) {
        debug_assert!(self.solver.var_name(witness).is_some());
        self.var_env.record_counterexample_witness(name, witness);
    }

    /// Return the number of active variable bindings in the encoder shell.
    pub(super) fn var_count(&self) -> usize {
        self.var_env.var_count()
    }

    /// Get the term for a declared variable, if it exists.
    ///
    /// This is the shell-level accessor for `verify/*` and other subsystems
    /// that only need read access to the variable environment. (#1584)
    pub(crate) fn var_term(&self, name: &str) -> Option<Term> {
        self.var_env.var_term(name)
    }

    /// Test-only read access to the variable environment for crate-root unit
    /// tests that still inspect the shell state directly. (#1584)
    #[cfg(test)]
    pub(crate) fn vars_for_test(&self) -> &HashMap<String, Term> {
        self.var_env.vars_for_test()
    }

    /// Test-only mutable access to the variable environment for focused unit
    /// tests that seed bindings directly. (#1584)
    #[cfg(test)]
    pub(crate) fn vars_mut_for_test(&mut self) -> &mut HashMap<String, Term> {
        self.var_env.vars_mut_for_test()
    }

    /// Get the sort of a declared variable, if it exists.
    pub(crate) fn var_sort(&self, name: &str) -> Option<&Sort> {
        self.var_env.var_sort(name)
    }

    /// Test-only read access to tracked variable sorts for crate-root unit
    /// tests that validate sort registration details. (#1584)
    #[cfg(test)]
    pub(crate) fn var_sorts_for_test(&self) -> &HashMap<String, Sort> {
        self.var_env.var_sorts_for_test()
    }

    /// Test-only mutable access to tracked variable sorts for focused unit
    /// tests that seed sort metadata directly. (#1584)
    #[cfg(test)]
    pub(crate) fn var_sorts_mut_for_test(&mut self) -> &mut HashMap<String, Sort> {
        self.var_env.var_sorts_mut_for_test()
    }

    /// Check whether a variable has been declared.
    pub(super) fn has_var(&self, name: &str) -> bool {
        self.var_env.has_var(name)
    }

    /// Insert (or overwrite) a variable binding. Returns the previous term, if any.
    ///
    /// Encoder-internal helper — callers that also need sort tracking should use
    /// `rebind_var` or `get_or_declare_var` instead. (#1584)
    pub(super) fn insert_var(&mut self, name: String, term: Term) -> Option<Term> {
        self.var_env.insert_var(name, term)
    }

    /// Remove a variable binding. Returns the previous term, if any.
    #[cfg(test)]
    pub(crate) fn remove_var(&mut self, name: &str) -> Option<Term> {
        self.var_env.remove_var(name)
    }

    /// Restore a variable binding to its previous state.
    ///
    /// This is the save/restore epilogue for the quantifier binding pattern:
    /// ```text
    /// let old = self.insert_var(name.clone(), new_term);
    /// // ... encode ...
    /// self.restore_var(&name, old);
    /// ```
    pub(super) fn restore_var(&mut self, name: &str, old: Option<Term>) {
        self.var_env.restore_var(name, old);
    }

    /// Insert (or overwrite) a variable sort. Returns the previous sort, if any.
    pub(super) fn insert_var_sort(&mut self, name: String, sort: Sort) -> Option<Sort> {
        self.var_env.insert_var_sort(name, sort)
    }

    /// Remove a variable sort entry. Returns the previous sort, if any.
    pub(super) fn remove_var_sort(&mut self, name: &str) -> Option<Sort> {
        self.var_env.remove_var_sort(name)
    }

    /// Restore a variable sort to its previous state.
    pub(super) fn restore_var_sort(&mut self, name: &str, old: Option<Sort>) {
        self.var_env.restore_var_sort(name, old);
    }

    /// Check whether a variable sort has been recorded.
    pub(super) fn has_var_sort(&self, name: &str) -> bool {
        self.var_env.has_var_sort(name)
    }

    /// Record a variable as unit-sorted. (#1271)
    pub(super) fn mark_unit_sorted_var(&mut self, name: String) {
        self.var_env.mark_unit_sorted_var(name);
    }

    /// Check whether any unit-sorted variables are currently tracked.
    pub(super) fn has_unit_sorted_vars(&self) -> bool {
        self.var_env.has_unit_sorted_vars()
    }

    /// Return the names of all tracked unit-sorted variables.
    pub(super) fn unit_sorted_var_names(&self) -> Vec<String> {
        self.var_env.unit_sorted_var_names()
    }

    /// Test-only read access to the tracked unit-sorted variables set for
    /// crate-root unit tests that inspect tuple singleton seeding. (#1584)
    #[cfg(test)]
    pub(crate) fn unit_sorted_vars_for_test(&self) -> &HashSet<String> {
        self.var_env.unit_sorted_vars_for_test()
    }

    /// Test-only mutable access to the tracked unit-sorted variables set for
    /// focused unit tests that seed singleton candidates directly. (#1584)
    #[cfg(test)]
    pub(crate) fn unit_sorted_vars_mut_for_test(&mut self) -> &mut HashSet<String> {
        self.var_env.unit_sorted_vars_mut_for_test()
    }
}
