// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use ay_dpll::api::Term;

use super::AssertionPipelineState;

impl AssertionPipelineState {
    /// Push a side-effect assertion for later flushing by `assert_term`.
    #[cfg(any(test, feature = "sep-logic"))]
    pub(crate) fn push_pending_assertion(&mut self, term: Term) {
        self.pending_assertions.push(term);
    }

    /// Drain all pending assertions, returning them as a `Vec`.
    ///
    /// Called once per `assert_term` to flush pending foralls. Returns
    /// an owned Vec so the caller can iterate without borrowing `self`.
    pub(crate) fn drain_pending_assertions(&mut self) -> Vec<Term> {
        std::mem::take(&mut self.pending_assertions)
    }

    /// Check if any side-effect assertions are pending.
    pub(crate) fn has_pending_assertions(&self) -> bool {
        !self.pending_assertions.is_empty()
    }

    /// Push a cross-footprint constraint set to pending and eagerly register
    /// all terms in `quantified_disjoint_terms`. This ensures
    /// `mentions_quantified_term` can use O(1) HashSet lookup instead of
    /// scanning pending constraint Vecs with O(C*T) `Vec::contains`.
    #[cfg(any(test, feature = "sep-logic"))]
    pub(crate) fn push_pending_disjoint_constraint(
        &mut self,
        left_terms: Vec<Term>,
        right_terms: Vec<Term>,
    ) {
        for &t in &left_terms {
            self.quantified_disjoint_terms.insert(t);
        }
        for &t in &right_terms {
            self.quantified_disjoint_terms.insert(t);
        }
        self.pending_quantified_disjoint_constraints
            .push((left_terms, right_terms));
    }

    /// Record a pure equality (`==`) term pair seen during encoding.
    pub(crate) fn push_pending_pure_equality(&mut self, pair: (Term, Term)) {
        self.pending_pure_equality_terms.push(pair);
    }

    /// Clear all pending pure equality terms (called during `assert_term` flush).
    pub(crate) fn clear_pending_pure_equalities(&mut self) {
        self.pending_pure_equality_terms.clear();
    }

    /// Check if any pure equality terms are pending.
    pub(crate) fn has_pending_pure_equalities(&self) -> bool {
        !self.pending_pure_equality_terms.is_empty()
    }

    /// Borrow the pending pure equality terms as a slice.
    pub(crate) fn pending_pure_equalities(&self) -> &[(Term, Term)] {
        &self.pending_pure_equality_terms
    }

    /// Check if a cross-footprint `!=` pair has already been asserted.
    pub(crate) fn has_asserted_neq_pair(&self, pair: (Term, Term)) -> bool {
        self.asserted_quantified_neq_pairs.contains(&pair)
    }

    /// Record that a cross-footprint `!=` pair has been asserted.
    ///
    /// Returns `true` if the pair was newly inserted.
    pub(crate) fn insert_asserted_neq_pair(&mut self, pair: (Term, Term)) -> bool {
        self.asserted_quantified_neq_pairs.insert(pair)
    }

    /// Snapshot the quantified neq pairs dedup set.
    pub(crate) fn neq_pairs_snapshot(&self) -> HashSet<(Term, Term)> {
        self.asserted_quantified_neq_pairs.clone()
    }

    /// Restore the quantified neq pairs dedup set from a snapshot.
    pub(crate) fn restore_neq_pairs(&mut self, snapshot: HashSet<(Term, Term)>) {
        self.asserted_quantified_neq_pairs = snapshot;
    }

    /// Increment the assertion revision counter and return the new value.
    ///
    /// Called once per `assert_term` invocation. Uses `saturating_add` to
    /// prevent overflow (would require >18 quintillion assertions).
    pub(crate) fn increment_revision(&mut self) -> u64 {
        self.assertion_revision = self.assertion_revision.saturating_add(1);
        self.assertion_revision
    }

    /// Check if new assertions arrived since the last disjoint recheck.
    ///
    /// Returns `true` when `assertion_revision > quantified_pairs_revision`,
    /// meaning `check_sat` should run the semantic-overlap recheck loop.
    pub(crate) fn needs_disjoint_recheck(&self) -> bool {
        self.assertion_revision > self.quantified_pairs_revision
    }

    /// Synchronize pairs revision to current assertion revision.
    ///
    /// Called at the end of the recheck loop so subsequent `check_sat` calls
    /// skip the recheck unless new assertions arrive.
    pub(crate) fn sync_pairs_revision(&mut self) {
        self.quantified_pairs_revision = self.assertion_revision;
    }

    pub(crate) fn record_sat_solve_snapshot(&mut self, solver_assertion_count: usize) {
        self.last_sat_solve_revision = Some(self.assertion_revision);
        self.last_sat_solver_assertion_count = Some(solver_assertion_count);
    }

    pub(crate) fn clear_sat_solve_snapshot(&mut self) {
        self.last_sat_solve_revision = None;
        self.last_sat_solver_assertion_count = None;
    }

    pub(crate) fn has_current_sat_solve_snapshot(&self, solver_assertion_count: usize) -> bool {
        self.last_sat_solve_revision == Some(self.assertion_revision)
            && self.last_sat_solver_assertion_count == Some(solver_assertion_count)
    }

    /// Update pairs revision based on whether a relevant quantified equality
    /// was seen. When relevant, sets to `revision - 1` (forces recheck on
    /// next `check_sat`); otherwise sets to `revision` (skips recheck).
    pub(crate) fn update_pairs_revision(
        &mut self,
        relevant_quantified_equality: bool,
        revision: u64,
    ) {
        self.quantified_pairs_revision = if relevant_quantified_equality {
            revision.saturating_sub(1)
        } else {
            revision
        };
    }

    /// Check if any pending disjoint constraints are waiting for activation.
    pub(crate) fn has_pending_disjoint_constraints(&self) -> bool {
        !self.pending_quantified_disjoint_constraints.is_empty()
    }

    /// Activate pending disjoint constraints: drain pending into active set,
    /// register terms in the disjoint terms index, and update pairs revision.
    ///
    /// Replaces the `activate_pending_disjoint_pairs` helper in solver.rs.
    /// All field access is local to `AssertionPipelineState`. (#1584)
    pub(crate) fn activate_pending_constraints(
        &mut self,
        relevant_quantified_equality: bool,
        assertion_revision: u64,
    ) {
        let activated_pairs = !self.pending_quantified_disjoint_constraints.is_empty();
        for (left_terms, right_terms) in self.pending_quantified_disjoint_constraints.drain(..) {
            for &t in &left_terms {
                self.quantified_disjoint_terms.insert(t);
            }
            for &t in &right_terms {
                self.quantified_disjoint_terms.insert(t);
            }
            self.quantified_disjoint_constraints
                .push((left_terms, right_terms));
        }

        if activated_pairs || !self.quantified_disjoint_constraints.is_empty() {
            self.update_pairs_revision(relevant_quantified_equality, assertion_revision);
        }
    }

    /// Check if any active disjoint constraints exist.
    pub(crate) fn has_active_disjoint_constraints(&self) -> bool {
        !self.quantified_disjoint_constraints.is_empty()
    }

    /// Borrow the active disjoint constraints as a slice.
    pub(crate) fn active_disjoint_constraints(&self) -> &[(Vec<Term>, Vec<Term>)] {
        &self.quantified_disjoint_constraints
    }

    /// Check if a term participates in active quantified disjointness pairs.
    pub(crate) fn contains_disjoint_term(&self, term: Term) -> bool {
        self.quantified_disjoint_terms.contains(&term)
    }
}
