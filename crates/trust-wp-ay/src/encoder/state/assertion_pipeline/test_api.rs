// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Term;

use super::AssertionPipelineState;

impl AssertionPipelineState {
    /// Set assertion_revision and quantified_pairs_revision for test setup.
    ///
    /// The common test pattern `assertion_revision = 1; quantified_pairs_revision = 0;`
    /// forces the semantic-overlap recheck path in `check_sat`.
    #[cfg(test)]
    pub(crate) fn prime_recheck_for_test(&mut self) {
        self.assertion_revision = 1;
        self.quantified_pairs_revision = 0;
    }

    /// Set assertion_revision directly (test setup only).
    #[cfg(test)]
    pub(crate) fn set_assertion_revision_for_test(&mut self, rev: u64) {
        self.assertion_revision = rev;
    }

    /// Set quantified_pairs_revision directly (test setup only).
    #[cfg(test)]
    pub(crate) fn set_quantified_pairs_revision_for_test(&mut self, rev: u64) {
        self.quantified_pairs_revision = rev;
    }

    /// Set solver panic reason directly (test setup only).
    #[cfg(test)]
    pub(crate) fn set_solver_panic_reason_for_test(&mut self, reason: Option<String>) {
        self.solver_panic_reason = reason;
    }

    /// Number of pending pure equality terms (test inspection only).
    #[cfg(test)]
    pub(crate) fn pending_pure_equalities_len(&self) -> usize {
        self.pending_pure_equality_terms.len()
    }

    /// Read the current assertion revision (test inspection only).
    #[cfg(test)]
    pub(crate) fn assertion_revision(&self) -> u64 {
        self.assertion_revision
    }

    /// Read the current quantified pairs revision (test inspection only).
    #[cfg(test)]
    pub(crate) fn quantified_pairs_revision(&self) -> u64 {
        self.quantified_pairs_revision
    }

    /// Number of asserted cross-footprint `!=` pairs (test inspection only).
    #[cfg(test)]
    pub(crate) fn asserted_neq_pairs_len(&self) -> usize {
        self.asserted_quantified_neq_pairs.len()
    }

    /// Check if no cross-footprint `!=` pairs have been asserted yet (test only).
    #[cfg(test)]
    pub(crate) fn asserted_neq_pairs_is_empty(&self) -> bool {
        self.asserted_quantified_neq_pairs.is_empty()
    }

    /// Number of pending side-effect assertions (test inspection only).
    #[cfg(test)]
    pub(crate) fn pending_assertions_len(&self) -> usize {
        self.pending_assertions.len()
    }

    /// Check if pending assertions is empty (test inspection only).
    #[cfg(test)]
    pub(crate) fn pending_assertions_is_empty(&self) -> bool {
        self.pending_assertions.is_empty()
    }

    /// Clear pending assertions directly (test setup only).
    #[cfg(test)]
    pub(crate) fn clear_pending_assertions_for_test(&mut self) {
        self.pending_assertions.clear();
    }

    /// Borrow pending disjoint constraints as a slice (test inspection only).
    #[cfg(test)]
    pub(crate) fn pending_disjoint_constraints(&self) -> &[(Vec<Term>, Vec<Term>)] {
        &self.pending_quantified_disjoint_constraints
    }

    /// Clear pending disjoint constraints directly (test setup only).
    #[cfg(test)]
    pub(crate) fn clear_pending_disjoint_constraints_for_test(&mut self) {
        self.pending_quantified_disjoint_constraints.clear();
    }

    /// Push a constraint set directly into active constraints (test setup only).
    #[cfg(test)]
    pub(crate) fn push_active_disjoint_constraint_for_test(
        &mut self,
        left: Vec<Term>,
        right: Vec<Term>,
    ) {
        self.quantified_disjoint_constraints.push((left, right));
    }

    /// Insert a term into the disjoint terms index (test setup only).
    #[cfg(test)]
    pub(crate) fn insert_disjoint_term_for_test(&mut self, term: Term) {
        self.quantified_disjoint_terms.insert(term);
    }

    /// Number of active disjoint constraint sets (test inspection only).
    #[cfg(test)]
    pub(crate) fn active_disjoint_constraints_len(&self) -> usize {
        self.quantified_disjoint_constraints.len()
    }

    /// Check if active disjoint constraints is empty (test inspection only).
    #[cfg(test)]
    pub(crate) fn active_disjoint_constraints_is_empty(&self) -> bool {
        self.quantified_disjoint_constraints.is_empty()
    }

    /// Number of terms in the disjoint terms index (test inspection only).
    #[cfg(test)]
    pub(crate) fn disjoint_terms_len(&self) -> usize {
        self.quantified_disjoint_terms.len()
    }

    /// Check if the disjoint terms index is empty (test inspection only).
    #[cfg(test)]
    pub(crate) fn disjoint_terms_is_empty(&self) -> bool {
        self.quantified_disjoint_terms.is_empty()
    }
}
