// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use ay_dpll::api::Term;

mod diagnostics;
mod disjoint;
mod labels;
#[cfg(test)]
mod test_api;

pub(crate) use labels::AssertionPhase;

/// Side-effect assertion state accumulated during encoding.
///
/// All fields are private with accessor methods (#1584).
pub(crate) struct AssertionPipelineState {
    /// Side-effect assertions accumulated during encoding.
    ///
    /// Quantified disjointness foralls from `encode_quantified_disjointness`
    /// are stored here. `assert_term` flushes them differently depending on
    /// whether the current assertion contains quantified-term equalities:
    /// - relevant quantified-term equality present: assert forall at top-level
    /// - otherwise: embed forall into the same conjunction for SAT performance
    ///
    /// Private; access through `push_pending_assertion()`,
    /// `drain_pending_assertions()`, `has_pending_assertions()`. (#1584)
    pending_assertions: Vec<Term>,
    /// Pending cross-footprint constraint sets from quantified `sep_conj` nodes
    /// that have been encoded but not yet asserted.
    ///
    /// Each entry is `(left_terms, right_terms)` — the full constraint set from
    /// one `encode_quantified_disjointness` call, stored as O(L+R) instead of
    /// the O(L*R) Cartesian product (#668).
    ///
    /// Private; access through `has_pending_disjoint_constraints()`,
    /// `activate_pending_constraints()`, `push_pending_disjoint_constraint()`.
    /// Test-only: `pending_disjoint_constraints()`,
    /// `clear_pending_disjoint_constraints_for_test()`. (#1584)
    pending_quantified_disjoint_constraints: Vec<(Vec<Term>, Vec<Term>)>,
    /// Pure equality terms (`==`) seen since the last `assert_term`.
    ///
    /// Used to decide whether the next SAT check should run the quantified
    /// semantic-overlap recheck. Only equalities that mention quantified-pair
    /// location terms trigger recheck (#625).
    ///
    /// Private; access through `push_pending_pure_equality()`,
    /// `clear_pending_pure_equalities()`, `has_pending_pure_equalities()`,
    /// `pending_pure_equalities()`. (#1584)
    pending_pure_equality_terms: Vec<(Term, Term)>,
    /// Cross-footprint constraint sets for quantified `sep_conj` nodes that
    /// are active in the solver.
    ///
    /// Stored as `(left_terms, right_terms)` constraint sets — O(n) storage
    /// instead of O(n²) explicit pairs (#668).
    ///
    /// Private; access through `has_active_disjoint_constraints()`,
    /// `active_disjoint_constraints()`. Test-only:
    /// `push_active_disjoint_constraint_for_test()`. (#1584)
    quantified_disjoint_constraints: Vec<(Vec<Term>, Vec<Term>)>,
    /// Terms that participate in active quantified disjointness pairs.
    ///
    /// Private; access through `contains_disjoint_term()`. Test-only:
    /// `insert_disjoint_term_for_test()`, `disjoint_terms_len()`,
    /// `disjoint_terms_is_empty()`. (#1584)
    quantified_disjoint_terms: HashSet<Term>,
    /// Tracks which cross-footprint pairs already have explicit `!=` assertions
    /// materialized after SAT-model rechecks.
    ///
    /// Private; access through `has_asserted_neq_pair()`,
    /// `insert_asserted_neq_pair()`. (#1584)
    asserted_quantified_neq_pairs: HashSet<(Term, Term)>,
    /// Monotonic count of asserted top-level terms.
    ///
    /// Private; access through `increment_revision()`, `assertion_revision()`,
    /// `needs_disjoint_recheck()`, `sync_pairs_revision()`. (#1584)
    assertion_revision: u64,
    /// Whether an assertion term was produced via encoder APIs since the last
    /// `assert_term` call.
    ///
    /// Used to avoid conservative raw-assertion rechecks for normal encoded
    /// formula assertions while still handling direct solver assertions in tests.
    ///
    /// Private; access through `mark_encoded()`, `clear_encoded_mark()`,
    /// `was_encoded_since_assert()`. (#1584)
    saw_encoded_term_since_assert: bool,
    /// Revision when quantified disjointness pairs were last activated.
    ///
    /// `check_sat` only runs semantic-overlap rechecks when a newer assertion
    /// has been added since this revision.
    ///
    /// Private; access through `quantified_pairs_revision()`,
    /// `sync_pairs_revision()`, `update_pairs_revision()`. (#1584)
    quantified_pairs_revision: u64,
    /// Panic reason if any solver assertion operation panicked.
    ///
    /// Once set, SAT queries return `Unknown` so verification cannot
    /// accidentally continue after dropping an assertion. Stores the
    /// first panic message for diagnostic surfacing (#1009).
    ///
    /// Private; access through `record_solver_panic()`, `is_panicked()`,
    /// `solver_panic_reason()`. First-write-wins semantics enforced by
    /// `record_solver_panic()`. (#1584)
    solver_panic_reason: Option<String>,
    /// Current assertion family for named production assertions. (#2414)
    current_phase: AssertionPhase,
    /// Monotonic suffix for named assertions.
    named_assertion_counter: u64,
    /// Label to attach to the next `assert_solver_term` call via
    /// `try_assert_named`. Set by the verification tail before asserting
    /// the negated postcondition so the unsat core can identify whether
    /// the negated goal participated in the proof. (#2414)
    ///
    /// Consumed (taken) by `assert_solver_term` on the next call.
    next_assertion_label: Option<String>,
    /// The assertion label used for the most recent negated-goal assertion.
    /// Stored so that `check_vacuity` can look for this label in the
    /// unsat core after an UNSAT result. (#2414)
    negated_goal_label: Option<String>,
    /// Solver state snapshot for a SAT result at the current top-level
    /// assertion revision. Used to avoid repeating an identical incremental
    /// SAT query when no assertions changed between `check_sat` calls.
    last_sat_solve_revision: Option<u64>,
    last_sat_solver_assertion_count: Option<usize>,
}

impl AssertionPipelineState {
    pub(crate) fn new() -> Self {
        Self {
            pending_assertions: Vec::new(),
            pending_quantified_disjoint_constraints: Vec::new(),
            pending_pure_equality_terms: Vec::new(),
            quantified_disjoint_constraints: Vec::new(),
            quantified_disjoint_terms: HashSet::new(),
            asserted_quantified_neq_pairs: HashSet::new(),
            assertion_revision: 0,
            saw_encoded_term_since_assert: false,
            quantified_pairs_revision: 0,
            solver_panic_reason: None,
            current_phase: AssertionPhase::Other,
            named_assertion_counter: 0,
            next_assertion_label: None,
            negated_goal_label: None,
            last_sat_solve_revision: None,
            last_sat_solver_assertion_count: None,
        }
    }
}
