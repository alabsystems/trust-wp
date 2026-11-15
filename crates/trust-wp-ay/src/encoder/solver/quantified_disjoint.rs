// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy quantified-disjointness recheck pipeline.
//!
//! Quantified `sep_conj` encoding avoids O(L×R) upfront constraints. If the
//! solver finds a SAT model where cross-footprint terms collide, this module
//! materializes `neq` constraints only for the colliding pairs and rechecks.
//! Loops until fixpoint or a safety bound (#618, #668, #680).
//!
//! Uses value-indexed collision detection: left term model values are indexed
//! by their Display string, then each right term is checked against the index.
//! This is O(L+R) per constraint instead of O(L×R) (#668).

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{NativeReplayMetadata, SolveDetails, SolveResult, Term};
use tracing::warn;

use super::super::{replay_artifact::ReplayResultStatus, AYEncoder};
use crate::shared_types::{SolveStatisticsSnapshot, UnknownReason};

/// Outcome of checking one quantified disjoint constraint set against the model.
enum RecheckOutcome {
    /// At least one new `neq` constraint was materialized.
    NewNeq,
    /// No collisions found — constraint set is satisfied in the current model.
    NoChange,
    /// Model extraction failed (`get_value` returned `None`) or assertion
    /// panicked — caller should return `SolveResult::Unknown`.
    Abort,
}

impl AYEncoder {
    /// SAT check with lazy semantic-overlap enforcement for quantified
    /// disjointness (#618).
    ///
    /// Quantified `sep_conj` encoding avoids O(L*R) upfront constraints, but an
    /// external equality can still expose semantic overlap after assertion.
    /// If assertions changed since the last recheck (including first activation
    /// of quantified pairs) and a SAT model sets any cross-footprint pair equal, we
    /// materialize `lt != rt` only for those equal pairs and re-check.
    ///
    /// Loops until fixpoint: each recheck may reveal new cascading collisions
    /// in the updated model that the previous pass did not see (#680). The loop
    /// terminates when no new neq constraints are materialized or the result
    /// becomes Unsat, with a safety bound of 10 iterations.
    pub(super) fn check_sat_with_quantified_disjoint_recheck(&mut self) -> SolveResult {
        self.check_sat_with_quantified_disjoint_recheck_bounded(Self::MAX_RECHECK_PASSES)
    }

    /// Default safety bound for the recheck loop. In practice, convergence
    /// happens in 1-3 passes because each pass eliminates at least one collision.
    const MAX_RECHECK_PASSES: usize = 10;

    /// Inner implementation with configurable pass bound (for testing).
    pub(super) fn check_sat_with_quantified_disjoint_recheck_bounded(
        &mut self,
        max_passes: usize,
    ) -> SolveResult {
        debug_assert!(max_passes > 0, "recheck bound must be at least 1");
        // Fail closed if pending assertions were not flushed via assert_term.
        // This is a programming error but must not produce unsound Sat results.
        // The debug_assert! that was here previously panicked with a message
        // not recognized by catch_ay_panics, escaping the catch_solver_panic
        // wrapper. A runtime guard returning Unknown is strictly safer.
        if self.assertion_pipeline.has_pending_assertions()
            || self.assertion_pipeline.has_pending_disjoint_constraints()
        {
            self.assertion_pipeline
                .record_solver_panic_with(|| "unflushed pending assertions".to_string());
            return SolveResult::Unknown;
        }
        let mut result = self.solve_and_cache_details();
        if !matches!(result, SolveResult::Sat | SolveResult::Unknown)
            || !self.assertion_pipeline.has_active_disjoint_constraints()
            || !self.assertion_pipeline.needs_disjoint_recheck()
        {
            return result;
        }

        let mut exhausted_bound = false;
        for pass in 0..max_passes {
            let mut asserted_new_neq = false;

            // Build a shared value cache for all terms across all constraint
            // sets. In left-recursive SepConj chains, the left side of
            // constraint set k is a superset of set k-1, so the naive
            // per-set loop calls get_value O(N^2) times total. A shared
            // cache reduces this to O(N) get_value calls per pass (#1970).
            let Ok(value_cache) = self.build_term_value_cache() else {
                return SolveResult::Unknown;
            };

            let constraint_count = self.assertion_pipeline.active_disjoint_constraints().len();
            for idx in 0..constraint_count {
                let (left_terms, right_terms) = {
                    let (left_terms, right_terms) =
                        &self.assertion_pipeline.active_disjoint_constraints()[idx];
                    (left_terms.clone(), right_terms.clone())
                };

                match self.recheck_one_constraint_set_cached(left_terms, right_terms, &value_cache)
                {
                    RecheckOutcome::NewNeq => asserted_new_neq = true,
                    RecheckOutcome::NoChange => {}
                    RecheckOutcome::Abort => return SolveResult::Unknown,
                }
            }

            if !asserted_new_neq {
                // Fixpoint: no new collisions found in the current model.
                break;
            }

            // Recheck with the newly materialized neq constraints.
            result = self.solve_and_cache_details();
            if !matches!(result, SolveResult::Sat | SolveResult::Unknown) {
                break;
            }
            // If still Sat, loop to check for cascading collisions in the new model.

            // If this is the last pass and we're still finding collisions,
            // the loop will exit without reaching fixpoint.
            if pass == max_passes - 1 {
                exhausted_bound = true;
            }
        }

        // If the safety bound was exhausted without convergence, the SAT result
        // may violate disjointness constraints that we couldn't fully enforce.
        // Return Unknown rather than a potentially spurious Sat. (#1208)
        if exhausted_bound {
            warn!(
                max_passes,
                "quantified disjoint recheck exhausted bound without convergence — returning Unknown"
            );
            result = SolveResult::Unknown;
        }

        // Synchronize revisions so subsequent check_sat calls skip the recheck
        // unless new assertions arrive (or new quantified pairs are activated).
        //
        // Guard: do NOT sync if the result is Unknown from a solver timeout
        // during recheck (not exhausted-bound). Syncing would cause
        // retry_check_sat_on_timeout to skip the recheck on its next attempt,
        // potentially returning a spurious Sat. (#2354)
        //
        // Exhausted-bound Unknown IS safe to sync: all max_passes ran and
        // the recheck state is consistent — retrying won't help.
        if !matches!(result, SolveResult::Unknown) || exhausted_bound {
            self.assertion_pipeline.sync_pairs_revision();
        }
        result
    }

    /// Build a shared value cache for all terms across all active constraint
    /// sets. Calls `get_value` once per unique term, reducing the total from
    /// O(N^2) to O(N) for left-recursive SepConj chains where constraint set
    /// left sides overlap (#1970).
    ///
    /// Returns `Err(())` if any `get_value` call returns `None`.
    fn build_term_value_cache(&mut self) -> Result<HashMap<Term, String>, ()> {
        let mut all_terms = HashSet::new();
        for (left_terms, right_terms) in self.assertion_pipeline.active_disjoint_constraints() {
            for &t in left_terms {
                all_terms.insert(t);
            }
            for &t in right_terms {
                all_terms.insert(t);
            }
        }

        let mut cache = HashMap::with_capacity(all_terms.len());
        for term in all_terms {
            if let Some(val) = self.solver.value(term) {
                cache.insert(term, val.to_string());
            } else {
                warn!(
                    "get_value returned None for term in quantified disjoint recheck — returning Unknown"
                );
                return Err(());
            }
        }
        Ok(cache)
    }

    /// Check one constraint set for collisions using a pre-built value cache.
    ///
    /// This is the cached variant of the collision check — instead of calling
    /// `get_value` per term, it reads from the shared `value_cache` built by
    /// `build_term_value_cache`. The cache eliminates redundant solver queries
    /// for terms shared across constraint sets (#1970).
    ///
    /// If a term is missing from the cache (should not happen if the cache was
    /// built correctly), returns `Abort`. (#1780)
    fn recheck_one_constraint_set_cached(
        &mut self,
        left_terms: Vec<Term>,
        right_terms: Vec<Term>,
        value_cache: &HashMap<Term, String>,
    ) -> RecheckOutcome {
        let mut left_by_value: HashMap<&str, Vec<Term>> = HashMap::new();
        for lt in left_terms {
            if let Some(val) = value_cache.get(&lt) {
                left_by_value.entry(val.as_str()).or_default().push(lt);
            } else {
                warn!(
                    "term missing from value cache in quantified disjoint recheck — returning Unknown"
                );
                return RecheckOutcome::Abort;
            }
        }

        let mut outcome = RecheckOutcome::NoChange;
        for rt in right_terms {
            if let Some(val) = value_cache.get(&rt) {
                if let Some(colliding_lefts) = left_by_value.get(val.as_str()) {
                    for &lt in colliding_lefts {
                        if self.assertion_pipeline.has_asserted_neq_pair((lt, rt)) {
                            continue;
                        }
                        let neq = self.solver.neq(lt, rt);
                        if self.assert_solver_term("check_sat/recheck/assert_quantified_neq", neq) {
                            self.assertion_pipeline.insert_asserted_neq_pair((lt, rt));
                            outcome = RecheckOutcome::NewNeq;
                        } else {
                            return RecheckOutcome::Abort;
                        }
                    }
                }
            } else {
                warn!(
                    "term missing from value cache in quantified disjoint recheck — returning Unknown"
                );
                return RecheckOutcome::Abort;
            }
        }
        outcome
    }

    /// Invoke `check_sat_with_details()` and cache the solve diagnostics
    /// (statistics, unknown reason, executor error) on the encoder. Returns
    /// the bare `SolveResult` for use in the recheck loop. (#2639)
    fn solve_and_cache_details(&mut self) -> SolveResult {
        self.replay_recorder.record_check_sat("check_sat");
        let details = self.solver.check_sat_with_details();
        self.cache_native_replay_json(Some(&details));
        let stats = SolveStatisticsSnapshot::from(&details.statistics);
        let evidence = self.consumer_solve_evidence(&details);
        tracing::debug!(
            decisions = stats.decisions,
            conflicts = stats.conflicts,
            propagations = stats.propagations,
            theory_conflicts = stats.theory_conflicts,
            num_vars = stats.num_vars,
            "solve_statistics"
        );
        self.encoding_cache.set_solve_statistics(stats);
        self.encoding_cache.set_solve_evidence(evidence);
        if let Some(reason) = details.unknown_reason.as_ref() {
            self.encoding_cache
                .set_solve_unknown_reason(UnknownReason::from_ay_unknown_reason(reason));
        }
        if let Some(err) = details.executor_error.clone() {
            self.encoding_cache.set_solve_executor_error(err);
        }
        let result = details.result.into_inner();
        if matches!(result, SolveResult::Unsat(_)) {
            if let Some(context) = self.encoding_cache.fail_closed_solver_context() {
                let message = format!("fail-closed UNSAT: {context}");
                self.encoding_cache
                    .set_solve_unknown_reason(UnknownReason::SolverMessage(message.clone()));
                self.replay_recorder
                    .record_result_with_detail(ReplayResultStatus::Unknown, message);
                return SolveResult::Unknown;
            }
        }
        self.replay_recorder
            .record_result(replay_status_from_solve_result(&result));
        result
    }

    pub(super) fn has_relevant_quantified_equality(&self) -> bool {
        if !self.assertion_pipeline.has_pending_pure_equalities() {
            return false;
        }

        self.assertion_pipeline
            .pending_pure_equalities()
            .iter()
            .any(|(lt, rt)| {
                self.mentions_quantified_term(*lt) || self.mentions_quantified_term(*rt)
            })
    }

    pub(super) fn mentions_quantified_term(&self, term: Term) -> bool {
        // O(1) HashSet lookup. Terms are eagerly inserted into
        // quantified_disjoint_terms when pushed to pending constraints
        // (sep_logic.rs), so the fallback Vec scan is no longer needed.
        self.assertion_pipeline.contains_disjoint_term(term)
    }
}

impl AYEncoder {
    pub(super) fn cache_native_replay_json(&mut self, details: Option<&SolveDetails>) {
        let artifact = self
            .solver
            .export_native_replay_artifact(NativeReplayMetadata::default(), details);
        self.encoding_cache
            .set_native_replay_json(artifact.to_pretty_json());
    }
}

fn replay_status_from_solve_result(result: &SolveResult) -> ReplayResultStatus {
    match result {
        SolveResult::Sat => ReplayResultStatus::Sat,
        SolveResult::Unsat(_) => ReplayResultStatus::Unsat,
        SolveResult::Unknown => ReplayResultStatus::Unknown,
        _ => ReplayResultStatus::Unknown,
    }
}
