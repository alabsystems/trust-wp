// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Encoding cache state: option assertion tracking, ext_eq congruence registry,
//! FMap length proxies, sort inference cache, and logic ground instantiation
//! mode. Extracted from AYEncoder (#2655).

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{Sort, Term};

use crate::{
    encoder::LogicGroundInstantiationMode,
    shared_types::{SolveEvidenceSnapshot, SolveStatisticsSnapshot, UnknownReason},
};

/// Assorted encoding caches, tracking state, and solve diagnostics.
///
/// - `is_option_asserted`: terms already asserted as `is_option(term)` by the
///   match encoder. Prevents redundant global assertions. (#1642)
/// - `ext_eq_registry`: Tseitin variables for ext_eq congruence bridging. (#2116)
/// - `fmap_len_proxies`: memoized Int proxies for `fmap_len(map)` in logics
///   where UF-headed arithmetic atoms are not accepted by LRA.
/// - `logic_ground_mode`: controls whether logic ground-pool flushing fires
///   during `check_sat`. (#1925)
/// - Solve diagnostics: cached statistics and unknown reason from the last
///   `check_sat()` call, merged from `SolveDiagnosticsState` (#2655).
#[derive(Debug)]
pub(crate) struct EncodingCacheState {
    is_option_asserted: HashSet<Term>,
    ext_eq_registry: Vec<(Term, Term, Term)>,
    /// Running count of congruence bridge assertions emitted across all
    /// `encode_ext_eq` calls. Used to enforce `TRUST_WP_MAX_CONGRUENCE_BRIDGES`. (#2708)
    ext_eq_bridge_count: usize,
    fmap_len_proxies: HashMap<Term, Term>,
    option_bridge_terms: HashMap<(Term, String), Term>,
    fmap_value_sorts: HashMap<Term, Sort>,
    fmap_value_sort_names: HashMap<String, Sort>,
    logic_ground_mode: LogicGroundInstantiationMode,
    logic_fn_defining_axioms_ground_only: bool,
    fail_closed_solver_context: Option<String>,
    // -- Solve diagnostics (merged from SolveDiagnosticsState, #2655) --
    solve_statistics: Option<SolveStatisticsSnapshot>,
    solve_evidence: Option<SolveEvidenceSnapshot>,
    solve_unknown_reason: Option<UnknownReason>,
    solve_executor_error: Option<String>,
    native_replay_json: Option<String>,
    /// Exact native problem whose strict proof replay installed the current
    /// UNSAT authority. Ordinary diagnostics must never populate this slot.
    strict_proof_native_replay_json: Option<String>,
    structural_ground_consequence_details: Vec<String>,
}

impl EncodingCacheState {
    pub(crate) fn new() -> Self {
        Self {
            is_option_asserted: HashSet::new(),
            ext_eq_registry: Vec::new(),
            ext_eq_bridge_count: 0,
            fmap_len_proxies: HashMap::new(),
            option_bridge_terms: HashMap::new(),
            fmap_value_sorts: HashMap::new(),
            fmap_value_sort_names: HashMap::new(),
            logic_ground_mode: LogicGroundInstantiationMode::default(),
            logic_fn_defining_axioms_ground_only: false,
            fail_closed_solver_context: None,
            solve_statistics: None,
            solve_evidence: None,
            solve_unknown_reason: None,
            solve_executor_error: None,
            native_replay_json: None,
            strict_proof_native_replay_json: None,
            structural_ground_consequence_details: Vec::new(),
        }
    }

    // -- is_option_asserted --

    pub(crate) fn is_option_asserted_contains(&self, term: &Term) -> bool {
        self.is_option_asserted.contains(term)
    }

    pub(crate) fn is_option_asserted_insert(&mut self, term: Term) {
        self.is_option_asserted.insert(term);
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn is_option_asserted_set(&self) -> &HashSet<Term> {
        &self.is_option_asserted
    }

    pub(crate) fn is_option_asserted_clone(&self) -> HashSet<Term> {
        self.is_option_asserted.clone()
    }

    pub(crate) fn restore_is_option_asserted(&mut self, set: HashSet<Term>) {
        self.is_option_asserted = set;
    }

    // -- ext_eq_registry --

    pub(crate) fn ext_eq_registry(&self) -> &[(Term, Term, Term)] {
        &self.ext_eq_registry
    }

    pub(crate) fn ext_eq_registry_len(&self) -> usize {
        self.ext_eq_registry.len()
    }

    pub(crate) fn ext_eq_registry_push(&mut self, entry: (Term, Term, Term)) {
        self.ext_eq_registry.push(entry);
    }

    // -- ext_eq_bridge_count --

    /// Current count of congruence bridge assertions emitted. (#2708)
    pub(crate) fn ext_eq_bridge_count(&self) -> usize {
        self.ext_eq_bridge_count
    }

    /// Increment the congruence bridge count and return the new value.
    pub(crate) fn increment_ext_eq_bridge_count(&mut self) -> usize {
        self.ext_eq_bridge_count += 1;
        self.ext_eq_bridge_count
    }

    // -- FMap length proxy cache --

    pub(crate) fn fmap_len_proxy(&self, receiver: Term) -> Option<Term> {
        self.fmap_len_proxies.get(&receiver).copied()
    }

    pub(crate) fn insert_fmap_len_proxy(&mut self, receiver: Term, proxy: Term) {
        self.fmap_len_proxies.insert(receiver, proxy);
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fmap_len_proxy_count(&self) -> usize {
        self.fmap_len_proxies.len()
    }

    // -- Legacy Option bridge cache --

    pub(crate) fn option_bridge_term(&self, term: Term, target_key: &str) -> Option<Term> {
        self.option_bridge_terms
            .get(&(term, target_key.to_string()))
            .copied()
    }

    pub(crate) fn insert_option_bridge_term(
        &mut self,
        term: Term,
        target_key: String,
        bridge_term: Term,
    ) {
        self.option_bridge_terms
            .insert((term, target_key), bridge_term);
    }

    // -- FMap value sort cache --

    pub(crate) fn fmap_value_sort(&self, receiver: Term) -> Option<Sort> {
        self.fmap_value_sorts.get(&receiver).cloned()
    }

    pub(crate) fn insert_fmap_value_sort(&mut self, receiver: Term, value_sort: Sort) {
        self.fmap_value_sorts.insert(receiver, value_sort);
    }

    pub(crate) fn fmap_value_sort_name(&self, name: &str) -> Option<Sort> {
        self.fmap_value_sort_names.get(name).cloned()
    }

    pub(crate) fn insert_fmap_value_sort_name(&mut self, name: String, value_sort: Sort) {
        self.fmap_value_sort_names.insert(name, value_sort);
    }

    // NOTE: there is deliberately NO encoder-lifetime `InferExprSortCache`
    // here. That memo is keyed by `*const PureExpr`, so an encoder-lifetime
    // instance outlives the temporaries it keyed on and turns freed-address
    // reuse into wrong sorts (see `InferExprSortCache`'s lifetime contract).
    // `infer_encoded_sort` owns a call-scoped memo instead.

    // -- logic_ground_mode --

    pub(crate) fn logic_ground_mode(&self) -> LogicGroundInstantiationMode {
        self.logic_ground_mode
    }

    pub(crate) fn set_logic_ground_mode(&mut self, mode: LogicGroundInstantiationMode) {
        self.logic_ground_mode = mode;
    }

    // -- logic function defining axiom mode --
    pub(crate) fn logic_fn_defining_axioms_ground_only(&self) -> bool {
        self.logic_fn_defining_axioms_ground_only
    }

    pub(crate) fn set_logic_fn_defining_axioms_ground_only(&mut self, enabled: bool) {
        self.logic_fn_defining_axioms_ground_only = enabled;
    }

    // -- Known solver-limited fail-closed context --

    pub(crate) fn set_fail_closed_solver_context(&mut self, context: impl Into<String>) {
        self.fail_closed_solver_context = Some(context.into());
    }

    pub(crate) fn fail_closed_solver_context(&self) -> Option<&str> {
        self.fail_closed_solver_context.as_deref()
    }

    // -- Solve diagnostics (merged from SolveDiagnosticsState, #2655) --

    /// Clear all cached solve diagnostics before a new solve call.
    pub(crate) fn clear_solve_diagnostics(&mut self) {
        self.solve_statistics = None;
        self.solve_evidence = None;
        self.solve_unknown_reason = None;
        self.solve_executor_error = None;
        self.native_replay_json = None;
        self.strict_proof_native_replay_json = None;
    }

    pub(crate) fn set_solve_statistics(&mut self, stats: SolveStatisticsSnapshot) {
        self.strict_proof_native_replay_json = None;
        self.solve_statistics = Some(stats);
    }

    pub(crate) fn set_solve_evidence(&mut self, evidence: SolveEvidenceSnapshot) {
        self.strict_proof_native_replay_json = None;
        self.solve_evidence = Some(evidence);
    }

    pub(crate) fn set_solve_unknown_reason(&mut self, reason: UnknownReason) {
        self.strict_proof_native_replay_json = None;
        self.solve_unknown_reason = Some(reason);
    }

    pub(crate) fn set_solve_executor_error(&mut self, error: String) {
        self.strict_proof_native_replay_json = None;
        self.solve_executor_error = Some(error);
    }

    pub(crate) fn set_native_replay_json(&mut self, json: String) {
        self.strict_proof_native_replay_json = None;
        self.native_replay_json = Some(json);
    }

    /// Atomically replace ordinary solve diagnostics with authority from one
    /// exact strict native replay.
    pub(crate) fn set_strict_unsat_authority(
        &mut self,
        statistics: SolveStatisticsSnapshot,
        evidence: SolveEvidenceSnapshot,
        native_replay_json: String,
    ) {
        self.solve_statistics = Some(statistics);
        self.solve_evidence = Some(evidence);
        self.solve_unknown_reason = None;
        self.solve_executor_error = None;
        self.native_replay_json = Some(native_replay_json.clone());
        self.strict_proof_native_replay_json = Some(native_replay_json);
    }

    pub(crate) fn record_structural_ground_consequence(&mut self, detail: impl Into<String>) {
        let detail = detail.into();
        if !self
            .structural_ground_consequence_details
            .iter()
            .any(|existing| existing == &detail)
        {
            self.structural_ground_consequence_details.push(detail);
        }
    }

    pub(crate) fn solve_statistics(&self) -> Option<&SolveStatisticsSnapshot> {
        self.solve_statistics.as_ref()
    }

    pub(crate) fn solve_evidence(&self) -> Option<&SolveEvidenceSnapshot> {
        self.solve_evidence.as_ref()
    }

    pub(crate) fn solve_unknown_reason(&self) -> Option<&UnknownReason> {
        self.solve_unknown_reason.as_ref()
    }

    pub(crate) fn solve_executor_error(&self) -> Option<&str> {
        self.solve_executor_error.as_deref()
    }

    pub(crate) fn native_replay_json(&self) -> Option<&str> {
        self.native_replay_json.as_deref()
    }

    pub(crate) fn strict_proof_native_replay_json(&self) -> Option<&str> {
        self.strict_proof_native_replay_json.as_deref()
    }

    pub(crate) fn structural_ground_consequence_details(&self) -> &[String] {
        &self.structural_ground_consequence_details
    }

    pub(crate) fn has_structural_ground_consequence(&self, detail: &str) -> bool {
        self.structural_ground_consequence_details
            .iter()
            .any(|existing| existing == detail)
    }
}
