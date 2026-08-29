// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Assertion-phase, path-condition, and runtime shell methods for `AYEncoder`.
//!
//! These methods own the boundary between the encoder's assertion pipeline,
//! path-condition stack, and general runtime state (logic mode, division
//! obligations, total-int arithmetic, ground pool flushing).
//!
//! Issue: #2588

use std::collections::HashSet;

use ay_dpll::api::Term;
use trust_wp_core::formula::PureExpr;

#[cfg(test)]
use crate::encoder::AssertionPipelineState;
#[cfg(test)]
use crate::memory_model::MemState;
use crate::{
    encoder::{
        ground_pool, AYEncoder, AssertionPhase, DedupSnapshot, LogicGroundInstantiationMode,
        PathConditionGuard,
    },
    error::EncodingError,
};

/// Map common collection method names to their corresponding SMT UF names.
///
/// Returns an iterator of SMT symbol names that the given source-level method
/// may encode to. For example, `"len"` maps to `"seq_len"` because
/// `v.len()` encodes to the `seq_len` uninterpreted function application.
///
/// Only covers the most common Seq/FMap/FSet collection methods that appear in
/// quantified postconditions. Unmapped methods return an empty list — the worst
/// case is that their axiom ground instances don't get postcondition-critical
/// priority, which only affects performance (not correctness). (#2696)
fn method_to_smt_symbols(method: &str) -> &'static [&'static str] {
    match method {
        // Seq operations
        "len" | "len_ghost" | "len_logic" => &["seq_len"],
        "get" | "get_ghost" | "get_mut_ghost" | "index" | "index_logic" => &["seq_get"],
        "set" => &["seq_set"],
        "push_back" | "push_back_ghost" => &["seq_push_back"],
        "push_front" | "push_front_ghost" => &["seq_push_front"],
        "tail" => &["seq_tail"],
        "subsequence" => &["seq_subsequence"],
        "concat" => &["seq_concat"],
        "reverse" => &["seq_reverse"],
        "ext_eq" => &["seq_ext_eq"],
        "contains" | "contains_ghost" => &["seq_contains", "fset_contains"],
        "permutation_of" => &["seq_permutation_of"],
        "exchange" => &["seq_exchange"],
        "count" => &["seq_count"],
        // FMap operations
        "lookup" => &["fmap_lookup"],
        "insert" | "insert_ghost" => &["fmap_insert"],
        "contains_key" => &["fmap_contains_key"],
        // FSet operations
        "is_subset" => &["fset_is_subset"],
        "union" => &["fset_union"],
        "intersection" => &["fset_intersection"],
        _ => &[],
    }
}

impl AYEncoder {
    pub(crate) fn with_assertion_phase<T>(
        &mut self,
        phase: AssertionPhase,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous = self.assertion_pipeline.replace_phase(phase);
        let result = f(self);
        self.assertion_pipeline.replace_phase(previous);
        result
    }

    pub(crate) fn with_negated_goal_label_prefix<T>(
        &mut self,
        label_prefix: String,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let previous = self
            .assertion_pipeline
            .negated_goal_label_prefix()
            .map(str::to_string);
        self.assertion_pipeline
            .set_negated_goal_label_prefix(label_prefix);
        let result = f(self);
        match previous {
            Some(label) => self.assertion_pipeline.set_negated_goal_label_prefix(label),
            None => self.assertion_pipeline.clear_negated_goal_label(),
        }
        result
    }

    /// Push a condition onto the path-condition stack and return an RAII guard
    /// that pops it on drop. Encapsulates the raw `path_conditions` access so
    /// `encode_pure_impl` never touches the field directly. (#1584)
    pub(in crate::encoder) fn push_path_condition(&mut self, cond: Term) -> PathConditionGuard {
        self.traversal.path_conditions.push(cond);
        PathConditionGuard(&raw mut self.traversal.path_conditions)
    }

    /// Guard a side-effect assertion with the current branch path.
    ///
    /// When no branch context is active, returns `fact` unchanged.
    /// Inside nested `Ite` branches, returns `(path_1 && ... && path_n) => fact`.
    pub(in crate::encoder) fn guard_with_active_path(&mut self, fact: Term) -> Term {
        match self.traversal.path_conditions.len() {
            0 => fact,
            1 => self.solver.implies(self.traversal.path_conditions[0], fact),
            _ => {
                let path_guard = self.solver.and_many(&self.traversal.path_conditions);
                self.solver.implies(path_guard, fact)
            }
        }
    }

    /// Clone the currently active path conditions for deferred bookkeeping. (#1584)
    pub(in crate::encoder) fn active_path_conditions_cloned(&self) -> Vec<Term> {
        self.traversal.path_conditions.clone()
    }

    /// Whether encoding is currently inside a conditional branch.
    pub(in crate::encoder) fn has_active_path_conditions(&self) -> bool {
        !self.traversal.path_conditions.is_empty()
    }

    /// Whether this encoder's selected logic supports quantifiers. (#1584, #2655)
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn supports_quantifiers(&self) -> bool {
        self.traversal.supports_quantifiers
    }

    /// Return the SMT logic selected when the encoder was constructed. (#1584, #2655)
    pub(crate) fn logic(&self) -> ay_dpll::api::Logic {
        self.traversal.logic
    }

    /// Produce a stable debug/dedup key for the active path-condition stack. (#1584)
    pub(in crate::encoder) fn active_path_condition_key(&self) -> String {
        self.traversal
            .path_conditions
            .iter()
            .map(|term| format!("{term:?}"))
            .collect::<Vec<_>>()
            .join(" && ")
    }

    /// Drain and return all accumulated division-obligation terms. (#1584)
    ///
    /// Used by the verification layer to extract obligations after encoding
    /// postconditions.
    pub(crate) fn take_division_obligations(&mut self) -> Vec<Term> {
        self.arithmetic_mode.take_division_obligations()
    }

    /// Run `f` with `cond` pushed on the path-condition stack.
    ///
    /// Verify-layer entry point for branch-scoped encoding (the raw
    /// `push_path_condition` guard is encoder-private): side obligations
    /// collected inside `f` — `divisor != 0`, shift-amount range — are
    /// guarded by `cond` exactly as if the expression had been encoded
    /// inside the corresponding `Ite` branch of `encode_pure_impl`. Used by
    /// the guarded-ITE result-binding lane, whose per-branch `encode_pure`
    /// calls previously collected branch-body obligations UNGUARDED (the
    /// bits.rs `empty` false counterexample, ledger int-shift-full).
    pub(crate) fn with_path_condition<R>(
        &mut self,
        cond: Term,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let guard = self.push_path_condition(cond);
        let result = f(self);
        drop(guard);
        result
    }

    /// Run `f` with the encoder in ASSUMPTION position: shift-amount range
    /// obligations are not collected for expressions encoded inside `f`.
    ///
    /// Assumption-position expressions (preconditions, `LetAssume`
    /// assumptions, path-condition facts) re-state what an already-verified
    /// body execution established; the shift obligations they embed are
    /// owned — path-guarded — by the body VALUE encoding, and re-collecting
    /// them here would conjoin them into a foreign goal WITHOUT their
    /// execution-path guard. See
    /// `ArithmeticModeState::assumption_position`. (ledger int-shift-full)
    pub(crate) fn with_assumption_position<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.arithmetic_mode.enter_assumption_position();
        let result = f(self);
        self.arithmetic_mode.exit_assumption_position();
        result
    }

    /// Set total integer arithmetic mode (suppresses division obligations). (#1584)
    pub(crate) fn set_total_int_arithmetic(&mut self, total: bool) {
        self.arithmetic_mode.set_total_int_arithmetic(total);
    }

    /// Set bitwise proof mode. When true, bitwise operations use ay's native
    /// BV theory via Int<->BV conversion instead of UF approximations. (#2666)
    pub(crate) fn set_bitwise_proof_mode(&mut self, enabled: bool) {
        self.arithmetic_mode.set_bitwise_proof_mode(enabled);
    }

    /// Set the logic ground instantiation mode (#1925).
    pub(crate) fn set_logic_ground_mode(&mut self, mode: LogicGroundInstantiationMode) {
        self.encoding_cache.set_logic_ground_mode(mode);
    }

    pub(crate) fn logic_ground_mode(&self) -> LogicGroundInstantiationMode {
        self.encoding_cache.logic_ground_mode()
    }

    /// Prefer ground-pool instances over global quantified defining axioms for
    /// open logic functions registered after this point.
    pub(crate) fn set_logic_fn_defining_axioms_ground_only(&mut self, enabled: bool) {
        self.encoding_cache
            .set_logic_fn_defining_axioms_ground_only(enabled);
    }

    /// Assert logic ground-pool instances if the mode is `Enabled`.
    ///
    /// Centralizes the ground-pool flushing gate so that all call sites
    /// (check_sat, solver_tail, loop encoder) share the same mode check.
    /// When `Disabled`, this is a no-op -- ay-dpll handles
    /// quantified axiom instantiation. (#1925)
    pub(crate) fn maybe_assert_logic_ground_instances(&mut self) -> Result<usize, EncodingError> {
        let mut struct_aliases = self.assert_struct_field_placeholder_ground_aliases();
        if self.encoding_cache.logic_ground_mode() == LogicGroundInstantiationMode::Disabled {
            return Ok(struct_aliases);
        }
        let instances = self.assert_ground_pool_instances()?;
        // Logic ground instantiation can materialize new struct-field
        // placeholder applications. Run the ground alias pass again so those
        // fresh applications are connected before the solver consumes the VC.
        struct_aliases += self.assert_struct_field_placeholder_ground_aliases();
        Ok(instances.saturating_add(struct_aliases))
    }

    /// Set or clear the obligation-local ground-pool relevance filter (#2674).
    pub(crate) fn set_ground_pool_relevance_filter(&mut self, symbols: Option<HashSet<String>>) {
        self.ground_pool.set_relevance_filter(symbols);
    }

    /// Registered ground-pool axioms used by verification-side rewrites that
    /// inline transparent open logic functions before solver encoding.
    pub(crate) fn ground_pool_axioms(&self) -> &[ground_pool::AxiomEntry] {
        self.ground_pool.axioms()
    }

    /// Clear the obligation-local ground-pool relevance filter (#2674).
    pub(crate) fn clear_ground_pool_relevance_filter(&mut self) {
        self.ground_pool.clear_relevance_filter();
    }

    /// Override the ground-pool instance budget for the current slice (#2674).
    pub(crate) fn set_ground_pool_per_slice_budget(&mut self, budget: Option<usize>) {
        self.ground_pool.set_per_slice_budget(budget);
    }

    /// Number of axioms currently registered in the ground pool. Used by the
    /// `TRUST_WP_PROFILE` instrumentation to report per-slice axiom counts
    /// (#2674 Phase 1). Zero-cost read; does not mutate pool state.
    pub(crate) fn ground_pool_axiom_count(&self) -> usize {
        self.ground_pool.axiom_count()
    }

    /// Register contract-critical function symbols in the ground pool (#1296).
    ///
    /// Scans the given contract expressions for `LogicFnCall` and `MethodCall`
    /// nodes and marks their SMT function names as postcondition-critical. This
    /// ensures that axioms for these functions:
    /// 1. Bypass the `TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND` parameter complexity gate
    /// 2. Receive highest priority in the global instantiation budget
    ///
    /// Should be called before `assert_ground_pool_instances()` — typically
    /// in the verification tail after postcondition encoding but before the
    /// ground pool flush. Called with both ensures and requires expressions:
    /// logic functions in requires clauses establish precondition facts that
    /// the solver needs to constrain the proof.
    ///
    /// Also marks common collection method SMT names when `MethodCall` nodes
    /// are present. Method calls like `v.len()`, `v.get(i)`, `v[i]` encode to
    /// UF applications (`seq_len`, `seq_get`, etc.) that need postcondition-
    /// critical priority for ground instantiation. Without this, Skolemized
    /// universal postconditions like `forall<i> ... ==> v.get(i) == w.get(i)`
    /// have their ground instances deprioritized, causing quantifier-unhandled
    /// results. (#2696)
    pub(crate) fn mark_postcondition_logic_fn_symbols(&mut self, ensures: &[PureExpr]) {
        use trust_wp_core::formula::PureExprDepthLimitedTraversalExt as _;

        for expr in ensures {
            expr.for_each_recursive_with_depth_limit(crate::encoder::MAX_ENCODING_DEPTH, |node| {
                match node {
                    PureExpr::LogicFnCall { name, .. } => {
                        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
                        self.ground_pool.mark_postcondition_symbol(smt_name);
                    }
                    PureExpr::MethodCall { method, .. } => {
                        let logic_smt_name = trust_wp_core::logic::logic_fn_smt_name(method);
                        self.ground_pool.mark_postcondition_symbol(logic_smt_name);
                        // Type-invariant methods are registered under
                        // sort-specialized `method_<source>_<arity>_<sorts>`
                        // symbols. Mark the registered symbols, not the raw
                        // source method name, so relevance filtering preserves
                        // direct invariant postconditions.
                        if method.starts_with("__trust_wp_invariant_") {
                            let prefix = format!("method_{method}_");
                            let symbols: Vec<String> = self
                                .ground_pool
                                .axioms()
                                .iter()
                                .filter(|axiom| axiom.fn_symbol.starts_with(&prefix))
                                .map(|axiom| axiom.fn_symbol.clone())
                                .collect();
                            for smt_name in symbols {
                                self.ground_pool.mark_postcondition_symbol(smt_name);
                            }
                        }
                        // Map common collection methods to their SMT UF names.
                        // These methods encode to uninterpreted function
                        // applications that need postcondition-critical priority
                        // in the ground pool. (#2696)
                        for smt_name in method_to_smt_symbols(method) {
                            self.ground_pool
                                .mark_postcondition_symbol(smt_name.to_string());
                        }
                    }
                    _ => {}
                }
            });
        }
    }

    /// Snapshot the current ground-term pool so callers can restore it after
    /// temporary goal encodings. The SMT solver scope stack rolls back
    /// assertions, but the ground-pool cache is process-local state. (#2616)
    pub(crate) fn ground_pool_snapshot(&self) -> ground_pool::GroundTermPool {
        self.ground_pool.clone()
    }

    /// Restore a previously snapped ground-term pool. This prevents
    /// goal-scoped term registrations from contaminating later base rechecks or
    /// sibling obligation slices after the solver scope has been popped. (#2616)
    pub(crate) fn restore_ground_pool(&mut self, snapshot: ground_pool::GroundTermPool) {
        self.ground_pool = snapshot;
    }

    /// Capture all scope-sensitive assert-once state for obligation slice
    /// isolation. Call before the slice loop; restore at the top of each
    /// iteration so every slice starts from the same baseline. (#2618)
    pub(crate) fn dedup_snapshot(&self) -> DedupSnapshot {
        DedupSnapshot {
            is_option_asserted: self.encoding_cache.is_option_asserted_clone(),
            view_identity_asserted: self.sort_resolver.view_identity_snapshot(),
            asserted_quantified_neq_pairs: self.assertion_pipeline.neq_pairs_snapshot(),
            produces_ground_calls: self.sort_resolver.produces_ground_snapshot(),
            ground_pool: self.ground_pool.clone(),
            logic_fn_axioms: self.decls.logic_fn_axiom_snapshot(),
            sum_axioms_asserted: self.seq_state.sum_axioms_asserted(),
            get_axioms_asserted: self.seq_state.get_axioms_asserted(),
            contains_axioms_asserted: self.seq_state.contains_axioms_asserted(),
            concat_axioms_asserted: self.seq_state.concat_axioms_asserted(),
            reverse_axioms_asserted: self.seq_state.reverse_axioms_asserted(),
            permutation_axioms_asserted: self.seq_state.permutation_axioms_asserted(),
        }
    }

    /// Restore slice-sensitive assert-once state from a pre-slice snapshot.
    /// Ensures each obligation slice sees the same encoding baseline. (#2618)
    pub(crate) fn restore_dedup(&mut self, snapshot: DedupSnapshot) {
        self.encoding_cache
            .restore_is_option_asserted(snapshot.is_option_asserted);
        self.sort_resolver
            .restore_view_identity(snapshot.view_identity_asserted);
        self.assertion_pipeline
            .restore_neq_pairs(snapshot.asserted_quantified_neq_pairs);
        self.sort_resolver
            .restore_produces_ground(snapshot.produces_ground_calls);
        self.ground_pool = snapshot.ground_pool;
        self.decls.restore_logic_fn_axioms(snapshot.logic_fn_axioms);
        self.seq_state
            .restore_sum_axioms_asserted(snapshot.sum_axioms_asserted);
        self.seq_state
            .restore_get_axioms_asserted(snapshot.get_axioms_asserted);
        self.seq_state
            .restore_contains_axioms_asserted(snapshot.contains_axioms_asserted);
        self.seq_state
            .restore_concat_axioms_asserted(snapshot.concat_axioms_asserted);
        self.seq_state
            .restore_reverse_axioms_asserted(snapshot.reverse_axioms_asserted);
        self.seq_state
            .restore_permutation_axioms_asserted(snapshot.permutation_axioms_asserted);
    }

    // ── Test-only accessors ────────────────────────────────────────

    /// Test-only escape hatch for crate-root unit tests that validate the
    /// assertion pipeline without keeping the field crate-visible. (#1584)
    #[cfg(test)]
    pub(crate) fn assertion_pipeline_for_test(&self) -> &AssertionPipelineState {
        &self.assertion_pipeline
    }

    /// Mutable test-only access to the assertion pipeline for focused unit
    /// tests that seed recheck state directly. (#1584)
    #[cfg(test)]
    pub(crate) fn assertion_pipeline_mut_for_test(&mut self) -> &mut AssertionPipelineState {
        &mut self.assertion_pipeline
    }

    /// Test-only read access to the path-condition stack. (#1584)
    #[cfg(test)]
    pub(crate) fn path_conditions_for_test(&self) -> &[Term] {
        &self.traversal.path_conditions
    }

    /// Test-only read access to the recursion-depth counter. (#1584)
    #[cfg(test)]
    pub(crate) fn recursion_depth_for_test(&self) -> usize {
        self.traversal.recursion_depth
    }

    /// Test-only accessor: read-only view of the is_option_asserted set. (#1584)
    #[cfg(test)]
    pub(crate) fn is_option_asserted_for_test(&self) -> &HashSet<Term> {
        self.encoding_cache.is_option_asserted_set()
    }

    /// Test-only read access to the division-obligations vector. (#1584)
    #[cfg(test)]
    pub(crate) fn division_obligations_for_test(&self) -> &[Term] {
        self.arithmetic_mode.division_obligations()
    }

    /// Test-only entry point to the shift-amount range collector (ledger
    /// int-shift-full): lets tests hand a BV-sorted amount term directly to
    /// pin the native-BV obligation form (no Int round-trip, no aux).
    #[cfg(test)]
    pub(crate) fn collect_shift_amount_range_obligation_for_test(
        &mut self,
        amount: Term,
        bits: u32,
    ) -> Term {
        self.collect_shift_amount_range_obligation(amount, bits)
    }

    /// Test-only read access to the total_int_arithmetic flag. (#1584)
    #[cfg(test)]
    pub(crate) fn total_int_arithmetic_for_test(&self) -> bool {
        self.arithmetic_mode.total_int_arithmetic()
    }

    /// Test-only read access to the memory state (heap, domain, permissions). (#1584)
    #[cfg(test)]
    pub(crate) fn mem_state_for_test(&self) -> &MemState {
        &self.mem_state
    }

    /// Test-only mutable access to the memory state (heap, domain, permissions). (#1584)
    #[cfg(test)]
    pub(crate) fn mem_state_for_test_mut(&mut self) -> &mut MemState {
        &mut self.mem_state
    }

    /// Test-only read access to the ground-term pool. (#1584)
    #[cfg(test)]
    pub(crate) fn ground_pool_for_test(&self) -> &ground_pool::GroundTermPool {
        &self.ground_pool
    }

    /// Test-only mutable access to the ground-term pool. (#1584)
    #[cfg(test)]
    pub(crate) fn ground_pool_for_test_mut(&mut self) -> &mut ground_pool::GroundTermPool {
        &mut self.ground_pool
    }

    /// Hidden bench helper for verifying ground-pool registration paths.
    #[cfg(feature = "internal-bench-api")]
    #[doc(hidden)]
    pub fn ground_pool_entry_count_for_internal_bench(&self, symbol: &str) -> usize {
        self.ground_pool
            .entries_for(symbol)
            .map_or(0, |entries| entries.len())
    }
}
