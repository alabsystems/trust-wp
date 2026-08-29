// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{hash_map::Entry, HashMap, HashSet};

use ay_dpll::api::Term;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::{
    produces_ground::ProducesGroundCalls,
    sort_context::{is_collection_expr_sort, RegisteredClosureStructSort},
};

/// Maximum number of distinct produces function symbols tracked in the
/// `produces_ground_calls` HashMap. Beyond this cap, new function symbols
/// are silently dropped — their calls will NOT generate ground instances,
/// falling back entirely to the quantified axiom.
///
/// This prevents the HashMap itself from growing unboundedly for
/// iterator-heavy functions that generate many distinct `method_produces_*`
/// symbols (e.g., chained adapters like `map().filter().enumerate()`).
/// Each entry costs ~12 `ProducesGroundCall` structs (3 Terms each) plus
/// the String key, so 200 entries bounds the tracker at roughly
/// 200 * 12 * 3 * 8 = ~57 KB of Term storage. (#2709)
const TRUST_WP_PRODUCES_SYMBOL_CAP: usize = 200;

/// Sort resolution, type constant lookup, and one-shot axiom dedup state (#840).
///
/// Groups the fields used by the sort inference subsystem (`sort_context.rs`),
/// type-level constant resolution (`mod.rs`), and axiom dedup guards
/// (`view_identity_asserted` in `mod.rs`).
pub(crate) struct SortResolverState {
    /// Sort hints keyed by canonical variable names.
    ///
    /// Powers deterministic declaration sort resolution for vars/wrappers/views.
    /// Written by `record_sort_hint`, read by `resolve_decl_sort` and `is_bool_var`.
    /// Private — all accesses go through methods. (#1584 Slice B)
    sort_hints: HashMap<String, ExprSort>,
    /// Whether `register_sort_hints` has been called. When true, `encode_pure`
    /// skips redundant per-call sort hint scanning since all hints are already registered.
    sort_hints_registered: bool,
    /// Type-level constants for resolving `Self::MIN`, `Self::MAX`, etc.
    ///
    /// When verifying a spec like `i32::checked_add`, the driver populates this
    /// map with `{"Self::MIN" => Int(-2147483648), "Self::MAX" => Int(2147483647)}`.
    /// For wider types (u64, u128), values are exact symbolic expressions
    /// (e.g., `BinOp(pow2(64), Sub, Int(1))` for `u64::MAX`).
    /// The encoder checks this map when encountering `Var("Self::MIN")` or
    /// `View(Var("Self::MIN"))` and encodes the stored `PureExpr` instead of
    /// declaring an uninterpreted variable. (#688, #2315)
    type_constants: HashMap<String, PureExpr>,
    /// Tracks which integer view identity axioms (`x = x_view`) have been asserted.
    ///
    /// For integer types, `@` (view) is the identity function. `n@` is the same
    /// as `n` in the mathematical domain. When the encoder creates both `n` and
    /// `n_view` as SMT variables, this set ensures we assert `n = n_view` exactly
    /// once, connecting contracts that use `n@` with body expressions using `n`. (#359)
    view_identity_asserted: HashSet<String>,
    /// Ground `produces` calls seen so far, grouped by SMT function symbol.
    ///
    /// Uses `ProducesGroundCalls` for O(1) dedup and a cap to prevent
    /// combinatorial explosion of SMT assertions. (#935)
    produces_ground_calls: HashMap<String, ProducesGroundCalls>,
    /// Closure-struct sorts registered lazily from closure spec usage.
    ///
    /// Keyed by closure identity (`def_id` string) and used to avoid
    /// redeclaring constructor/accessor symbols on repeated registrations.
    closure_struct_sorts: HashMap<String, RegisteredClosureStructSort>,
    /// Ground `deep_model` applications recorded during encoding (#2117).
    ///
    /// Each entry is `(smt_func_name, receiver_term)` from an
    /// `encode_deep_model_uf` call.
    /// Used by `assert_deep_model_axioms` to eagerly instantiate the
    /// identity axiom as ground equalities, bypassing ay-dpll E-matching
    /// limitations that prevent the quantified axiom from firing.
    deep_model_ground_terms: Vec<(String, Term)>,
}

impl SortResolverState {
    pub(crate) fn new() -> Self {
        Self {
            sort_hints: HashMap::new(),
            sort_hints_registered: false,
            type_constants: HashMap::new(),
            view_identity_asserted: HashSet::new(),
            produces_ground_calls: HashMap::new(),
            closure_struct_sorts: HashMap::new(),
            deep_model_ground_terms: Vec::new(),
        }
    }

    // --- Sort hint registry ---

    /// Look up a sort hint by canonical variable name.
    pub(crate) fn get_sort_hint(&self, name: &str) -> Option<&ExprSort> {
        self.sort_hints.get(name)
    }

    /// Record a sort hint for a canonical variable name.
    pub(crate) fn record_sort_hint(&mut self, name: String, hint: ExprSort) {
        match self.sort_hints.entry(name) {
            Entry::Occupied(existing)
                if is_collection_expr_sort(existing.get()) && hint == ExprSort::Bool =>
            {
                // Collection hints are more specific than Bool -- keep the existing hint.
            }
            Entry::Occupied(existing)
                if *existing.get() == ExprSort::FMap && hint == ExprSort::Seq =>
            {
                // FMap is more specific than Seq. The prescan's ambiguous-method
                // heuristic tags some receivers as Seq by default, so keep the
                // stronger FMap evidence when it already exists. (#994, #2316)
            }
            Entry::Occupied(mut existing) => {
                existing.insert(hint);
            }
            Entry::Vacant(vacant) => {
                vacant.insert(hint);
            }
        }
    }

    /// Insert a sort hint only when the name has no prior entry.
    pub(crate) fn record_sort_hint_if_absent(&mut self, name: String, hint: ExprSort) {
        self.sort_hints.entry(name).or_insert(hint);
    }

    /// Remove a sort hint (used to clear stale Bool hints). (#585)
    pub(crate) fn remove_sort_hint(&mut self, name: &str) {
        self.sort_hints.remove(name);
    }

    /// Whether sort hints have already been globally registered.
    pub(crate) fn are_sort_hints_registered(&self) -> bool {
        self.sort_hints_registered
    }

    /// Mark sort hints as globally registered.
    pub(crate) fn mark_sort_hints_registered(&mut self) {
        self.sort_hints_registered = true;
    }

    // --- Type constant registry ---

    /// Look up a type-level constant (e.g. `Self::MIN`, `Self::MAX`).
    pub(crate) fn get_type_constant(&self, name: &str) -> Option<&PureExpr> {
        self.type_constants.get(name)
    }

    /// Set all type-level constants (called once from driver context).
    pub(crate) fn set_type_constants(&mut self, constants: HashMap<String, PureExpr>) {
        self.type_constants = constants;
    }

    // --- View identity dedup ---

    /// Check if a view identity axiom has been asserted for this variable.
    pub(crate) fn has_view_identity(&self, name: &str) -> bool {
        self.view_identity_asserted.contains(name)
    }

    /// Record that a view identity axiom has been asserted.
    pub(crate) fn mark_view_identity(&mut self, name: String) {
        self.view_identity_asserted.insert(name);
    }

    /// Number of view identity axioms asserted (for test assertions).
    #[cfg(test)]
    pub(crate) fn view_identity_count(&self) -> usize {
        self.view_identity_asserted.len()
    }

    // --- Produces ground calls ---

    /// Get or create the produces ground calls registry for a function symbol.
    ///
    /// Returns `None` if the symbol is not already tracked and the HashMap
    /// has reached `TRUST_WP_PRODUCES_SYMBOL_CAP` distinct entries. This prevents
    /// unbounded growth of the tracker for iterator-heavy functions that
    /// generate many distinct `method_produces_*` symbols. (#2709)
    pub(crate) fn get_or_create_produces_ground(
        &mut self,
        fn_symbol: &str,
    ) -> Option<&mut ProducesGroundCalls> {
        // Fast path: symbol already tracked — always allow access.
        if self.produces_ground_calls.contains_key(fn_symbol) {
            return Some(
                self.produces_ground_calls
                    .get_mut(fn_symbol)
                    .expect("key verified present"),
            );
        }
        // Slow path: new symbol — reject if at the symbol cap.
        if self.produces_ground_calls.len() >= TRUST_WP_PRODUCES_SYMBOL_CAP {
            return None;
        }
        Some(
            self.produces_ground_calls
                .entry(fn_symbol.to_string())
                .or_default(),
        )
    }

    // --- Closure struct sorts ---

    /// Look up a registered closure struct sort by def_id.
    pub(crate) fn get_closure_struct_sort(
        &self,
        def_id: &str,
    ) -> Option<&RegisteredClosureStructSort> {
        self.closure_struct_sorts.get(def_id)
    }

    /// Register a closure struct sort.
    pub(crate) fn insert_closure_struct_sort(
        &mut self,
        def_id: String,
        sort: RegisteredClosureStructSort,
    ) {
        self.closure_struct_sorts.insert(def_id, sort);
    }

    // --- Deep model ground terms ---

    /// Take all deep model ground terms, leaving the vec empty.
    pub(crate) fn take_deep_model_ground_terms(&mut self) -> Vec<(String, Term)> {
        std::mem::take(&mut self.deep_model_ground_terms)
    }

    /// Record a deep model ground application.
    pub(crate) fn record_deep_model_ground(&mut self, smt_name: String, receiver: Term) {
        self.deep_model_ground_terms.push((smt_name, receiver));
    }

    /// Restore deep model ground terms (after temporary borrow for iteration).
    pub(crate) fn restore_deep_model_ground_terms(&mut self, terms: Vec<(String, Term)>) {
        self.deep_model_ground_terms = terms;
    }

    /// Check if a sort hint exists for the given name.
    pub(crate) fn has_sort_hint(&self, name: &str) -> bool {
        self.sort_hints.contains_key(name)
    }

    /// Check if any sort hint value matches a predicate (for test assertions).
    #[cfg(test)]
    pub(crate) fn any_sort_hint_value(&self, pred: impl Fn(&ExprSort) -> bool) -> bool {
        self.sort_hints.values().any(pred)
    }

    /// Iterator over registered closure struct sorts.
    pub(crate) fn closure_struct_sorts_iter(
        &self,
    ) -> impl Iterator<Item = &RegisteredClosureStructSort> {
        self.closure_struct_sorts.values()
    }

    // --- Snapshot/restore for obligation slice isolation (#2618) ---

    /// Snapshot the view identity dedup set.
    pub(crate) fn view_identity_snapshot(&self) -> HashSet<String> {
        self.view_identity_asserted.clone()
    }

    /// Restore the view identity dedup set from a snapshot.
    pub(crate) fn restore_view_identity(&mut self, snapshot: HashSet<String>) {
        self.view_identity_asserted = snapshot;
    }

    /// Snapshot the produces ground calls registry.
    pub(crate) fn produces_ground_snapshot(&self) -> HashMap<String, ProducesGroundCalls> {
        self.produces_ground_calls.clone()
    }

    /// Restore the produces ground calls registry from a snapshot.
    pub(crate) fn restore_produces_ground(
        &mut self,
        snapshot: HashMap<String, ProducesGroundCalls>,
    ) {
        self.produces_ground_calls = snapshot;
    }

    // --- Test-only state inspection ---

    /// Check if the sort hints map is empty (for fresh-state assertions).
    #[cfg(test)]
    pub(crate) fn sort_hints_is_empty(&self) -> bool {
        self.sort_hints.is_empty()
    }

    /// Check if the type constants map is empty (for fresh-state assertions).
    #[cfg(test)]
    pub(crate) fn type_constants_is_empty(&self) -> bool {
        self.type_constants.is_empty()
    }

    /// Check if the view identity set is empty (for fresh-state assertions).
    #[cfg(test)]
    pub(crate) fn view_identity_is_empty(&self) -> bool {
        self.view_identity_asserted.is_empty()
    }

    /// Check if the produces ground calls map is empty (for fresh-state assertions).
    #[cfg(test)]
    pub(crate) fn produces_ground_is_empty(&self) -> bool {
        self.produces_ground_calls.is_empty()
    }

    /// Number of distinct function symbols tracked in the produces ground map.
    #[cfg(test)]
    pub(crate) fn produces_ground_symbol_count(&self) -> usize {
        self.produces_ground_calls.len()
    }
}

#[cfg(test)]
mod tests {
    use trust_wp_core::formula::ExprSort;

    use super::*;

    // ── initialization ──

    #[test]
    fn test_new_sort_resolver_state_is_empty() {
        let state = SortResolverState::new();
        assert!(state.sort_hints_is_empty());
        assert!(state.type_constants_is_empty());
        assert!(state.view_identity_is_empty());
        assert!(state.produces_ground_is_empty());
        assert!(!state.are_sort_hints_registered());
    }

    // ── sort hint registry ──

    #[test]
    fn test_record_and_get_sort_hint() {
        let mut state = SortResolverState::new();
        assert!(state.get_sort_hint("x").is_none());

        state.record_sort_hint("x".to_string(), ExprSort::Int);
        assert_eq!(state.get_sort_hint("x"), Some(&ExprSort::Int));
        assert!(state.has_sort_hint("x"));
        assert!(!state.has_sort_hint("y"));
    }

    #[test]
    fn test_record_sort_hint_overwrites_by_default() {
        let mut state = SortResolverState::new();
        state.record_sort_hint("x".to_string(), ExprSort::Int);
        state.record_sort_hint("x".to_string(), ExprSort::Bool);
        assert_eq!(state.get_sort_hint("x"), Some(&ExprSort::Bool));
    }

    #[test]
    fn test_record_sort_hint_preserves_collection_over_bool() {
        let mut state = SortResolverState::new();
        // Seq is a collection sort; it should be preserved when Bool hint arrives
        state.record_sort_hint("v".to_string(), ExprSort::Seq);
        state.record_sort_hint("v".to_string(), ExprSort::Bool);
        assert_eq!(state.get_sort_hint("v"), Some(&ExprSort::Seq));
    }

    #[test]
    fn test_record_sort_hint_preserves_fmap_over_seq() {
        let mut state = SortResolverState::new();
        // FMap is more specific than Seq
        state.record_sort_hint("m".to_string(), ExprSort::FMap);
        state.record_sort_hint("m".to_string(), ExprSort::Seq);
        assert_eq!(state.get_sort_hint("m"), Some(&ExprSort::FMap));
    }

    #[test]
    fn test_record_sort_hint_if_absent() {
        let mut state = SortResolverState::new();
        state.record_sort_hint_if_absent("x".to_string(), ExprSort::Int);
        assert_eq!(state.get_sort_hint("x"), Some(&ExprSort::Int));

        // Second call should not overwrite
        state.record_sort_hint_if_absent("x".to_string(), ExprSort::Bool);
        assert_eq!(state.get_sort_hint("x"), Some(&ExprSort::Int));
    }

    #[test]
    fn test_remove_sort_hint() {
        let mut state = SortResolverState::new();
        state.record_sort_hint("x".to_string(), ExprSort::Bool);
        assert!(state.has_sort_hint("x"));

        state.remove_sort_hint("x");
        assert!(!state.has_sort_hint("x"));
        assert!(state.get_sort_hint("x").is_none());
    }

    #[test]
    fn test_sort_hints_registered_flag() {
        let mut state = SortResolverState::new();
        assert!(!state.are_sort_hints_registered());

        state.mark_sort_hints_registered();
        assert!(state.are_sort_hints_registered());
    }

    #[test]
    fn test_any_sort_hint_value() {
        let mut state = SortResolverState::new();
        state.record_sort_hint("x".to_string(), ExprSort::Int);
        state.record_sort_hint("y".to_string(), ExprSort::Bool);

        assert!(state.any_sort_hint_value(|s| *s == ExprSort::Bool));
        assert!(!state.any_sort_hint_value(|s| *s == ExprSort::Seq));
    }

    // ── type constant registry ──

    #[test]
    fn test_type_constants() {
        let mut state = SortResolverState::new();
        assert!(state.get_type_constant("Self::MIN").is_none());

        let mut constants = HashMap::new();
        constants.insert("Self::MIN".to_string(), PureExpr::Int(-128));
        constants.insert("Self::MAX".to_string(), PureExpr::Int(127));
        state.set_type_constants(constants);

        assert_eq!(
            state.get_type_constant("Self::MIN"),
            Some(&PureExpr::Int(-128))
        );
        assert_eq!(
            state.get_type_constant("Self::MAX"),
            Some(&PureExpr::Int(127))
        );
        assert!(state.get_type_constant("Self::BITS").is_none());
        assert!(!state.type_constants_is_empty());
    }

    // ── view identity dedup ──

    #[test]
    fn test_view_identity_mark_and_check() {
        let mut state = SortResolverState::new();
        assert!(!state.has_view_identity("x"));
        assert!(state.view_identity_is_empty());

        state.mark_view_identity("x".to_string());
        assert!(state.has_view_identity("x"));
        assert!(!state.has_view_identity("y"));
        assert_eq!(state.view_identity_count(), 1);
    }

    #[test]
    fn test_view_identity_snapshot_and_restore() {
        let mut state = SortResolverState::new();
        state.mark_view_identity("x".to_string());
        state.mark_view_identity("y".to_string());

        let snapshot = state.view_identity_snapshot();
        assert_eq!(snapshot.len(), 2);

        // Add more after snapshot
        state.mark_view_identity("z".to_string());
        assert_eq!(state.view_identity_count(), 3);

        // Restore removes "z"
        state.restore_view_identity(snapshot);
        assert!(state.has_view_identity("x"));
        assert!(state.has_view_identity("y"));
        assert!(!state.has_view_identity("z"));
        assert_eq!(state.view_identity_count(), 2);
    }

    // ── produces ground calls ──

    #[test]
    fn test_produces_ground_calls_get_or_create() {
        let mut state = SortResolverState::new();
        assert!(state.produces_ground_is_empty());

        // get_or_create should create a new entry
        let entry = state.get_or_create_produces_ground("produces_f");
        assert!(entry.is_some(), "fresh symbol below cap should succeed");
        assert!(!state.produces_ground_is_empty());
    }

    #[test]
    fn test_produces_ground_snapshot_and_restore() {
        let mut state = SortResolverState::new();
        let _entry = state
            .get_or_create_produces_ground("produces_f")
            .expect("below cap");
        let snapshot = state.produces_ground_snapshot();

        let _entry2 = state
            .get_or_create_produces_ground("produces_g")
            .expect("below cap");

        state.restore_produces_ground(snapshot);
        // After restore, "produces_g" should be gone — only "produces_f" remains
    }

    #[test]
    fn test_produces_ground_symbol_cap() {
        let mut state = SortResolverState::new();

        // Fill to exactly TRUST_WP_PRODUCES_SYMBOL_CAP entries.
        for i in 0..TRUST_WP_PRODUCES_SYMBOL_CAP {
            let sym = format!("produces_{i}");
            assert!(
                state.get_or_create_produces_ground(&sym).is_some(),
                "insert at index {i} should succeed"
            );
        }
        assert_eq!(
            state.produces_ground_symbol_count(),
            TRUST_WP_PRODUCES_SYMBOL_CAP
        );

        // New symbol beyond cap should be rejected.
        assert!(
            state
                .get_or_create_produces_ground("produces_overflow")
                .is_none(),
            "new symbol beyond cap should return None"
        );
        assert_eq!(
            state.produces_ground_symbol_count(),
            TRUST_WP_PRODUCES_SYMBOL_CAP,
            "map size should not grow beyond cap"
        );

        // Existing symbol should still be accessible.
        assert!(
            state.get_or_create_produces_ground("produces_0").is_some(),
            "existing symbol should still be accessible after cap"
        );
    }

    #[test]
    fn test_produces_ground_symbol_cap_value_is_200() {
        // Pin the symbol cap so changes require updating this test.
        assert_eq!(
            TRUST_WP_PRODUCES_SYMBOL_CAP, 200,
            "symbol cap should be 200 per design (#2709)"
        );
    }

    // ── deep model ground terms ──

    #[test]
    fn test_deep_model_ground_terms() {
        let mut state = SortResolverState::new();
        let mut solver = ay_dpll::api::Solver::new(ay_dpll::api::Logic::QfAuflia);
        let term = solver.declare_const("x", ay_dpll::api::Sort::Int);

        state.record_deep_model_ground("deep_model_Foo".to_string(), term);
        state.record_deep_model_ground("deep_model_Bar".to_string(), term);

        let taken = state.take_deep_model_ground_terms();
        assert_eq!(taken.len(), 2);
        assert_eq!(taken[0].0, "deep_model_Foo");
        assert_eq!(taken[1].0, "deep_model_Bar");

        // After take, the vec should be empty
        let taken2 = state.take_deep_model_ground_terms();
        assert!(taken2.is_empty());
    }

    #[test]
    fn test_restore_deep_model_ground_terms() {
        let mut state = SortResolverState::new();
        let mut solver = ay_dpll::api::Solver::new(ay_dpll::api::Logic::QfAuflia);
        let term = solver.declare_const("x", ay_dpll::api::Sort::Int);

        let terms = vec![("deep_model_A".to_string(), term)];
        state.restore_deep_model_ground_terms(terms);

        let taken = state.take_deep_model_ground_terms();
        assert_eq!(taken.len(), 1);
        assert_eq!(taken[0].0, "deep_model_A");
    }
}
