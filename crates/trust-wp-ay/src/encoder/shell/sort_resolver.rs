// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort-resolver forwarding methods for `AYEncoder`.
//!
//! These methods delegate to `SortResolverState` for type constants, sort
//! hints, view-identity dedup, closure-sort metadata, deep-model ground
//! terms, and produces-ground tracking.
//!
//! Issue: #2588

use std::collections::HashMap;

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{ExprSort, PureExpr};

#[cfg(test)]
use crate::encoder::SortResolverState;
use crate::encoder::{
    closure_sorts,
    produces_ground::{is_adapter_produces_symbol, ProducesGroundCall},
    AYEncoder,
};

impl AYEncoder {
    /// Set type-level constants for resolving `Self::MIN`, `Self::MAX`, etc.
    ///
    /// Call this before encoding specs that reference type-bound constants.
    /// The map should contain entries like `{"Self::MIN" => Int(-2147483648), "Self::MAX" => Int(2147483647)}`
    /// for the concrete integer type being verified. For wider types, values
    /// can be symbolic arithmetic expressions (e.g., `BinOp(pow2(64), Sub, Int(1))`). (#688, #2315)
    pub fn set_type_constants(&mut self, constants: HashMap<String, PureExpr>) {
        self.sort_resolver.set_type_constants(constants);
    }

    /// Look up a type-level constant through the encoder shell. (#1584)
    pub(in crate::encoder) fn type_constant(&self, name: &str) -> Option<&PureExpr> {
        self.sort_resolver.get_type_constant(name)
    }

    /// Clone a type-level constant so callers can continue encoding without
    /// holding a borrow into the sort-resolver state. (#1584)
    pub(crate) fn type_constant_cloned(&self, name: &str) -> Option<PureExpr> {
        self.type_constant(name).cloned()
    }

    /// Look up a recorded expression sort hint through the encoder shell. (#1584)
    pub(in crate::encoder) fn sort_hint(&self, name: &str) -> Option<&ExprSort> {
        self.sort_resolver.get_sort_hint(name)
    }

    /// Clone a recorded expression sort hint for use across mutable encoder work. (#1584)
    pub(in crate::encoder) fn sort_hint_cloned(&self, name: &str) -> Option<ExprSort> {
        self.sort_hint(name).cloned()
    }

    /// Check whether a name has a specific recorded sort hint. (#1584)
    pub(in crate::encoder) fn sort_hint_matches(&self, name: &str, hint: &ExprSort) -> bool {
        self.sort_hint(name) == Some(hint)
    }

    /// Check whether a sort hint exists for a name. (#1584)
    pub(in crate::encoder) fn has_sort_hint(&self, name: &str) -> bool {
        self.sort_resolver.has_sort_hint(name)
    }

    /// Remove a recorded sort hint through the encoder shell. (#1584)
    pub(in crate::encoder) fn remove_sort_hint(&mut self, name: &str) {
        self.sort_resolver.remove_sort_hint(name);
    }

    /// Check whether global sort-hint registration has already run. (#1584)
    pub(in crate::encoder) fn are_sort_hints_registered(&self) -> bool {
        self.sort_resolver.are_sort_hints_registered()
    }

    /// Mark sort hints as globally registered through the encoder shell. (#1584)
    pub(in crate::encoder) fn mark_sort_hints_registered(&mut self) {
        self.sort_resolver.mark_sort_hints_registered();
    }

    /// Check whether a view-identity axiom has already been asserted. (#1584)
    ///
    /// `pub(crate)` (not encoder-private) so mut-borrow final-value binding can
    /// detect entry-pinned base views before advancing them to a post-write
    /// state (see `verify::mut_borrow::bindings::bind_view_aliases`).
    pub(crate) fn has_view_identity(&self, name: &str) -> bool {
        self.sort_resolver.has_view_identity(name)
    }

    /// Record that a view-identity axiom has been asserted. (#1584)
    pub(in crate::encoder) fn record_view_identity(&mut self, name: String) {
        self.sort_resolver.mark_view_identity(name);
    }

    /// Clone registered closure-sort metadata through the encoder shell. (#1584)
    pub(crate) fn closure_struct_sort_cloned(
        &self,
        def_id: &str,
    ) -> Option<closure_sorts::RegisteredClosureStructSort> {
        self.sort_resolver.get_closure_struct_sort(def_id).cloned()
    }

    /// Store registered closure-sort metadata through the encoder shell. (#1584)
    pub(in crate::encoder) fn store_closure_struct_sort(
        &mut self,
        def_id: String,
        sort: closure_sorts::RegisteredClosureStructSort,
    ) {
        self.sort_resolver.insert_closure_struct_sort(def_id, sort);
    }

    /// Temporarily move out recorded deep-model ground terms. (#1584)
    pub(in crate::encoder) fn take_deep_model_ground_terms(&mut self) -> Vec<(String, Term)> {
        self.sort_resolver.take_deep_model_ground_terms()
    }

    /// Restore recorded deep-model ground terms after iteration. (#1584)
    pub(in crate::encoder) fn restore_deep_model_ground_terms(
        &mut self,
        terms: Vec<(String, Term)>,
    ) {
        self.sort_resolver.restore_deep_model_ground_terms(terms);
    }

    /// Record one deep-model ground application through the encoder shell. (#1584)
    pub(in crate::encoder) fn record_deep_model_ground_term(
        &mut self,
        smt_name: String,
        receiver: Term,
    ) {
        self.sort_resolver
            .record_deep_model_ground(smt_name, receiver);
    }

    /// Insert a produces-ground call and snapshot the tracker state without
    /// keeping the sort-resolver borrow alive across later solver work. (#1584)
    ///
    /// Returns `(is_capped, is_four_hop_disabled, is_three_hop_disabled, prior_calls, all_calls)`.
    /// `is_four_hop_disabled` is true when the call count exceeds the four-hop
    /// threshold, meaning only 2-hop and 3-hop instances should be emitted. (#3313)
    /// `is_three_hop_disabled` is true when the call count exceeds the three-hop
    /// threshold, meaning only 2-hop instances should be emitted. (#2688)
    ///
    /// For adapter-typed produces functions (Map, Filter, FilterMap, MapInv),
    /// uses tighter caps because their opaque produces definitions make ground
    /// instances less valuable than for concrete iterator types. (#2688)
    pub(in crate::encoder) fn record_produces_ground_call(
        &mut self,
        fn_symbol: &str,
        call: ProducesGroundCall,
    ) -> Option<(
        bool,
        bool,
        bool,
        Vec<ProducesGroundCall>,
        Vec<ProducesGroundCall>,
    )> {
        let tracker = self
            .sort_resolver
            .get_or_create_produces_ground(fn_symbol)?;
        if !tracker.insert(call) {
            return None;
        }
        let is_adapter = is_adapter_produces_symbol(fn_symbol);
        let is_capped = if is_adapter {
            tracker.is_adapter_capped()
        } else {
            tracker.is_capped()
        };
        let is_four_hop_disabled = if is_adapter {
            tracker.is_adapter_four_hop_disabled()
        } else {
            tracker.is_four_hop_disabled()
        };
        let is_three_hop_disabled = if is_adapter {
            tracker.is_adapter_three_hop_disabled()
        } else {
            tracker.is_three_hop_disabled()
        };
        Some((
            is_capped,
            is_four_hop_disabled,
            is_three_hop_disabled,
            tracker.prior_calls().to_vec(),
            tracker.all_calls().to_vec(),
        ))
    }

    /// Find a registered closure struct sort that matches `sort` by normalized
    /// name or by direct equality. Returns the full registration entry. (#1584)
    pub(in crate::encoder) fn find_closure_struct_by_sort(
        &self,
        sort: &Sort,
    ) -> Option<closure_sorts::RegisteredClosureStructSort> {
        let sort_name = closure_sorts::closure_env_sort_name(sort);
        self.sort_resolver
            .closure_struct_sorts_iter()
            .find(|entry| {
                let entry_name = closure_sorts::closure_env_sort_name(&entry.sort);
                (entry_name == sort_name && sort_name.is_some()) || entry.sort == *sort
            })
            .cloned()
    }

    /// Collect all registered closure struct sorts (just the `Sort` values). (#1584)
    pub(in crate::encoder) fn collect_closure_struct_sorts(&self) -> Vec<Sort> {
        self.sort_resolver
            .closure_struct_sorts_iter()
            .map(|entry| entry.sort.clone())
            .collect()
    }

    // ── Test-only accessors ────────────────────────────────────────

    /// Test-only read access to sort-resolver state for crate-root unit
    /// tests that inspect hint registration, view-identity dedup, etc. (#1584)
    #[cfg(test)]
    pub(crate) fn sort_resolver_for_test(&self) -> &SortResolverState {
        &self.sort_resolver
    }

    /// Mutable test-only access to sort-resolver state for test setup
    /// (recording hints, seeding deep-model ground terms). (#1584)
    #[cfg(test)]
    pub(crate) fn sort_resolver_mut_for_test(&mut self) -> &mut SortResolverState {
        &mut self.sort_resolver
    }
}
