// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Remaining shell accessors for small state owners: quantifier, seq, ADT.
//!
//! These methods forward into `QuantifierState`, `SeqState`, and `AdtState`.
//!
//! Issue: #2588

use ay_dpll::api::Term;
use trust_wp_core::{
    formula::PureExpr,
    logic::{AdtCtorFieldRanges, AdtFieldRanges},
};

use crate::encoder::{AYEncoder, ContainerElementInvariantSpec, SeqFunctions, SeqValue};
#[cfg(test)]
use crate::encoder::{SeqState, SynthesizedTriggerDiagnostic};

impl AYEncoder {
    // ── quantifier_state boundary helpers (#1584) ──────────────────

    /// Check if a variable is currently bound in a quantifier scope.
    pub(crate) fn is_quantifier_bound(&self, name: &str) -> bool {
        self.quantifier_state.is_bound(name)
    }

    /// Check if any variables are currently bound in a quantifier scope.
    pub(crate) fn has_bound_quantifier_vars(&self) -> bool {
        self.quantifier_state.has_bound_vars()
    }

    /// Allocate the next unique quantifier variable ID.
    pub(crate) fn next_quantifier_var_id(&mut self) -> usize {
        self.quantifier_state.next_id()
    }

    /// Record a variable as bound in a quantifier scope.
    pub(crate) fn bind_quantifier_var(&mut self, name: String) -> usize {
        self.quantifier_state.bind_var(name)
    }

    /// Decrement the binding depth of a variable; removes when depth reaches 0.
    pub(crate) fn unbind_quantifier_var(&mut self, name: &str) {
        self.quantifier_state.unbind_var(name);
    }

    /// Record a variable as a match-arm pattern binder (Fix A guard scope).
    pub(crate) fn bind_match_binder_var(&mut self, name: String) {
        self.quantifier_state.bind_match_binder(name);
    }

    /// Decrement the match-binder depth of a variable.
    pub(crate) fn unbind_match_binder_var(&mut self, name: &str) {
        self.quantifier_state.unbind_match_binder(name);
    }

    /// Check if a variable is currently a match-arm pattern binder.
    pub(crate) fn is_match_binder_var(&self, name: &str) -> bool {
        self.quantifier_state.is_match_binder(name)
    }

    /// The innermost written `forall`/`exists` binding of `name`, with the
    /// sort the text wrote for it.
    pub(crate) fn written_binder_sort(
        &self,
        name: &str,
    ) -> Option<crate::encoder::state::WrittenBinderSort<'_>> {
        self.quantifier_state.written_binder(name)
    }

    /// Record synthesized trigger patterns used for one quantifier.
    pub(crate) fn record_synthesized_triggers(
        &mut self,
        vars: &[String],
        patterns: &[Vec<PureExpr>],
    ) {
        self.quantifier_state
            .record_synthesized_triggers(vars, patterns);
    }

    /// Return synthesized-trigger diagnostics from the most recent top-level encode.
    #[cfg(test)]
    pub(crate) fn synthesized_triggers(&self) -> &[SynthesizedTriggerDiagnostic] {
        self.quantifier_state.synthesized_triggers()
    }

    // ── seq_state boundary helpers (#1584) ──────────────────────────

    /// Test-only read access to Seq state for crate-root unit tests. (#1584)
    #[cfg(test)]
    pub(crate) fn seq_state_for_test(&self) -> &SeqState {
        &self.seq_state
    }

    /// Mutable test-only access to Seq state for focused test setup. (#1584)
    #[cfg(test)]
    pub(crate) fn seq_state_mut_for_test(&mut self) -> &mut SeqState {
        &mut self.seq_state
    }

    /// Check whether a term has a concrete SeqValue registered.
    pub(crate) fn has_seq_value(&self, term: Term) -> bool {
        self.seq_state.has_seq_value(&term)
    }

    /// Look up and clone a concrete SeqValue by term.
    pub(crate) fn get_seq_value_cloned(&self, term: Term) -> Option<SeqValue> {
        self.seq_state.get_seq_value_cloned(&term)
    }

    /// Register a concrete SeqValue without changing component identities that
    /// have already escaped into the current VC.
    ///
    /// An unknown ground Seq is first represented by stable finite projector
    /// proxies. Later encoding can discover an exact constructor/operation
    /// representation for the same carrier. Replacing the registry entry at
    /// that point would make an earlier `len(s)` (or array/offset projection)
    /// denote a different SMT term from a later one. Keep the first component
    /// triple as the carrier identity and equate every refinement to it under
    /// the active path.
    pub(crate) fn insert_seq_value(&mut self, term: Term, value: SeqValue) {
        let existing = self.seq_state.get_seq_value_cloned(&term);
        let branch_local = self.has_active_path_conditions();
        let value_arr_sort = self.solver.get_sort(value.arr);
        // A registered SeqValue is already available to internal shape
        // synthesis even before a public projector accessor is called, so its
        // components must be treated as observed. Falling back to the explicit
        // auxiliary maps covers a projector that escaped before the first
        // SeqValue was registered. A first value discovered inside an ITE arm
        // is not a global identity: allocate an unguarded neutral carrier proxy
        // and relate the arm's value to it only through the active path.
        let anchor_arr = existing
            .as_ref()
            .map_or_else(
                || self.seq_state.get_seq_array_aux(&term),
                |sv| Some(sv.arr),
            )
            .unwrap_or_else(|| {
                if branch_local {
                    self.solver
                        .fresh_var("seq_array_branch_proxy", value_arr_sort.clone())
                } else {
                    value.arr
                }
            });
        let anchor_len = existing
            .as_ref()
            .map_or_else(|| self.seq_state.get_seq_len_aux(&term), |sv| Some(sv.len))
            .unwrap_or_else(|| {
                if branch_local {
                    self.solver
                        .fresh_var("seq_len_branch_proxy", ay_dpll::api::Sort::Int)
                } else {
                    value.len
                }
            });
        let anchor_offset = existing
            .as_ref()
            .map_or_else(
                || self.seq_state.get_seq_offset_aux(&term),
                |sv| Some(sv.offset),
            )
            .unwrap_or_else(|| {
                if branch_local {
                    self.solver
                        .fresh_var("seq_offset_branch_proxy", ay_dpll::api::Sort::Int)
                } else {
                    value.offset
                }
            });

        if branch_local && existing.is_none() {
            self.seq_state.insert_seq_array_aux(term, anchor_arr);
            self.seq_state.insert_seq_len_aux(term, anchor_len);
            self.seq_state.insert_seq_offset_aux(term, anchor_offset);
        }

        for (label, anchor, refinement) in [
            ("seq_value_refinement/array", anchor_arr, value.arr),
            ("seq_value_refinement/len", anchor_len, value.len),
            ("seq_value_refinement/offset", anchor_offset, value.offset),
        ] {
            if anchor == refinement {
                continue;
            }
            let equality = self.eq_term(anchor, refinement);
            let guarded = self.guard_with_active_path(equality);
            self.assert_solver_term(label, guarded);
        }

        // `known_len` is compile-time metadata, not a solver identity.  An
        // unconditional exact refinement may therefore improve an earlier
        // proxy-only entry without changing any escaped SMT term.  Conversely,
        // a fact learned in one branch must never become global metadata.
        let known_len = if branch_local {
            existing.as_ref().and_then(|previous| previous.known_len)
        } else {
            match (
                existing.as_ref().and_then(|previous| previous.known_len),
                value.known_len,
            ) {
                (None, refinement) => refinement,
                (Some(previous), None) => Some(previous),
                (Some(previous), Some(refinement)) if previous == refinement => Some(previous),
                (Some(_), Some(_)) => None,
            }
        };
        self.seq_state.insert_seq_value(
            term,
            SeqValue {
                arr: anchor_arr,
                len: anchor_len,
                offset: anchor_offset,
                known_len,
            },
        );
    }

    /// Enable ground `seq_index_logic` UF equality assertions.
    pub(crate) fn set_needs_seq_index_ground_terms(&mut self) {
        self.seq_state.set_needs_index_ground_terms();
    }

    /// Borrow the Seq functions (returns `None` if not yet initialized).
    pub(crate) fn seq_funcs_ref(&self) -> Option<&SeqFunctions> {
        self.seq_state.funcs()
    }

    /// Clone the Seq functions (returns `None` if not yet initialized).
    pub(crate) fn seq_funcs_clone(&self) -> Option<SeqFunctions> {
        self.seq_state.funcs_clone()
    }

    /// Register a shared container-element invariant for a Seq view term.
    pub(crate) fn register_container_element_invariant(
        &mut self,
        seq_term: Term,
        spec: ContainerElementInvariantSpec,
    ) {
        self.seq_state
            .register_container_element_invariant(seq_term, spec);
    }

    // ── adt_state boundary helpers (#1584) ──────────────────────────

    /// Set ADT field range constraints (called during verification setup).
    pub(crate) fn set_adt_field_ranges(&mut self, ranges: AdtFieldRanges) {
        self.adt_state.set_field_ranges(ranges);
    }

    /// Look up field range constraints for a datatype by name (cloned to avoid borrow).
    pub(crate) fn adt_field_ranges_for(&self, name: &str) -> Option<AdtCtorFieldRanges> {
        self.adt_state.field_ranges_for(name).cloned()
    }

    /// Non-cloning existence check for field-range hints; used on the hot
    /// variable-binding path (`rebind_var`) before any layout lookup.
    pub(crate) fn has_adt_field_ranges(&self, name: &str) -> bool {
        self.adt_state.field_ranges_for(name).is_some()
    }
}
