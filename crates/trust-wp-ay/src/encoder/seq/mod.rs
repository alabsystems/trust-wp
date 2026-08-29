// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq (logical sequence) encoding for the ay encoder.
//!
//! This module handles:
//! - Pre-scan: identifying variables that need `Seq` sort from their usage context
//! - Declaration: creating the `Seq` uninterpreted sort and its function symbols
//! - Axioms: defining the semantics of `push_back`, `len`, `index_logic`, `sum`, `get`, and `set`
//! - Encoding: translating `Seq` method calls to ay function applications
//!
//! # Submodule layout
//!
//! - `mod.rs` — Seq sort/function infrastructure, UF projectors, receiver normalization
//! - `classification` — Method classification predicates (single source of truth)
//! - `prescan` — Pre-scan expression walkers for sort hint collection
//! - `coercion` — Sort coercion (`coerce_to_seq`) and equality decomposition
//! - `axioms` — Residual, sum, and reverse axiom assertions
//! - `constructors` — `encode_seq_singleton`, `encode_seq_push_back`, `encode_seq_empty`
//! - `operations` — Main Seq method dispatcher (`encode_seq_operation_impl`)
//!
//! # Panic isolation bypass (#1806)
//!
//! Axiom assertions in this module use `self.solver.assert_term()` directly
//! (bypassing the panic-isolated `assert_solver_term` wrapper). This is safe
//! for the same reasons documented in `axioms.rs`: all sorts are
//! solver-constructed with fixed signatures, axioms are asserted once during
//! theory setup, and revision tracking is not needed before `check_sat`.
//! Expression-encoding call sites (e.g., `assert_seq_index_logic_ground`)
//! use `assert_solver_term` for panic isolation.

mod axioms;
pub(crate) mod classification;
mod coercion;
mod constructors;
mod operations;
mod permutation;
pub(crate) mod prescan;

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
};

use ay_dpll::api::{Logic, Sort, Term, TermKind};
// Re-export classification predicates at the seq module level so existing
// callers (`use crate::encoder::seq::method_produces_seq`) continue to work.
pub(crate) use classification::{is_seq_only_method, method_produces_seq_unconditional};
pub(in crate::encoder) use coercion::sort_is_seq_iterator_carrier;
pub(crate) use operations::{
    seq_singleton_literal_arg, should_encode_singleton_prefix_concat_opaque,
};
#[cfg(test)]
pub(crate) use prescan::collect_seq_view_names;
// Re-export prescan helpers used by sort_context and sibling modules.
pub(crate) use prescan::{
    collect_view_names_as_seq, expr_produces_seq, normalize_seq_receiver_for_scan,
};
use tracing::debug;
use trust_wp_core::formula::PureExpr;

use super::{resolve_view_var_name, AYEncoder, SeqFunctions, SeqValue};
use crate::{encoder::sort_context::sort_mapping::SeqCarrier, error::EncodingError};

/// Source chosen for a receiver `len` term.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SeqLenSource {
    /// Receiver already carried a concrete SeqValue.
    ConcreteSeqValue,
    /// Receiver was coerced to a Seq carrier and the coerced term had a SeqValue.
    AliasBackedSeqValue,
    /// Receiver reused a previously selected fallback length term.
    CachedAuxLen,
    /// Receiver fell back to a fresh length term.
    AuxLenFallback,
}

impl SeqLenSource {
    fn as_str(self) -> &'static str {
        match self {
            Self::ConcreteSeqValue => "concrete_seq_value",
            Self::AliasBackedSeqValue => "alias_backed_seq_value",
            Self::CachedAuxLen => "cached_aux_len",
            Self::AuxLenFallback => "aux_len_fallback",
        }
    }
}

fn seq_alias_root(parent: &mut HashMap<Term, Term>, term: Term) -> Term {
    let parent_term = *parent.entry(term).or_insert(term);
    if parent_term == term {
        return term;
    }
    let root = seq_alias_root(parent, parent_term);
    parent.insert(term, root);
    root
}

fn union_seq_alias_terms(parent: &mut HashMap<Term, Term>, lhs: Term, rhs: Term) {
    let lhs_root = seq_alias_root(parent, lhs);
    let rhs_root = seq_alias_root(parent, rhs);
    if lhs_root != rhs_root {
        parent.insert(rhs_root, lhs_root);
    }
}

// ============================================================================
// AYEncoder impl methods for Seq infrastructure
// ============================================================================

impl AYEncoder {
    /// The model-validation gate cannot certify arbitrary ground Seq-projector
    /// applications in the ground/mixed `QF_AUFLIA`/`UFLIA`/`ALL`/`AUFLIA`
    /// lanes.
    /// Keep the public projector declarations for bound terms and trigger
    /// detection, but use one stable component proxy for every observed ground
    /// Seq term in these logics. Ground Seq equality is encoded extensionally
    /// over the same Array+Length+Offset triple, so no opaque carrier equality
    /// is needed.
    pub(crate) fn use_seq_len_proxies(&self) -> bool {
        matches!(
            self.logic(),
            Logic::QfAuflia | Logic::Uflia | Logic::All | Logic::Auflia
        )
    }

    fn observe_seq_len_component(&mut self, seq_term: Term, component: Term) -> Term {
        if let Some(anchor) = self.seq_state.get_seq_len_aux(&seq_term) {
            if anchor != component {
                let equality = self.eq_term(anchor, component);
                let guarded = self.guard_with_active_path(equality);
                self.assert_solver_term("seq_component_observation/len", guarded);
            }
            anchor
        } else {
            self.seq_state.insert_seq_len_aux(seq_term, component);
            component
        }
    }

    fn observe_seq_offset_component(&mut self, seq_term: Term, component: Term) -> Term {
        if let Some(anchor) = self.seq_state.get_seq_offset_aux(&seq_term) {
            if anchor != component {
                let equality = self.eq_term(anchor, component);
                let guarded = self.guard_with_active_path(equality);
                self.assert_solver_term("seq_component_observation/offset", guarded);
            }
            anchor
        } else {
            self.seq_state.insert_seq_offset_aux(seq_term, component);
            component
        }
    }

    fn observe_seq_array_component(&mut self, seq_term: Term, component: Term) -> Term {
        if let Some(anchor) = self.seq_state.get_seq_array_aux(&seq_term) {
            if anchor != component {
                let equality = self.eq_term(anchor, component);
                let guarded = self.guard_with_active_path(equality);
                self.assert_solver_term("seq_component_observation/array", guarded);
            }
            anchor
        } else {
            self.seq_state.insert_seq_array_aux(seq_term, component);
            component
        }
    }

    /// Get the Seq sort, creating it if needed.
    pub(crate) fn get_seq_sort(&mut self) -> Sort {
        self.seq_state.get_or_init_sort()
    }

    /// The Seq carrier every Seq-sorted term in this encoder must use.
    ///
    /// Read-only and non-forcing, so the sort plan and the domain-hint
    /// collectors can ask which spelling to mint without materializing the
    /// sort or borrowing the encoder mutably. This is the value that makes
    /// the stateless `expr_sort_to_ay_sort_for_carrier` agree with the carrier
    /// `ensure_seq_theory` declares the projectors over.
    pub(crate) fn seq_carrier(&self) -> SeqCarrier {
        self.seq_state.carrier()
    }

    pub(crate) fn force_uninterpreted_seq_sort_for_mixed_datatype(&mut self) {
        self.seq_state.force_uninterpreted_sort();
    }

    /// Put this encoder's sequences on the carrier whose proofs ay can
    /// independently certify.
    ///
    /// Changes the Seq sort's *spelling* only — every axiom `ensure_seq_theory`
    /// asserts over the native carrier is still asserted. The reason is the
    /// proof surface: `unsat_proof_references_uncheckable_seq_theory` withholds
    /// strict authority from any refutation mentioning a native `Sort::Seq(_)`
    /// term, because carcara rejects such a problem at parse time. trust-wp
    /// models every sequence operation through its own UF projectors, so the
    /// native sort buys no reasoning power and costs the certificate.
    ///
    /// This belongs to the *verification track*, not to the logic: a bare
    /// `AYEncoder::new_pure_with_quantifiers()` keeps the historical native
    /// carrier, because that constructor is also the workbench the encoder's
    /// own unit tests build Seq terms on by hand. Only the lanes that produce
    /// a proof anyone will try to check should pay the spelling change. Call
    /// it immediately after construction, before any Seq sort is handed out.
    pub(crate) fn use_certifiable_seq_carrier(&mut self) {
        self.seq_state.use_uninterpreted_carrier();
    }

    /// Ensure the Seq theory is initialized and return its function table.
    ///
    /// These functions model `Seq<T>` operations:
    /// - `seq_array`: Seq -> Array<Int, Int> (backing storage projection)
    /// - `seq_len`: Seq -> Int
    /// - `seq_offset`: Seq -> Int (logical start index into backing storage)
    /// - `seq_index_logic`: Seq x Int -> Int
    /// - `seq_push_back`: Seq x Int -> Seq
    /// - `seq_sum`: Seq -> Int
    /// - `seq_get`: Seq x Int -> Int (Option-encoded, #1882)
    /// - `seq_contains`: Seq x Int -> Bool (#699)
    /// - `seq_set`: Seq x Int x Int -> Seq (pointwise update, #969)
    #[allow(clippy::too_many_lines)]
    pub(crate) fn ensure_seq_theory(&mut self) -> SeqFunctions {
        if let Some(funcs) = self.seq_state.funcs_clone() {
            return funcs;
        }

        let seq_sort = self.get_seq_sort();

        // seq_array: Seq -> Array<Int, Int> (backing storage)
        let seq_array = self.solver.declare_fun(
            "seq_array",
            std::slice::from_ref(&seq_sort),
            Sort::array(Sort::Int, Sort::Int),
        );

        // seq_len: Seq -> Int
        let seq_len =
            self.solver
                .declare_fun("seq_len", std::slice::from_ref(&seq_sort), Sort::Int);

        // seq_offset: Seq -> Int
        let seq_offset =
            self.solver
                .declare_fun("seq_offset", std::slice::from_ref(&seq_sort), Sort::Int);

        // seq_index_logic: Seq x Int -> Int
        let seq_index_logic =
            self.solver
                .declare_fun("seq_index_logic", &[seq_sort.clone(), Sort::Int], Sort::Int);

        // seq_push_back: Seq x Int -> Seq
        let seq_push_back = self.solver.declare_fun(
            "seq_push_back",
            &[seq_sort.clone(), Sort::Int],
            seq_sort.clone(),
        );

        // seq_sum: Seq -> Int (sum of all elements)
        let seq_sum =
            self.solver
                .declare_fun("seq_sum", std::slice::from_ref(&seq_sort), Sort::Int);

        // seq_get: Seq x Int -> Int (Option-returning bounds-checked access, #1882)
        // Returns logic_Some(index_logic(s, i)) in-bounds, logic_None() out-of-bounds.
        // Options are encoded as integers with is_some/spec_unwrap testers.
        let seq_get = self
            .solver
            .declare_fun("seq_get", &[seq_sort.clone(), Sort::Int], Sort::Int);

        // seq_contains: Seq x Int -> Bool (element membership test, #699)
        let seq_contains =
            self.solver
                .declare_fun("seq_contains", &[seq_sort.clone(), Sort::Int], Sort::Bool);

        // seq_contains_pair: Seq x Int x Int -> Bool (pair membership test, #2514)
        let seq_contains_pair = self.solver.declare_fun(
            "seq_contains_pair",
            &[seq_sort.clone(), Sort::Int, Sort::Int],
            Sort::Bool,
        );

        // seq_subsequence: Seq x Int x Int -> Seq (slice extraction, #737)
        // subsequence(s, from, to) extracts s[from..to] as a new Seq.
        let seq_subsequence = self.solver.declare_fun(
            "seq_subsequence",
            &[seq_sort.clone(), Sort::Int, Sort::Int],
            seq_sort.clone(),
        );

        // seq_concat: Seq x Seq -> Seq (sequence concatenation, #379)
        let seq_concat = self.solver.declare_fun(
            "seq_concat",
            &[seq_sort.clone(), seq_sort.clone()],
            seq_sort.clone(),
        );

        // seq_singleton: Int -> Seq (single-element sequence, #379)
        let seq_singleton =
            self.solver
                .declare_fun("seq_singleton", &[Sort::Int], seq_sort.clone());

        // seq_set: Seq x Int x Int -> Seq (pointwise update, #969)
        // set(s, i, v) returns a new sequence identical to s except at index i
        // which has value v. Used for mutable slice indexing (a[2] = 3).
        let seq_set = self.solver.declare_fun(
            "seq_set",
            &[seq_sort.clone(), Sort::Int, Sort::Int],
            seq_sort.clone(),
        );

        // seq_reverse: Seq -> Seq (element reversal, #1581)
        let seq_reverse = self.solver.declare_fun(
            "seq_reverse",
            std::slice::from_ref(&seq_sort),
            seq_sort.clone(),
        );

        // seq_push_front: Seq x Int -> Seq (prepend element, #1581)
        let seq_push_front = self.solver.declare_fun(
            "seq_push_front",
            &[seq_sort.clone(), Sort::Int],
            seq_sort.clone(),
        );

        // seq_empty: Seq constant (declared before struct init so it can be stored, #737)
        let seq_empty = self.solver.declare_const("seq_empty", seq_sort.clone());

        // seq_permutation_of: Seq x Seq -> Bool (multiset equality, permutation theory)
        // Uninterpreted relation whose semantics come from the laws asserted by
        // `assert_seq_permutation_axioms` (refl/sym/trans + count-preservation).
        let seq_permutation_of = self.solver.declare_fun(
            "seq_permutation_of",
            &[seq_sort.clone(), seq_sort.clone()],
            Sort::Bool,
        );

        // seq_exchange: Seq x Seq x Int x Int -> Bool (two-element swap relation).
        // exchange(t, s, i, j) holds iff t is s with indices i and j swapped.
        let seq_exchange = self.solver.declare_fun(
            "seq_exchange",
            &[seq_sort.clone(), seq_sort.clone(), Sort::Int, Sort::Int],
            Sort::Bool,
        );

        // seq_count: Seq x Int -> Int (number of occurrences of an element, the
        // multiset-count characterization that `permutation_of` preserves).
        let seq_count =
            self.solver
                .declare_fun("seq_count", &[seq_sort.clone(), Sort::Int], Sort::Int);

        let seq_funcs = SeqFunctions {
            seq_array: seq_array.clone(),
            seq_len: seq_len.clone(),
            seq_offset: seq_offset.clone(),
            seq_index_logic: seq_index_logic.clone(),
            seq_push_back: seq_push_back.clone(),
            seq_sum: seq_sum.clone(),
            seq_get: seq_get.clone(),
            seq_contains: seq_contains.clone(),
            seq_contains_pair: seq_contains_pair.clone(),
            seq_subsequence: seq_subsequence.clone(),
            seq_concat: seq_concat.clone(),
            seq_singleton: seq_singleton.clone(),
            seq_set: seq_set.clone(),
            seq_reverse: seq_reverse.clone(),
            seq_push_front: seq_push_front.clone(),
            seq_permutation_of: seq_permutation_of.clone(),
            seq_exchange: seq_exchange.clone(),
            seq_count: seq_count.clone(),
            seq_empty,
        };
        self.seq_state.set_funcs(seq_funcs.clone());

        // Concrete empty-sequence shape: array defaults to 0, len = 0, offset = 0.
        let zero = self.solver.int_const(0);
        let empty_arr = self.solver.const_array(Sort::Int, zero);
        if self.use_seq_len_proxies() {
            self.seq_state.insert_seq_len_aux(seq_empty, zero);
            self.seq_state.insert_seq_offset_aux(seq_empty, zero);
            self.seq_state.insert_seq_array_aux(seq_empty, empty_arr);
        } else {
            let empty_len_proj = self.solver.apply(&seq_len, &[seq_empty]);
            let empty_len_eq = self.eq_term(empty_len_proj, zero);
            self.solver.assert_term(empty_len_eq);
            let empty_off_proj = self.solver.apply(&seq_offset, &[seq_empty]);
            let empty_off_eq = self.eq_term(empty_off_proj, zero);
            self.solver.assert_term(empty_off_eq);
        }

        // Register concrete SeqValue for empty sequence (#1317).
        self.insert_seq_value(
            seq_empty,
            SeqValue {
                arr: empty_arr,
                len: zero,
                offset: zero,
                known_len: Some(0),
            },
        );

        // Withheld only in a mixed native-collection lane, where ay-dpll
        // rejects the Seq carrier quantified together with the array theory.
        // This used to test the *sort spelling* instead, which silently tied
        // the axiom to the carrier: the moment a lane moved to the
        // uninterpreted carrier for proof-certifiability it also lost this
        // bridge, turning a spelling change into a reasoning-power change.
        if self.seq_state.mixed_collection_lane() {
            return seq_funcs;
        }

        // Bridge axiom: index_logic(s, i) = select(seq_array(s), seq_offset(s) + i).
        // This keeps legacy `seq_index_logic` call sites aligned with array-backed terms.
        let s = self.solver.fresh_var("seq_ax_select_s", seq_sort.clone());
        let i = self.solver.fresh_var("seq_ax_select_i", Sort::Int);
        let s_arr = self.solver.apply(&seq_array, &[s]);
        let s_off = self.solver.apply(&seq_offset, &[s]);
        let shifted = self.solver.add(s_off, i);
        let selected = self.solver.select(s_arr, shifted);
        let idx = self.solver.apply(&seq_index_logic, &[s, i]);
        let idx_select_eq = self.eq_term(idx, selected);
        // Trigger: seq_index_logic(s, i) — instantiate when index_logic applied (#1586).
        let idx_select_axiom = self
            .solver
            .forall_with_triggers(&[s, i], idx_select_eq, &[&[idx]]);
        self.solver.assert_term(idx_select_axiom);

        seq_funcs
    }

    /// Ensure Seq uninterpreted functions are declared.
    #[cfg(any(test, feature = "sep-logic"))]
    pub(super) fn ensure_seq_functions(&mut self) {
        let _ = self.ensure_seq_theory();
    }

    /// Test-only compatibility accessor for the initialized `SeqFunctions`. (#1809)
    #[cfg(test)]
    pub(crate) fn seq_funcs(&mut self) -> SeqFunctions {
        self.ensure_seq_theory()
    }

    pub(crate) fn seq_len_term(&mut self, seq_term: Term) -> Result<Term, EncodingError> {
        let (len, _source) = self.seq_len_term_with_source(seq_term)?;
        Ok(len)
    }

    /// Resolve `len(seq_term)` for equality decomposition without materializing
    /// a `SeqValue` for an otherwise-unknown receiver.
    pub(super) fn seq_len_projector_term(&mut self, seq_term: Term) -> Result<Term, EncodingError> {
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&seq_term) {
            return Ok(self.observe_seq_len_component(seq_term, sv.len));
        }
        let seq_term = self.bridge_int_to_seq_carrier(seq_term);
        let seq_term = self.coerce_to_seq(seq_term);
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&seq_term) {
            return Ok(self.observe_seq_len_component(seq_term, sv.len));
        }
        if self.quantifier_state.quantifier_depth() > 0 {
            return self.seq_len_fallback_term(seq_term);
        }
        if let Some(aux) = self.seq_state.get_seq_len_aux(&seq_term) {
            return Ok(aux);
        }
        let len_term = self.seq_len_fallback_term(seq_term)?;
        self.assert_seq_len_nonnegative(len_term);
        self.register_standard_ground_application("seq_len", len_term, vec![seq_term]);
        self.seq_state.insert_seq_len_aux(seq_term, len_term);
        Ok(len_term)
    }

    pub(crate) fn assert_seq_component_aliases_from_assertions(&mut self) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }

        for (lhs, rhs) in self.authenticated_seq_component_alias_pairs_from_assertions() {
            let lhs_text = self.solver.format_term(lhs);
            let rhs_text = self.solver.format_term(rhs);
            let dedup_key = format!("seq_component_alias/direct::{lhs_text}::{rhs_text}");
            if self.mark_logic_fn_axiom_asserted(dedup_key) {
                let eq = self.eq_term(lhs, rhs);
                self.assert_solver_term("seq_component_alias/direct", eq);
            }
        }
    }

    /// Recover Seq carrier pairs whose Array, length, and offset components
    /// are all equated by positive assertions.  Callers may use this bounded
    /// authentication graph without materializing native Seq equalities.
    pub(in crate::encoder) fn authenticated_seq_component_alias_pairs_from_assertions(
        &self,
    ) -> Vec<(Term, Term)> {
        if self.quantifier_state.quantifier_depth() != 0 {
            return Vec::new();
        }

        const ARRAY_COMPONENT: u8 = 0b001;
        const LEN_COMPONENT: u8 = 0b010;
        const OFFSET_COMPONENT: u8 = 0b100;
        const ALL_COMPONENTS: u8 = ARRAY_COMPONENT | LEN_COMPONENT | OFFSET_COMPONENT;

        let assertions = self.solver.assertions();
        let positive_assertions: HashSet<Term> = assertions.iter().copied().collect();
        let mut parent = HashMap::new();
        let mut projector_apps = Vec::new();
        for assertion in assertions {
            self.collect_positive_asserted_seq_equalities(
                assertion,
                &mut parent,
                &mut HashSet::new(),
            );
            self.collect_seq_projector_apps_from_term(
                assertion,
                &mut projector_apps,
                &mut HashSet::new(),
            );
        }
        // Finite ground projectors are fresh proxy variables, and concrete
        // SeqValues store component terms directly, so the term walker above
        // cannot recover their Seq receiver. Add both authenticated
        // component-to-receiver associations from SeqState explicitly. This
        // lets three proven component equalities expose one bounded alias pair
        // without restoring any global projector axioms.
        for (receiver, value) in self.seq_state.seq_value_entries() {
            projector_apps.push(("seq_array".to_string(), value.arr, receiver));
            projector_apps.push(("seq_len".to_string(), value.len, receiver));
            projector_apps.push(("seq_offset".to_string(), value.offset, receiver));
        }
        projector_apps.extend(
            self.seq_state
                .seq_array_aux_entries()
                .map(|(receiver, proxy)| ("seq_array".to_string(), proxy, receiver)),
        );
        projector_apps.extend(
            self.seq_state
                .seq_len_aux_entries()
                .map(|(receiver, proxy)| ("seq_len".to_string(), proxy, receiver)),
        );
        projector_apps.extend(
            self.seq_state
                .seq_offset_aux_entries()
                .map(|(receiver, proxy)| ("seq_offset".to_string(), proxy, receiver)),
        );

        let mut component_classes: HashMap<(String, Term), Vec<Term>> = HashMap::new();
        for (component, app, receiver) in projector_apps {
            let root = seq_alias_root(&mut parent, app);
            let receivers = component_classes.entry((component, root)).or_default();
            if !receivers.contains(&receiver) {
                receivers.push(receiver);
            }
        }

        let mut pair_components: HashMap<(String, String), (Term, Term, u8)> = HashMap::new();
        for ((component, _root), receivers) in component_classes {
            let bit = match component.as_str() {
                "seq_array" => ARRAY_COMPONENT,
                "seq_len" => LEN_COMPONENT,
                "seq_offset" => OFFSET_COMPONENT,
                _ => continue,
            };
            for (left_index, lhs) in receivers.iter().copied().enumerate() {
                for rhs in receivers.iter().copied().skip(left_index + 1) {
                    if lhs == rhs {
                        continue;
                    }
                    let lhs_sort = self.solver.get_sort(lhs).as_term_sort();
                    let rhs_sort = self.solver.get_sort(rhs).as_term_sort();
                    if lhs_sort != rhs_sort {
                        continue;
                    }
                    let lhs_text = self.solver.format_term(lhs);
                    let rhs_text = self.solver.format_term(rhs);
                    let (key, pair_lhs, pair_rhs) = if lhs_text <= rhs_text {
                        ((lhs_text, rhs_text), lhs, rhs)
                    } else {
                        ((rhs_text, lhs_text), rhs, lhs)
                    };
                    pair_components
                        .entry(key)
                        .and_modify(|(_, _, components)| *components |= bit)
                        .or_insert((pair_lhs, pair_rhs, bit));
                }
            }
        }

        // A symbolic semantic equality contains an empty-length disjunct, so
        // its Array/Offset leaves are intentionally not unconditional. Recover
        // the original authenticated pair only when every positive top-level
        // leaf returned by the equality encoder is currently asserted. A
        // negated goal keeps those leaves beneath `not` and cannot authenticate
        // an alias through this lane.
        for (lhs, rhs, leaves) in self.seq_state.semantic_equality_certificates() {
            if !leaves.iter().all(|leaf| positive_assertions.contains(leaf)) {
                continue;
            }
            let lhs_text = self.solver.format_term(lhs);
            let rhs_text = self.solver.format_term(rhs);
            let (key, pair_lhs, pair_rhs) = if lhs_text <= rhs_text {
                ((lhs_text, rhs_text), lhs, rhs)
            } else {
                ((rhs_text, lhs_text), rhs, lhs)
            };
            pair_components
                .entry(key)
                .and_modify(|(_, _, components)| *components = ALL_COMPONENTS)
                .or_insert((pair_lhs, pair_rhs, ALL_COMPONENTS));
        }

        pair_components
            .into_iter()
            .filter_map(|((lhs_text, rhs_text), (lhs, rhs, components))| {
                (components == ALL_COMPONENTS
                    && !Self::seq_alias_crosses_temporal_final_boundary(&lhs_text, &rhs_text))
                .then_some((lhs, rhs))
            })
            .collect()
    }

    fn seq_alias_crosses_temporal_final_boundary(lhs_text: &str, rhs_text: &str) -> bool {
        let lhs_final = Self::term_text_mentions_temporal_final(lhs_text);
        let rhs_final = Self::term_text_mentions_temporal_final(rhs_text);
        lhs_final ^ rhs_final
    }

    fn term_text_mentions_temporal_final(term_text: &str) -> bool {
        term_text.contains("_final") || term_text.contains("final_")
    }

    fn collect_positive_asserted_seq_equalities(
        &self,
        term: Term,
        parent: &mut HashMap<Term, Term>,
        seen: &mut HashSet<Term>,
    ) {
        if !seen.insert(term) {
            return;
        }
        match self.solver.term_kind(term) {
            TermKind::App { name, num_args: 2 } if name == "=" => {
                let children = self.solver.term_children(term);
                if let [lhs, rhs] = children.as_slice() {
                    union_seq_alias_terms(parent, *lhs, *rhs);
                }
            }
            TermKind::App { name, .. } if name == "and" => {
                for child in self.solver.term_children(term) {
                    self.collect_positive_asserted_seq_equalities(child, parent, seen);
                }
            }
            _ => {}
        }
    }

    fn collect_seq_projector_apps_from_term(
        &self,
        term: Term,
        out: &mut Vec<(String, Term, Term)>,
        seen: &mut HashSet<Term>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let Some((component, receiver)) = self.seq_projector_app_receiver(term) {
            out.push((component, term, receiver));
        }
        for child in self.solver.term_children(term) {
            self.collect_seq_projector_apps_from_term(child, out, seen);
        }
    }

    fn seq_projector_app_receiver(&self, term: Term) -> Option<(String, Term)> {
        let TermKind::App { name, num_args: 1 } = self.solver.term_kind(term) else {
            return None;
        };
        if !matches!(name.as_str(), "seq_array" | "seq_len" | "seq_offset") {
            return None;
        }
        let children = self.solver.term_children(term);
        let [receiver] = children.as_slice() else {
            return None;
        };
        Some((name, *receiver))
    }

    fn seq_len_fallback_term(&mut self, seq_term: Term) -> Result<Term, EncodingError> {
        if self.use_seq_len_proxies() && self.quantifier_state.quantifier_depth() == 0 {
            return Ok(self.solver.fresh_var("seq_len_proxy", Sort::Int));
        }
        let seq_len = self.ensure_seq_theory().seq_len.clone();
        self.safe_apply("seq_len", &seq_len, &[seq_term])
    }

    /// Resolve `len(seq_term)` and return the source used for the receiver.
    pub(crate) fn seq_len_term_with_source(
        &mut self,
        seq_term: Term,
    ) -> Result<(Term, SeqLenSource), EncodingError> {
        // Fast path: concrete Seq value in registry — return len directly (#1317).
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&seq_term) {
            let len = self.observe_seq_len_component(seq_term, sv.len);
            debug!(
                "[TRUST_WP_DEBUG] seq_len_term source={} seq_term={seq_term:?} len={:?}",
                SeqLenSource::ConcreteSeqValue.as_str(),
                len
            );
            return Ok((len, SeqLenSource::ConcreteSeqValue));
        }
        // Coerce fallback Int carriers and Vec-sorted terms to Seq before
        // applying UF projectors (#2124, Slot 7I).
        let original_seq_term = seq_term;
        let seq_term = self.bridge_int_to_seq_carrier(seq_term);
        let seq_term = self.coerce_to_seq(seq_term);
        // Re-check registry after coercion (coerced term may have a SeqValue).
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&seq_term) {
            let source = if seq_term == original_seq_term {
                SeqLenSource::ConcreteSeqValue
            } else {
                SeqLenSource::AliasBackedSeqValue
            };
            let len = self.observe_seq_len_component(seq_term, sv.len);
            debug!(
                "[TRUST_WP_DEBUG] seq_len_term source={} original_seq_term={original_seq_term:?} seq_term={seq_term:?} len={:?}",
                source.as_str(),
                len
            );
            return Ok((len, source));
        }
        // Quantified logic-function bodies must keep the receiver-dependent
        // `seq_len(seq)` application. A fresh ALL-logic proxy here would be a
        // single constant captured by the quantified axiom instead of a length
        // that depends on the quantified receiver.
        if self.quantifier_state.quantifier_depth() > 0 {
            let len_term = self.seq_len_fallback_term(seq_term)?;
            debug!(
                "[TRUST_WP_DEBUG] seq_len_term source={} seq_term={seq_term:?} len_term={len_term:?} quantifier_depth={}",
                SeqLenSource::AuxLenFallback.as_str(),
                self.quantifier_state.quantifier_depth()
            );
            return Ok((len_term, SeqLenSource::AuxLenFallback));
        }
        // Cached auxiliary variable for this seq_term (#2323).
        if let Some(aux) = self.seq_state.get_seq_len_aux(&seq_term) {
            debug!(
                "[TRUST_WP_DEBUG] seq_len_term source={} seq_term={seq_term:?} aux={aux:?}",
                SeqLenSource::CachedAuxLen.as_str()
            );
            return Ok((aux, SeqLenSource::CachedAuxLen));
        }
        // Fallback: choose the Int term used for unknown Seq receiver lengths.
        //
        // We still cache the chosen Int term so later arithmetic sees a stable
        // source. In finite-projector logics this is a component proxy; in
        // narrower logics it remains the `seq_len` UF.
        let len_term = self.seq_len_fallback_term(seq_term)?;
        self.assert_seq_len_nonnegative(len_term);
        // Register ground application for standard axiom instantiation (#2288).
        self.register_standard_ground_application("seq_len", len_term, vec![seq_term]);
        self.seq_state.insert_seq_len_aux(seq_term, len_term);
        let arr = self.seq_array_term(seq_term)?;
        let offset = self.seq_offset_term(seq_term)?;
        self.insert_seq_value(
            seq_term,
            SeqValue {
                arr,
                len: len_term,
                offset,
                known_len: None,
            },
        );
        debug!(
            "[TRUST_WP_DEBUG] seq_len_term source={} seq_term={seq_term:?} len_term={len_term:?}",
            SeqLenSource::AuxLenFallback.as_str(),
        );
        Ok((len_term, SeqLenSource::AuxLenFallback))
    }

    fn assert_seq_len_nonnegative(&mut self, len_term: Term) {
        let zero = self.solver.int_const(0);
        let nonnegative = self.solver.ge(len_term, zero);
        let guarded = self.guard_with_active_path(nonnegative);
        self.assert_solver_term("seq_len_nonnegative_ground", guarded);
    }

    pub(super) fn seq_array_term(&mut self, seq_term: Term) -> Result<Term, EncodingError> {
        // Fast path: concrete Seq value in registry (#1317).
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&seq_term) {
            return Ok(self.observe_seq_array_component(seq_term, sv.arr));
        }
        let seq_term = self.bridge_int_to_seq_carrier(seq_term);
        let seq_term = self.coerce_to_seq(seq_term);
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&seq_term) {
            return Ok(self.observe_seq_array_component(seq_term, sv.arr));
        }
        // In finite-projector logic, use one stable Array component per
        // observed ground Seq term. Ground Seq equality is defined over the
        // complete component triple, so a second raw-carrier congruence axiom
        // would be redundant and would make the independent SAT gate unable to
        // validate an otherwise first-order Array/Int base.
        if self.use_seq_len_proxies() && self.quantifier_state.quantifier_depth() == 0 {
            if let Some(aux) = self.seq_state.get_seq_array_aux(&seq_term) {
                return Ok(aux);
            }
            let array_sort = Sort::array(Sort::Int, Sort::Int);
            let aux = self.solver.fresh_var("seq_array_proxy", array_sort);
            self.seq_state.insert_seq_array_aux(seq_term, aux);
            return Ok(aux);
        }

        // Bound and non-finite contexts retain the conservative UF projector.
        let seq_array = self.ensure_seq_theory().seq_array.clone();
        self.safe_apply("seq_array", &seq_array, &[seq_term])
    }

    pub(super) fn seq_offset_term(&mut self, seq_term: Term) -> Result<Term, EncodingError> {
        // Fast path: concrete Seq value in registry (#1317).
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&seq_term) {
            return Ok(self.observe_seq_offset_component(seq_term, sv.offset));
        }
        let seq_term = self.bridge_int_to_seq_carrier(seq_term);
        let seq_term = self.coerce_to_seq(seq_term);
        if let Some(sv) = self.seq_state.get_seq_value_cloned(&seq_term) {
            return Ok(self.observe_seq_offset_component(seq_term, sv.offset));
        }
        if self.use_seq_len_proxies() && self.quantifier_state.quantifier_depth() == 0 {
            if let Some(aux) = self.seq_state.get_seq_offset_aux(&seq_term) {
                return Ok(aux);
            }
            let aux = self.solver.fresh_var("seq_offset_proxy", Sort::Int);
            self.seq_state.insert_seq_offset_aux(seq_term, aux);
            return Ok(aux);
        }

        // Bound and non-finite contexts retain the conservative UF projector.
        let seq_offset = self.ensure_seq_theory().seq_offset.clone();
        self.safe_apply("seq_offset", &seq_offset, &[seq_term])
    }

    pub(super) fn seq_index_term(
        &mut self,
        seq_term: Term,
        index_term: Term,
    ) -> Result<Term, EncodingError> {
        if let Some(result) = self.seq_concat_index_term(seq_term, index_term)? {
            return Ok(result);
        }

        // Fast path: concrete Seq value in registry — direct select (#1317).
        if let Some(sv) = self.seq_state.get_seq_value(&seq_term) {
            let arr = sv.arr;
            let off = sv.offset;
            // Guard: index_term must be Int-sorted. A Seq-sorted index indicates
            // a Mapping/predicate lookup misrouted as Seq indexing (#1554).
            let shifted =
                super::type_resolve::catch_solver_panic_with_reason("seq_index_term:add", || {
                    self.solver.add(off, index_term)
                })
                .map_err(|err| {
                    EncodingError::solver_error(format!(
                        "seq_index_term: index argument has wrong sort \
                     (expected Int for Seq indexing): {}",
                        err.reason()
                    ))
                })?;
            let select_result = self.solver.select(arr, shifted);
            self.seq_state
                .insert_seq_index_source(select_result, (seq_term, index_term));
            let result =
                self.prefer_seq_index_logic_ground_term(seq_term, index_term, select_result);
            self.assert_registered_container_element_invariants_for_index(
                seq_term, index_term, result,
            )?;
            self.assert_ext_eq_ground_index_consequences(seq_term, index_term)?;
            return Ok(result);
        }
        // Fallback: use UF projectors.
        let arr = self.seq_array_term(seq_term)?;
        let off = self.seq_offset_term(seq_term)?;
        // Guard: same sort validation as fast path (#1554).
        let shifted =
            super::type_resolve::catch_solver_panic_with_reason("seq_index_term:add", || {
                self.solver.add(off, index_term)
            })
            .map_err(|err| {
                EncodingError::solver_error(format!(
                    "seq_index_term: index argument has wrong sort \
                 (expected Int for Seq indexing): {}",
                    err.reason()
                ))
            })?;
        let select_result = self.solver.select(arr, shifted);
        self.seq_state
            .insert_seq_index_source(select_result, (seq_term, index_term));
        let result = self.prefer_seq_index_logic_ground_term(seq_term, index_term, select_result);
        self.assert_registered_container_element_invariants_for_index(
            seq_term, index_term, result,
        )?;
        self.assert_ext_eq_ground_index_consequences(seq_term, index_term)?;
        Ok(result)
    }

    fn seq_concat_index_term(
        &mut self,
        seq_term: Term,
        index_term: Term,
    ) -> Result<Option<Term>, EncodingError> {
        let Some((left, right)) = self.seq_state.get_seq_concat_args(&seq_term) else {
            return Ok(None);
        };

        if self.solver.term_sort(index_term) != Sort::Int {
            return Err(EncodingError::solver_error(
                "seq_index_term: index argument has wrong sort \
                 (expected Int for Seq indexing)",
            ));
        }

        let left_len = self.seq_len_term(left)?;
        let in_left = self.solver.lt(index_term, left_len);
        let left_value = self.seq_index_term(left, index_term)?;
        let right_index = self.solver.sub(index_term, left_len);
        let right_value = self.seq_index_term(right, right_index)?;
        let result = self.solver.ite(in_left, left_value, right_value);

        self.seq_state
            .insert_seq_index_source(result, (seq_term, index_term));
        self.assert_registered_container_element_invariants_for_index(
            seq_term, index_term, result,
        )?;
        self.assert_ext_eq_ground_index_consequences(seq_term, index_term)?;
        Ok(Some(result))
    }

    /// Return a UF-backed ground index term when trigger support is enabled.
    ///
    /// When `seq_index_term` produces an Array `select(arr, offset + idx)`,
    /// the `seq_index_logic` UF application is absent from the E-graph. This
    /// means quantifiers triggered on `seq_index_logic(view, i)` (container
    /// element invariants, bridge axioms) never fire. Asserting the ground
    /// equality introduces the UF term, but the caller still returns the Array
    /// `select` result. In the container-invariant lane that leaves the goal on
    /// `get_k(select(...))`, which ay-dpll may fail to match back to the trigger
    /// term in the same round. Returning the UF application keeps the goal on
    /// the triggerable term while the asserted equality preserves Array-backed
    /// semantics. (#2438)
    ///
    /// Only enabled when `needs_index_ground_terms` is set (by container
    /// element invariant assertion or related bridge synthesis) to avoid
    /// performance regressions in contexts that do not need UF-triggered
    /// quantifier matching.
    fn prefer_seq_index_logic_ground_term(
        &mut self,
        seq_term: Term,
        index_term: Term,
        select_result: Term,
    ) -> Term {
        if !self.seq_state.needs_index_ground_terms() {
            return select_result;
        }
        let seq_term = self.bridge_int_to_seq_carrier(seq_term);
        let seq_term = self.coerce_to_seq(seq_term);
        if let Some(funcs) = self.seq_state.funcs() {
            let seq_idx_fn = funcs.seq_index_logic.clone();
            let uf_app = self.solver.apply(&seq_idx_fn, &[seq_term, index_term]);
            let eq = self.eq_term(uf_app, select_result);
            self.assert_solver_term("seq_index_logic_ground", eq);
            self.seq_state
                .insert_seq_index_source(uf_app, (seq_term, index_term));
            return uf_app;
        }
        select_result
    }

    pub(crate) fn assert_seq_shape_constraints(
        &mut self,
        seq_term: Term,
        array_term: Term,
        len_term: Term,
        offset_term: Term,
        context: &str,
    ) -> Result<(), EncodingError> {
        // Coerce Vec-sorted terms to Seq before applying UF projectors (#2124).
        let seq_term = self.bridge_int_to_seq_carrier(seq_term);
        let seq_term = self.coerce_to_seq(seq_term);
        let arr_proj = self.seq_array_term(seq_term)?;
        let len_proj = if self.use_seq_len_proxies() {
            self.seq_len_term(seq_term)?
        } else {
            let seq_len = self.ensure_seq_theory().seq_len.clone();
            self.safe_apply(&format!("{context}:seq_len"), &seq_len, &[seq_term])?
        };
        let off_proj = self.seq_offset_term(seq_term)?;

        let arr_eq = self.eq_term(arr_proj, array_term);
        let arr_guarded = self.guard_with_active_path(arr_eq);
        self.assert_term(arr_guarded);

        let len_eq = self.eq_term(len_proj, len_term);
        let len_guarded = self.guard_with_active_path(len_eq);
        self.assert_term(len_guarded);

        let off_eq = self.eq_term(off_proj, offset_term);
        let off_guarded = self.guard_with_active_path(off_eq);
        self.assert_term(off_guarded);

        Ok(())
    }

    /// Ensure Seq methods are encoded against a logical view.
    ///
    /// Delegates to the free function `normalize_seq_receiver_for_scan` to
    /// maintain a single implementation. Any method name updates only need
    /// to happen in one place.
    pub(super) fn normalize_seq_receiver(receiver: &PureExpr) -> Cow<'_, PureExpr> {
        normalize_seq_receiver_for_scan(receiver)
    }
}
