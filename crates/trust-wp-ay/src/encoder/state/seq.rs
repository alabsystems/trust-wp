// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ay_dpll::api::{FuncDecl, Sort, Term};
use trust_wp_core::formula::PureExpr;

use crate::encoder::sort_context::sort_mapping::SeqCarrier;

/// Concrete Array+Length+Offset representation of a Seq value (#1317).
///
/// Instead of relying on uninterpreted function projectors (`seq_array`,
/// `seq_len`, `seq_offset`) and quantified axioms that ay-dpll cannot chain,
/// the encoder tracks concrete `(arr, len, offset)` components for each
/// known Seq term. Operations like `seq_len` and `seq_index` consult this
/// registry first, falling back to UF projectors only for unknown terms.
///
/// See `designs/2026-02-14-seq-array-encoding-alternative.md` (EXECUTE).
#[derive(Clone, Debug)]
pub(crate) struct SeqValue {
    /// Backing array: `Array<Int, Int>`.
    pub(crate) arr: Term,
    /// Logical length: `Int`.
    pub(crate) len: Term,
    /// Logical offset into `arr` (0 for non-subsequence terms): `Int`.
    pub(crate) offset: Term,
    /// Known concrete length (when the length is a compile-time constant).
    ///
    /// Set by `encode_seq_literal_as_fresh_constant` for seq literals. When
    /// present, `try_decompose_seq_equality` uses pointwise `select`
    /// comparisons instead of Array extensional equality, avoiding ay-dpll's
    /// Array theory timeout on negated array equalities (#2242).
    pub(crate) known_len: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ContainerElementInvariantSpec {
    Method { element_invariant_method: String },
    Body { self_param: String, body: PureExpr },
}

/// Mutation footprint retained for finite, ground `resolve_elsewhere`
/// consequences.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ResolveElsewhereFootprint {
    Index(Term),
    RangeInclusive { start: Term, end: Term },
}

/// One encoded `SliceIndexSpec::resolve_elsewhere` predicate.
///
/// `predicate` is the fresh conservative monitor used only in the
/// quantifier-free lane.  `predicate => ground_instance` is valid for every
/// authenticated observed index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ResolveElsewhereFrame {
    pub(crate) predicate: Term,
    pub(crate) old_seq: Term,
    pub(crate) new_seq: Term,
    pub(crate) old_len: Term,
    pub(crate) footprint: ResolveElsewhereFootprint,
}

/// Seq sort and function declaration state (#840).
///
/// Groups the lazy-initialized Seq sort and uninterpreted functions used
/// primarily by `seq.rs`, with read access from `mod.rs` for `ext_eq`
/// and `produces` encoding.
///
/// All fields private; access through typed methods (#1584).
pub(crate) struct SeqState {
    /// Seq sort (lazy initialized when needed).
    sort: Option<Sort>,
    /// Whether this encoder is a mixed native-collection lane, where ay-dpll
    /// rejects a Seq carrier quantified together with the array theory.
    ///
    /// Deliberately separate from the carrier. These were one flag until the
    /// carrier became a proof-surface decision: `ensure_seq_theory` decided
    /// whether to assert the `index_logic(s, i) = select(seq_array(s),
    /// seq_offset(s) + i)` bridge by *looking at the sort spelling*, so any
    /// lane that moved to the uninterpreted carrier for certifiability
    /// silently lost that axiom too. Which sort carries a sequence and which
    /// axioms are sound to assert about it are independent questions.
    mixed_collection_lane: bool,
    /// Seq uninterpreted functions (lazy initialized via `ensure_seq_theory`).
    funcs: Option<SeqFunctions>,
    /// Registry mapping concrete Seq terms to their Array+Length+Offset components (#1317).
    seq_values: HashMap<Term, SeqValue>,
    /// When true, `seq_index_term` asserts ground `seq_index_logic` UF equalities
    /// alongside Array select results (#1575).
    needs_index_ground_terms: bool,
    /// Whether sum-specific Seq axioms (6-7) have been asserted.
    sum_axioms_asserted: bool,
    /// Whether get-specific Seq axioms (8a-8b) have been asserted.
    get_axioms_asserted: bool,
    /// Whether contains-specific Seq axioms (9-10) have been asserted.
    contains_axioms_asserted: bool,
    /// Whether concat-specific Seq axioms and push bridges have been asserted.
    concat_axioms_asserted: bool,
    /// Whether reverse-specific Seq axioms have been asserted (#1581).
    reverse_axioms_asserted: bool,
    /// Whether permutation/multiset-specific Seq axioms have been asserted.
    permutation_axioms_asserted: bool,
    /// Cache of Vec-sorted terms coerced to Seq sort (#2124).
    coerced_terms: HashMap<Term, Term>,
    /// Bridge UF functions for Vec-like sort -> Seq coercion (#2124).
    bridge_fns: HashMap<String, FuncDecl>,
    /// Original non-Int sort for Seq element bridge outputs (#2316).
    seq_elem_sorts: HashMap<Term, Sort>,
    /// Exact original term for a Seq element bridge output (#2316).
    seq_elem_sources: HashMap<Term, Term>,
    /// Provenance for Int-sorted `seq.index_logic(i)` terms (#2316).
    seq_index_sources: HashMap<Term, (Term, Term)>,
    /// Encoded `resolve_elsewhere` predicates awaiting finite consequences at
    /// the ground indices that the current VC actually observes.
    resolve_elsewhere_frames: Vec<ResolveElsewhereFrame>,
    /// Stable conservative equality monitors for symbolic temporal post-state
    /// Seq assignments. Each monitor is certified in the forward direction:
    /// `monitor => exact Array+Length+Offset equality`.
    certified_equality_monitors: Vec<(Term, Term, Term)>,
    /// Positive formula leaves that certify semantic equality for a Seq pair.
    semantic_equality_certificates: Vec<(Term, Term, Vec<Term>)>,
    /// Shared container-element invariants keyed by the concrete Seq view term.
    container_element_invariants: HashMap<Term, Vec<ContainerElementInvariantSpec>>,
    /// Per-sort UFs that reconstruct a typed element from `(seq, index)`.
    seq_index_restore_fns: HashMap<String, FuncDecl>,
    /// Counter for fresh seq literal constants (#2242).
    fresh_seq_lit_counter: u32,
    /// Cached Int terms chosen for `seq_len` fallback results (#2323).
    ///
    /// In finite-projector logics these are component proxies, one per
    /// observed ground receiver. In other logics they cache the direct UF
    /// application so later lookups still have a stable receiver-specific
    /// source.
    seq_len_aux_vars: HashMap<Term, Term>,
    /// Finite component proxies for observed ground `seq_offset(seq)` terms.
    seq_offset_aux_vars: HashMap<Term, Term>,
    /// Finite component proxies for observed ground `seq_array(seq)` terms.
    seq_array_aux_vars: HashMap<Term, Term>,
    /// Arguments for encoded concat terms.
    ///
    /// Symbolic concat cannot be represented as one finite store-chain array.
    /// Keeping the operands lets `seq_index_term` encode observed concat
    /// indexes directly as left/right conditional reads.
    seq_concat_args: HashMap<Term, (Term, Term)>,
    /// Auxiliary Int variables for general Int-returning UF applications (#2323).
    ///
    /// Maps a UF application term (e.g., `method_start_log_1_Seq(iter)`) to
    /// an auxiliary Int constant. Used by `encode_int_method_uf` and similar
    /// UF-generating paths to keep UF terms out of LIA arithmetic. Stored
    /// here alongside `seq_len_aux_vars` to reuse the fresh-name counter.
    uf_int_aux_vars: HashMap<Term, Term>,
    /// len==0 base carrier names whose push_back chain has already been
    /// reconstructed into a ground store-chain (#1317 pre-seed). Lets the
    /// post-encoding reconstruction pass skip a base that the pre-encoding
    /// pre-seed already materialized, so the same ground shape constraints
    /// are not asserted twice.
    reconstructed_chain_bases: std::collections::HashSet<String>,
}

#[allow(clippy::trivially_copy_pass_by_ref)] // Term accessors mirror HashMap::get(&K) convention
impl SeqState {
    pub(crate) fn new() -> Self {
        Self {
            sort: None,
            mixed_collection_lane: false,
            funcs: None,
            seq_values: HashMap::new(),
            needs_index_ground_terms: false,
            sum_axioms_asserted: false,
            get_axioms_asserted: false,
            contains_axioms_asserted: false,
            concat_axioms_asserted: false,
            reverse_axioms_asserted: false,
            permutation_axioms_asserted: false,
            coerced_terms: HashMap::new(),
            bridge_fns: HashMap::new(),
            seq_elem_sorts: HashMap::new(),
            seq_elem_sources: HashMap::new(),
            seq_index_sources: HashMap::new(),
            resolve_elsewhere_frames: Vec::new(),
            certified_equality_monitors: Vec::new(),
            semantic_equality_certificates: Vec::new(),
            container_element_invariants: HashMap::new(),
            seq_index_restore_fns: HashMap::new(),
            fresh_seq_lit_counter: 0,
            seq_len_aux_vars: HashMap::new(),
            seq_offset_aux_vars: HashMap::new(),
            seq_array_aux_vars: HashMap::new(),
            seq_concat_args: HashMap::new(),
            uf_int_aux_vars: HashMap::new(),
            reconstructed_chain_bases: std::collections::HashSet::new(),
        }
    }

    /// Record that the push_back chain rooted at `base_name` has been
    /// reconstructed into a ground store-chain. Returns `true` if the base
    /// was newly inserted (i.e., not already reconstructed). (#1317 pre-seed)
    pub(crate) fn mark_reconstructed_chain_base(&mut self, base_name: &str) -> bool {
        self.reconstructed_chain_bases.insert(base_name.to_string())
    }

    /// Whether the push_back chain rooted at `base_name` has already been
    /// reconstructed into a ground store-chain. (#1317 pre-seed)
    pub(crate) fn chain_base_reconstructed(&self, base_name: &str) -> bool {
        self.reconstructed_chain_bases.contains(base_name)
    }

    // --- Sort ---

    /// Get the Seq sort, creating it lazily if needed.
    pub(crate) fn get_or_init_sort(&mut self) -> Sort {
        self.sort
            .get_or_insert_with(|| SeqCarrier::default().sort())
            .clone()
    }

    /// Borrow the initialized Seq sort, if one has been chosen.
    pub(crate) fn sort(&self) -> Option<&Sort> {
        self.sort.as_ref()
    }

    /// The carrier every Seq-sorted term in this encoder must use.
    ///
    /// Answers before the sort has been materialized, so callers that only
    /// need to know *which spelling* to mint (the sort plan, domain hints)
    /// need neither `&mut self` nor to force lazy initialization.
    pub(crate) fn carrier(&self) -> SeqCarrier {
        self.sort
            .as_ref()
            .and_then(SeqCarrier::classify)
            .unwrap_or_default()
    }

    /// Select the uninterpreted Seq carrier for this encoder.
    ///
    /// Changes the *spelling* of the Seq sort and nothing else: every axiom
    /// `ensure_seq_theory` asserts over the native carrier is still asserted
    /// over this one. Use it when the reason is the proof surface — ay's
    /// `unsat_proof_references_uncheckable_seq_theory` refuses to certify any
    /// refutation mentioning a native `Sort::Seq(_)` term. See [`SeqCarrier`].
    ///
    /// Refuses once a carrier has actually been handed out. Switching after
    /// the fact is precisely the split this carrier notion exists to prevent:
    /// terms already minted as `(Seq Int)` would keep that sort while
    /// everything after the switch got `Seq`.
    pub(crate) fn use_uninterpreted_carrier(&mut self) {
        if self.funcs.is_none() && self.sort.is_none() {
            self.sort = Some(SeqCarrier::Uninterpreted.sort());
        }
    }

    /// Mark this encoder a mixed native-collection lane and put Seq on the
    /// uninterpreted carrier.
    ///
    /// ay-dpll reports native `Seq` + native datatype VCs as an unsupported
    /// mixed collection fragment. trust-wp's Seq encoding already models
    /// sequence operations through UF projectors, so such an encoding can keep
    /// the same API surface while avoiding ay's native Seq sort — but it must
    /// also drop the array-backed `index_logic` bridge axiom, which is what
    /// [`Self::mixed_collection_lane`] records.
    pub(crate) fn force_uninterpreted_sort(&mut self) {
        self.mixed_collection_lane = true;
        self.use_uninterpreted_carrier();
    }

    /// Whether Seq axioms that quantify over the carrier alongside the array
    /// theory must be withheld. See [`Self::force_uninterpreted_sort`].
    pub(crate) fn mixed_collection_lane(&self) -> bool {
        self.mixed_collection_lane
    }

    // --- Functions ---

    /// Borrow the Seq functions (returns `None` if not yet initialized).
    pub(crate) fn funcs(&self) -> Option<&SeqFunctions> {
        self.funcs.as_ref()
    }

    /// Clone the Seq functions (returns `None` if not yet initialized).
    pub(crate) fn funcs_clone(&self) -> Option<SeqFunctions> {
        self.funcs.clone()
    }

    /// Set the Seq functions after declaration.
    pub(crate) fn set_funcs(&mut self, funcs: SeqFunctions) {
        self.funcs = Some(funcs);
    }

    // --- SeqValue registry ---

    /// Look up a concrete SeqValue by term.
    pub(crate) fn get_seq_value(&self, term: &Term) -> Option<&SeqValue> {
        self.seq_values.get(term)
    }

    /// Look up and clone a concrete SeqValue by term.
    pub(crate) fn get_seq_value_cloned(&self, term: &Term) -> Option<SeqValue> {
        self.seq_values.get(term).cloned()
    }

    /// Check whether a term has a concrete SeqValue registered.
    pub(crate) fn has_seq_value(&self, term: &Term) -> bool {
        self.seq_values.contains_key(term)
    }

    /// Register a concrete SeqValue for a term.
    pub(crate) fn insert_seq_value(&mut self, term: Term, value: SeqValue) {
        self.seq_values.insert(term, value);
    }

    /// Register a SeqValue only if the term has no existing entry.
    pub(crate) fn insert_seq_value_if_absent(&mut self, term: Term, value: SeqValue) {
        self.seq_values.entry(term).or_insert(value);
    }

    /// Iterate over authenticated concrete component associations.
    pub(crate) fn seq_value_entries(&self) -> impl Iterator<Item = (Term, &SeqValue)> {
        self.seq_values
            .iter()
            .map(|(receiver, value)| (*receiver, value))
    }

    /// Return the stable certified monitor for an unordered Seq-term pair.
    pub(crate) fn certified_equality_monitor(&self, lhs: Term, rhs: Term) -> Option<Term> {
        self.certified_equality_monitors
            .iter()
            .find_map(|(stored_lhs, stored_rhs, monitor)| {
                ((*stored_lhs == lhs && *stored_rhs == rhs)
                    || (*stored_lhs == rhs && *stored_rhs == lhs))
                    .then_some(*monitor)
            })
    }

    /// Record one certified equality monitor for an unordered Seq-term pair.
    pub(crate) fn insert_certified_equality_monitor(
        &mut self,
        lhs: Term,
        rhs: Term,
        monitor: Term,
    ) {
        self.certified_equality_monitors.push((lhs, rhs, monitor));
    }

    /// Record the top-level positive leaves that certify one semantic Seq
    /// equality. Multiple certificates for the same pair are retained because
    /// later encodings may have more precise finite-shape metadata.
    pub(crate) fn insert_semantic_equality_certificate(
        &mut self,
        lhs: Term,
        rhs: Term,
        positive_leaves: Vec<Term>,
    ) {
        if positive_leaves.is_empty()
            || self.semantic_equality_certificates.iter().any(
                |(stored_lhs, stored_rhs, stored_leaves)| {
                    ((*stored_lhs == lhs && *stored_rhs == rhs)
                        || (*stored_lhs == rhs && *stored_rhs == lhs))
                        && *stored_leaves == positive_leaves
                },
            )
        {
            return;
        }
        self.semantic_equality_certificates
            .push((lhs, rhs, positive_leaves));
    }

    /// Iterate semantic Seq equality certificates for positive-assertion
    /// authentication.
    pub(crate) fn semantic_equality_certificates(
        &self,
    ) -> impl Iterator<Item = (Term, Term, &[Term])> {
        self.semantic_equality_certificates
            .iter()
            .map(|(lhs, rhs, leaves)| (*lhs, *rhs, leaves.as_slice()))
    }

    /// Iterate the finite Array proxies keyed by their observed Seq receiver.
    pub(crate) fn seq_array_aux_entries(&self) -> impl Iterator<Item = (Term, Term)> + '_ {
        self.seq_array_aux_vars
            .iter()
            .map(|(receiver, proxy)| (*receiver, *proxy))
    }

    /// Iterate the finite Length proxies keyed by their observed Seq receiver.
    pub(crate) fn seq_len_aux_entries(&self) -> impl Iterator<Item = (Term, Term)> + '_ {
        self.seq_len_aux_vars
            .iter()
            .map(|(receiver, proxy)| (*receiver, *proxy))
    }

    /// Iterate the finite Offset proxies keyed by their observed Seq receiver.
    pub(crate) fn seq_offset_aux_entries(&self) -> impl Iterator<Item = (Term, Term)> + '_ {
        self.seq_offset_aux_vars
            .iter()
            .map(|(receiver, proxy)| (*receiver, *proxy))
    }

    /// Record the operands for a concat term.
    pub(crate) fn insert_seq_concat_args(&mut self, term: Term, left: Term, right: Term) {
        self.seq_concat_args.insert(term, (left, right));
    }

    /// Look up the operands for a concat term.
    pub(crate) fn get_seq_concat_args(&self, term: &Term) -> Option<(Term, Term)> {
        self.seq_concat_args.get(term).copied()
    }

    // --- Flags ---

    /// Whether ground `seq_index_logic` UF equalities should be asserted.
    pub(crate) fn needs_index_ground_terms(&self) -> bool {
        self.needs_index_ground_terms
    }

    /// Enable ground `seq_index_logic` UF equality assertions.
    pub(crate) fn set_needs_index_ground_terms(&mut self) {
        self.needs_index_ground_terms = true;
    }

    /// Whether sum-specific Seq axioms have been asserted.
    pub(crate) fn sum_axioms_asserted(&self) -> bool {
        self.sum_axioms_asserted
    }

    /// Mark sum-specific Seq axioms as asserted.
    pub(crate) fn mark_sum_axioms_asserted(&mut self) {
        self.sum_axioms_asserted = true;
    }

    /// Whether get-specific Seq axioms have been asserted.
    pub(crate) fn get_axioms_asserted(&self) -> bool {
        self.get_axioms_asserted
    }

    /// Mark get-specific Seq axioms as asserted.
    pub(crate) fn mark_get_axioms_asserted(&mut self) {
        self.get_axioms_asserted = true;
    }

    /// Whether contains-specific Seq axioms have been asserted.
    pub(crate) fn contains_axioms_asserted(&self) -> bool {
        self.contains_axioms_asserted
    }

    /// Mark contains-specific Seq axioms as asserted.
    pub(crate) fn mark_contains_axioms_asserted(&mut self) {
        self.contains_axioms_asserted = true;
    }

    /// Whether concat-specific Seq axioms have been asserted.
    pub(crate) fn concat_axioms_asserted(&self) -> bool {
        self.concat_axioms_asserted
    }

    /// Mark concat-specific Seq axioms as asserted.
    pub(crate) fn mark_concat_axioms_asserted(&mut self) {
        self.concat_axioms_asserted = true;
    }

    /// Whether reverse-specific Seq axioms have been asserted.
    pub(crate) fn reverse_axioms_asserted(&self) -> bool {
        self.reverse_axioms_asserted
    }

    /// Mark reverse-specific Seq axioms as asserted.
    pub(crate) fn mark_reverse_axioms_asserted(&mut self) {
        self.reverse_axioms_asserted = true;
    }

    /// Whether permutation/multiset-specific Seq axioms have been asserted.
    pub(crate) fn permutation_axioms_asserted(&self) -> bool {
        self.permutation_axioms_asserted
    }

    /// Mark permutation/multiset-specific Seq axioms as asserted.
    pub(crate) fn mark_permutation_axioms_asserted(&mut self) {
        self.permutation_axioms_asserted = true;
    }

    // --- Snapshot/restore for obligation slice isolation (#2618) ---

    /// Restore the sum axioms asserted flag from a snapshot.
    pub(crate) fn restore_sum_axioms_asserted(&mut self, val: bool) {
        self.sum_axioms_asserted = val;
    }

    /// Restore the get axioms asserted flag from a snapshot.
    pub(crate) fn restore_get_axioms_asserted(&mut self, val: bool) {
        self.get_axioms_asserted = val;
    }

    /// Restore the contains axioms asserted flag from a snapshot.
    pub(crate) fn restore_contains_axioms_asserted(&mut self, val: bool) {
        self.contains_axioms_asserted = val;
    }

    /// Restore the concat axioms asserted flag from a snapshot.
    pub(crate) fn restore_concat_axioms_asserted(&mut self, val: bool) {
        self.concat_axioms_asserted = val;
    }

    /// Restore the reverse axioms asserted flag from a snapshot.
    pub(crate) fn restore_reverse_axioms_asserted(&mut self, val: bool) {
        self.reverse_axioms_asserted = val;
    }

    /// Restore the permutation axioms asserted flag from a snapshot.
    pub(crate) fn restore_permutation_axioms_asserted(&mut self, val: bool) {
        self.permutation_axioms_asserted = val;
    }

    // --- Coerced terms ---

    /// Look up a coerced term by its original.
    pub(crate) fn get_coerced_term(&self, term: &Term) -> Option<Term> {
        self.coerced_terms.get(term).copied()
    }

    /// Register a Vec->Seq coercion.
    pub(crate) fn insert_coerced_term(&mut self, original: Term, coerced: Term) {
        self.coerced_terms.insert(original, coerced);
    }

    // --- Bridge functions ---

    /// Look up a bridge UF for a Vec-like sort name.
    pub(crate) fn get_bridge_fn(&self, sort_name: &str) -> Option<&FuncDecl> {
        self.bridge_fns.get(sort_name)
    }

    /// Register a bridge UF for a Vec-like sort name.
    pub(crate) fn insert_bridge_fn(&mut self, sort_name: String, decl: FuncDecl) {
        self.bridge_fns.insert(sort_name, decl);
    }

    // --- Element sort coercion ---

    /// Look up the original sort for a coerced Int element.
    pub(crate) fn get_seq_elem_sort(&self, term: &Term) -> Option<&Sort> {
        self.seq_elem_sorts.get(term)
    }

    /// Record the original sort and exact source for a coerced Int element.
    pub(crate) fn insert_seq_elem_source(&mut self, term: Term, sort: Sort, source: Term) {
        self.seq_elem_sorts.insert(term, sort);
        self.seq_elem_sources.insert(term, source);
    }

    /// Look up the exact source for a coerced Int element.
    pub(crate) fn get_seq_elem_source(&self, term: &Term) -> Option<Term> {
        self.seq_elem_sources.get(term).copied()
    }

    // --- Index provenance ---

    /// Look up the `(seq, index)` source for an Int-sorted index result.
    pub(crate) fn get_seq_index_source(&self, term: &Term) -> Option<&(Term, Term)> {
        self.seq_index_sources.get(term)
    }

    /// Record the `(seq, index)` source for an Int-sorted index result.
    pub(crate) fn insert_seq_index_source(&mut self, result: Term, source: (Term, Term)) {
        self.seq_index_sources.insert(result, source);
    }

    /// Return all recorded index result sources for a Seq term.
    pub(crate) fn seq_index_sources_for_seq(&self, seq_term: &Term) -> Vec<(Term, Term)> {
        self.seq_index_sources
            .iter()
            .filter_map(|(result, (source_seq, index))| {
                (source_seq == seq_term).then_some((*result, *index))
            })
            .collect()
    }

    /// Return all recorded index result sources, grouped by their source Seq.
    pub(crate) fn all_seq_index_sources(&self) -> Vec<(Term, Term, Term)> {
        self.seq_index_sources
            .iter()
            .map(|(result, (source_seq, index))| (*source_seq, *index, *result))
            .collect()
    }

    /// Retain a `resolve_elsewhere` predicate for bounded ground closure.
    pub(crate) fn register_resolve_elsewhere_frame(&mut self, frame: ResolveElsewhereFrame) {
        if !self.resolve_elsewhere_frames.contains(&frame) {
            self.resolve_elsewhere_frames.push(frame);
        }
    }

    /// Clone the finite set of encoded `resolve_elsewhere` predicates.
    pub(crate) fn resolve_elsewhere_frames_cloned(&self) -> Vec<ResolveElsewhereFrame> {
        self.resolve_elsewhere_frames.clone()
    }

    /// Clone the registered container-element invariants for a Seq view term.
    pub(crate) fn container_element_invariants_cloned(
        &self,
        seq_term: &Term,
    ) -> Option<Vec<ContainerElementInvariantSpec>> {
        self.container_element_invariants.get(seq_term).cloned()
    }

    /// Register a shared container-element invariant for a Seq view term.
    pub(crate) fn register_container_element_invariant(
        &mut self,
        seq_term: Term,
        spec: ContainerElementInvariantSpec,
    ) {
        let entry = self
            .container_element_invariants
            .entry(seq_term)
            .or_default();
        if !entry.contains(&spec) {
            entry.push(spec);
        }
    }

    /// Look up a per-sort restore UF by sort key.
    pub(crate) fn get_seq_index_restore_fn(&self, key: &str) -> Option<&FuncDecl> {
        self.seq_index_restore_fns.get(key)
    }

    /// Register a per-sort restore UF.
    pub(crate) fn insert_seq_index_restore_fn(&mut self, key: String, decl: FuncDecl) {
        self.seq_index_restore_fns.insert(key, decl);
    }

    // --- Fresh literal counter ---

    /// Allocate the next fresh seq literal ID, returning the current value
    /// and incrementing the counter.
    pub(crate) fn next_fresh_seq_lit_id(&mut self) -> u32 {
        let id = self.fresh_seq_lit_counter;
        self.fresh_seq_lit_counter += 1;
        id
    }

    // --- seq_len auxiliary Int variables (#2323) ---

    /// Look up an existing auxiliary Int variable for `seq_len(seq_term)`.
    pub(crate) fn get_seq_len_aux(&self, seq_term: &Term) -> Option<Term> {
        self.seq_len_aux_vars.get(seq_term).copied()
    }

    /// Register an auxiliary Int variable for `seq_len(seq_term)`.
    pub(crate) fn insert_seq_len_aux(&mut self, seq_term: Term, aux_var: Term) {
        self.seq_len_aux_vars.insert(seq_term, aux_var);
    }

    // --- seq_offset auxiliary Int variables ---

    pub(crate) fn get_seq_offset_aux(&self, seq_term: &Term) -> Option<Term> {
        self.seq_offset_aux_vars.get(seq_term).copied()
    }

    pub(crate) fn insert_seq_offset_aux(&mut self, seq_term: Term, aux_var: Term) {
        self.seq_offset_aux_vars.insert(seq_term, aux_var);
    }

    // --- seq_array auxiliary Array variables ---

    pub(crate) fn get_seq_array_aux(&self, seq_term: &Term) -> Option<Term> {
        self.seq_array_aux_vars.get(seq_term).copied()
    }

    pub(crate) fn insert_seq_array_aux(&mut self, seq_term: Term, aux_var: Term) {
        self.seq_array_aux_vars.insert(seq_term, aux_var);
    }

    // --- General UF→Int auxiliary variables (#2323) ---

    /// Look up an existing auxiliary Int variable for a UF application term.
    pub(crate) fn get_uf_int_aux(&self, uf_term: &Term) -> Option<Term> {
        self.uf_int_aux_vars.get(uf_term).copied()
    }

    /// Register an auxiliary Int variable for a UF application term.
    pub(crate) fn insert_uf_int_aux(&mut self, uf_term: Term, aux_var: Term) {
        self.uf_int_aux_vars.insert(uf_term, aux_var);
    }

    // --- Test-only accessors ---

    /// Whether Seq functions have been initialized (test alias for `has_funcs`).
    #[cfg(test)]
    pub(crate) fn funcs_is_some(&self) -> bool {
        self.funcs.is_some()
    }

    /// Whether Seq functions are absent (test inspection).
    #[cfg(test)]
    pub(crate) fn funcs_is_none(&self) -> bool {
        self.funcs.is_none()
    }

    /// Number of registered SeqValues (test inspection).
    #[cfg(test)]
    pub(crate) fn seq_values_len(&self) -> usize {
        self.seq_values.len()
    }

    /// Whether a seq index source has been recorded for the given term (test inspection).
    #[cfg(test)]
    pub(crate) fn has_seq_index_source(&self, term: &Term) -> bool {
        self.seq_index_sources.contains_key(term)
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::Logic;
    use trust_wp_core::formula::PureExpr;

    use super::*;

    // ── initialization ──

    #[test]
    fn test_new_seq_state_is_empty() {
        let state = SeqState::new();
        assert!(state.funcs_is_none());
        assert_eq!(state.seq_values_len(), 0);
        assert!(!state.needs_index_ground_terms());
        assert!(!state.sum_axioms_asserted());
        assert!(!state.get_axioms_asserted());
        assert!(!state.contains_axioms_asserted());
        assert!(!state.concat_axioms_asserted());
        assert!(!state.reverse_axioms_asserted());
    }

    // ── sort lazy initialization ──

    #[test]
    fn test_get_or_init_sort_creates_seq_sort() {
        let mut state = SeqState::new();
        let sort = state.get_or_init_sort();
        // Sort::seq(Sort::Int) should produce a Seq sort
        assert_eq!(format!("{sort}"), format!("{}", Sort::seq(Sort::Int)));
    }

    #[test]
    fn test_get_or_init_sort_idempotent() {
        let mut state = SeqState::new();
        let sort1 = state.get_or_init_sort();
        let sort2 = state.get_or_init_sort();
        assert_eq!(format!("{sort1}"), format!("{sort2}"));
    }

    // ── functions lifecycle ──

    #[test]
    fn test_funcs_lifecycle() {
        let mut state = SeqState::new();
        assert!(state.funcs_is_none());
        assert!(state.funcs().is_none());
        assert!(state.funcs_clone().is_none());

        // Create minimal SeqFunctions via a solver
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let seq_sort = Sort::seq(Sort::Int);
        let arr_sort = Sort::array(Sort::Int, Sort::Int);
        let funcs = SeqFunctions {
            seq_array: solver.declare_fun("seq_array", &[seq_sort.clone()], arr_sort),
            seq_len: solver.declare_fun("seq_len", &[seq_sort.clone()], Sort::Int),
            seq_offset: solver.declare_fun("seq_offset", &[seq_sort.clone()], Sort::Int),
            seq_index_logic: solver.declare_fun(
                "seq_index_logic",
                &[seq_sort.clone(), Sort::Int],
                Sort::Int,
            ),
            seq_push_back: solver.declare_fun(
                "seq_push_back",
                &[seq_sort.clone(), Sort::Int],
                seq_sort.clone(),
            ),
            seq_sum: solver.declare_fun("seq_sum", &[seq_sort.clone()], Sort::Int),
            seq_get: solver.declare_fun("seq_get", &[seq_sort.clone(), Sort::Int], Sort::Int),
            seq_contains: solver.declare_fun(
                "seq_contains",
                &[seq_sort.clone(), Sort::Int],
                Sort::Bool,
            ),
            seq_contains_pair: solver.declare_fun(
                "seq_contains_pair",
                &[seq_sort.clone(), Sort::Int, Sort::Int],
                Sort::Bool,
            ),
            seq_subsequence: solver.declare_fun(
                "seq_subsequence",
                &[seq_sort.clone(), Sort::Int, Sort::Int],
                seq_sort.clone(),
            ),
            seq_concat: solver.declare_fun(
                "seq_concat",
                &[seq_sort.clone(), seq_sort.clone()],
                seq_sort.clone(),
            ),
            seq_singleton: solver.declare_fun("seq_singleton", &[Sort::Int], seq_sort.clone()),
            seq_set: solver.declare_fun(
                "seq_set",
                &[seq_sort.clone(), Sort::Int, Sort::Int],
                seq_sort.clone(),
            ),
            seq_reverse: solver.declare_fun("seq_reverse", &[seq_sort.clone()], seq_sort.clone()),
            seq_push_front: solver.declare_fun(
                "seq_push_front",
                &[seq_sort.clone(), Sort::Int],
                seq_sort.clone(),
            ),
            seq_permutation_of: solver.declare_fun(
                "seq_permutation_of",
                &[seq_sort.clone(), seq_sort.clone()],
                Sort::Bool,
            ),
            seq_exchange: solver.declare_fun(
                "seq_exchange",
                &[seq_sort.clone(), seq_sort.clone(), Sort::Int, Sort::Int],
                Sort::Bool,
            ),
            seq_count: solver.declare_fun("seq_count", &[seq_sort.clone(), Sort::Int], Sort::Int),
            seq_empty: solver.declare_const("seq_empty", seq_sort),
        };

        state.set_funcs(funcs);
        assert!(state.funcs_is_some());
        assert!(state.funcs().is_some());
        assert!(state.funcs_clone().is_some());
    }

    // ── SeqValue registry ──

    #[test]
    fn test_seq_value_insert_and_lookup() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let term = solver.declare_const("s", Sort::seq(Sort::Int));
        let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
        let len = solver.int_const(5);
        let offset = solver.int_const(0);

        let sv = SeqValue {
            arr,
            len,
            offset,
            known_len: Some(5),
        };
        state.insert_seq_value(term, sv);

        assert!(state.has_seq_value(&term));
        assert_eq!(state.seq_values_len(), 1);
        let retrieved = state.get_seq_value(&term).unwrap();
        assert_eq!(retrieved.known_len, Some(5));
    }

    #[test]
    fn test_seq_value_insert_if_absent_does_not_overwrite() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let term = solver.declare_const("s", Sort::seq(Sort::Int));
        let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));

        let sv1 = SeqValue {
            arr,
            len: solver.int_const(3),
            offset: solver.int_const(0),
            known_len: Some(3),
        };
        state.insert_seq_value(term, sv1);

        let arr2 = solver.declare_const("arr2", Sort::array(Sort::Int, Sort::Int));
        let sv2 = SeqValue {
            arr: arr2,
            len: solver.int_const(10),
            offset: solver.int_const(0),
            known_len: Some(10),
        };
        state.insert_seq_value_if_absent(term, sv2);

        // Original value should be preserved
        assert_eq!(state.get_seq_value(&term).unwrap().known_len, Some(3));
    }

    #[test]
    fn test_get_seq_value_cloned() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let term = solver.declare_const("s", Sort::seq(Sort::Int));
        let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
        let sv = SeqValue {
            arr,
            len: solver.int_const(2),
            offset: solver.int_const(0),
            known_len: Some(2),
        };
        state.insert_seq_value(term, sv);

        let cloned = state.get_seq_value_cloned(&term);
        assert!(cloned.is_some());
        assert_eq!(cloned.unwrap().known_len, Some(2));
    }

    // ── flags ──

    #[test]
    fn test_needs_index_ground_terms_flag() {
        let mut state = SeqState::new();
        assert!(!state.needs_index_ground_terms());
        state.set_needs_index_ground_terms();
        assert!(state.needs_index_ground_terms());
    }

    #[test]
    fn test_sum_axioms_asserted_flag() {
        let mut state = SeqState::new();
        assert!(!state.sum_axioms_asserted());
        state.mark_sum_axioms_asserted();
        assert!(state.sum_axioms_asserted());
    }

    #[test]
    fn test_get_axioms_asserted_flag() {
        let mut state = SeqState::new();
        assert!(!state.get_axioms_asserted());
        state.mark_get_axioms_asserted();
        assert!(state.get_axioms_asserted());
    }

    #[test]
    fn test_contains_axioms_asserted_flag() {
        let mut state = SeqState::new();
        assert!(!state.contains_axioms_asserted());
        state.mark_contains_axioms_asserted();
        assert!(state.contains_axioms_asserted());
    }

    #[test]
    fn test_concat_axioms_asserted_flag() {
        let mut state = SeqState::new();
        assert!(!state.concat_axioms_asserted());
        state.mark_concat_axioms_asserted();
        assert!(state.concat_axioms_asserted());
    }

    #[test]
    fn test_reverse_axioms_asserted_flag() {
        let mut state = SeqState::new();
        assert!(!state.reverse_axioms_asserted());
        state.mark_reverse_axioms_asserted();
        assert!(state.reverse_axioms_asserted());
    }

    #[test]
    fn test_permutation_axioms_asserted_flag() {
        let mut state = SeqState::new();
        assert!(!state.permutation_axioms_asserted());
        state.mark_permutation_axioms_asserted();
        assert!(state.permutation_axioms_asserted());
    }

    #[test]
    fn test_restore_axiom_flags() {
        let mut state = SeqState::new();
        state.mark_sum_axioms_asserted();
        state.mark_get_axioms_asserted();
        state.mark_contains_axioms_asserted();
        state.mark_concat_axioms_asserted();
        state.mark_reverse_axioms_asserted();
        state.mark_permutation_axioms_asserted();
        assert!(state.sum_axioms_asserted());
        assert!(state.get_axioms_asserted());
        assert!(state.contains_axioms_asserted());
        assert!(state.concat_axioms_asserted());
        assert!(state.reverse_axioms_asserted());
        assert!(state.permutation_axioms_asserted());

        // Restore to un-asserted
        state.restore_sum_axioms_asserted(false);
        state.restore_get_axioms_asserted(false);
        state.restore_contains_axioms_asserted(false);
        state.restore_concat_axioms_asserted(false);
        state.restore_reverse_axioms_asserted(false);
        state.restore_permutation_axioms_asserted(false);
        assert!(!state.sum_axioms_asserted());
        assert!(!state.get_axioms_asserted());
        assert!(!state.contains_axioms_asserted());
        assert!(!state.concat_axioms_asserted());
        assert!(!state.reverse_axioms_asserted());
        assert!(!state.permutation_axioms_asserted());
    }

    // ── coerced terms ──

    #[test]
    fn test_coerced_term_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let original = solver.declare_const("vec_v", Sort::Int);
        let coerced = solver.declare_const("seq_v", Sort::seq(Sort::Int));

        assert!(state.get_coerced_term(&original).is_none());
        state.insert_coerced_term(original, coerced);
        assert_eq!(state.get_coerced_term(&original), Some(coerced));
    }

    // ── bridge functions ──

    #[test]
    fn test_bridge_fn_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl = solver.declare_fun("bridge_Vec_to_Seq", &[Sort::Int], Sort::seq(Sort::Int));

        assert!(state.get_bridge_fn("Vec_Int").is_none());
        state.insert_bridge_fn("Vec_Int".to_string(), decl);
        assert!(state.get_bridge_fn("Vec_Int").is_some());
    }

    // ── element sort coercion ──

    #[test]
    fn test_seq_elem_sort_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let term = solver.declare_const("elem", Sort::Int);
        let source = solver.declare_const("source", Sort::Bool);

        assert!(state.get_seq_elem_sort(&term).is_none());
        assert!(state.get_seq_elem_source(&term).is_none());
        state.insert_seq_elem_source(term, Sort::Bool, source);
        assert_eq!(state.get_seq_elem_sort(&term), Some(&Sort::Bool));
        assert_eq!(state.get_seq_elem_source(&term), Some(source));
    }

    // ── index provenance ──

    #[test]
    fn test_seq_index_source_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let result = solver.declare_const("idx_result", Sort::Int);
        let seq_term = solver.declare_const("s", Sort::seq(Sort::Int));
        let index_term = solver.int_const(3);

        assert!(!state.has_seq_index_source(&result));
        state.insert_seq_index_source(result, (seq_term, index_term));
        assert!(state.has_seq_index_source(&result));
        let (s, i) = state.get_seq_index_source(&result).unwrap();
        assert_eq!(*s, seq_term);
        assert_eq!(*i, index_term);
    }

    // ── container element invariants ──

    #[test]
    fn test_container_element_invariant_registration() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let seq_term = solver.declare_const("s", Sort::seq(Sort::Int));

        assert!(state
            .container_element_invariants_cloned(&seq_term)
            .is_none());

        let spec = ContainerElementInvariantSpec::Method {
            element_invariant_method: "inv_elem".to_string(),
        };
        state.register_container_element_invariant(seq_term, spec.clone());

        let retrieved = state
            .container_element_invariants_cloned(&seq_term)
            .unwrap();
        assert_eq!(retrieved.len(), 1);
    }

    #[test]
    fn test_container_element_invariant_dedup() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let seq_term = solver.declare_const("s", Sort::seq(Sort::Int));

        let spec = ContainerElementInvariantSpec::Method {
            element_invariant_method: "inv_elem".to_string(),
        };
        state.register_container_element_invariant(seq_term, spec.clone());
        state.register_container_element_invariant(seq_term, spec.clone());

        // Should still have just one (dedup by PartialEq)
        let retrieved = state
            .container_element_invariants_cloned(&seq_term)
            .unwrap();
        assert_eq!(retrieved.len(), 1);
    }

    #[test]
    fn test_container_element_invariant_body_variant() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let seq_term = solver.declare_const("s", Sort::seq(Sort::Int));

        let spec = ContainerElementInvariantSpec::Body {
            self_param: "x".to_string(),
            body: PureExpr::Bool(true),
        };
        state.register_container_element_invariant(seq_term, spec);

        let retrieved = state
            .container_element_invariants_cloned(&seq_term)
            .unwrap();
        assert_eq!(retrieved.len(), 1);
        match &retrieved[0] {
            ContainerElementInvariantSpec::Body { self_param, body } => {
                assert_eq!(self_param, "x");
                assert_eq!(*body, PureExpr::Bool(true));
            }
            _ => panic!("expected Body variant"),
        }
    }

    // ── fresh seq literal counter ──

    #[test]
    fn test_fresh_seq_lit_counter_increments() {
        let mut state = SeqState::new();
        assert_eq!(state.next_fresh_seq_lit_id(), 0);
        assert_eq!(state.next_fresh_seq_lit_id(), 1);
        assert_eq!(state.next_fresh_seq_lit_id(), 2);
    }

    // ── seq_len auxiliary variables ──

    #[test]
    fn test_seq_len_aux_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let seq_term = solver.declare_const("s", Sort::seq(Sort::Int));
        let aux_var = solver.declare_const("aux_len_s", Sort::Int);

        assert!(state.get_seq_len_aux(&seq_term).is_none());
        state.insert_seq_len_aux(seq_term, aux_var);
        assert_eq!(state.get_seq_len_aux(&seq_term), Some(aux_var));
    }

    #[test]
    fn test_seq_offset_aux_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let seq_term = solver.declare_const("s", Sort::seq(Sort::Int));
        let aux_var = solver.declare_const("aux_offset_s", Sort::Int);

        assert!(state.get_seq_offset_aux(&seq_term).is_none());
        state.insert_seq_offset_aux(seq_term, aux_var);
        assert_eq!(state.get_seq_offset_aux(&seq_term), Some(aux_var));
    }

    #[test]
    fn test_seq_array_aux_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let seq_term = solver.declare_const("s", Sort::seq(Sort::Int));
        let aux_var = solver.declare_const("aux_array_s", Sort::array(Sort::Int, Sort::Int));

        assert!(state.get_seq_array_aux(&seq_term).is_none());
        state.insert_seq_array_aux(seq_term, aux_var);
        assert_eq!(state.get_seq_array_aux(&seq_term), Some(aux_var));
    }

    // ── UF->Int auxiliary variables ──

    #[test]
    fn test_uf_int_aux_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let uf_term = solver.declare_const("uf_app", Sort::Int);
        let aux_var = solver.declare_const("aux_uf", Sort::Int);

        assert!(state.get_uf_int_aux(&uf_term).is_none());
        state.insert_uf_int_aux(uf_term, aux_var);
        assert_eq!(state.get_uf_int_aux(&uf_term), Some(aux_var));
    }

    // ── seq index restore fn ──

    #[test]
    fn test_seq_index_restore_fn_registry() {
        let mut state = SeqState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl = solver.declare_fun(
            "restore_Bool",
            &[Sort::seq(Sort::Int), Sort::Int],
            Sort::Bool,
        );

        assert!(state.get_seq_index_restore_fn("Bool").is_none());
        state.insert_seq_index_restore_fn("Bool".to_string(), decl);
        assert!(state.get_seq_index_restore_fn("Bool").is_some());
    }
}

/// Uninterpreted functions for `Seq<T>` logical sequences.
///
/// These model the Seq operations from trust-wp-std:
/// - `seq_array`: Seq -> Array<Int, Int> (backing storage projection)
/// - `seq_len`: Seq -> Int
/// - `seq_offset`: Seq -> Int (logical start index in backing storage)
/// - `seq_index_logic`: Seq x Int -> Int
/// - `seq_push_back`: Seq x Int -> Seq
/// - `seq_sum`: Seq -> Int (sum of integer elements)
/// - `seq_get`: Seq x Int -> Int (bounds-checked access, Option-returning)
/// - `seq_contains`: Seq x Int -> Bool (element membership test)
///
/// Note: Field names intentionally match SMT function names for clarity.
#[derive(Clone)]
#[allow(clippy::struct_field_names)]
pub(crate) struct SeqFunctions {
    /// `seq_array`: Seq -> Array<Int, Int>
    pub(crate) seq_array: FuncDecl,
    /// `seq_len`: Seq -> Int
    pub(crate) seq_len: FuncDecl,
    /// `seq_offset`: Seq -> Int
    pub(crate) seq_offset: FuncDecl,
    /// `seq_index_logic`: Seq x Int -> Int
    pub(crate) seq_index_logic: FuncDecl,
    /// `seq_push_back`: Seq x Int -> Seq
    pub(crate) seq_push_back: FuncDecl,
    /// `seq_sum`: Seq -> Int (sum of all elements)
    pub(crate) seq_sum: FuncDecl,
    /// `seq_get`: Seq x Int -> Int (Option-returning bounds-checked access, #1882)
    pub(crate) seq_get: FuncDecl,
    /// `seq_contains`: Seq x Int -> Bool (element membership test, #699)
    pub(crate) seq_contains: FuncDecl,
    /// `seq_contains_pair`: Seq x Int x Int -> Bool (pair membership test, #2514)
    pub(crate) seq_contains_pair: FuncDecl,
    /// `seq_subsequence`: Seq x Int x Int -> Seq (slice extraction, #737)
    pub(crate) seq_subsequence: FuncDecl,
    /// `seq_concat`: Seq x Seq -> Seq (sequence concatenation, #379)
    pub(crate) seq_concat: FuncDecl,
    /// `seq_singleton`: Int -> Seq (single-element sequence, #379)
    pub(crate) seq_singleton: FuncDecl,
    /// `seq_set`: Seq x Int x Int -> Seq (pointwise update, #969)
    pub(crate) seq_set: FuncDecl,
    /// `seq_reverse`: Seq -> Seq (element reversal, #1581)
    pub(crate) seq_reverse: FuncDecl,
    /// `seq_push_front`: Seq x Int -> Seq (prepend element, #1581)
    pub(crate) seq_push_front: FuncDecl,
    /// `seq_permutation_of`: Seq x Seq -> Bool (multiset equality / permutation).
    pub(crate) seq_permutation_of: FuncDecl,
    /// `seq_exchange`: Seq x Seq x Int x Int -> Bool (two-element swap relation).
    pub(crate) seq_exchange: FuncDecl,
    /// `seq_count`: Seq x Int -> Int (number of occurrences of an element).
    pub(crate) seq_count: FuncDecl,
    /// `seq_empty`: Seq constant (empty sequence, #737)
    pub(crate) seq_empty: Term,
}
