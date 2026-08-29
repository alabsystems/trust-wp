// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// EXPERIMENTAL: Not used in the production verification pipeline. Gated behind
// `#[cfg(any(test, feature = "sep-logic"))]` — compiled for tests but excluded
// from production binaries. The production pipeline uses pure first-order logic
// (PureExpr + encode_pure + encode_mut_borrow). This module is reserved for
// future unsafe Rust support. See designs/2026-03-08-2129-separation-logic-identity-recommendation.md.
//!
//! Separation logic encoding for the AY encoder (experimental, feature-gated).
//!
//! This module handles the core separation logic primitives:
//! - Points-to assertions: `location ↦ value` with fractional permissions
//! - Separating conjunction: `P * Q` with disjointness enforcement
//! - Magic wand: `P -* Q` (adjoint of separating conjunction)
//! - Footprint extraction and caching
//!
//! The production `encode_mut_borrow()` lives in `mut_borrow_enc.rs`.
//! See #2214.

use std::{collections::HashSet, rc::Rc};

use ay_dpll::api::{FuncDecl, Sort, Term};
use trust_wp_core::formula::{Formula, Location, Permission, Value};

use super::{AYEncoder, FormulaCacheKey, TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD};
use crate::error::EncodingError;

impl AYEncoder {
    /// Encode a points-to assertion: location ↦ value with permission
    pub(super) fn encode_points_to(
        &mut self,
        location: &Location,
        value: &Value,
        permission: Permission,
    ) -> Result<Term, EncodingError> {
        // Get location as an integer variable
        let loc_term = self.get_or_declare_var(&location.0, Sort::Int)?;

        // Location must be in domain (domain is Array<Int,Int>, 1 = allocated; #1603)
        let dom_val = self.solver.select(self.mem_state.domain, loc_term);
        let one = self.solver.int_const(1);
        let in_domain = self.eq_term(dom_val, one);

        // Heap at location equals value (if known)
        let value_constraint = match value {
            Value::Expr(expr) => {
                let val_term = self.encode_pure(expr)?;
                let heap_at_loc = self.solver.select(self.mem_state.heap, loc_term);
                Some(self.eq_term(heap_at_loc, val_term))
            }
            Value::Unknown => None,
            // Value is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns)]
            _ => None,
        };

        // Permission constraints — all asserted via pending_assertions pipeline
        // because ay-dpll's AUFLIA path does not decompose nested `and` terms
        // into individual assertions (#1788). Top-level assertions are required
        // for the solver to detect contradictions with externally pinned values.
        let current_perm = self.solver.select(self.mem_state.permissions, loc_term);

        // Required permission: perms[loc] >= required_permission
        // PERM_SCALE (2520 = LCM(1..10)) ensures exact division for denominators ≤ 10,
        // avoiding the integer truncation bug with the old scale of 100 (#741).
        let perm_value = permission.scaled_value();
        let required_perm = self.solver.int_const(perm_value);
        let perm_ok = self.solver.ge(current_perm, required_perm);
        self.assertion_pipeline.push_pending_assertion(perm_ok);

        // Upper-bound: perms[loc] <= PERM_SCALE (#1879).
        // Without this, the permissions array is unconstrained above PERM_SCALE,
        // allowing two FULL PointsTo assertions for the same location in an And
        // conjunct to be simultaneously satisfiable.
        let perm_scale = self.solver.int_const(Permission::PERM_SCALE);
        let perm_bounded = self.solver.le(current_perm, perm_scale);
        self.assertion_pipeline.push_pending_assertion(perm_bounded);

        // Lower-bound: perms[loc] >= 0 (#1879).
        // Prevents the solver from assigning negative permission values.
        let zero = self.solver.int_const(0);
        let perm_non_neg = self.solver.ge(current_perm, zero);
        self.assertion_pipeline.push_pending_assertion(perm_non_neg);

        // Combine domain + value constraints (permissions asserted via pipeline)
        let mut result = in_domain;
        if let Some(val_constr) = value_constraint {
            result = self.solver.and(result, val_constr);
        }

        Ok(result)
    }

    /// Encode separating conjunction: P * Q
    ///
    /// The key property is that P and Q operate on disjoint heap regions.
    /// We encode this by:
    /// 1. Encoding both sub-formulas
    /// 2. Extracting the footprint (locations) from each
    /// 3. Asserting that footprints are disjoint
    ///
    /// # Frame Rule
    ///
    /// The frame rule in separation logic states:
    /// ```text
    /// {P} C {Q}
    /// ─────────────── (Frame)
    /// {P * R} C {Q * R}
    /// ```
    ///
    /// This encoding enables the frame rule by ensuring that when we have
    /// P * R, the locations in R are separate from those modified by C.
    pub(super) fn encode_sep_conj(
        &mut self,
        sep_conj: &Formula,
        l: &Formula,
        r: &Formula,
    ) -> Result<Term, EncodingError> {
        // Encode both formulas first. This recursively populates the footprint
        // cache for inner SepConj nodes, avoiding O(N^2) re-traversal.
        let lt = self.encode(l)?;
        let rt = self.encode(r)?;

        // Retrieve footprints, using the cache populated by inner encode calls.
        // If the child was a SepConj, its combined footprint is already cached.
        // Rc clone is O(1) — avoids O(N) string cloning per level (#668).
        let left_locs = self.footprint_cached(l);
        let right_locs = self.footprint_cached(r);

        // Conjunction of both formulas
        let conj = self.solver.and(lt, rt);

        // Cache the combined footprint for this SepConj node before early return.
        // Build combined Vec with one allocation, iterating both Rc'd Vecs.
        let cache_key = FormulaCacheKey::for_formula(sep_conj);
        let mut combined = Vec::with_capacity(left_locs.len() + right_locs.len());
        combined.extend_from_slice(&left_locs);
        combined.extend_from_slice(&right_locs);
        self.sep_cache
            .insert_footprint(cache_key, Rc::new(combined));

        // If either formula has no heap footprint (pure formulas), no disjointness needed
        if left_locs.is_empty() || right_locs.is_empty() {
            return Ok(conj);
        }

        // Choose encoding strategy based on footprint size and quantifier support.
        // Cross-pair disjointness: O(L*R) pairwise `l != r` constraints.
        // Domain-fact disjointness: O(L+R) UF domain facts plus cached term sets.
        // NOTE: We must NOT use `distinct(all_locs)` — that adds intra-side
        // constraints which is semantically incorrect. See #449.
        let total_locs = left_locs.len() + right_locs.len();
        let use_quantified =
            self.supports_quantifiers() && total_locs >= TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD;

        let disjoint = if use_quantified {
            // Check if left child has a cached combined domain + resolved Terms
            // from a prior quantified SepConj encoding. Reusing both avoids O(L)
            // membership re-declarations AND O(L) term re-resolution per level,
            // reducing total encoding from O(N²) to O(N) for chains (#668).
            let left_key = FormulaCacheKey::for_formula(l);
            let left_cache = self.sep_cache.get_combined_domain(&left_key);
            let (disjoint_term, combined_domain, combined_terms) = self
                .encode_quantified_disjointness_incremental(&left_locs, &right_locs, left_cache)?;
            // Cache the combined domain + terms for this SepConj node so parent
            // boundaries can reuse them.
            self.sep_cache
                .insert_combined_domain(cache_key, (combined_domain, combined_terms));
            disjoint_term
        } else {
            let mut left_terms = Vec::with_capacity(left_locs.len());
            for loc in left_locs.iter() {
                left_terms.push(self.get_or_declare_var(loc, Sort::Int)?);
            }
            let mut right_terms = Vec::with_capacity(right_locs.len());
            for loc in right_locs.iter() {
                right_terms.push(self.get_or_declare_var(loc, Sort::Int)?);
            }
            self.heap_disjoint(&left_terms, &right_terms)
        };

        // Combine: (P ∧ Q ∧ disjoint)
        Ok(self.solver.and(conj, disjoint))
    }

    /// Retrieve the cached footprint for a formula, or compute it if not cached.
    ///
    /// During `SepConj` encoding, child formulas are encoded first which populates
    /// the cache for inner `SepConj` nodes. This avoids the O(N^2) re-traversal
    /// that occurs when `extract_footprint` re-walks the entire subtree at each
    /// level of a `SepConj` chain.
    ///
    /// Returns `Rc<Vec<String>>` so that cloning the return value is O(1) instead
    /// of O(N). For a left-recursive SepConj chain of N elements, this reduces
    /// total footprint-clone cost from O(N²) string bytes to O(N) Rc bumps (#668).
    fn footprint_cached(&self, formula: &Formula) -> Rc<Vec<String>> {
        let key = FormulaCacheKey::for_formula(formula);
        if let Some(cached) = self.sep_cache.get_footprint(&key) {
            return cached;
        }
        Rc::new(self.extract_footprint(formula))
    }

    /// Encode cross-domain disjointness using finite UF domain facts, with
    /// incremental domain reuse for left-recursive SepConj chains (#668).
    ///
    /// When `left_parent_domain` is `None` (first quantified boundary in a chain),
    /// creates fresh `D_left` and `D_right` predicates with ground membership
    /// assertions for all locations on each side, plus finite exclusion facts.
    ///
    /// When `left_parent_cache` is `Some((d_parent, parent_terms))` (subsequent
    /// boundaries in a chain), reuses `d_parent` as the left domain AND
    /// `parent_terms` as the already-resolved left Terms — skipping both O(L)
    /// membership re-declarations and O(L) term re-resolution for the left side.
    /// Right-side membership, left-exclusion, and combined-domain membership
    /// facts are asserted for the finite footprint terms so that parent SepConj
    /// boundaries can reuse the combined domain in turn.
    ///
    /// Returns `(disjointness_conjunction, combined_domain, combined_terms)`.
    /// The caller caches the combined domain + terms for the parent to use.
    ///
    /// **Syntactic overlap guard**: If any location name appears in both
    /// footprints, the formula is trivially unsatisfiable and the method
    /// returns `(false, dummy_domain, empty_terms)`.
    ///
    /// Requires AUFLIA logic (quantifiers).
    fn encode_quantified_disjointness_incremental(
        &mut self,
        left_locs: &[String],
        right_locs: &[String],
        left_parent_cache: Option<(FuncDecl, Rc<Vec<Term>>)>,
    ) -> Result<(Term, FuncDecl, Rc<Vec<Term>>), EncodingError> {
        // Syntactic overlap check: if any location name appears in both
        // footprints, the SepConj is immediately unsatisfiable.
        // In incremental mode, the left set was already checked at lower levels;
        // we only need to check right against the entire left set.
        let left_set: HashSet<&str> = left_locs.iter().map(String::as_str).collect();
        for r in right_locs {
            if left_set.contains(r.as_str()) {
                let id = self.sep_cache.next_domain_id();
                let dummy =
                    self.solver
                        .declare_fun(&format!("__sep_dc_{id}"), &[Sort::Int], Sort::Bool);
                return Ok((self.solver.bool_const(false), dummy, Rc::new(Vec::new())));
            }
        }

        let id = self.sep_cache.next_domain_id();

        // Resolve right-side location terms (always needed, O(R)).
        let mut right_terms = Vec::with_capacity(right_locs.len());
        for loc in right_locs {
            right_terms.push(self.get_or_declare_var(loc, Sort::Int)?);
        }

        let true_val = self.solver.bool_const(true);

        // Declare right-domain predicate: D_right_N : Int -> Bool
        let dr = self
            .solver
            .declare_fun(&format!("__sep_dr_{id}"), &[Sort::Int], Sort::Bool);

        let (_dl, left_terms) = if let Some((d_parent, cached_terms)) = left_parent_cache {
            // Incremental path: reuse parent's combined domain as left domain
            // AND reuse cached Terms — O(1) Rc clone, no re-resolution.
            (d_parent, cached_terms)
        } else {
            // Fresh path: create new left-domain with ground membership.
            let dl = self
                .solver
                .declare_fun(&format!("__sep_dl_{id}"), &[Sort::Int], Sort::Bool);
            let mut lt = Vec::with_capacity(left_locs.len());
            for loc in left_locs {
                lt.push(self.get_or_declare_var(loc, Sort::Int)?);
            }
            for &t in &lt {
                let dl_t = self.solver.apply(&dl, &[t]);
                // Domain predicates return Bool; native equality now handles
                // Bool/Bool constraints directly in the current ay pin (#1179).
                let membership = self.eq_term(dl_t, true_val);
                self.assertion_pipeline.push_pending_assertion(membership);
            }
            (dl, Rc::new(lt))
        };

        // Right-side membership assertions (always O(R)). Stage them as
        // top-level pending assertions so the solver sees the trigger terms
        // directly instead of buried in a nested conjunction.
        for &rt in &right_terms {
            let dr_rt = self.solver.apply(&dr, &[rt]);
            // Domain predicates return Bool; native equality now handles
            // Bool/Bool constraints directly in the current ay pin (#1179).
            let membership = self.eq_term(dr_rt, true_val);
            self.assertion_pipeline.push_pending_assertion(membership);
        }

        // Ground disjointness over the finite footprint: right-domain membership
        // is false for every left term. Together with `D_right(rt) = true`, EUF
        // congruence makes any semantic alias between a left and right location
        // contradictory, without relying on ay quantifier instantiation.
        let false_val = self.solver.bool_const(false);
        for &lt in left_terms.iter() {
            let dr_lt = self.solver.apply(&dr, &[lt]);
            let excluded = self.eq_term(dr_lt, false_val);
            self.assertion_pipeline.push_pending_assertion(excluded);
        }

        // Build combined domain predicate for parent SepConj boundaries. We only
        // need finite membership facts for actual footprint terms; parent
        // boundaries carry the exact term set separately in `combined_terms`.
        let dc = self
            .solver
            .declare_fun(&format!("__sep_dc_{id}"), &[Sort::Int], Sort::Bool);

        // Build combined Terms: parent's terms + right terms.
        // For incremental path, this extends the Rc'd parent vec with O(R) new terms.
        let combined_terms = {
            let mut ct = Vec::with_capacity(left_terms.len() + right_terms.len());
            ct.extend_from_slice(&left_terms);
            ct.extend_from_slice(&right_terms);
            Rc::new(ct)
        };

        for &term in combined_terms.iter() {
            let dc_term = self.solver.apply(&dc, &[term]);
            let membership = self.eq_term(dc_term, true_val);
            self.assertion_pipeline.push_pending_assertion(membership);
        }

        // Record cross-footprint constraint set for lazy recheck (#668).
        // Use Rc-backed Vecs to share Terms across constraint sets.
        self.assertion_pipeline
            .push_pending_disjoint_constraint((*left_terms).clone(), right_terms);

        Ok((self.solver.bool_const(true), dc, combined_terms))
    }

    /// Extract the footprint (set of heap locations) from a formula.
    ///
    /// The footprint is the set of all locations referenced by `PointsTo` assertions.
    /// This is used for enforcing disjointness in separating conjunction.
    #[allow(clippy::unused_self)] // Method signature kept for API consistency; may use encoder state in future
    pub(crate) fn extract_footprint(&self, formula: &Formula) -> Vec<String> {
        let mut seen: HashSet<&str> = HashSet::new();
        let mut locs = Vec::new();
        // Preserve first-seen order to match trust_wp_core::smt::extract_footprint_names().
        let mut stack = vec![formula];
        while let Some(current) = stack.pop() {
            match current {
                Formula::PointsTo { location, .. } => {
                    let name = location.0.as_str();
                    if seen.insert(name) {
                        locs.push(location.0.clone());
                    }
                }
                Formula::SepConj(l, r)
                | Formula::And(l, r)
                | Formula::Or(l, r)
                | Formula::Implies(l, r)
                | Formula::MagicWand(l, r) => {
                    stack.push(r);
                    stack.push(l);
                }
                Formula::Exists { body, .. } | Formula::Forall { body, .. } => {
                    stack.push(body);
                }
                Formula::True | Formula::False | Formula::Pure(_) | Formula::MutBorrow { .. } => {
                    // No heap footprint
                }
                // Formula is #[non_exhaustive]; required for cross-crate match.
                #[allow(unreachable_patterns)]
                _ => {}
            }
        }
        locs
    }

    /// Encode the magic wand: P -* Q
    ///
    /// The magic wand `P -* Q` is the adjoint of separating conjunction.
    /// Semantically: "if you add heap satisfying P (disjoint from current heap),
    /// the combined heap satisfies Q."
    ///
    /// # Encoding
    ///
    /// The magic wand is encoded as:
    /// ```text
    /// ∀ h_ext. (P(h_ext) ∧ disjoint(h, h_ext)) → Q(h ∪ h_ext)
    /// ```
    ///
    /// Since we use a simplified heap model where Rust's ownership system
    /// guarantees disjointness, we can encode this as:
    /// ```text
    /// ∀ vars_in_P. P → Q
    /// ```
    ///
    /// # Use in Rust Verification
    ///
    /// Magic wand is primarily used for:
    /// 1. **Borrow return**: When a mutable borrow ends, we "apply" the wand
    ///    to regain permission: `(y ↦ v' -* x ↦ v')` becomes `x ↦ v'`
    /// 2. **Frame reasoning**: Track what resources are "owed" back
    ///
    /// # Reference
    ///
    /// See: designs/2026-01-31-separation-logic-encoding.md Section 5
    #[cfg(not(feature = "unsafe-heap"))]
    pub(super) fn encode_magic_wand(
        &mut self,
        antecedent: &Formula,
        consequent: &Formula,
    ) -> Result<Term, EncodingError> {
        // For safe Rust with RustHorn encoding, the magic wand simplifies to
        // an implication because Rust's ownership system guarantees heap disjointness.
        //
        // Simplified encoding for safe Rust: P → Q
        // This is sound because:
        // - Rust's ownership prevents aliasing, so disjointness is automatic
        // - The "extension" heap is implicitly the borrow's heap region
        //
        // For unsafe Rust, use the heap operations (heap_read, heap_write, etc.)
        // and fresh_heap_extension() to construct full heap-based encoding:
        // `∀ h_ext. (P(h_ext) ∧ disjoint(h, h_ext)) → Q(h ∪ h_ext)`
        // See: designs/2026-01-31-separation-logic-encoding.md Section 5
        let ante_term = self.encode(antecedent)?;
        let conseq_term = self.encode(consequent)?;
        Ok(self.solver.implies(ante_term, conseq_term))
    }

    #[cfg(feature = "unsafe-heap")]
    pub(super) fn encode_magic_wand(
        &mut self,
        _antecedent: &Formula,
        _consequent: &Formula,
    ) -> Result<Term, EncodingError> {
        Err(EncodingError::unsupported(
            "magic wand implication encoding is safe-Rust-only; unsafe-heap mode requires full heap extension encoding",
        ))
    }
}

#[cfg(test)]
mod tests;
