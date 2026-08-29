// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tseitin-style `ext_eq` encoding for sequence pointwise equality.

use ay_dpll::api::{Sort, Term, TermKind};
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::{
    seq::{seq_singleton_literal_arg, should_encode_singleton_prefix_concat_opaque},
    sort_context::resolve_view_var_name,
    AYEncoder,
};
use crate::error::EncodingError;

/// Maximum number of entries in `ext_eq_registry`. Matches the existing
/// `TRUST_WP_CAP_PER_SYMBOL` convention from `ground_pool.rs`. Beyond this cap,
/// new ext_eq entries are not recorded for bridge derivation — fail-closed
/// (may return Unknown, never strengthens the VC). (#2535)
const TRUST_WP_EXT_EQ_REGISTRY_CAP: usize = 50;

/// Maximum total congruence bridge assertions across all `encode_ext_eq`
/// calls. Without this cap, the bridge loop produces O(n^2) assertions
/// where n is the registry size (each call scans all previous entries
/// with the same receiver). With `TRUST_WP_EXT_EQ_REGISTRY_CAP=50`, worst case
/// is 50*49/2 = 1225 bridges. This cap bounds total bridge assertions
/// to prevent OOM for functions with many ext_eq entries. (#2708)
///
/// Fail-closed: beyond this cap, new congruence bridges are skipped.
/// The existing bridges still provide solver information; the cap only
/// prevents the quadratic blowup from consuming all memory.
const TRUST_WP_MAX_CONGRUENCE_BRIDGES: usize = 100;

fn concat_operands(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "concat" || args.len() != 1 {
        return None;
    }
    Some((receiver.as_ref(), &args[0]))
}

/// Detect `seq_empty()` / `Seq::empty()` at the PureExpr level.
fn is_seq_empty_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args } => name == "seq_empty" && args.is_empty(),
        PureExpr::MethodCall { method, args, .. } => method == "empty" && args.is_empty(),
        _ => false,
    }
}

fn has_opaque_singleton_prefix_concat_expr(expr: &PureExpr) -> bool {
    let Some((left, right)) = concat_operands(expr) else {
        return false;
    };
    should_encode_singleton_prefix_concat_opaque(left, right)
}

fn opaque_singleton_prefix_concat_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let (left, right) = concat_operands(expr)?;
    if !should_encode_singleton_prefix_concat_opaque(left, right) {
        return None;
    }
    let elem = seq_singleton_literal_arg(left)?;
    Some((elem, right))
}

fn normalize_empty_concat_expr(mut expr: &PureExpr) -> &PureExpr {
    loop {
        let Some((left, right)) = concat_operands(expr) else {
            return expr;
        };
        if is_seq_empty_expr(left) {
            expr = right;
        } else if is_seq_empty_expr(right) {
            expr = left;
        } else {
            return expr;
        }
    }
}

impl AYEncoder {
    fn encode_ext_eq_operand(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let Some((elem, other)) = opaque_singleton_prefix_concat_parts(expr) {
            return self.opaque_singleton_prefix_concat_carrier_term(elem, other, prefix);
        }
        self.encode_pure_impl(expr, prefix)
    }

    /// Build the index value used by one extensional-equality quantifier.
    ///
    /// A concrete concat is expanded into a local ITE over its recorded
    /// operands. This is the same Seq law as the former global Axioms 16/17,
    /// but it has only the ext-equality index binder instead of adding two
    /// more universally quantified sequence operands to every concat query.
    /// Non-concat leaves retain the legacy `seq_index_logic` bridge.
    fn ext_eq_pointwise_index_term(
        &mut self,
        seq_term: Term,
        index: Term,
        visiting: &mut std::collections::HashSet<Term>,
    ) -> Result<(Term, Term), EncodingError> {
        if visiting.insert(seq_term) {
            if let Some((left, right)) = self.seq_state.get_seq_concat_args(&seq_term) {
                let left_len = self.seq_len_term(left)?;
                let in_left = self.solver.lt(index, left_len);
                let (left_value, left_trigger) =
                    self.ext_eq_pointwise_index_term(left, index, visiting)?;
                let right_index = self.solver.sub(index, left_len);
                let (right_value, _right_trigger) =
                    self.ext_eq_pointwise_index_term(right, right_index, visiting)?;
                visiting.remove(&seq_term);
                let value = self.solver.ite(in_left, left_value, right_value);
                return Ok((value, left_trigger));
            }
            visiting.remove(&seq_term);
        }

        let seq_idx_fn = self.ensure_seq_theory().seq_index_logic.clone();
        let value = self.safe_apply("ext_eq/pointwise", &seq_idx_fn, &[seq_term, index])?;
        Ok((value, value))
    }

    fn assert_ext_eq_ground_index_for_pair(
        &mut self,
        r_term: Term,
        o_term: Term,
        ext_eq_var: Term,
        index: Term,
    ) -> Result<(), EncodingError> {
        let len_r = self.seq_len_term(r_term)?;
        let zero = self.solver.int_const(0);
        let index_ge_zero = self.solver.ge(index, zero);
        let index_lt_len = self.solver.lt(index, len_r);
        let in_bounds = self.solver.and(index_ge_zero, index_lt_len);

        let receiver_arr = self.seq_array_term(r_term)?;
        let receiver_offset = self.seq_offset_term(r_term)?;
        let other_arr = self.seq_array_term(o_term)?;
        let other_offset = self.seq_offset_term(o_term)?;
        let receiver_idx = self.solver.add(receiver_offset, index);
        let other_idx = self.solver.add(other_offset, index);
        let receiver_value = self.safe_select("ext_eq/ground_index", receiver_arr, receiver_idx)?;
        let other_value = self.safe_select("ext_eq/ground_index", other_arr, other_idx)?;
        let values_eq = self.eq_term(receiver_value, other_value);
        let body = self.solver.implies(in_bounds, values_eq);
        let implication = self.solver.implies(ext_eq_var, body);
        self.assert_solver_term("ext_eq/ground_index", implication);
        Ok(())
    }

    fn assert_opaque_singleton_prefix_first_element(
        &mut self,
        concat_expr: &PureExpr,
        other_term: Term,
        ext_eq_var: Term,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        let Some((elem, _rest)) = opaque_singleton_prefix_concat_parts(concat_expr) else {
            return Ok(());
        };
        let elem_term = self.encode_pure_impl(elem, prefix)?;
        let zero = self.solver.int_const(0);
        let other_len = self.seq_len_term(other_term)?;
        let other_non_empty = self.solver.lt(zero, other_len);
        let other_first = self.seq_index_term(other_term, zero)?;
        let first_matches_elem = self.eq_term(other_first, elem_term);
        let guarded_match = self.solver.implies(other_non_empty, first_matches_elem);
        let implication = self.solver.implies(ext_eq_var, guarded_match);
        self.assert_solver_term("ext_eq/opaque_singleton_prefix_first", implication);
        Ok(())
    }

    pub(crate) fn assert_ext_eq_ground_index_consequences(
        &mut self,
        seq_term: Term,
        index: Term,
    ) -> Result<(), EncodingError> {
        let entries: Vec<(Term, Term, Term)> = self
            .encoding_cache
            .ext_eq_registry()
            .iter()
            .copied()
            .filter(|(r_term, o_term, _)| *r_term == seq_term || *o_term == seq_term)
            .collect();
        for (r_term, o_term, ext_eq_var) in entries {
            self.assert_ext_eq_ground_index_for_pair(r_term, o_term, ext_eq_var, index)?;
        }
        Ok(())
    }

    /// Encode `ext_eq`: pointwise equality of two sequences (#737).
    ///
    /// For Seq receivers, uses Tseitin-style encoding: creates a fresh Bool
    /// variable `ext_eq_N` and currently asserts the two forward axioms:
    ///   1. `ext_eq_N => len(a) == len(b)`
    ///   2. `ext_eq_N => forall i. in_bounds(i) => index(a,i) == index(b,i)`
    ///
    /// This avoids combining `len_eq` and `forall(pointwise)` in a single
    /// `and(...)` term, which prevents ay's E-matching engine from
    /// instantiating quantified Seq length axioms on the ground terms
    /// inside the conjunction (#962). The reverse implication
    /// `(len(a) == len(b) AND pointwise) => ext_eq_N` is suppressed because
    /// it causes ay quantifier instantiation loops even with the ay#6481
    /// NNF skolemization fix. The encoding is one-directional: positive
    /// `ext_eq` uses are sound, negated `ext_eq` is conservative.
    ///
    /// For non-Seq receivers, falls back to a Bool uninterpreted function.
    #[allow(clippy::too_many_lines)] // Seq ext_eq encoding with skolemization and fallback
    pub(super) fn encode_ext_eq(
        &mut self,
        receiver: &PureExpr,
        other: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let receiver_sort = self.infer_encoded_sort(receiver, prefix);
        let other_sort = self.infer_encoded_sort(other, prefix);
        let receiver_is_seq_sort = receiver_sort.is_seq();
        let other_is_seq_sort = other_sort.is_seq();
        let seq_operands = self.is_seq_receiver(receiver, prefix)
            || self.is_seq_receiver(other, prefix)
            || receiver_is_seq_sort
            || other_is_seq_sort;

        if seq_operands {
            // For Seq, ext_eq normally means equal length and identical
            // elements. Singleton-prefix concat is a solver-limited shape:
            // encoding the full extensional bridge currently creates false
            // UNSAT base contexts in ay, so that branch below weakens the
            // bridge instead of claiming full semantic equivalence.
            self.ensure_seq_theory();
            let r = Self::normalize_seq_receiver(normalize_empty_concat_expr(receiver));
            let o = Self::normalize_seq_receiver(normalize_empty_concat_expr(other));

            // Record Seq sort hints for both receivers
            if let Some(name) = resolve_view_var_name(r.as_ref(), prefix) {
                self.record_sort_hint(name, ExprSort::Seq);
            }
            if let Some(name) = resolve_view_var_name(o.as_ref(), prefix) {
                self.record_sort_hint(name, ExprSort::Seq);
            }

            if r.as_ref() == o.as_ref() {
                // Encode both sides so any Seq sort/ground-term side effects still
                // happen, then short-circuit the equality itself. This turns
                // trivial identities like ext_eq(s, seq_empty().concat(s)) into a
                // ground Bool instead of forcing the full Tseitin/pointwise path.
                let _ = self.encode_pure_impl(r.as_ref(), prefix)?;
                let _ = self.encode_pure_impl(o.as_ref(), prefix)?;
                return Ok(self.solver.bool_const(true));
            }

            let opaque_singleton_prefix_concat =
                has_opaque_singleton_prefix_concat_expr(r.as_ref())
                    || has_opaque_singleton_prefix_concat_expr(o.as_ref());
            let r_term = self.encode_ext_eq_operand(r.as_ref(), prefix)?;
            let o_term = self.encode_ext_eq_operand(o.as_ref(), prefix)?;

            let mut len_r = None;
            let mut len_eq = None;
            let mut concat_len_facts = Vec::new();
            if !opaque_singleton_prefix_concat {
                // Length equality
                let receiver_len = self.seq_len_term(r_term)?;
                let other_len = self.seq_len_term(o_term)?;
                len_r = Some(receiver_len);
                len_eq = Some(self.eq_term(receiver_len, other_len));

                for (concat_expr, concat_term) in [(r.as_ref(), r_term), (o.as_ref(), o_term)] {
                    let Some((left, right)) = concat_operands(concat_expr) else {
                        continue;
                    };
                    let left_term = self.encode_pure_impl(left, prefix)?;
                    let right_term = self.encode_pure_impl(right, prefix)?;
                    let len_concat = self.seq_len_term(concat_term)?;
                    let len_left = self.seq_len_term(left_term)?;
                    let len_right = self.seq_len_term(right_term)?;
                    let len_sum = self.solver.add(len_left, len_right);
                    concat_len_facts.push(self.eq_term(len_concat, len_sum));

                    // Ground concat identity: if either operand is seq_empty,
                    // assert concat(empty, s) = s or concat(s, empty) = s directly.
                    // This bypasses ay-dpll's single-round E-matching limitation
                    // for the quantified identity axioms (15c/15d). (#2116)
                    if is_seq_empty_expr(left) {
                        let identity = self.eq_term(concat_term, right_term);
                        self.assert_solver_term("ext_eq/concat_left_identity", identity);
                    } else if is_seq_empty_expr(right) {
                        let identity = self.eq_term(concat_term, left_term);
                        self.assert_solver_term("ext_eq/concat_right_identity", identity);
                    }
                }
            }

            // Tseitin variable: fresh Bool constant representing ext_eq result.
            // Defined by three separate axioms to avoid combining len_eq and
            // pointwise in a single conjunction (#962).
            let ext_eq_var = self.solver.fresh_var("ext_eq", Sort::Bool);
            if opaque_singleton_prefix_concat {
                self.assert_opaque_singleton_prefix_first_element(
                    r.as_ref(),
                    o_term,
                    ext_eq_var,
                    prefix,
                )?;
                self.assert_opaque_singleton_prefix_first_element(
                    o.as_ref(),
                    r_term,
                    ext_eq_var,
                    prefix,
                )?;
            }

            // Axiom 1: ext_eq_var => len_eq
            if let Some(len_eq) = len_eq {
                let fwd_len = self.solver.implies(ext_eq_var, len_eq);
                self.assert_solver_term("ext_eq/fwd_len", fwd_len);
            } else {
                tracing::debug!("suppressing opaque singleton-prefix ext_eq length implication");
            }
            for concat_len in concat_len_facts {
                let fwd_concat_len = self.solver.implies(ext_eq_var, concat_len);
                self.assert_solver_term("ext_eq/fwd_concat_len", fwd_concat_len);
            }

            // Pointwise element equality: forall i. 0 <= i < len(a) =>
            // element(a, i) == element(b, i).
            //
            // Prefer direct Array selects when either side already has a
            // concrete SeqValue. This keeps singleton/concat cases on the
            // Array+Length model instead of routing back through the older
            // seq_index_logic UF + concat axioms path, which is the remaining
            // false-Unsat surface in #2404.
            //
            // Fully symbolic non-concat leaves use seq_index_logic UF
            // applications. Concrete concat terms are expanded locally into
            // their exact left/right ITE, avoiding the global three-binder
            // concat-index schemas while preserving their relevant instance.
            //
            // The iterator-produced shape `concat(seq![v], next@)` is a
            // ay-sensitive case: even small forward/reverse ext_eq facts over
            // the synthesized Array-backed concat value can false-UNSAT
            // otherwise satisfiable base contexts. Suppress the pointwise
            // schema for that shape. This is conservative for verification:
            // preconditions become weaker and postconditions become harder to
            // prove rather than producing vacuous proofs.
            let suppress_quantified_pointwise = opaque_singleton_prefix_concat;
            let use_array_pointwise = !suppress_quantified_pointwise
                && (self.has_seq_value(r_term) || self.has_seq_value(o_term));

            if !suppress_quantified_pointwise {
                let len_r = len_r.expect("non-opaque ext_eq computes receiver length");
                let i = self.solver.fresh_var("ext_eq_i", Sort::Int);
                let zero = self.solver.int_const(0);
                let i_ge_zero = self.solver.ge(i, zero);
                let i_lt_len = self.solver.lt(i, len_r);
                let in_bounds = self.solver.and(i_ge_zero, i_lt_len);
                let (idx_r, idx_o, trigger_r, trigger_o) = if use_array_pointwise {
                    let receiver_arr = self.seq_array_term(r_term)?;
                    let receiver_offset = self.seq_offset_term(r_term)?;
                    let other_arr = self.seq_array_term(o_term)?;
                    let other_offset = self.seq_offset_term(o_term)?;
                    let receiver_shifted = self.solver.add(receiver_offset, i);
                    let other_shifted = self.solver.add(other_offset, i);
                    let idx_r =
                        self.safe_select("ext_eq/pointwise", receiver_arr, receiver_shifted)?;
                    let idx_o = self.safe_select("ext_eq/pointwise", other_arr, other_shifted)?;
                    (idx_r, idx_o, idx_r, idx_o)
                } else {
                    let (idx_r, trigger_r) = self.ext_eq_pointwise_index_term(
                        r_term,
                        i,
                        &mut std::collections::HashSet::new(),
                    )?;
                    let (idx_o, trigger_o) = self.ext_eq_pointwise_index_term(
                        o_term,
                        i,
                        &mut std::collections::HashSet::new(),
                    )?;
                    (idx_r, idx_o, trigger_r, trigger_o)
                };
                let elems_eq = self.eq_term(idx_r, idx_o);
                let pointwise_body = self.solver.implies(in_bounds, elems_eq);
                // Trigger on either index application so the quantifier fires when
                // ay sees a ground element-read term for either operand (#1136).
                let pointwise = self.solver.forall_with_triggers(
                    &[i],
                    pointwise_body,
                    &[&[trigger_r], &[trigger_o]],
                );

                // Axiom 2: ext_eq_var => pointwise
                let fwd_pw = self.solver.implies(ext_eq_var, pointwise);
                self.assert_solver_term("ext_eq/fwd_pw", fwd_pw);
            } else {
                tracing::debug!(
                    "suppressing quantified ext_eq pointwise axiom for opaque singleton-prefix concat"
                );
            }

            if use_array_pointwise && !suppress_quantified_pointwise {
                // Single-step iterator proofs need the first element relation at
                // index 0. Assert that ground implication directly on the
                // Array-backed path when an index-0 read is already present so
                // we do not rely on quantifier triggering to propagate the
                // concrete prefix element from concat.
                let zero_idx = self.solver.int_const(0);
                let receiver_len = len_r.expect("non-opaque ext_eq computes receiver length");
                let idx0_in_bounds = self.solver.lt(zero_idx, receiver_len);
                let receiver_arr = self.seq_array_term(r_term)?;
                let receiver_offset = self.seq_offset_term(r_term)?;
                let other_arr = self.seq_array_term(o_term)?;
                let other_offset = self.seq_offset_term(o_term)?;
                let receiver_idx0 = self.solver.add(receiver_offset, zero_idx);
                let other_idx0 = self.solver.add(other_offset, zero_idx);
                let receiver_value_idx0 =
                    self.safe_select("ext_eq/fwd_idx0", receiver_arr, receiver_idx0)?;
                let other_value_idx0 =
                    self.safe_select("ext_eq/fwd_idx0", other_arr, other_idx0)?;
                let idx0_eq = self.eq_term(receiver_value_idx0, other_value_idx0);
                let idx0_body = self.solver.implies(idx0_in_bounds, idx0_eq);
                let fwd_idx0 = self.solver.implies(ext_eq_var, idx0_body);
                self.assert_solver_term("ext_eq/fwd_idx0", fwd_idx0);
            } else if use_array_pointwise {
                tracing::debug!("suppressing opaque singleton-prefix ext_eq index-0 bridge");
            }

            // Seed ground `seq_index_logic(s, 0)` terms only on the fully
            // symbolic path (#2172). The symbolic pointwise quantifier
            // triggers on the UF applications, so ext_eq still needs a ground
            // `seq_index_logic` term to fire at i=0. On the Array-backed path
            // above, the triggers are direct `select` terms and `fwd_idx0`
            // already propagates the first element without re-entering the
            // legacy bridge/concat axiom chain from #2404.
            if !use_array_pointwise && !suppress_quantified_pointwise {
                self.set_needs_seq_index_ground_terms();
                let zero = self.solver.int_const(0);
                let _ = self.seq_index_term(r_term, zero)?;
                let _ = self.seq_index_term(o_term, zero)?;
            }

            // Axiom 3 (full reverse direction) is SUPPRESSED:
            // Even with the ay#6481 NNF skolemization fix (included in
            // the current ay pin), the reverse axiom
            //   (len_eq AND pointwise) => ext_eq_var
            // causes quantifier instantiation loops when the pointwise
            // forall appears in the antecedent.
            //
            // Instead, assert a GROUND reverse: if the two sequence terms
            // are equal in the SMT model, ext_eq must hold. This avoids
            // quantifiers while enabling initialization proofs where
            // concat identity reduces both sides to the same term. (#2116)
            if !opaque_singleton_prefix_concat {
                let terms_equal = self.eq_term(r_term, o_term);
                let rev_eq = self.solver.implies(terms_equal, ext_eq_var);
                self.assert_solver_term("ext_eq/rev_term_eq", rev_eq);
            } else {
                tracing::debug!(
                    "suppressing opaque singleton-prefix ext_eq reverse term-equality implication"
                );
            }

            // Congruence bridge: propagate ext_eq across Tseitin variables that
            // share the same receiver (#2116, #2465). When two ext_eq's have
            //   ext_eq_old = ext_eq(A, B_old)  and  ext_eq_new = ext_eq(A, B_new)
            // the bridge asserts: ext_eq_old AND (B_old = B_new) => ext_eq_new.
            // The solver's E-graph evaluates B_old = B_new through ground axiom
            // chains (push_back-concat identity + iterator step transition fact),
            // closing preservation proofs without the suppressed quantified
            // reverse Tseitin. In the finite ground lane,
            // `assert_seq_component_aliases_from_assertions` emits this native
            // alias only after Array+Length+Offset equality is authenticated.
            //
            // The bridge loop is O(n) per call and O(n^2) total across all calls
            // sharing a receiver. Cap total bridges at TRUST_WP_MAX_CONGRUENCE_BRIDGES to
            // prevent OOM for functions with many ext_eq entries. (#2708)
            {
                let bridge_budget_remaining = TRUST_WP_MAX_CONGRUENCE_BRIDGES
                    .saturating_sub(self.encoding_cache.ext_eq_bridge_count());
                if bridge_budget_remaining > 0 {
                    let bridges: Vec<(Term, Term)> = self
                        .encoding_cache
                        .ext_eq_registry()
                        .iter()
                        .filter(|(prev_r, _, _)| *prev_r == r_term)
                        .map(|(_, prev_o, prev_eq)| (*prev_o, *prev_eq))
                        .collect();
                    for (prev_o, prev_eq) in bridges.into_iter().take(bridge_budget_remaining) {
                        let o_eq = self.eq_term(prev_o, o_term);
                        let antecedent = self.solver.and(prev_eq, o_eq);
                        let bridge = self.solver.implies(antecedent, ext_eq_var);
                        self.assert_solver_term("ext_eq/congruence_bridge", bridge);
                        self.encoding_cache.increment_ext_eq_bridge_count();
                    }
                } else {
                    tracing::debug!(
                        cap = TRUST_WP_MAX_CONGRUENCE_BRIDGES,
                        "ext_eq congruence bridge cap reached, skipping bridges for this call"
                    );
                }
                if self.encoding_cache.ext_eq_registry_len() < TRUST_WP_EXT_EQ_REGISTRY_CAP {
                    self.encoding_cache
                        .ext_eq_registry_push((r_term, o_term, ext_eq_var));
                }
            }

            Ok(ext_eq_var)
        } else {
            // Non-Seq: fall back to Bool uninterpreted function
            let result = self.encode_bool_method_predicate(
                receiver,
                "ext_eq",
                std::slice::from_ref(other),
                prefix,
            )?;
            // FMap ext_eq equal-args ground law. The FMap EXT_EQ contract
            // (trust-wp-std/src/logic/fmap.rs `FMap::ext_eq`):
            //   result == (self.len() == arg1.len() &&
            //       forall<k> self.contains(k) ==> arg1.contains(k)
            //           && arg1.lookup(k) == self.lookup(k))
            // instantiated at equal arguments reduces propositionally to
            // `true` (len m == len m; contains(m,k) ==> contains(m,k) &&
            // lookup(m,k) == lookup(m,k)), so `a == b ==> ext_eq(a, b)` is
            // entailed by the law plus congruence — a ground, direction-safe
            // instance. Without it the fallback UF has no defining law in
            // scope and even the reflexive `r@.ext_eq(xs_snap@)` (equal-view)
            // goal is unprovable. Scoped to FMap-sorted operands, where the
            // cited law governs. (ce-census 2026-08-20, cc/collections
            // roundtrip_hashmap_into_iter proof_assert#4)
            if self.quantifier_state.quantifier_depth() == 0 {
                if let TermKind::App { num_args: 2, .. } = self.solver.term_kind(result) {
                    let children = self.solver.term_children(result);
                    if let [a, b] = children.as_slice() {
                        let fmap = crate::encoder::sort_context::sort_inference::fmap_sort();
                        if self.solver.get_sort(*a) == fmap && self.solver.get_sort(*b) == fmap {
                            let args_eq = self.eq_term(*a, *b);
                            let guarded = self.solver.implies(args_eq, result);
                            self.assert_solver_term("fmap_ext_eq_equal_args_ground", guarded);
                        }
                    }
                }
            }
            Ok(result)
        }
    }
}
