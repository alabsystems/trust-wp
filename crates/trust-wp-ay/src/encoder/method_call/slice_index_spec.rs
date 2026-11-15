// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SliceIndexSpec predicate encoding for usize and range indices.
//!
//! When the Vec/slice indexing contracts use the generic `SliceIndexSpec`
//! predicate surface (`ix.in_bounds(self@)`, `ix.has_value(self@, result)`,
//! `ix.resolve_elsewhere(self@, (^self)@)`), these predicates are
//! uninterpreted in the SMT encoding — no axioms connect them to concrete
//! semantics. This module provides concrete semantics for `usize` (Int)
//! indices and `RangeInclusive<usize>` receivers:
//!
//! - `in_bounds(ix, seq)` => `ix >= 0 && ix < seq_len(seq)`
//! - `has_value(ix, seq, out)` => `seq_index_logic(seq, ix) == out`
//! - `resolve_elsewhere(ix, old_seq, new_seq)` => for each protected index j,
//!   `0 <= j < len(old_seq) ==> old_seq[j] == new_seq[j]`
//!
//! Quantified logics return that universal frame condition directly.  The
//! QF_AUFLIA lane instead returns a fresh conservative monitor and emits only
//! predicate-guarded instances at authenticated ground indices observed by the
//! VC.  This keeps the query genuinely quantifier-free: the abstraction admits
//! more models than the universal semantics, so it can lose proofs but cannot
//! create a false verification.
//!
//! References:
//! - Trait: `crates/trust-wp-std/src/std/slice.rs` (`SliceIndexSpec`)
//! - Spec strings: `crates/trust-wp-std/src/std/builtin_registry.rs`

use std::sync::Arc;

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{resolve_sort_name, ExprSort, PureExpr};

use super::super::{AYEncoder, ResolveElsewhereFootprint, ResolveElsewhereFrame};
use crate::{
    encoder::sort_context::{
        effective_expr_annotation, extract_base_var_name, resolve_nameable_expr,
    },
    error::EncodingError,
};

impl AYEncoder {
    fn expr_sort_is_range_inclusive(sort: &ExprSort) -> bool {
        match sort {
            ExprSort::Datatype(id) => {
                resolve_sort_name(*id).rsplit("::").next() == Some("RangeInclusive")
            }
            ExprSort::Ref(inner) | ExprSort::MutRef(inner) => {
                Self::expr_sort_is_range_inclusive(inner)
            }
            _ => false,
        }
    }

    fn receiver_is_range_inclusive(
        &self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> bool {
        effective_expr_annotation(receiver).is_some_and(Self::expr_sort_is_range_inclusive)
            || resolve_nameable_expr(receiver, prefix)
                .and_then(|name| self.sort_hint(&name))
                .is_some_and(Self::expr_sort_is_range_inclusive)
            || extract_base_var_name(receiver)
                .and_then(|name| self.sort_hint(name))
                .is_some_and(Self::expr_sort_is_range_inclusive)
    }

    fn range_inclusive_endpoint_terms(
        &mut self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(Term, Term), EncodingError> {
        let start_expr = PureExpr::MethodCall {
            receiver: Arc::new(receiver.clone()),
            method: "start_log".to_string(),
            args: vec![],
        };
        let end_expr = PureExpr::MethodCall {
            receiver: Arc::new(receiver.clone()),
            method: "end_log".to_string(),
            args: vec![],
        };
        let start = self.encode_pure_impl(&start_expr, prefix)?;
        let end = self.encode_pure_impl(&end_expr, prefix)?;
        Ok((start, end))
    }

    fn in_bounds_len_bridge_candidates(seq_arg: &PureExpr) -> Vec<PureExpr> {
        let mut candidates = Vec::new();

        if let PureExpr::View(viewed) = seq_arg {
            if let PureExpr::Deref(derefed) = viewed.as_ref() {
                candidates.push(PureExpr::Deref(Arc::clone(derefed)));
                candidates.push(derefed.as_ref().clone());
            }
        }

        candidates
    }

    fn assert_in_bounds_len_bridges(
        &mut self,
        seq_arg: &PureExpr,
        seq_len: Term,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        for candidate in Self::in_bounds_len_bridge_candidates(seq_arg) {
            if !self.is_seq_receiver(&candidate, prefix) {
                continue;
            }
            let Ok(len) = self.encode_len_dispatch(&candidate, &[], prefix) else {
                continue;
            };
            if self.solver.get_sort(len) != Sort::Int {
                continue;
            }
            if len != seq_len {
                let eq = self.eq_term(len, seq_len);
                self.assert_term(eq);
            }
        }
    }

    /// Encode `ix.in_bounds(seq)` for a usize (Int-sorted) index.
    ///
    /// Concrete semantics: `ix >= 0 && ix < seq_len(seq)`
    ///
    /// When the receiver is NOT Int-sorted, falls back to the generic
    /// Bool predicate UF encoding (for range types etc.).
    pub(super) fn encode_in_bounds(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if args.len() != 1 {
            return Err(EncodingError::unsupported(format!(
                "in_bounds expects 1 argument (seq), got {}",
                args.len()
            )));
        }

        if self.receiver_is_range_inclusive(receiver, prefix) {
            let seq_term = self.encode_pure_impl(&args[0], prefix)?;
            let (start, end) = self.range_inclusive_endpoint_terms(receiver, prefix)?;

            let zero = self.solver.int_const(0);
            let start_ge_zero = self.solver.ge(start, zero);
            let end_ge_zero = self.solver.ge(end, zero);
            let start_le_end = self.solver.le(start, end);
            let seq_len = self.seq_len_term(seq_term)?;
            let end_lt_len = self.solver.lt(end, seq_len);
            let bounds = self.solver.and(start_le_end, end_lt_len);
            let nonnegative = self.solver.and(end_ge_zero, bounds);

            return Ok(self.solver.and(start_ge_zero, nonnegative));
        }

        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let receiver_sort = self.solver.get_sort(receiver_term);

        // Only inline concrete semantics for Int (usize) indices
        if receiver_sort != Sort::Int {
            return self.encode_bool_method_predicate(receiver, "in_bounds", args, prefix);
        }

        let seq_term = self.encode_pure_impl(&args[0], prefix)?;

        // in_bounds(ix, seq) <=> ix >= 0 && ix < seq_len(seq)
        let zero = self.solver.int_const(0);
        let ix_ge_zero = self.solver.ge(receiver_term, zero);
        let seq_len = self.seq_len_term(seq_term)?;
        self.assert_in_bounds_len_bridges(&args[0], seq_len, prefix);
        let ix_lt_len = self.solver.lt(receiver_term, seq_len);
        let result = self.solver.and(ix_ge_zero, ix_lt_len);

        Ok(result)
    }

    /// Encode `ix.has_value(seq, out)` for a usize (Int-sorted) index.
    ///
    /// Concrete semantics: `seq_index_logic(seq, ix) == out`
    ///
    /// When the receiver is NOT Int-sorted, falls back to the generic
    /// Bool predicate UF encoding (for range types etc.).
    pub(super) fn encode_has_value(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if args.len() != 2 {
            return Err(EncodingError::unsupported(format!(
                "has_value expects 2 arguments (seq, out), got {}",
                args.len()
            )));
        }

        if self.receiver_is_range_inclusive(receiver, prefix) {
            let seq_term = self.encode_pure_impl(&args[0], prefix)?;
            let out_term = self.encode_pure_impl(&args[1], prefix)?;
            let (start, end) = self.range_inclusive_endpoint_terms(receiver, prefix)?;
            let one = self.solver.int_const(1);
            let end_exclusive = self.solver.add(end, one);

            let seq_funcs = self.ensure_seq_theory();
            let subseq = self.solver.apply(
                &seq_funcs.seq_subsequence,
                &[seq_term, start, end_exclusive],
            );

            return Ok(self.eq_term(subseq, out_term));
        }

        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let receiver_sort = self.solver.get_sort(receiver_term);

        // Only inline concrete semantics for Int (usize) indices
        if receiver_sort != Sort::Int {
            return self.encode_bool_method_predicate(receiver, "has_value", args, prefix);
        }

        let seq_term = self.encode_pure_impl(&args[0], prefix)?;
        let out_term = self.encode_pure_impl(&args[1], prefix)?;

        // has_value(ix, seq, out) <=> seq_index_logic(seq, ix) == out
        let indexed = self.seq_index_term(seq_term, receiver_term)?;
        let result = self.eq_term(indexed, out_term);

        Ok(result)
    }

    /// Encode `ix.resolve_elsewhere(old_seq, new_seq)` for a usize (Int-sorted) index.
    ///
    /// Concrete semantics: for all j, j != ix && 0 <= j < len(old_seq) ==>
    ///   seq_index_logic(old_seq, j) == seq_index_logic(new_seq, j)
    ///
    /// The quantified frame condition is returned directly as the Bool term.
    /// This avoids the UF + axiom indirection that would require ay-dpll to
    /// chain E-matching across the biconditional boundary.
    ///
    /// When the receiver is NOT Int-sorted, falls back to the generic
    /// Bool predicate UF encoding (for range types etc.).
    pub(super) fn encode_resolve_elsewhere(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if args.len() != 2 {
            return Err(EncodingError::unsupported(format!(
                "resolve_elsewhere expects 2 arguments (old_seq, new_seq), got {}",
                args.len()
            )));
        }

        if self.receiver_is_range_inclusive(receiver, prefix) {
            let old_seq = Self::normalize_seq_receiver(&args[0]);
            let new_seq = Self::normalize_seq_receiver(&args[1]);
            let old_seq_term = self.encode_pure_impl(old_seq.as_ref(), prefix)?;
            let new_seq_term = self.encode_pure_impl(new_seq.as_ref(), prefix)?;
            let (start, end) = self.range_inclusive_endpoint_terms(receiver, prefix)?;

            self.seq_state.set_needs_index_ground_terms();

            // Resolve the exact receiver-owned length component before
            // constructing either representation.  In finite-projector lanes
            // this authenticates the method-local receiver/projector pair;
            // there is deliberately no global raw `seq_len` bridge.
            let old_len = self.seq_len_term(old_seq_term)?;
            let footprint = ResolveElsewhereFootprint::RangeInclusive { start, end };
            if !self.supports_quantifiers() {
                let id = self.seq_state.next_fresh_seq_lit_id();
                let predicate = self
                    .solver
                    .declare_const(&format!("__trust_wp_resolve_elsewhere_{id}"), Sort::Bool);
                self.seq_state
                    .register_resolve_elsewhere_frame(ResolveElsewhereFrame {
                        predicate,
                        old_seq: old_seq_term,
                        new_seq: new_seq_term,
                        old_len,
                        footprint,
                    });
                return Ok(predicate);
            }

            let seq_funcs = self.ensure_seq_theory();
            let j = self.solver.fresh_var("re_rng_j", Sort::Int);
            let zero = self.solver.int_const(0);
            let j_ge_zero = self.solver.ge(j, zero);
            let j_lt_len = self.solver.lt(j, old_len);
            let before_start = self.solver.lt(j, start);
            let after_end = self.solver.lt(end, j);
            let outside_range = self.solver.or(before_start, after_end);
            let in_old = self.solver.and(j_lt_len, outside_range);
            let guard = self.solver.and(j_ge_zero, in_old);

            let old_at_j = self
                .solver
                .apply(&seq_funcs.seq_index_logic, &[old_seq_term, j]);
            let new_at_j = self
                .solver
                .apply(&seq_funcs.seq_index_logic, &[new_seq_term, j]);
            let eq_at_j = self.eq_term(old_at_j, new_at_j);
            let body = self.solver.implies(guard, eq_at_j);

            return Ok(self
                .solver
                .forall_with_triggers(&[j], body, &[&[old_at_j], &[new_at_j]]));
        }

        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let receiver_sort = self.solver.get_sort(receiver_term);

        // Only inline concrete semantics for Int (usize) indices
        if receiver_sort != Sort::Int {
            return self.encode_bool_method_predicate(receiver, "resolve_elsewhere", args, prefix);
        }

        let old_seq = Self::normalize_seq_receiver(&args[0]);
        let new_seq = Self::normalize_seq_receiver(&args[1]);
        let old_seq_term = self.encode_pure_impl(old_seq.as_ref(), prefix)?;
        let new_seq_term = self.encode_pure_impl(new_seq.as_ref(), prefix)?;

        // The forall quantifier below uses seq_index_logic UF triggers.
        // Enable ground term synthesis so that subsequent index_logic
        // method calls produce seq_index_logic UF applications in the
        // e-graph, allowing ay-dpll's E-matching to fire the triggers.
        self.seq_state.set_needs_index_ground_terms();

        // Use the authenticated receiver-owned component.  A raw projector
        // equality here would become a global axiom and could couple unrelated
        // receivers that merely share part of their finite representation.
        let old_len = self.seq_len_term(old_seq_term)?;
        let footprint = ResolveElsewhereFootprint::Index(receiver_term);
        if !self.supports_quantifiers() {
            let id = self.seq_state.next_fresh_seq_lit_id();
            let predicate = self
                .solver
                .declare_const(&format!("__trust_wp_resolve_elsewhere_{id}"), Sort::Bool);
            self.seq_state
                .register_resolve_elsewhere_frame(ResolveElsewhereFrame {
                    predicate,
                    old_seq: old_seq_term,
                    new_seq: new_seq_term,
                    old_len,
                    footprint,
                });
            return Ok(predicate);
        }

        let seq_funcs = self.ensure_seq_theory();

        // Build: forall j. (0 <= j < len(old) && j != ix) ==>
        //          index_logic(old, j) == index_logic(new, j)
        let j = self.solver.fresh_var("re_j", Sort::Int);
        let zero = self.solver.int_const(0);
        let j_ge_zero = self.solver.ge(j, zero);
        let j_lt_len = self.solver.lt(j, old_len);
        let j_eq_ix = self.eq_term(j, receiver_term);
        let j_ne_ix = self.solver.not(j_eq_ix);
        let j_in_range = self.solver.and(j_lt_len, j_ne_ix);
        let guard = self.solver.and(j_ge_zero, j_in_range);

        let old_at_j = self
            .solver
            .apply(&seq_funcs.seq_index_logic, &[old_seq_term, j]);
        let new_at_j = self
            .solver
            .apply(&seq_funcs.seq_index_logic, &[new_seq_term, j]);
        let eq_at_j = self.eq_term(old_at_j, new_at_j);
        let body = self.solver.implies(guard, eq_at_j);

        // Use dual triggers on index_logic to control instantiation:
        // fires when either old or new array is accessed at any index.
        let forall_frame =
            self.solver
                .forall_with_triggers(&[j], body, &[&[old_at_j], &[new_at_j]]);

        Ok(forall_frame)
    }

    /// Materialize the quantifier-free `resolve_elsewhere` monitor at every
    /// authenticated ground index observed on either participating receiver.
    ///
    /// Each emitted implication is guarded by the exact fresh predicate that
    /// the method returned, preserving arbitrary caller polarity.  Receiver
    /// and length identities must still match the method-local association;
    /// sharing only a length (or any other partial component) is insufficient.
    pub(crate) fn assert_resolve_elsewhere_ground_instances(&mut self) -> usize {
        const INSTANCE_BUDGET: usize = 64;

        let frames = self.seq_state.resolve_elsewhere_frames_cloned();
        if frames.is_empty() {
            return 0;
        }
        let sources = self.seq_state.all_seq_index_sources();
        let seq_funcs = self.ensure_seq_theory();
        let mut emitted = 0usize;
        let mut seen = std::collections::HashSet::new();

        for frame in frames {
            if emitted >= INSTANCE_BUDGET {
                break;
            }
            let predicate_asserted =
                self.solver.assertions().iter().any(|assertion| {
                    self.term_contains_positive_conjunct(*assertion, frame.predicate)
                });
            if !predicate_asserted {
                // An unasserted or negatively-used monitor carries no positive
                // frame fact.  Skipping its dormant implications also keeps
                // unsupported UF/Array terms out of otherwise certifiable SAT
                // models.
                continue;
            }
            if self.seq_state.get_seq_len_aux(&frame.old_seq) != Some(frame.old_len) {
                // Fail closed if the finite length component is not still
                // authenticated to the exact old receiver.
                continue;
            }

            for (source_seq, index, _) in &sources {
                if emitted >= INSTANCE_BUDGET {
                    break;
                }
                if *source_seq != frame.old_seq && *source_seq != frame.new_seq {
                    continue;
                }
                if !seen.insert((frame.predicate, *index)) {
                    continue;
                }

                let zero = self.solver.int_const(0);
                let nonnegative = self.solver.ge(*index, zero);
                let below_len = self.solver.lt(*index, frame.old_len);
                let outside_footprint = match frame.footprint {
                    ResolveElsewhereFootprint::Index(changed) => {
                        let at_changed = self.eq_term(*index, changed);
                        self.solver.not(at_changed)
                    }
                    ResolveElsewhereFootprint::RangeInclusive { start, end } => {
                        let before = self.solver.lt(*index, start);
                        let after = self.solver.lt(end, *index);
                        self.solver.or(before, after)
                    }
                };
                let protected = self
                    .solver
                    .and_many(&[nonnegative, below_len, outside_footprint]);
                let old_at_index = self
                    .solver
                    .apply(&seq_funcs.seq_index_logic, &[frame.old_seq, *index]);
                let new_at_index = self
                    .solver
                    .apply(&seq_funcs.seq_index_logic, &[frame.new_seq, *index]);
                let same_value = self.eq_term(old_at_index, new_at_index);
                let consequence = self.solver.implies(protected, same_value);
                let guarded = self.solver.implies(frame.predicate, consequence);

                if !self.solver.assertions().contains(&guarded) {
                    self.assert_solver_term("ground/resolve_elsewhere", guarded);
                    emitted = emitted.saturating_add(1);
                }
            }
        }

        emitted
    }

    fn term_contains_positive_conjunct(&self, term: Term, target: Term) -> bool {
        if term == target {
            return true;
        }
        let ay_dpll::api::TermKind::App { name, .. } = self.solver.term_kind(term) else {
            return false;
        };
        name == "and"
            && self
                .solver
                .term_children(term)
                .into_iter()
                .any(|child| self.term_contains_positive_conjunct(child, target))
    }

    /// Reroute a name-collided SliceIndexSpec predicate `LogicFnCall` back to
    /// its builtin method semantics (#knights_tour).
    ///
    /// The driver's contract rewrite (`rewrite_logic_method_calls_expr`)
    /// converts `receiver.method(args)` to `LogicFnCall(method, [receiver,
    /// ...args])` for every method whose NAME matches a user-defined logic
    /// function — with no receiver-type check. When a user logic fn shares a
    /// name with the std `SliceIndexSpec` surface (e.g. knights_tour's
    /// `Board::in_bounds(Board, Point)` vs the std `usize::in_bounds(Seq)`
    /// used by Vec/slice indexing contracts), the std call is rewritten too
    /// and lands on the registered user declaration with wholesale-mismatched
    /// argument sorts. `apply_logic_fn` then bridges EVERY argument to a
    /// fresh, unconstrained coercion constant, so the negated goal
    /// `not(logic_in__bounds(c0, c1))` is trivially SAT over constants
    /// disconnected from the program state — a false reject.
    ///
    /// Detection is sort-based, mirroring the method-call dispatch: the
    /// builtin semantics only apply to Int (usize) receivers, so the reroute
    /// fires only when the encoded receiver is Int-sorted AND the registered
    /// user logic fn expects a non-Int receiver (i.e. the registered decl
    /// cannot be the intended target). The user's own calls (receiver sort
    /// matching the declaration) stay on the registered logic-fn path.
    ///
    /// Returns `Ok(None)` when the call is not a SliceIndexSpec collision.
    pub(in crate::encoder) fn try_reroute_slice_index_spec_logic_fn_collision(
        &mut self,
        name: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        let arity_matches = match name {
            // receiver + seq
            "in_bounds" => args.len() == 2,
            // receiver + seq + out / receiver + old + fin
            "has_value" | "resolve_elsewhere" => args.len() == 3,
            _ => false,
        };
        if !arity_matches {
            return Ok(None);
        }
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        let Some(decl) = self.logic_func_decl_cloned(&smt_name) else {
            // No registered user logic fn under this name — no collision. The
            // driver only rewrites method calls whose name matches a user
            // logic fn, so leave everything else on the existing paths.
            return Ok(None);
        };
        let Some(receiver_domain_sort) = decl.domain().first() else {
            return Ok(None);
        };
        // If the registered user logic fn itself takes an Int receiver, it is
        // the plausible target for an Int-receiver call; keep the registered
        // path (its declared semantics win over the builtin).
        if receiver_domain_sort.as_term_sort() == Sort::Int {
            return Ok(None);
        }
        let receiver_term = self.encode_pure_impl(&args[0], prefix)?;
        if self.solver.get_sort(receiver_term) != Sort::Int {
            return Ok(None);
        }
        // Int-sorted receiver against a non-Int user declaration: this is the
        // std `usize` SliceIndexSpec predicate, not the user's logic fn.
        // Encode the builtin concrete semantics (`ix >= 0 && ix < seq.len()`
        // etc.) exactly as the un-collided MethodCall path would have.
        tracing::debug!(
            "  [slice-index-spec-collision] rerouting LogicFnCall `{name}` with Int receiver \
             away from registered `{smt_name}` (non-Int receiver domain) to builtin semantics"
        );
        match name {
            "in_bounds" => self
                .encode_in_bounds(&args[0], &args[1..], prefix)
                .map(Some),
            "has_value" => self
                .encode_has_value(&args[0], &args[1..], prefix)
                .map(Some),
            _ => self
                .encode_resolve_elsewhere(&args[0], &args[1..], prefix)
                .map(Some),
        }
    }
}
