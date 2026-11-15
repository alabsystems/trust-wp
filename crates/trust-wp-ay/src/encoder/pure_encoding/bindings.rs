// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::PureExpr;

use super::super::{
    unsoundness::{self, UnsoundnessCategory},
    AYEncoder,
};
use crate::{
    error::EncodingError,
    expr::{
        instantiate_standard_precondition_foralls_from, is_grounding_exempt_standard_forall,
        is_standard_data_structure_precondition_forall,
    },
};

impl AYEncoder {
    /// Encodes a scoped call assumption (`LetAssume`). (#815)
    ///
    /// When `body` is Bool (formula context), encode as implication:
    ///   `(=> assumption body)`
    /// When `body` is non-Bool (value context), assert a path-guarded
    /// implication and return the body term.
    ///
    /// Postcondition assumptions from predicate-style specs (#997) may
    /// reference sorts that the encoder cannot yet handle. When the assumption
    /// fails to encode, propagate the error instead of silently dropping the
    /// guard; continuing with an unconstrained body can produce false proofs.
    pub(super) fn encode_let_assume(
        &mut self,
        assumption: &PureExpr,
        body: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Use context-aware inference so LogicFnCall bodies returning Bool
        // are correctly detected (pure infer_expr_sort defaults to Int). (#1965)
        //
        // Bracket SortFallbackToIntFromLogicFn for the same reason as in
        // `encode_let_obligation`: this is a Bool-vs-non-Bool discriminator,
        // not an encoding step.
        let before_body_infer = unsoundness::snapshot();
        let body_is_bool = matches!(self.infer_expr_sort_with_context(body, prefix), Sort::Bool);
        unsoundness::restore_category(
            &before_body_infer,
            UnsoundnessCategory::SortFallbackToIntFromLogicFn,
        );
        if !body_is_bool && is_standard_data_structure_precondition_forall(assumption) {
            let instances = instantiate_standard_precondition_foralls_from(&[assumption], &[body]);
            for instance in &instances {
                let instance_term = self.encode_pure_impl(instance, prefix)?;
                let instance_bool = self.coerce_bool_operand(instance_term);
                let guarded = self.guard_with_active_path(instance_bool);
                self.assert_term(guarded);
            }
            // Ground-then-drop coherence, the same rule the requires path
            // applies (`verify/setup.rs`, `is_grounding_exempt_standard_forall`).
            // `instantiate_standard_precondition_foralls_from` EXEMPTS
            // negative-contains foralls (FSet/FMap `EMPTY`'s
            // `forall<k> !s.contains(k)`) from grounding and returns ZERO
            // instances for them, so dropping the universal here loses the
            // premise entirely: neither grounded nor asserted. Assert the
            // exempted universal; skip only the foralls grounding consumed.
            //
            // PREMISE RESTORATION, not premise addition: the clause asserted is
            // the callee's own committed `ensures`, which this call site is
            // already entitled to assume — the same fact the non-exempt branch
            // asserts in grounded form.
            if is_grounding_exempt_standard_forall(assumption) {
                match self.with_assumption_position(|encoder| {
                    encoder.encode_pure_impl(assumption, prefix)
                }) {
                    Ok(assumption_term) => {
                        let assumption_bool = self.coerce_bool_operand(assumption_term);
                        let guarded = self.guard_with_active_path(assumption_bool);
                        self.assert_term(guarded);
                        tracing::debug!(
                            "asserting grounding-exempt negative-contains standard LetAssume forall"
                        );
                    }
                    Err(e) => {
                        // Dropping the exempted universal on an encoding failure
                        // is safe: a dropped assumption only weakens the
                        // premises, so nothing unsound is admitted.
                        tracing::debug!(
                            error = %e,
                            "grounding-exempt standard LetAssume forall did not encode — dropped as before"
                        );
                    }
                }
            } else {
                tracing::debug!(
                    instances = instances.len(),
                    "skipping quantified standard-library LetAssume after grounding"
                );
            }
            let body_term = self.encode_pure_impl(body, prefix)?;
            return Ok(body_term);
        }

        if body_is_bool {
            let body_term = self.encode_pure_impl(body, prefix)?;
            // Assumption position: shift-amount range obligations embedded in
            // the fact are owned by the body VALUE encoding — see
            // `with_assumption_position`. (ledger int-shift-full)
            let assumption_result = self
                .with_assumption_position(|encoder| encoder.encode_pure_impl(assumption, prefix));
            return match assumption_result {
                Ok(assumption_term) => {
                    self.try_synthesize_index_mut_seq_value(assumption, prefix)?;
                    let a_sort = self.solver.get_sort(assumption_term);
                    let b_sort = self.solver.get_sort(body_term);
                    if b_sort == Sort::Bool {
                        let antecedent = if a_sort == Sort::Bool {
                            assumption_term
                        } else {
                            self.coerce_bool_operand(assumption_term)
                        };
                        Ok(self.solver.implies(antecedent, body_term))
                    } else {
                        let assumption_bool = self.coerce_bool_operand(assumption_term);
                        let guarded = self.guard_with_active_path(assumption_bool);
                        self.assert_term(guarded);
                        Ok(body_term)
                    }
                }
                Err(e) => {
                    unsoundness::increment(unsoundness::UnsoundnessCategory::LetAssumeDropped);
                    tracing::warn!(
                        assumption = ?assumption,
                        error = %e,
                        "call assumption encoding failed — propagating as error"
                    );
                    Err(e)
                }
            };
        }

        // Assumption position — same rationale as the Bool-body branch above.
        let assumption_result =
            self.with_assumption_position(|encoder| encoder.encode_pure_impl(assumption, prefix));
        match assumption_result {
            Ok(assumption_term) => {
                // After encoding the assumption, synthesize a SeqValue for
                // IndexMut point-write postconditions (#1317). The assumption
                // encoding creates the final-view variable; this registers
                // concrete Array backing so that subsequent LetAssume
                // assumptions (frame condition, length preservation) and
                // postcondition verification use the Array theory fast path.
                self.try_synthesize_index_mut_seq_value(assumption, prefix)?;
                let body_term = self.encode_pure_impl(body, prefix)?;
                {
                    // Coerce assumption to Bool for guard_with_active_path,
                    // which uses implies() when path conditions are active.
                    let assumption_bool = self.coerce_bool_operand(assumption_term);
                    let guarded = self.guard_with_active_path(assumption_bool);
                    self.assert_term(guarded);
                    Ok(body_term)
                }
            }
            Err(e) => {
                unsoundness::increment(unsoundness::UnsoundnessCategory::LetAssumeDropped);
                // Assumption encoding failed (sort mismatch, unsupported
                // construct, etc.). Propagate the EncodingError rather than
                // dropping the assumption and continuing with the body: an
                // unconstrained result would let a false proof through, while
                // the error turns it into Unknown (the safe direction).
                // (#1537, #2663)
                tracing::warn!(
                    assumption = ?assumption,
                    error = %e,
                    "call assumption encoding failed — propagating as error"
                );
                Err(e)
            }
        }
    }

    /// Encodes a scoped call obligation (`LetObligation`). (#815)
    ///
    /// When `body` is Bool (formula context), encode as conjunction:
    ///   `(and obligation body)`
    /// When `body` is non-Bool (value context), assert a path-guarded
    /// implication and return the body term.
    ///
    /// Unlike `LetAssume`, skipping a failed obligation is UNSOUND —
    /// the error must propagate. (#1029)
    pub(super) fn encode_let_obligation(
        &mut self,
        obligation: &PureExpr,
        body: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Detect constant-false obligations early. These come from opaque call
        // `requires(false)` patterns (handle_opaque_call in trust-wp-driver). In
        // the non-Bool body path, asserting `false` as a solver fact makes the
        // context trivially UNSAT, producing a false "Verified." Instead, return
        // an encoding error so the function gets Unknown/demotion — the caller
        // cannot satisfy `requires(false)` and therefore cannot be verified.
        // In the Bool body path, `and(false, body)` = `false` correctly
        // propagates failure, but we still reject it to be consistent: any
        // function calling an unspecified function should fail verification
        // rather than relying on sort-dependent encoding behavior. (#2663)
        if matches!(obligation, PureExpr::Bool(false)) {
            return Err(EncodingError::unsupported(
                "LetObligation with constant false: function calls an opaque/unspecified \
                 function whose precondition is `requires(false)` — verification cannot \
                 proceed (no spec available for this call)"
                    .to_string(),
            ));
        }

        // Use context-aware inference so LogicFnCall bodies returning Bool
        // are correctly detected (pure infer_expr_sort defaults to Int). (#1965)
        //
        // Bracket with unsoundness snapshot/restore for
        // `SortFallbackToIntFromLogicFn`: this is an analytical Bool-vs-non-Bool
        // discriminator, not an encoding step. The encoded body uses the
        // declared LogicFnCall signature via `encode_pure_impl`. When the body
        // is a recursive lemma call (e.g., `lemma_fib_bound(i-1)`) and the
        // AST-level inference falls back to Int for a logic fn whose
        // declaration hasn't been threaded through the context-aware lookup
        // (e.g., self-recursion during body encoding), we should not record
        // a demoting fallback. Same rationale as the bracket in
        // `result_binding.rs::assert_result_scalar_binding`. (#2671 follow-up)
        let before_body_infer = unsoundness::snapshot();
        let body_is_bool = matches!(self.infer_expr_sort_with_context(body, prefix), Sort::Bool);
        unsoundness::restore_category(
            &before_body_infer,
            UnsoundnessCategory::SortFallbackToIntFromLogicFn,
        );
        let obligation_term = self.encode_pure_impl(obligation, prefix)?;
        let body_term = self.encode_pure_impl(body, prefix)?;
        if body_is_bool {
            let obligation_sort = self.solver.get_sort(obligation_term);
            let body_sort = self.solver.get_sort(body_term);
            if obligation_sort == Sort::Bool && body_sort == Sort::Bool {
                Ok(self.solver.and(obligation_term, body_term))
            } else {
                Err(EncodingError::solver_error(format!(
                    "sort mismatch in LetObligation Bool body: expected Bool obligation/body, got {obligation_sort:?} and {body_sort:?}"
                )))
            }
        } else {
            let obligation_sort = self.solver.get_sort(obligation_term);
            if obligation_sort != Sort::Bool {
                return Err(EncodingError::solver_error(format!(
                    "sort mismatch in LetObligation non-Bool body: expected Bool obligation, got {obligation_sort:?}"
                )));
            }
            let guarded = self.guard_with_active_path(obligation_term);
            self.assert_term(guarded);
            Ok(body_term)
        }
    }
}
