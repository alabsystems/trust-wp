// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq constructor encoding: singleton, push_back (standalone), and empty.

use ay_dpll::api::{Sort, Term};

use super::{AYEncoder, SeqValue};
#[cfg(test)]
use crate::error::EncodingError;

impl AYEncoder {
    /// Encode a singleton sequence: `seq_singleton(value)`.
    ///
    /// Used to link the `seq!` macro (which compiles to `LogicFnCall { name: "seq" }`)
    /// with the `seq_singleton` SMT function and its axioms (#379).
    pub(in crate::encoder) fn encode_seq_singleton(&mut self, value_term: Term) -> Term {
        let seq_funcs = self.ensure_seq_theory();
        let value_term = self.coerce_seq_element_to_int(value_term);
        let result = self.solver.apply(&seq_funcs.seq_singleton, &[value_term]);

        // Concrete singleton shape: arr = store(const_array(0), 0, value), len = 1, offset = 0.
        //
        // Keep this shape in the in-memory SeqValue registry only. Asserting
        // global projector equalities for `seq_array(seq_singleton(v))` can
        // false-UNSAT satisfiable contexts on current ay when `v != 0`, the
        // same failure mode that led multi-element literals to use assertion-
        // free fresh SeqValues (#2242). Direct len/index users still read the
        // concrete shape through `seq_len_term`/`seq_index_term`.
        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);
        let base_arr = self.solver.const_array(Sort::Int, zero);
        let singleton_arr = self.solver.store(base_arr, zero, value_term);

        // Register concrete SeqValue for direct Array access (#1317).
        self.insert_seq_value(
            result,
            SeqValue {
                arr: singleton_arr,
                len: one,
                offset: zero,
                known_len: Some(1),
            },
        );
        result
    }

    /// Encode `push_back(receiver_term, value)` with Array+Length encoding (#1317).
    ///
    /// Creates the UF application, asserts shape constraints, and registers the
    /// resulting SeqValue. This is a standalone version of the push_back arm in
    /// `encode_seq_operation_impl`, usable when the receiver/value are already
    /// SMT terms (e.g., in tests that build push_back chains manually).
    #[cfg(test)]
    pub(in crate::encoder) fn encode_seq_push_back(
        &mut self,
        receiver_term: Term,
        value_term: Term,
    ) -> Result<Term, EncodingError> {
        let seq_funcs = self.ensure_seq_theory();
        let base_known_len = self
            .seq_state
            .get_seq_value(&receiver_term)
            .and_then(|value| value.known_len);
        let known_len = base_known_len.and_then(|len| len.checked_add(1));
        let base_arr = self.seq_array_term(receiver_term)?;
        let base_len = self.seq_len_term(receiver_term)?;
        let base_off = self.seq_offset_term(receiver_term)?;
        let write_offset = base_known_len
            .and_then(|len| i64::try_from(len).ok())
            .map_or(base_len, |len| self.solver.int_const(len));
        let write_index = self.solver.add(base_off, write_offset);
        let new_arr = self.solver.store(base_arr, write_index, value_term);
        let new_len = if let Some(len) = known_len.and_then(|len| i64::try_from(len).ok()) {
            self.solver.int_const(len)
        } else {
            let one = self.solver.int_const(1);
            self.solver.add(base_len, one)
        };
        let result = self.safe_apply(
            "seq_push_back",
            &seq_funcs.seq_push_back,
            &[receiver_term, value_term],
        )?;
        // Register the exact finite components before shape observation.  If
        // projector access runs first it allocates three unrelated proxies and
        // turns a ground push-back chain into avoidable Array/LIA congruence.
        // `insert_seq_value` still installs guarded neutral anchors when this
        // constructor is encoded under an active path.
        self.insert_seq_value(
            result,
            SeqValue {
                arr: new_arr,
                len: new_len,
                offset: base_off,
                known_len,
            },
        );
        self.assert_seq_shape_constraints(result, new_arr, new_len, base_off, "seq_push_back")?;
        Ok(result)
    }

    /// Encode `Seq::empty()` / `seq_empty` as the axiom-backed Seq constant (#737).
    pub(crate) fn encode_seq_empty(&mut self) -> Term {
        self.ensure_seq_theory().seq_empty
    }

    /// Encode a multi-element seq literal as a fresh Seq-sort constant with
    /// direct Array components (#2242).
    ///
    /// Instead of `push_back(push_back(empty, v1), v2)` which creates N
    /// intermediate Seq-sort terms each with 3 solver-level shape constraint
    /// assertions, this creates:
    /// - One Array built from `store` operations: `store(store(base, 0, v1), 1, v2)`
    /// - One fresh Seq-sort constant with a SeqValue pointing to that Array
    /// - No solver-level assertions (SeqValue is in-memory only)
    ///
    /// The push_back chain approach caused ay-dpll to produce false UNSAT on
    /// negated seq postconditions because the shape constraint assertions
    /// (N×3 equalities involving UF projectors) over-constrained the solver's
    /// finite model for the Seq sort.
    pub(in crate::encoder) fn encode_seq_literal_as_fresh_constant(
        &mut self,
        args: &[trust_wp_core::formula::PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, crate::error::EncodingError> {
        let zero = self.solver.int_const(0);
        let base_arr = self.solver.const_array(Sort::Int, zero);

        let mut arr = base_arr;
        for (i, arg) in args.iter().enumerate() {
            let raw_val = self.encode_pure_impl(arg, prefix)?;
            let val = self.coerce_seq_element_to_int(raw_val);
            #[allow(clippy::cast_possible_wrap)] // Seq literal length < 2^63
            let idx = self.solver.int_const(i as i64);
            arr = self.solver.store(arr, idx, val);
        }

        #[allow(clippy::cast_possible_wrap)] // Seq literal length < 2^63
        let len = self.solver.int_const(args.len() as i64);

        let seq_sort = self.get_seq_sort();
        let fresh_name = format!("__seq_lit_{}", self.seq_state.next_fresh_seq_lit_id());
        let result = self.solver.declare_const(&fresh_name, seq_sort);

        self.insert_seq_value(
            result,
            super::SeqValue {
                arr,
                len,
                offset: zero,
                known_len: Some(args.len()),
            },
        );

        Ok(result)
    }
}
