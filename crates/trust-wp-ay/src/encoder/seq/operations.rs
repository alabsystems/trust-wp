// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq operation encoding: the main `encode_seq_operation_impl` dispatcher.

use ay_dpll::api::{Logic, Sort, Term};
use trust_wp_core::formula::{
    internal::tuple_lowering::{NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX},
    ExprSort, PureExpr,
};

use super::{resolve_view_var_name, AYEncoder, SeqValue};
use crate::error::EncodingError;

fn expr_is_structural_field_receiver(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, .. } => {
            name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX)
                || name.starts_with(NAMED_FIELD_LOGIC_FN_PREFIX)
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_is_structural_field_receiver(inner),
        _ => false,
    }
}

pub(crate) fn seq_singleton_literal_arg(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            if matches!(name.as_str(), "seq" | "Seq::singleton") && args.len() == 1 {
                Some(&args[0])
            } else {
                None
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if method == "singleton"
                && args.len() == 1
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "Seq")
            {
                Some(&args[0])
            } else {
                None
            }
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => seq_singleton_literal_arg(inner),
        _ => None,
    }
}

fn expr_is_seq_singleton_literal(expr: &PureExpr) -> bool {
    seq_singleton_literal_arg(expr).is_some()
}

fn expr_is_symbolic_seq_carrier(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(..) => true,
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_is_symbolic_seq_carrier(inner),
        _ => false,
    }
}

pub(crate) fn should_encode_singleton_prefix_concat_opaque(
    receiver: &PureExpr,
    other: &PureExpr,
) -> bool {
    let Some(singleton_arg) = seq_singleton_literal_arg(receiver) else {
        return false;
    };
    !matches!(singleton_arg, PureExpr::Int(_)) && expr_is_symbolic_seq_carrier(other)
}

impl AYEncoder {
    fn singleton_prefix_concat_bridge_term(&mut self, elem: Term, other: Term) -> Term {
        let seq_sort = self.get_seq_sort();
        let bridge_name = "__seq_singleton_prefix_concat";
        let bridge_fn = if let Some(existing) = self.seq_state.get_bridge_fn(bridge_name) {
            existing.clone()
        } else {
            let bridge = self.solver.declare_fun(
                bridge_name,
                &[Sort::Int, seq_sort.clone()],
                seq_sort.clone(),
            );
            self.seq_state
                .insert_bridge_fn(bridge_name.to_string(), bridge.clone());
            bridge
        };
        self.solver.apply(&bridge_fn, &[elem, other])
    }

    pub(in crate::encoder) fn opaque_singleton_prefix_concat_carrier_term(
        &mut self,
        elem_expr: &PureExpr,
        other_expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let raw_elem = self.encode_pure_impl(elem_expr, prefix)?;
        let elem = self.coerce_seq_element_to_int(raw_elem);
        let raw_other = self.encode_pure_impl(other_expr, prefix)?;
        let bridged_other = self.bridge_int_to_seq_for_operation(raw_other);
        let other = self.coerce_to_seq(bridged_other);
        Ok(self.singleton_prefix_concat_bridge_term(elem, other))
    }

    fn opaque_singleton_prefix_concat_term(
        &mut self,
        elem_expr: &PureExpr,
        other_expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let raw_elem = self.encode_pure_impl(elem_expr, prefix)?;
        let elem = self.coerce_seq_element_to_int(raw_elem);
        let raw_other = self.encode_pure_impl(other_expr, prefix)?;
        let bridged_other = self.bridge_int_to_seq_for_operation(raw_other);
        let other = self.coerce_to_seq(bridged_other);
        let other_known_len = self
            .seq_state
            .get_seq_value(&other)
            .and_then(|seq_value| seq_value.known_len);
        let other_arr = self.seq_array_term(other)?;
        let other_len = self.seq_len_term(other)?;
        let other_off = self.seq_offset_term(other)?;
        let result = self.singleton_prefix_concat_bridge_term(elem, other);

        // Keep the solver-facing term opaque, but preserve the concrete
        // singleton-prefix shape in the local SeqValue registry. This avoids
        // the false-UNSAT projector assertions from the ordinary concat path
        // while still allowing direct reads such as
        // `seq![x].concat(rest).index_logic(0)` to reduce to `x`.
        let one = self.solver.int_const(1);
        let result_off = self.solver.sub(other_off, one);
        let result_arr = self.solver.store(other_arr, result_off, elem);
        let result_len = self.solver.add(one, other_len);
        self.insert_seq_value(
            result,
            SeqValue {
                arr: result_arr,
                len: result_len,
                offset: result_off,
                known_len: other_known_len.map(|len| len + 1),
            },
        );

        Ok(result)
    }

    fn bridge_int_to_seq_for_operation(&mut self, term: Term) -> Term {
        if self.solver.term_sort(term) != Sort::Int {
            return term;
        }

        crate::encoder::unsoundness::increment(
            crate::encoder::unsoundness::UnsoundnessCategory::SortCoercionBridge,
        );
        let seq_sort = self.get_seq_sort();
        let bridge_name = "__int_to_seq_bridge";
        let bridge_fn = if let Some(existing) = self.seq_state.get_bridge_fn(bridge_name) {
            existing.clone()
        } else {
            let bridge =
                self.solver
                    .declare_fun(bridge_name, std::slice::from_ref(&Sort::Int), seq_sort);
            self.seq_state
                .insert_bridge_fn(bridge_name.to_string(), bridge.clone());
            bridge
        };
        self.solver.apply(&bridge_fn, &[term])
    }

    fn synthesize_concat_seq_value(
        &mut self,
        left: Term,
        right: Term,
    ) -> Result<Option<SeqValue>, EncodingError> {
        // Monoid identity (#2116): concat is monoidal with `seq_empty` as the
        // two-sided identity, so `concat(seq_empty, s) = s` and
        // `concat(s, seq_empty) = s` are GENUINE Seq theorems. When an operand is
        // SYNTACTICALLY the `seq_empty` constant, the concat result IS the other
        // operand: synthesize the other operand's array/len/offset shape for the
        // result so the equality decomposition in `try_decompose_seq_equality`
        // (array/len/offset projector conjuncts) sees matching projectors at
        // ENCODE time. Without this, the projectors are only unified by a UF
        // identity that ay-dpll's congruence-free core cannot propagate, leaving
        // the negated `original == concat(seq_empty, original)` initialization
        // obligation spuriously SAT. SOUNDNESS: this only fires for a literal
        // `seq_empty` operand, where the identity is unconditionally valid.
        let empty = self.seq_state.funcs_clone().map(|f| f.seq_empty);
        if let Some(empty) = empty {
            if left == empty {
                let arr = self.seq_array_term(right)?;
                let len = self.seq_len_projector_term(right)?;
                let offset = self.seq_offset_term(right)?;
                let known_len = self
                    .seq_state
                    .get_seq_value(&right)
                    .and_then(|sv| sv.known_len);
                return Ok(Some(SeqValue {
                    arr,
                    len,
                    offset,
                    known_len,
                }));
            }
            if right == empty {
                let arr = self.seq_array_term(left)?;
                let len = self.seq_len_projector_term(left)?;
                let offset = self.seq_offset_term(left)?;
                let known_len = self
                    .seq_state
                    .get_seq_value(&left)
                    .and_then(|sv| sv.known_len);
                return Ok(Some(SeqValue {
                    arr,
                    len,
                    offset,
                    known_len,
                }));
            }
        }

        let Some(left_sv) = self.seq_state.get_seq_value(&left) else {
            return Ok(None);
        };
        let Some(left_known_len) = left_sv.known_len else {
            return Ok(None);
        };

        let left_arr = left_sv.arr;
        let left_len = left_sv.len;
        let left_off = left_sv.offset;
        let right_arr = self.seq_array_term(right)?;
        let right_len = self.seq_len_term(right)?;
        let right_off = self.seq_offset_term(right)?;

        #[allow(clippy::cast_possible_wrap)] // known_len originates from a concrete Seq literal
        let left_known_len_term = self.solver.int_const(left_known_len as i64);
        let result_off = self.solver.sub(right_off, left_known_len_term);
        let mut result_arr = right_arr;
        for i in 0..left_known_len {
            #[allow(clippy::cast_possible_wrap)] // loop index is bounded by known_len
            let idx = self.solver.int_const(i as i64);
            let left_pos = self.solver.add(left_off, idx);
            let left_elem = self.solver.select(left_arr, left_pos);
            let result_pos = self.solver.add(result_off, idx);
            result_arr = self.solver.store(result_arr, result_pos, left_elem);
        }

        let result_len = self.solver.add(left_len, right_len);
        let known_len = self
            .seq_state
            .get_seq_value(&right)
            .and_then(|right_sv| right_sv.known_len)
            .map(|right_known_len| left_known_len + right_known_len);

        Ok(Some(SeqValue {
            arr: result_arr,
            len: result_len,
            offset: result_off,
            known_len,
        }))
    }

    /// Internal implementation for Seq operation encoding with optional prefix.
    #[allow(clippy::too_many_lines)]
    pub(in crate::encoder) fn encode_seq_operation_impl(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Encode the receiver (must be a Seq)
        let receiver_expr = Self::normalize_seq_receiver(receiver);

        // Self-register: any View used as a Seq method receiver must have Seq sort.
        // This ensures correct encoding even without a prior register_sort_hints() call,
        // making the pre-scan optional for direct encode_pure() usage (e.g., in tests).
        if let Some(name) = resolve_view_var_name(receiver_expr.as_ref(), prefix) {
            self.record_sort_hint(name, ExprSort::Seq);
        }

        if method == "concat" && args.len() != 1 {
            return Err(EncodingError::unsupported(format!(
                "concat expects 1 argument, got {}",
                args.len()
            )));
        }

        if method == "concat"
            && should_encode_singleton_prefix_concat_opaque(receiver_expr.as_ref(), &args[0])
        {
            let mut seq_names = std::collections::HashSet::new();
            super::collect_view_names_as_seq(&args[0], &mut seq_names);
            for name in seq_names {
                self.record_sort_hint(name, ExprSort::Seq);
            }
            tracing::debug!("encoding singleton-prefix concat as early opaque Seq carrier");
            let singleton_arg = seq_singleton_literal_arg(receiver_expr.as_ref())
                .expect("predicate already checked singleton receiver");
            return self.opaque_singleton_prefix_concat_term(singleton_arg, &args[0], prefix);
        }

        let receiver_term = if expr_is_structural_field_receiver(receiver_expr.as_ref()) {
            let seq_sort = self.get_seq_sort();
            self.encode_structural_receiver_with_expected_sort(
                receiver_expr.as_ref(),
                &seq_sort,
                prefix,
            )?
        } else {
            self.encode_pure_impl(receiver_expr.as_ref(), prefix)?
        };

        // D3 safety net (#994, #2231): if the receiver term is still Int-sorted
        // after encoding (e.g., due to sort hint propagation gaps or name chain
        // mismatches), bridge it to Seq here at the operation level. This
        // prevents downstream safe_apply errors while recording the approximation
        // through the unsoundness counter. The bridge is placed HERE (not in
        // coerce_to_seq) so internal reconstruction paths that rely on sort
        // mismatches as error signals are not affected.
        let receiver_term = self.bridge_int_to_seq_for_operation(receiver_term);

        // Coerce receiver to Seq sort if it has a non-Seq sort (e.g., List,
        // user-defined ADTs, or ay Datatype sorts from match encoding).
        // This is the single choke-point: every Seq operation goes through
        // encode_seq_operation_impl, so coercing here ensures all downstream
        // UF applications (seq_contains, seq_push_back, seq_get, etc.) receive
        // a Seq-sorted term. Previously only seq_len/seq_array/seq_offset
        // called coerce_to_seq individually, leaving contains/get/push_back
        // vulnerable to sort mismatch panics. (#2155)
        let receiver_term = self.coerce_to_seq(receiver_term);

        // Record concat's argument hint before encoding the argument. A bare
        // variable used as `s.concat(t)` must be declared Seq-sorted before
        // `encode_pure_impl(t)` runs; doing this after arg encoding leaves `t`
        // as the default Int carrier and `seq_concat` rejects it.
        if method == "concat" {
            if args.len() != 1 {
                return Err(EncodingError::unsupported(format!(
                    "concat expects 1 argument, got {}",
                    args.len()
                )));
            }
            let mut seq_names = std::collections::HashSet::new();
            super::collect_view_names_as_seq(&args[0], &mut seq_names);
            for name in seq_names {
                self.record_sort_hint(name, ExprSort::Seq);
            }
        }

        // Encode all arguments BEFORE borrowing seq_funcs to avoid borrow conflict
        let arg_terms: Vec<Term> = args
            .iter()
            .map(|arg| self.encode_pure_impl(arg, prefix))
            .collect::<Result<Vec<_>, _>>()?;

        let seq_funcs = self.ensure_seq_theory();

        match method {
            "len" => {
                // seq_len(receiver)
                self.seq_len_term(receiver_term)
            }
            // "index" is an alias for "index_logic" (Creusot compat: v@.index(0))
            "index" | "index_logic" => {
                // seq_index_logic(receiver, index)
                if arg_terms.len() != 1 {
                    return Err(EncodingError::unsupported(format!(
                        "{method} expects 1 argument, got {}",
                        arg_terms.len()
                    )));
                }
                self.seq_index_term(receiver_term, arg_terms[0])
            }
            "push_back" => {
                // seq_push_back(receiver, value)
                if arg_terms.len() != 1 {
                    return Err(EncodingError::unsupported(format!(
                        "push_back expects 1 argument, got {}",
                        arg_terms.len()
                    )));
                }
                // Coerce non-Int element to Int for Seq operation compatibility (#994).
                let elem = self.coerce_seq_element_to_int(arg_terms[0]);
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
                let new_arr = self.solver.store(base_arr, write_index, elem);
                let new_len = if let Some(len) = known_len.and_then(|len| i64::try_from(len).ok()) {
                    self.solver.int_const(len)
                } else {
                    let one = self.solver.int_const(1);
                    self.solver.add(base_len, one)
                };
                let result = self.safe_apply(
                    "seq_push_back",
                    &seq_funcs.seq_push_back,
                    &[receiver_term, elem],
                )?;
                // Register ground application for standard axiom instantiation (#2288).
                self.register_standard_ground_application(
                    "seq_push_back",
                    result,
                    vec![receiver_term, elem],
                );
                // Publish the exact finite components before any projector
                // observation can allocate unrelated ground proxies.  Under a
                // branch, `insert_seq_value` preserves the guarded neutral
                // carrier discipline.
                self.insert_seq_value(
                    result,
                    SeqValue {
                        arr: new_arr,
                        len: new_len,
                        offset: base_off,
                        known_len,
                    },
                );
                self.assert_seq_shape_constraints(
                    result,
                    new_arr,
                    new_len,
                    base_off,
                    "seq_push_back",
                )?;
                let zero = self.solver.int_const(0);
                let len_is_zero = self.eq_term(new_len, zero);
                let non_empty = self.solver.not(len_is_zero);
                self.assert_solver_term("seq_push_back_nonempty", non_empty);
                Ok(result)
            }
            "sum" => {
                // seq_sum(receiver) — sum of all elements in the sequence (#690)
                if !self.seq_state.sum_axioms_asserted() {
                    let seq_sort = self.get_seq_sort();
                    self.assert_seq_sum_axioms(&seq_sort, &seq_funcs);
                    self.seq_state.mark_sum_axioms_asserted();
                }
                self.safe_apply("seq_sum", &seq_funcs.seq_sum, &[receiver_term])
            }
            "get" => {
                // seq_get(receiver, index) — Option-returning bounds-checked access (#1882)
                // Returns logic_Some(index_logic(s, i)) in-bounds, logic_None() out-of-bounds.
                if arg_terms.len() != 1 {
                    return Err(EncodingError::unsupported(format!(
                        "get expects 1 argument, got {}",
                        arg_terms.len()
                    )));
                }
                let seq_sort = self.get_seq_sort();
                self.assert_seq_get_axioms(&seq_sort, &seq_funcs);
                let result = self.safe_apply(
                    "seq_get",
                    &seq_funcs.seq_get,
                    &[receiver_term, arg_terms[0]],
                )?;
                if self.quantifier_state.quantifier_depth() == 0 {
                    self.assert_seq_get_ground_semantics(receiver_term, arg_terms[0], result)?;
                }
                // Register ground application for standard axiom instantiation (#2288).
                self.register_standard_ground_application(
                    "seq_get",
                    result,
                    vec![receiver_term, arg_terms[0]],
                );
                Ok(result)
            }
            "contains" => {
                // seq_contains(receiver, elem) — element membership test (#699)
                if arg_terms.len() != 1 {
                    return Err(EncodingError::unsupported(format!(
                        "contains expects 1 argument, got {}",
                        arg_terms.len()
                    )));
                }
                if let PureExpr::LogicFnCall {
                    name,
                    args: tuple_args,
                } = &args[0]
                {
                    let tuple2_name =
                        trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2);
                    if name == &tuple2_name && tuple_args.len() == 2 {
                        let left_term = self.encode_pure_impl(&tuple_args[0], prefix)?;
                        let right_term = self.encode_pure_impl(&tuple_args[1], prefix)?;
                        let left = self.coerce_seq_element_to_int(left_term);
                        let right = self.coerce_seq_element_to_int(right_term);
                        let result = self.safe_apply(
                            "seq_contains_pair",
                            &seq_funcs.seq_contains_pair,
                            &[receiver_term, left, right],
                        )?;
                        self.register_standard_ground_application(
                            "seq_contains_pair",
                            result,
                            vec![receiver_term, left, right],
                        );
                        return Ok(result);
                    }
                }

                // Coerce non-Int element to Int for seq_contains compatibility.
                // Seq operations use Sort::Int elements; Tuple2/FMap/etc. need
                // bridging via an injective UF. (#994)
                let elem = self.coerce_seq_element_to_int(arg_terms[0]);
                let seq_sort = self.get_seq_sort();
                self.assert_seq_contains_axioms(&seq_sort, &seq_funcs);
                let result = self.safe_apply(
                    "seq_contains",
                    &seq_funcs.seq_contains,
                    &[receiver_term, elem],
                )?;
                // Register ground application for standard axiom instantiation (#2288).
                self.register_standard_ground_application(
                    "seq_contains",
                    result,
                    vec![receiver_term, elem],
                );
                Ok(result)
            }
            "subsequence" => {
                // seq_subsequence(receiver, from, to) — slice extraction (#737)
                if arg_terms.len() != 2 {
                    return Err(EncodingError::unsupported(format!(
                        "subsequence expects 2 arguments, got {}",
                        arg_terms.len()
                    )));
                }
                let base_arr = self.seq_array_term(receiver_term)?;
                let base_off = self.seq_offset_term(receiver_term)?;
                let zero = self.solver.int_const(0);
                let width = self.solver.sub(arg_terms[1], arg_terms[0]);
                let nonneg = self.solver.ge(width, zero);
                let new_len = self.solver.ite(nonneg, width, zero);
                let new_off = self.solver.add(base_off, arg_terms[0]);
                let result = self.safe_apply(
                    "seq_subsequence",
                    &seq_funcs.seq_subsequence,
                    &[receiver_term, arg_terms[0], arg_terms[1]],
                )?;
                self.register_standard_ground_application(
                    "seq_subsequence",
                    result,
                    vec![receiver_term, arg_terms[0], arg_terms[1]],
                );
                self.assert_seq_shape_constraints(
                    result,
                    base_arr,
                    new_len,
                    new_off,
                    "seq_subsequence",
                )?;
                // Register concrete SeqValue for direct Array access (#1317).
                self.insert_seq_value(
                    result,
                    SeqValue {
                        arr: base_arr,
                        len: new_len,
                        offset: new_off,
                        known_len: None,
                    },
                );
                Ok(result)
            }
            "tail" | "pop_front" => {
                // tail/pop_front are aliases for dropping the first element:
                // subsequence(receiver, 1, len(receiver)).
                if !arg_terms.is_empty() {
                    return Err(EncodingError::unsupported(format!(
                        "{method} expects 0 arguments, got {}",
                        arg_terms.len()
                    )));
                }
                let known_len = self
                    .seq_state
                    .get_seq_value(&receiver_term)
                    .and_then(|value| value.known_len)
                    .map(|len| len.saturating_sub(1));
                let base_arr = self.seq_array_term(receiver_term)?;
                let base_len = self.seq_len_term(receiver_term)?;
                let base_off = self.seq_offset_term(receiver_term)?;
                let one = self.solver.int_const(1);
                let zero = self.solver.int_const(0);
                let new_off = self.solver.add(base_off, one);
                let len_gt_zero = self.solver.gt(base_len, zero);
                let raw_new_len = self.solver.sub(base_len, one);
                let new_len = self.solver.ite(len_gt_zero, raw_new_len, zero);
                let result = self.safe_apply(
                    "seq_subsequence",
                    &seq_funcs.seq_subsequence,
                    &[receiver_term, one, base_len],
                )?;
                self.register_standard_ground_application(
                    "seq_subsequence",
                    result,
                    vec![receiver_term, one, base_len],
                );
                self.assert_seq_shape_constraints(result, base_arr, new_len, new_off, "seq_tail")?;
                self.insert_seq_value(
                    result,
                    SeqValue {
                        arr: base_arr,
                        len: new_len,
                        offset: new_off,
                        known_len,
                    },
                );
                Ok(result)
            }
            "concat" => {
                // seq_concat(receiver, other) — sequence concatenation (#379)
                // Sort hint for concat arg is recorded above, before seq_funcs borrow.
                if arg_terms.len() != 1 {
                    return Err(EncodingError::unsupported(format!(
                        "concat expects 1 argument, got {}",
                        arg_terms.len()
                    )));
                }
                let bridged_other = self.bridge_int_to_seq_for_operation(arg_terms[0]);
                let other_term = self.coerce_to_seq(bridged_other);
                let seq_sort = self.get_seq_sort();
                self.assert_seq_concat_axioms(&seq_sort, &seq_funcs);
                let result = self.safe_apply(
                    "seq_concat",
                    &seq_funcs.seq_concat,
                    &[receiver_term, other_term],
                )?;
                self.register_standard_ground_application(
                    "seq_concat",
                    result,
                    vec![receiver_term, other_term],
                );
                self.seq_state
                    .insert_seq_concat_args(result, receiver_term, other_term);
                if let Some(seq_value) =
                    self.synthesize_concat_seq_value(receiver_term, other_term)?
                {
                    self.assert_seq_shape_constraints(
                        result,
                        seq_value.arr,
                        seq_value.len,
                        seq_value.offset,
                        "seq_concat",
                    )?;
                    self.insert_seq_value(result, seq_value);
                }
                Ok(result)
            }
            "set" => {
                // seq_set(receiver, index, value) — pointwise update (#969)
                if arg_terms.len() != 2 {
                    return Err(EncodingError::unsupported(format!(
                        "set expects 2 arguments, got {}",
                        arg_terms.len()
                    )));
                }
                let elem = self.coerce_seq_element_to_int(arg_terms[1]);
                let base_arr = self.seq_array_term(receiver_term)?;
                let base_len = self.seq_len_term(receiver_term)?;
                let base_off = self.seq_offset_term(receiver_term)?;
                let shifted_index = self.solver.add(base_off, arg_terms[0]);
                let new_arr = self.solver.store(base_arr, shifted_index, elem);
                let result = self.safe_apply(
                    "seq_set",
                    &seq_funcs.seq_set,
                    &[receiver_term, arg_terms[0], elem],
                )?;
                self.assert_seq_shape_constraints(result, new_arr, base_len, base_off, "seq_set")?;
                // Register concrete SeqValue for direct Array access (#1317).
                self.insert_seq_value(
                    result,
                    SeqValue {
                        arr: new_arr,
                        len: base_len,
                        offset: base_off,
                        known_len: None,
                    },
                );
                Ok(result)
            }
            "reverse" => {
                // seq_reverse(receiver) — element reversal (#1581)
                // Quantifier-capable verification paths use finite ground
                // instances for observed reverse terms and ALSO assert the
                // quantified reverse axiom family (R1-R5) once per encoder. The
                // ground instances are E-graph-local and only fire when both the
                // push_back/push_front term and its reverse appear as ground
                // entries; for the `reverse_ghost_ref` / `to_owned_seq` path the
                // borrowed-element seq never accumulates those ground entries, leaving
                // `seq_reverse` effectively uninterpreted (forall=0 -> spurious
                // SAT, RC-B). Asserting the quantified, VALID reverse theorems is
                // monotone/completeness-only: it can only refute spurious models,
                // never create a false-UNSAT. R2 (len preservation) and R3 (index
                // mirror) supply exactly the facts the ground-only ref path lacks,
                // and R4/R5 carry FIX#1's outer-term multi-triggers so they fire
                // even when PB1/concat-associativity rewrite push_back into a
                // concat fan that dilutes the inner-pattern match (RC-A). (#1581)
                let seq_sort = self.get_seq_sort();
                if self.logic() != Logic::QfAuflia && !self.seq_state.reverse_axioms_asserted() {
                    // Skip R3 (index-mirror) in the production path: its
                    // nested-arithmetic trigger dominates E-matching and turns the
                    // structural reverse-of-push goals into timeouts. R1/R2/R4/R5
                    // suffice for the push-accumulator loops. R3 is still covered by
                    // ground per-index instances (seq_instances.rs) when a reversed
                    // sequence is actually indexed.
                    self.assert_seq_reverse_axioms_opts(&seq_sort, &seq_funcs, false);
                    self.seq_state.mark_reverse_axioms_asserted();
                }
                let result =
                    self.safe_apply("seq_reverse", &seq_funcs.seq_reverse, &[receiver_term])?;
                self.register_standard_ground_application(
                    "seq_reverse",
                    result,
                    vec![receiver_term],
                );
                // Ground R1 instantiation: assert reverse(X) = seq_empty when
                // X is known to equal seq_empty (via SeqValue len=0 or direct
                // equality). ay-dpll lacks UF congruence closure, so it cannot
                // derive `produced_view = seq_empty => reverse(produced_view) =
                // reverse(seq_empty)` from the quantifier-free R1 axiom alone.
                // This explicit ground instance bridges the gap.
                let is_empty = self
                    .seq_state
                    .get_seq_value(&receiver_term)
                    .is_some_and(|sv| {
                        // Check if the SeqValue has known len=0
                        sv.len == self.solver.int_const(0)
                    });
                if is_empty {
                    let r1_instance = self.eq_term(result, seq_funcs.seq_empty);
                    self.assert_term(r1_instance);
                    // Also assert receiver = result for the identity case
                    let recv_eq_result = self.eq_term(result, receiver_term);
                    self.assert_term(recv_eq_result);
                }
                Ok(result)
            }
            "to_owned_seq" => {
                // Logical identity: Seq<&T> → Seq<T> is transparent at SMT level (#1581).
                // References are erased in ghost code, so the receiver IS the result.
                Ok(receiver_term)
            }
            "pop_back" => {
                // pop_back: drop last element — subsequence(receiver, 0, len - 1).
                // Part of #1581 (ghost Seq operations).
                if !arg_terms.is_empty() {
                    return Err(EncodingError::unsupported(format!(
                        "pop_back expects 0 arguments, got {}",
                        arg_terms.len()
                    )));
                }
                let base_arr = self.seq_array_term(receiver_term)?;
                let base_len = self.seq_len_term(receiver_term)?;
                let base_off = self.seq_offset_term(receiver_term)?;
                let one = self.solver.int_const(1);
                let zero = self.solver.int_const(0);
                let len_gt_zero = self.solver.gt(base_len, zero);
                let raw_new_len = self.solver.sub(base_len, one);
                let new_len = self.solver.ite(len_gt_zero, raw_new_len, zero);
                let result = self.safe_apply(
                    "seq_subsequence",
                    &seq_funcs.seq_subsequence,
                    &[receiver_term, zero, new_len],
                )?;
                self.register_standard_ground_application(
                    "seq_subsequence",
                    result,
                    vec![receiver_term, zero, new_len],
                );
                self.assert_seq_shape_constraints(
                    result,
                    base_arr,
                    new_len,
                    base_off,
                    "seq_pop_back",
                )?;
                self.insert_seq_value(
                    result,
                    SeqValue {
                        arr: base_arr,
                        len: new_len,
                        offset: base_off,
                        known_len: None,
                    },
                );
                Ok(result)
            }
            "push_front" => {
                // seq_push_front(receiver, value) — prepend element (#1581)
                if arg_terms.len() != 1 {
                    return Err(EncodingError::unsupported(format!(
                        "push_front expects 1 argument, got {}",
                        arg_terms.len()
                    )));
                }
                // Coerce non-Int element to Int for Seq operation compatibility.
                // This is required for generic ghost loops like
                // `reverse_ghost_ref<T>`, where the iterator yields `&T`. (#2116)
                let elem = self.coerce_seq_element_to_int(arg_terms[0]);
                let base_arr = self.seq_array_term(receiver_term)?;
                let base_len = self.seq_len_term(receiver_term)?;
                let base_off = self.seq_offset_term(receiver_term)?;
                let one = self.solver.int_const(1);
                let new_off = self.solver.sub(base_off, one);
                let new_arr = self.solver.store(base_arr, new_off, elem);
                let new_len = self.solver.add(base_len, one);
                let result = self.safe_apply(
                    "seq_push_front",
                    &seq_funcs.seq_push_front,
                    &[receiver_term, elem],
                )?;
                // Register ground application so ext_eq preservation chain
                // can structurally verify the transition pattern. (#2116)
                self.register_standard_ground_application(
                    "seq_push_front",
                    result,
                    vec![receiver_term, elem],
                );
                self.assert_seq_shape_constraints(
                    result,
                    new_arr,
                    new_len,
                    new_off,
                    "seq_push_front",
                )?;
                self.insert_seq_value(
                    result,
                    SeqValue {
                        arr: new_arr,
                        len: new_len,
                        offset: new_off,
                        known_len: None,
                    },
                );
                Ok(result)
            }
            "permutation_of" => {
                // seq_permutation_of(receiver, other) — multiset equality.
                if arg_terms.len() != 1 {
                    return Err(EncodingError::unsupported(format!(
                        "permutation_of expects 1 argument, got {}",
                        arg_terms.len()
                    )));
                }
                let seq_sort = self.get_seq_sort();
                self.assert_seq_permutation_axioms(&seq_sort, &seq_funcs);
                // Coerce the `other` argument to Seq the same way contains does.
                let other = self.bridge_int_to_seq_for_operation(arg_terms[0]);
                let other = self.coerce_to_seq(other);
                let result = self.safe_apply(
                    "seq_permutation_of",
                    &seq_funcs.seq_permutation_of,
                    &[receiver_term, other],
                )?;
                self.register_standard_ground_application(
                    "seq_permutation_of",
                    result,
                    vec![receiver_term, other],
                );
                Ok(result)
            }
            "exchange" => {
                // seq_exchange(receiver, other, i, j) — two-element swap relation.
                if arg_terms.len() != 3 {
                    return Err(EncodingError::unsupported(format!(
                        "exchange expects 3 arguments, got {}",
                        arg_terms.len()
                    )));
                }
                let seq_sort = self.get_seq_sort();
                self.assert_seq_permutation_axioms(&seq_sort, &seq_funcs);
                let other = self.bridge_int_to_seq_for_operation(arg_terms[0]);
                let other = self.coerce_to_seq(other);
                let result = self.safe_apply(
                    "seq_exchange",
                    &seq_funcs.seq_exchange,
                    &[receiver_term, other, arg_terms[1], arg_terms[2]],
                )?;
                self.register_standard_ground_application(
                    "seq_exchange",
                    result,
                    vec![receiver_term, other, arg_terms[1], arg_terms[2]],
                );
                Ok(result)
            }
            "count" => {
                // seq_count(receiver, x) — number of occurrences of an element.
                if arg_terms.len() != 1 {
                    return Err(EncodingError::unsupported(format!(
                        "count expects 1 argument, got {}",
                        arg_terms.len()
                    )));
                }
                let seq_sort = self.get_seq_sort();
                self.assert_seq_permutation_axioms(&seq_sort, &seq_funcs);
                let elem = self.coerce_seq_element_to_int(arg_terms[0]);
                let result =
                    self.safe_apply("seq_count", &seq_funcs.seq_count, &[receiver_term, elem])?;
                self.register_standard_ground_application(
                    "seq_count",
                    result,
                    vec![receiver_term, elem],
                );
                Ok(result)
            }
            // Defensive: encode_method_call_impl pre-filters to known methods,
            // so this branch should not be reached for well-formed inputs.
            _ => Err(EncodingError::unsupported(format!(
                "unknown Seq method: {method}"
            ))),
        }
    }

    fn assert_seq_get_ground_semantics(
        &mut self,
        receiver_term: Term,
        index_term: Term,
        get_term: Term,
    ) -> Result<(), EncodingError> {
        let len_term = self.seq_len_term(receiver_term)?;
        let seq_index_logic = self.ensure_seq_theory().seq_index_logic.clone();
        let index_value = self.safe_apply(
            "seq_get/ground_index_logic",
            &seq_index_logic,
            &[receiver_term, index_term],
        )?;
        let zero = self.solver.int_const(0);

        let some_smt = trust_wp_core::logic::logic_fn_smt_name("Some");
        let none_smt = trust_wp_core::logic::logic_fn_smt_name("None");
        let some_decl = self.get_or_declare_logic_func(&some_smt, &[Sort::Int], Sort::Int);
        let none_decl = self.get_or_declare_logic_func(&none_smt, &[], Sort::Int);

        let i_ge_zero = self.solver.ge(index_term, zero);
        let i_lt_len = self.solver.lt(index_term, len_term);
        let in_bounds = self.solver.and(i_ge_zero, i_lt_len);
        let some_value = self.solver.apply(&some_decl, &[index_value]);
        let in_bounds_eq = self.eq_term(get_term, some_value);
        let in_bounds_fact = self.solver.implies(in_bounds, in_bounds_eq);
        self.assert_solver_term("seq_get/ground_inbounds", in_bounds_fact);

        let i_lt_zero = self.solver.lt(index_term, zero);
        let i_ge_len = self.solver.ge(index_term, len_term);
        let out_of_bounds = self.solver.or(i_lt_zero, i_ge_len);
        let none_value = self.solver.apply(&none_decl, &[]);
        let out_of_bounds_eq = self.eq_term(get_term, none_value);
        let out_of_bounds_fact = self.solver.implies(out_of_bounds, out_of_bounds_eq);
        self.assert_solver_term("seq_get/ground_oob", out_of_bounds_fact);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use ay_dpll::api::Sort;
    use ntest::timeout;
    use trust_wp_core::formula::{ExprSort, PureExpr};

    use crate::{encoder::AYEncoder, SolveResult};

    fn seq_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
    }

    fn view(e: PureExpr) -> PureExpr {
        PureExpr::View(Arc::new(e))
    }

    fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    fn logic_fn_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    // ── len encoding ─────────────────────────────────────────────────

    /// len(seq![1, 2, 3]) should be 3 (proven via UNSAT of the negation).
    #[test]
    #[timeout(30000)]
    fn test_seq_len_on_literal() {
        let mut encoder = AYEncoder::new();
        let seq_expr = logic_fn_call(
            "seq",
            vec![PureExpr::Int(1), PureExpr::Int(2), PureExpr::Int(3)],
        );
        let len_expr = method_call(seq_expr, "len", vec![]);
        let len_term = encoder
            .encode_pure(&len_expr)
            .expect("encode len(seq![1,2,3])");

        // len should be Int-sorted
        assert_eq!(
            encoder.solver.get_sort(len_term),
            Sort::Int,
            "len should produce Int-sorted term"
        );

        // Assert len != 3, expect UNSAT
        let three = encoder.solver.int_const(3);
        let eq = encoder.solver.eq(len_term, three);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "len(seq![1,2,3]) should be 3"
        );
    }

    /// len(seq_empty) should be 0.
    #[test]
    #[timeout(30000)]
    fn test_seq_len_on_empty() {
        let mut encoder = AYEncoder::new();
        let empty_expr = logic_fn_call("seq_empty", vec![]);
        let len_expr = method_call(empty_expr, "len", vec![]);
        let len_term = encoder
            .encode_pure(&len_expr)
            .expect("encode len(seq_empty)");

        let zero = encoder.solver.int_const(0);
        let eq = encoder.solver.eq(len_term, zero);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "len(seq_empty) should be 0"
        );
    }

    /// len(seq![]) should be 0 via the same empty-sequence lane as seq_empty.
    #[test]
    #[timeout(30000)]
    fn test_seq_len_on_empty_macro_literal() {
        let mut encoder = AYEncoder::new();
        let empty_expr = logic_fn_call("seq", vec![]);
        let len_expr = method_call(empty_expr, "len", vec![]);
        let len_term = encoder.encode_pure(&len_expr).expect("encode len(seq![])");

        let zero = encoder.solver.int_const(0);
        let eq = encoder.solver.eq(len_term, zero);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "len(seq![]) should be 0"
        );
    }

    // ── index_logic encoding ────────────────────────────────────────

    /// index_logic(seq![42], 0) should be 42.
    #[test]
    #[timeout(30000)]
    fn test_seq_index_logic_on_singleton() {
        let mut encoder = AYEncoder::new();
        let seq_expr = logic_fn_call("seq", vec![PureExpr::Int(42)]);
        let index_expr = method_call(seq_expr, "index_logic", vec![PureExpr::Int(0)]);
        let index_term = encoder
            .encode_pure(&index_expr)
            .expect("encode index_logic(seq![42], 0)");

        let forty_two = encoder.solver.int_const(42);
        let eq = encoder.solver.eq(index_term, forty_two);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "index_logic(seq![42], 0) should be 42"
        );
    }

    // ── get encoding ────────────────────────────────────────────────

    /// get(v@, 0) on a Seq-sorted variable should encode without error.
    #[test]
    #[timeout(30000)]
    fn test_seq_get_encodes_without_error() {
        let mut encoder = AYEncoder::new();
        let get_expr = method_call(view(seq_var("v")), "get", vec![PureExpr::Int(0)]);
        let result = encoder.encode_pure(&get_expr);
        assert!(
            result.is_ok(),
            "get(v@, 0) should encode without error: {:?}",
            result.err()
        );
    }

    /// get with wrong arg count should produce an error.
    #[test]
    #[timeout(30000)]
    fn test_seq_get_wrong_args() {
        let mut encoder = AYEncoder::new();
        let get_expr = method_call(
            view(seq_var("v")),
            "get",
            vec![PureExpr::Int(0), PureExpr::Int(1)],
        );
        let result = encoder.encode_pure(&get_expr);
        assert!(
            result.is_err(),
            "get with 2 arguments should produce an error"
        );
    }

    // ── set encoding ────────────────────────────────────────────────

    /// set(seq![10, 20, 30], 1, 99) then index_logic at position 1 should be 99.
    #[test]
    #[timeout(30000)]
    fn test_seq_set_then_index() {
        let mut encoder = AYEncoder::new();
        let seq_expr = logic_fn_call(
            "seq",
            vec![PureExpr::Int(10), PureExpr::Int(20), PureExpr::Int(30)],
        );
        let set_expr = method_call(seq_expr, "set", vec![PureExpr::Int(1), PureExpr::Int(99)]);
        let index_expr = method_call(set_expr, "index_logic", vec![PureExpr::Int(1)]);
        let index_term = encoder
            .encode_pure(&index_expr)
            .expect("encode set+index chain");

        let ninety_nine = encoder.solver.int_const(99);
        let eq = encoder.solver.eq(index_term, ninety_nine);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "index_logic(set(seq![10,20,30], 1, 99), 1) should be 99"
        );
    }

    /// set preserves length: len(set(s, i, v)) == len(s).
    #[test]
    #[timeout(30000)]
    fn test_seq_set_preserves_length() {
        let mut encoder = AYEncoder::new();
        let seq_expr = logic_fn_call("seq", vec![PureExpr::Int(1), PureExpr::Int(2)]);
        // Get length before set
        let len_before = method_call(seq_expr.clone(), "len", vec![]);
        // Get length after set
        let set_expr = method_call(seq_expr, "set", vec![PureExpr::Int(0), PureExpr::Int(99)]);
        let len_after = method_call(set_expr, "len", vec![]);

        let before_term = encoder.encode_pure(&len_before).expect("encode len_before");
        let after_term = encoder.encode_pure(&len_after).expect("encode len_after");

        // Assert they differ, expect UNSAT
        let eq = encoder.solver.eq(before_term, after_term);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "set should preserve sequence length"
        );
    }

    // ── subsequence encoding ────────────────────────────────────────

    /// subsequence(seq![10, 20, 30], 1, 3) should have length 2.
    #[test]
    #[timeout(30000)]
    fn test_seq_subsequence_length() {
        let mut encoder = AYEncoder::new();
        let seq_expr = logic_fn_call(
            "seq",
            vec![PureExpr::Int(10), PureExpr::Int(20), PureExpr::Int(30)],
        );
        let subseq_expr = method_call(
            seq_expr,
            "subsequence",
            vec![PureExpr::Int(1), PureExpr::Int(3)],
        );
        let len_expr = method_call(subseq_expr, "len", vec![]);
        let len_term = encoder
            .encode_pure(&len_expr)
            .expect("encode len(subsequence(...))");

        let two = encoder.solver.int_const(2);
        let eq = encoder.solver.eq(len_term, two);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "len(subsequence(seq![10,20,30], 1, 3)) should be 2"
        );
    }

    /// subsequence with wrong arg count should produce an error.
    #[test]
    #[timeout(30000)]
    fn test_seq_subsequence_wrong_args() {
        let mut encoder = AYEncoder::new();
        let seq_expr = logic_fn_call("seq", vec![PureExpr::Int(1)]);
        let subseq_expr = method_call(seq_expr, "subsequence", vec![PureExpr::Int(0)]);
        let result = encoder.encode_pure(&subseq_expr);
        assert!(
            result.is_err(),
            "subsequence with 1 argument should produce an error"
        );
    }

    // ── equality decomposition (via Seq terms) ──────────────────────

    /// Two seq_empty terms should be equal (proven via UNSAT of negation).
    #[test]
    #[timeout(30000)]
    fn test_seq_empty_equals_seq_empty() {
        let mut encoder = AYEncoder::new();
        let empty1 = logic_fn_call("seq_empty", vec![]);
        let empty2 = logic_fn_call("seq_empty", vec![]);

        let t1 = encoder.encode_pure(&empty1).expect("encode empty1");
        let t2 = encoder.encode_pure(&empty2).expect("encode empty2");

        // Assert t1 != t2, expect UNSAT (they should be the same constant)
        let eq = encoder.solver.eq(t1, t2);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "seq_empty should equal seq_empty"
        );
    }
}
