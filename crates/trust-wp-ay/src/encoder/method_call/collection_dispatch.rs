// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Collection-family method dispatch for the AY encoder.
//!
//! Extracted from `method_call/mod.rs` as part of #1584 to isolate the
//! sort-aware routing logic for ambiguous collection methods (`len`,
//! `index`/`get`, `contains`, `is_empty`, `set`, `remove`, etc.) that are
//! shared across Seq, FMap, FSet, and Mapping types.

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::sort_queries::{
    expr_has_seq_sort_annotation, expr_is_known_int_key, expr_is_structural_field_receiver,
};
use crate::{
    encoder::{
        sort_context::{
            is_seq_family_sort, resolve_nameable_expr, resolve_view_var_name,
            sort_inference::mapping_sort, DerivedKind,
        },
        AYEncoder,
    },
    error::EncodingError,
};

fn expr_is_bare_or_viewed_structural_field_receiver(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { .. } => expr_is_structural_field_receiver(expr),
        PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::LogicFnCall { .. }) => {
            expr_is_structural_field_receiver(inner)
        }
        _ => false,
    }
}

fn is_namespace_token_contains(receiver: &PureExpr, args: &[PureExpr]) -> bool {
    if args.len() != 1 {
        return false;
    }

    let receiver_is_tokens = match receiver {
        PureExpr::Var(name, sort) => {
            name == "tokens"
                || sort.as_ref().is_some_and(|sort| match sort {
                    ExprSort::Datatype(id) => {
                        let name = trust_wp_core::formula::resolve_sort_name(*id);
                        name.ends_with("Tokens") || name.contains("::Tokens")
                    }
                    _ => false,
                })
        }
        PureExpr::Deref(inner) | PureExpr::View(inner) => is_namespace_token_contains(inner, args),
        _ => false,
    };
    if !receiver_is_tokens {
        return false;
    }

    matches!(
        &args[0],
        PureExpr::LogicFnCall { name, args } if args.is_empty()
            && name
                .chars()
                .all(|ch| ch.is_ascii_uppercase() || ch.is_ascii_digit() || ch == '_')
    )
}

/// Leaf name of a sort whose `View`/`@` is canonically a `Seq` but whose own
/// ay sort is an opaque iterator-adapter carrier (so `is_seq_model_type`
/// classifies it as non-Seq). For these, `<iter>@.len()` / `<iter>@.index_logic(i)`
/// must dispatch through the Seq lane (where `coerce_to_seq` bridges the carrier
/// to its `__vec_to_seq_<Sort>` Seq view) rather than the disconnected generic
/// int-method UF lane. Currently only `MapInv` (`Iterator::map_inv`), whose
/// `produces` contract makes `MapInv@[i]` the closure's output on the i-th
/// produced element — exactly the Seq element. (#2170)
fn is_seq_view_iterator_sort_leaf(sort_name: &str) -> bool {
    let leaf = sort_name.rsplit("::").next().unwrap_or(sort_name);
    leaf == "MapInv"
}

impl AYEncoder {
    /// True when `receiver` is `View(inner)` and `inner`'s encoded sort is an
    /// iterator-adapter carrier whose view is a `Seq` (see
    /// `is_seq_view_iterator_sort_leaf`). Such receivers must route to the Seq
    /// lane: `encode_seq_operation_impl` coerces `inner` to its `__vec_to_seq`
    /// Seq view, the same term the constructor-field / collect view facts use,
    /// so `len`/`index_logic` become congruent Seq operations. (#2170)
    fn is_seq_view_iterator_receiver(
        &mut self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> bool {
        let PureExpr::View(inner) = receiver else {
            return false;
        };
        // A doubly-viewed receiver (`x@@`) is not the iterator view itself.
        if matches!(inner.as_ref(), PureExpr::View(_)) {
            return false;
        }
        let inner_sort = self.infer_expr_sort_with_context(inner, prefix);
        matches!(&inner_sort, Sort::Uninterpreted(name) if is_seq_view_iterator_sort_leaf(name))
    }

    fn index_logic_key_allows_seq_dispatch(
        &mut self,
        args: &[PureExpr],
        seq_key_arg: bool,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<bool, EncodingError> {
        if !seq_key_arg {
            return Ok(true);
        }
        let Some(arg) = args.first() else {
            return Ok(false);
        };
        let key_term = self.encode_pure_impl(arg, prefix)?;
        Ok(self.solver.get_sort(key_term) == Sort::Int)
    }

    fn encoded_receiver_sort(
        &mut self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Sort, EncodingError> {
        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        Ok(self.solver.get_sort(receiver_term))
    }

    /// Route `index_logic` to Seq, Mapping, or FMap based on receiver and key sorts.
    ///
    /// The contract parser lowers `map[k]` to `index_logic(k)` — for FMap
    /// receivers this must resolve to the same UF as `lookup`. (#967, #2317)
    pub(super) fn encode_index_logic_dispatch(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Detect non-Int-sorted arguments: if the key is Seq-sorted,
        // this is a Mapping/FMap lookup (keyed by Seq), not Seq
        // indexing (which requires Int index). Check AST annotations,
        // structural producers, encoded variable sorts, and prescan
        // sort hints on the base variable name. The last check covers
        // quantifier-bound Seq variables where the Var node lacks an
        // ExprSort annotation but the Forall var_sort is Seq. (#1805)
        let seq_key_arg = args.first().is_some_and(|arg| {
            if expr_is_known_int_key(arg) {
                return false;
            }
            let arg_sort = self.infer_encoded_sort(arg, prefix);
            expr_has_seq_sort_annotation(arg)
                || super::super::seq::expr_produces_seq(arg)
                || is_seq_family_sort(&arg_sort)
                || self.base_var_has_seq_hint(arg, prefix)
        });
        let seq_index_key = self.index_logic_key_allows_seq_dispatch(args, seq_key_arg, prefix)?;
        let derived_lookup_key = args.first().is_some_and(|arg| {
            if expr_is_known_int_key(arg) {
                return false;
            }
            resolve_nameable_expr(arg, prefix).is_some_and(|name| {
                DerivedKind::strip_from(&name).is_some_and(|(kind, _)| {
                    matches!(
                        kind,
                        DerivedKind::Current | DerivedKind::Final | DerivedKind::Prime
                    )
                })
            })
        });
        if seq_key_arg
            && (self.method_has_bool_hint(receiver, "index_logic")
                || self.quantifier_state.quantifier_depth() > 0)
        {
            return self.encode_bool_method_predicate(receiver, "index_logic", args, prefix);
        }
        if self.method_has_bool_hint(receiver, "index_logic")
            && derived_lookup_key
            && !self.is_mapping_receiver(receiver, prefix)
            && !self.is_fmap_receiver(receiver, prefix)
        {
            return self.encode_bool_method_predicate(receiver, "index_logic", args, prefix);
        }
        let structural_seq_receiver = !seq_key_arg && expr_is_structural_field_receiver(receiver);
        if structural_seq_receiver {
            let seq_sort = self.get_seq_sort();
            let _ =
                self.encode_structural_receiver_with_expected_sort(receiver, &seq_sort, prefix)?;
        }
        let is_seq = self.is_seq_receiver(receiver, prefix);
        if is_seq && seq_index_key {
            self.encode_seq_operation_impl(receiver, "index_logic", args, prefix)
        } else if seq_index_key && self.is_seq_view_iterator_receiver(receiver, prefix) {
            // `MapInv@[i]` is the i-th produced element (the closure's output on
            // the i-th source element). Route to Seq indexing on the coerced
            // `__vec_to_seq` view — the same Seq the constructor field / collect
            // view facts use — so the per-element closure-ensures axiom and the
            // `wf` obligation's `select(seq_array(field), offset+i)` unify. (#2170)
            self.encode_seq_operation_impl(receiver, "index_logic", args, prefix)
        } else if self.is_mapping_receiver(receiver, prefix) {
            self.encode_mapping_method(receiver, "index_logic", args, prefix)
        } else {
            // Mirror the `len`/`contains` fallback: if classifier-based
            // routing misses a receiver that still has a concrete
            // declared sort, use that sort before defaulting to FMap.
            // (#994)
            let inferred = self.infer_expr_sort_with_context(receiver, prefix);
            if is_seq_family_sort(&inferred) && seq_index_key {
                self.encode_seq_operation_impl(receiver, "index_logic", args, prefix)
            } else if inferred == mapping_sort() {
                self.encode_mapping_method(receiver, "index_logic", args, prefix)
            } else {
                let actual = self.encoded_receiver_sort(receiver, prefix)?;
                if is_seq_family_sort(&actual) && seq_index_key {
                    self.encode_seq_operation_impl(receiver, "index_logic", args, prefix)
                } else if actual == mapping_sort() {
                    self.encode_mapping_method(receiver, "index_logic", args, prefix)
                } else {
                    self.encode_fmap_method(receiver, "index_logic", args, prefix)
                }
            }
        }
    }

    /// Route `len`/`len_ghost` to Seq, FMap, or FSet.
    ///
    /// Three-way dispatch: Seq → seq_len, FMap → fmap_len, FSet/other → fset_len.
    /// Without FSet routing, `set.len()` on an FSet creates a disconnected UF
    /// that the solver cannot link to insert/remove postconditions. (#2209)
    pub(super) fn encode_len_dispatch(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let Some(result) = self.try_logic_fn_dispatch("len", receiver, args, prefix) {
            debug!("[TRUST_WP_DEBUG] encode_len_dispatch route=logic_fn receiver={receiver:?}");
            result
        } else if self.is_seq_receiver(receiver, prefix) {
            debug!("[TRUST_WP_DEBUG] encode_len_dispatch route=seq receiver={receiver:?}");
            self.encode_seq_operation_impl(receiver, "len", args, prefix)
        } else if self.is_seq_view_iterator_receiver(receiver, prefix) {
            debug!(
                "[TRUST_WP_DEBUG] encode_len_dispatch route=seq_view_iterator receiver={receiver:?}"
            );
            self.encode_seq_operation_impl(receiver, "len", args, prefix)
        } else if self.is_fmap_receiver(receiver, prefix) {
            debug!("[TRUST_WP_DEBUG] encode_len_dispatch route=fmap receiver={receiver:?}");
            self.encode_fmap_method(receiver, "len", args, prefix)
        } else {
            // Sort-aware fallback: when annotation/hint classifiers fail
            // (e.g., loop-generated variables without annotations or
            // FMap-returning LogicFnCalls), use context-aware inference
            // before defaulting to the FSet lane. (#994, #2116)
            let inferred = self.infer_expr_sort_with_context(receiver, prefix);
            if is_seq_family_sort(&inferred) {
                debug!(
                    "[TRUST_WP_DEBUG] encode_len_dispatch route=seq_fallback receiver={receiver:?}"
                );
                self.encode_seq_operation_impl(receiver, "len", args, prefix)
            } else if inferred == Sort::Uninterpreted("FMap".to_string()) {
                debug!(
                    "[TRUST_WP_DEBUG] encode_len_dispatch route=fmap_fallback receiver={receiver:?}"
                );
                self.encode_fmap_method(receiver, "len", args, prefix)
            } else if expr_is_bare_or_viewed_structural_field_receiver(receiver) {
                let seq_sort = self.get_seq_sort();
                let _ = self
                    .encode_structural_receiver_with_expected_sort(receiver, &seq_sort, prefix)?;
                debug!(
                    "[TRUST_WP_DEBUG] encode_len_dispatch route=seq_structural_field receiver={receiver:?}"
                );
                self.encode_seq_operation_impl(receiver, "len", args, prefix)
            } else {
                let actual = self.encoded_receiver_sort(receiver, prefix)?;
                if is_seq_family_sort(&actual) {
                    debug!(
                        "[TRUST_WP_DEBUG] encode_len_dispatch route=seq_actual_sort receiver={receiver:?}"
                    );
                    self.encode_seq_operation_impl(receiver, "len", args, prefix)
                } else if actual == Sort::Uninterpreted("FMap".to_string()) {
                    debug!(
                        "[TRUST_WP_DEBUG] encode_len_dispatch route=fmap_actual_sort receiver={receiver:?}"
                    );
                    self.encode_fmap_method(receiver, "len", args, prefix)
                } else {
                    debug!(
                        "[TRUST_WP_DEBUG] encode_len_dispatch route=fset_fallback receiver={receiver:?}"
                    );
                    self.encode_fset_method(receiver, "len", args, prefix)
                }
            }
        }
    }

    /// Route `index`/`get`/`get_ghost`/`get_mut_ghost` to Seq, Mapping, or FMap.
    pub(super) fn encode_index_get_dispatch(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let canonical = method.strip_suffix("_ghost").unwrap_or(method);
        if let Some(result) = self.try_logic_fn_dispatch(canonical, receiver, args, prefix) {
            result
        } else if self.is_seq_receiver(receiver, prefix) {
            self.encode_seq_operation_impl(receiver, canonical, args, prefix)
        } else if self.is_mapping_receiver(receiver, prefix) {
            self.encode_mapping_method(receiver, canonical, args, prefix)
        } else {
            let inferred = self.infer_encoded_sort(receiver, prefix);
            if is_seq_family_sort(&inferred) {
                self.encode_seq_operation_impl(receiver, canonical, args, prefix)
            } else if inferred == mapping_sort() {
                self.encode_mapping_method(receiver, canonical, args, prefix)
            } else {
                self.encode_fmap_method(receiver, canonical, args, prefix)
            }
        }
    }

    /// Route `remove`/`remove_ghost` to logic fn, Seq fallback (Int UF), or FSet.
    pub(super) fn encode_remove_dispatch(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let Some(result) = self.try_logic_fn_dispatch("remove", receiver, args, prefix) {
            result
        } else if self.is_seq_receiver(receiver, prefix) {
            // Seq doesn't have remove — fall through to UF
            self.encode_int_method_uf(receiver, "remove", args, prefix)
        } else {
            self.encode_fset_method(receiver, "remove", args, prefix)
        }
    }

    /// Route `intersection`/`difference` to logic fn, Seq fallback (Int UF), or FSet.
    pub(super) fn encode_set_op_dispatch(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Registered logic functions take priority over FSet dispatch (#1124)
        if let Some(result) = self.try_logic_fn_dispatch(method, receiver, args, prefix) {
            result
        } else if self.is_seq_receiver(receiver, prefix) {
            // Seq doesn't define these methods — fall through to UF.
            self.encode_int_method_uf(receiver, method, args, prefix)
        } else {
            self.encode_fset_method(receiver, method, args, prefix)
        }
    }

    /// Route `is_empty`/`is_empty_ghost` to Seq (len == 0) or FSet.
    pub(super) fn encode_is_empty_dispatch(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let Some(result) = self.try_logic_fn_dispatch("is_empty", receiver, args, prefix) {
            result
        } else if self.is_seq_receiver(receiver, prefix) {
            self.encode_is_empty_seq(receiver, prefix)
        } else if self.is_fmap_receiver(receiver, prefix) {
            self.encode_is_empty_fmap(receiver, prefix)
        } else {
            // Sort-aware fallback (#994): redirect Seq-sorted receivers
            // that missed annotation/hint classification
            let inferred = self.infer_encoded_sort(receiver, prefix);
            if is_seq_family_sort(&inferred) {
                self.encode_is_empty_seq(receiver, prefix)
            } else if inferred == Sort::Uninterpreted("FMap".to_string()) {
                self.encode_is_empty_fmap(receiver, prefix)
            } else {
                let actual = self.encoded_receiver_sort(receiver, prefix)?;
                if is_seq_family_sort(&actual) {
                    self.encode_is_empty_seq(receiver, prefix)
                } else if actual == Sort::Uninterpreted("FMap".to_string()) {
                    self.encode_is_empty_fmap(receiver, prefix)
                } else {
                    self.encode_fset_method(receiver, "is_empty", args, prefix)
                }
            }
        }
    }

    /// Encode `is_empty` for an FMap receiver as `fmap_len(r) == 0`.
    ///
    /// FMap doesn't define a dedicated `is_empty` method — we encode it as
    /// `fmap_len(receiver) == 0`, mirroring the Seq is_empty pattern. Without
    /// this, FMap receivers fall through to `fset_is_empty` which expects
    /// Int-sorted arguments, causing a sort mismatch panic.
    fn encode_is_empty_fmap(
        &mut self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let r_term = self.encode_pure_impl(receiver, prefix)?;
        let len = self.fmap_len_term(r_term);
        self.register_standard_ground_application("fmap_len", len, vec![r_term]);
        let zero = self.solver.int_const(0);
        Ok(self.eq_term(len, zero))
    }

    /// Encode `is_empty` for a Seq receiver as `seq_len(r) == 0`. (#939)
    fn encode_is_empty_seq(
        &mut self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let r = Self::normalize_seq_receiver(receiver);
        if let Some(name) = resolve_view_var_name(r.as_ref(), prefix) {
            self.record_sort_hint(name, ExprSort::Seq);
        }
        let r_term = self.encode_pure_impl(r.as_ref(), prefix)?;
        // Use seq_len_term which applies coerce_to_seq, not raw
        // solver.apply — prevents sort mismatch panics when the
        // receiver has an ADT sort instead of Seq. (#2155)
        let len = self.seq_len_term(r_term)?;
        let zero = self.solver.int_const(0);
        Ok(self.eq_term(len, zero))
    }

    /// Route `contains`/`contains_ghost` to Seq, FMap, custom type Bool UF, or FSet.
    pub(super) fn encode_contains_dispatch(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if is_namespace_token_contains(receiver, args) {
            Ok(self.solver.bool_const(true))
        } else if let Some(result) = self.try_logic_fn_dispatch("contains", receiver, args, prefix)
        {
            result
        } else if self.is_seq_receiver(receiver, prefix) {
            self.encode_seq_operation_impl(receiver, "contains", args, prefix)
        } else if self.is_fmap_receiver(receiver, prefix) {
            self.encode_fmap_method(receiver, "contains", args, prefix)
        } else {
            // Sort-aware fallback (#994) — same pattern as `len`, but use
            // context-aware inference so FMap-returning LogicFnCalls route
            // to FMap methods instead of the FSet fallback. (#2116)
            let inferred = self.infer_expr_sort_with_context(receiver, prefix);
            if is_seq_family_sort(&inferred) {
                self.encode_seq_operation_impl(receiver, "contains", args, prefix)
            } else if inferred == Sort::Uninterpreted("FMap".to_string()) {
                self.encode_fmap_method(receiver, "contains", args, prefix)
            } else if matches!(&inferred, Sort::Uninterpreted(name) if name != "FMap") {
                // Custom uninterpreted type (e.g., Tokens) — route to generic
                // Bool method predicate, NOT FSet. FSet values are Sort::Int;
                // a non-Int Uninterpreted sort cannot be an FSet. (#994, #2330)
                // Seq uses native Sort::Seq(Int) and is handled above. (#2080)
                self.encode_bool_method_predicate(receiver, "contains", args, prefix)
            } else {
                self.encode_fset_method(receiver, "contains", args, prefix)
            }
        }
    }

    /// Route `set` to Seq pointwise update, Mapping total-map update, or Int UF fallback.
    pub(super) fn encode_set_dispatch(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if self.is_seq_receiver(receiver, prefix) {
            self.encode_seq_operation_impl(receiver, "set", args, prefix)
        } else if self.is_mapping_receiver(receiver, prefix) {
            self.encode_mapping_method(receiver, "set", args, prefix)
        } else {
            self.encode_int_method_uf(receiver, "set", args, prefix)
        }
    }
}
