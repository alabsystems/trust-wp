// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Method-call sort inference for `PureExpr::MethodCall` arms.
//!
//! Extracted from the main `infer_expr_sort_impl` match expression to keep
//! the parent module under the 500-line guideline. Part of #1988.

use ay_dpll::api::Sort;
use tracing::debug;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::{
    expr_sort_to_ay_sort, fmap_sort, mapping_sort,
    receiver_shape::{
        receiver_annotation, receiver_annotation_is_seq_like, receiver_is_fmap_like,
        receiver_is_mapping_like, receiver_is_option_like, receiver_is_predcell_slice_like,
        receiver_is_result_like, receiver_is_seq_like, receiver_is_structural_field_like,
    },
};
use crate::encoder::{
    match_enc::SwitchTarget, seq::method_produces_seq_unconditional, unsoundness,
};

/// Infer the ay sort for a `MethodCall` expression.
///
/// This dispatches across all recognized method names and receiver shapes.
/// Returns `None` if no specific rule matches (caller falls through to
/// generic catch-all logic).
#[allow(clippy::match_same_arms, clippy::too_many_lines)]
pub(super) fn infer_method_call_sort(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
    infer_child: &mut impl FnMut(&PureExpr) -> Sort,
) -> Sort {
    // Boolean-returning methods: precondition/postcondition family, testers,
    // predicates, invariants, iterator predicates.
    if matches!(
        method,
        "precondition"
            | "postcondition"
            | "postcondition_once"
            | "postcondition_mut"
            | "is_some"
            | "is_none"
            | "is_ok"
            | "is_err"
            | "contains"
            | "contains_key"
            | "completed"
            | "produces"
            | "premise"
            | "ext_eq"
            | "is_empty"
            | "all"
            | "any"
            | "starts_with"
            | "ends_with"
            | "is_sorted"
            | "is_ascii"
            | "eq"
            | "ne"
            | "lt"
            | "le"
            | "gt"
            | "ge"
            | "is_positive"
            | "is_negative"
            | "is_power_of_two"
            | "is_finite"
            | "is_nan"
            | "is_infinite"
            | "in_bounds"
    ) || trust_wp_core::logic::is_invariant_method_name(method)
    {
        return Sort::Bool;
    }

    // FMap `into_seq()` returns a Seq witness rather than an FMap.
    if method == "into_seq" && receiver_is_fmap_like(receiver) {
        return Sort::seq(Sort::Int);
    }

    // Seq-producing methods (unconditional).
    if method_produces_seq_unconditional(method) {
        return Sort::seq(Sort::Int);
    }

    if method == "update"
        && args.len() == 2
        && matches!(
            receiver,
            PureExpr::LogicFnCall { name, args }
                if trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity(name)
                    == Some(2)
                    && args.len() == 2
        )
    {
        return Sort::Uninterpreted("Tuple2".to_string());
    }

    // Seq::empty() static constructor.
    if method == "empty"
        && args.is_empty()
        && matches!(receiver, PureExpr::Var(name, _) if name == "Seq")
    {
        return Sort::seq(Sort::Int);
    }

    // FMap::empty() static constructor. Without this rule, the expression
    // defaults to Int via the catch-all, causing sort mismatches when the
    // result is used in FMap operations. (#2207)
    if method == "empty"
        && args.is_empty()
        && matches!(receiver, PureExpr::Var(name, _) if name == "FMap")
    {
        return fmap_sort();
    }

    // Seq::set returns Seq sort.
    if method == "set" && receiver_is_seq_like(receiver) {
        return Sort::seq(Sort::Int);
    }

    // Mapping::set returns Mapping sort (total function update). (#2317)
    if method == "set" && receiver_is_mapping_like(receiver) {
        return mapping_sort();
    }

    // Option-returning methods on Option-like receivers: map, and_then,
    // or_else, filter, flatten, cloned, copied, and, or, xor, take,
    // replace, zip. These return Option<T> in all cases. (#2663)
    if matches!(
        method,
        "map"
            | "and_then"
            | "or_else"
            | "filter"
            | "flatten"
            | "cloned"
            | "copied"
            | "and"
            | "or"
            | "xor"
            | "take"
            | "replace"
            | "zip"
    ) && receiver_is_option_like(receiver)
    {
        return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
    }

    // Result-returning methods on Result-like receivers: map, map_err,
    // and_then, or_else. These return Result<T, E> in all cases. (#2663)
    if matches!(method, "map" | "map_err" | "and_then" | "or_else")
        && receiver_is_result_like(receiver)
    {
        return Sort::Uninterpreted(SwitchTarget::ResultIntInt.datatype().name);
    }

    // ok_or / ok_or_else on Option receivers return Result. (#2663)
    if matches!(method, "ok_or" | "ok_or_else") && receiver_is_option_like(receiver) {
        return Sort::Uninterpreted(SwitchTarget::ResultIntInt.datatype().name);
    }

    // ok() / err() on Result receivers return Option. (#2663)
    if matches!(method, "ok" | "err") && receiver_is_result_like(receiver) {
        return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
    }

    // checked_* arithmetic methods always return Option<T>. (#2663)
    if matches!(
        method,
        "checked_add"
            | "checked_sub"
            | "checked_mul"
            | "checked_div"
            | "checked_rem"
            | "checked_neg"
            | "checked_shl"
            | "checked_shr"
            | "checked_pow"
    ) {
        return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
    }

    // overflowing_* arithmetic methods return (T, bool) as a Tuple2. (#2663)
    if matches!(
        method,
        "overflowing_add"
            | "overflowing_sub"
            | "overflowing_mul"
            | "overflowing_neg"
            | "overflowing_shl"
            | "overflowing_shr"
            | "overflowing_pow"
    ) {
        return Sort::Uninterpreted("Tuple2".to_string());
    }

    // transpose on Option<Result<T,E>> or Result<Option<T>,E>:
    // the return type switches between the two wrappers. Since we cannot
    // determine which wrapper is outer from sort inference alone, use the
    // receiver's annotation to decide. On Option receivers → ResultIntInt,
    // on Result receivers → OptionInt. (#2663)
    if method == "transpose" {
        if receiver_is_option_like(receiver) {
            return Sort::Uninterpreted(SwitchTarget::ResultIntInt.datatype().name);
        }
        if receiver_is_result_like(receiver) {
            return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
        }
    }

    // PredCell slice indexing returns PredCell uninterpreted sort.
    if matches!(method, "index" | "index_logic") && receiver_is_predcell_slice_like(receiver) {
        return Sort::Uninterpreted("PredCell".to_string());
    }

    // FMap-returning methods: insert and merge on FMap receivers produce FMap.
    // Without this, these expressions default to Int, causing sort mismatches
    // when the result is used in FMap operations (contains, lookup). (#994 Phase 2c)
    if matches!(method, "insert" | "insert_ghost" | "merge") && receiver_is_fmap_like(receiver) {
        return fmap_sort();
    }

    // MethodCall receiver sort propagation: when the receiver carries a
    // Datatype ExprSort annotation and the method is not a known
    // element-accessor, propagate the receiver's sort. (#994 Phase 2c)
    // Extended exclusion list per #2663 to prevent element accessors,
    // value-extracting methods, and arithmetic methods from incorrectly
    // propagating the Datatype sort instead of their actual return sort.
    if !matches!(
        method,
        "len"
            | "len_logic"
            | "pow2"
            | "sum"
            | "get"
            | "index"
            | "index_logic"
            | "unwrap"
            | "unwrap_err"
            | "unwrap_or"
            | "unwrap_or_default"
            | "unwrap_or_else"
            | "expect"
            | "lookup"
            | "deep_model"
            | "shallow_model"
            | "capacity"
            | "abs"
            | "min"
            | "max"
            | "clamp"
            | "count"
            | "position"
            | "has_value"
            | "resolve_elsewhere"
    ) && matches!(receiver_annotation(receiver), Some(ExprSort::Datatype(_)))
    {
        return match receiver_annotation(receiver) {
            Some(sort) => expr_sort_to_ay_sort(sort),
            None => Sort::Int,
        };
    }

    // Ghost permission accessors (`perm.ward()`, `perm.val()`) return
    // references to the guarded value. The current AST-level sort
    // inference does not recover the pointee sort from bare permission
    // placeholders such as `__trust_wp_tuple_get_0(self)`, but routing these
    // nullary accessors through the generic HIGH-risk catch-all creates
    // false demotions in compat proofs like `*self.0.ward() == pc`.
    //
    // Keep them on the LOW-risk method-call lane instead: the fallback is
    // still `Int`, but it is the same conservative reference-erasure
    // approximation used for other value accessors until the encoder can
    // thread the guarded inner sort directly. (#994)
    if args.is_empty() && matches!(method, "ward" | "val") {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // Unconditionally Int-returning methods and model methods: these
    // return integers in the common case and other sorts are typically
    // resolved by sort hints and receiver annotations. LOW risk — the
    // Int fallback is correct for the dominant use case.
    // Reclassified LOW per #2202 AC2. Added `discriminant` per #2204.
    // Extended with arithmetic methods per #2663.
    if matches!(
        method,
        "len"
            | "len_logic"
            | "pow2"
            | "start_log"
            | "end_log"
            | "sum"
            | "deep_model"
            | "shallow_model"
            | "discriminant"
            | "namespace"
            | "capacity"
            | "abs"
            | "min"
            | "max"
            | "clamp"
            | "saturating_add"
            | "saturating_sub"
            | "saturating_mul"
            | "wrapping_add"
            | "wrapping_sub"
            | "wrapping_mul"
            | "count_ones"
            | "count_zeros"
            | "leading_zeros"
            | "trailing_zeros"
            | "leading_ones"
            | "trailing_ones"
            | "rotate_left"
            | "rotate_right"
            | "swap_bytes"
            | "reverse_bits"
            | "to_be"
            | "to_le"
            | "from_be"
            | "from_le"
            | "pow"
            | "ilog2"
            | "ilog10"
            | "count"
            | "position"
            | "unwrap_or"
            | "unwrap_or_default"
            | "unwrap_or_else"
            | "expect"
            | "has_value"
            | "resolve_elsewhere"
    ) {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // Ghost/container accessors like `Perm::ward()` return the guarded
    // carrier, not a Bool predicate. Falling back to Int here is still
    // conservative, but it should not trigger the generic demoting
    // SortFallbackToInt path that is reserved for Bool-vs-Int mismatches.
    // This exact receiver shape appears in `non_atomic_invariant_cellinv`
    // as `*self.0.ward() == pc`. (#994)
    if method == "ward" {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // Invariant `public()` is a value accessor returning the protocol's
    // associated `Public` carrier, not a Bool predicate. The current
    // encoding still models that carrier on the Int fallback lane rather
    // than with associated-type-aware sorts, but keeping it off the Bool
    // path avoids spurious demotions in invariant bootstrap formulas. (#994)
    if method == "public" {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // FMap element access is Int-valued in the current encoding:
    // `encode_fmap_method` always routes these calls to `fmap_lookup`,
    // whose UF declaration and linking axioms use `Sort::Int` for values.
    // This is the same fixed-sort situation as Seq element access on a
    // known Seq receiver, so keep it on the LOW-risk method-call lane
    // instead of demoting proofs through the generic high-risk fallback.
    // (#2209)
    if matches!(method, "get" | "index" | "index_logic" | "lookup")
        && receiver_is_fmap_like(receiver)
    {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // Mapping element access: `mapping_get` UF returns `Sort::Int` in the
    // current encoding (Mapping<K,V> with V=Int). Use LOW-risk fallback
    // since the Int default matches the dominant total-map use case. (#2317)
    if matches!(method, "get" | "index" | "index_logic") && receiver_is_mapping_like(receiver) {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // Element-access methods on Seq-like receivers: the element type is
    // overwhelmingly Int in practice (integer-indexed collections). When
    // the receiver carries a Seq or Seq-model annotation, use LOW-risk
    // fallback — the Int default is correct for the dominant case, and
    // Bool-element cases are caught by sort hints (register_formula_sort_hints).
    // Without Seq evidence, keep HIGH-risk since element could be Bool
    // (eq vs iff matters). (#2230, #2204)
    if matches!(method, "index" | "index_logic")
        && receiver_is_structural_field_like(receiver)
        && args
            .first()
            .is_some_and(|arg| infer_child(arg) == Sort::Int)
    {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // unwrap on Option-like receivers: the inner element type is Int in
    // the current encoding (Option<T> → OptionInt with Sort::Int payload).
    // Use LOW-risk fallback since the receiver annotation confirms the
    // composite type context, and Int is the correct element sort. (#2207)
    if method == "unwrap" && receiver_is_option_like(receiver) {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // unwrap/unwrap_err on Result-like receivers: both Ok and Err payloads
    // are Int in the current encoding (ResultIntInt). LOW-risk fallback. (#2207)
    if matches!(method, "unwrap" | "unwrap_err") && receiver_is_result_like(receiver) {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // Seq::get() returns Option<T> — infer as OptionInt Datatype sort rather
    // than Int, preventing sort mismatches when the result is used in Option
    // match contexts (is_some tester expects Datatype, not Int). (#2207)
    if method == "get" && receiver_annotation_is_seq_like(receiver) {
        return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
    }

    // Remaining get/index_logic: element access methods. Use LOW-risk
    // fallback regardless of receiver evidence (#2231): the method name
    // is known to be an element accessor, so Int is the correct default
    // for the dominant case (integer-indexed collections). Bool-element
    // cases are caught by sort hints. Previously only Seq-evidence
    // receivers used LOW-risk (#2230, #2204); now all element accessors
    // are LOW since the method name provides sufficient evidence.
    if matches!(method, "get" | "index_logic") {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // unwrap/lookup on unannotated receivers: element type depends on
    // Option<T>/FMap<K,V> inner type which is not carried by ExprSort.
    // Reclassified from HIGH to LOW (#2231): the method name itself is
    // known (unwrap/lookup), so this is not a blind catch-all. The Int
    // default is correct for the dominant case (integer payloads). Bool
    // payloads are caught by sort hints (register_formula_sort_hints).
    // Previously HIGH (#2204), demoted to LOW since annotation-bearing
    // receivers are already routed to the LOW path above.
    if matches!(method, "unwrap" | "lookup") {
        debug!(
            "[TRUST_WP_DEBUG] SortFallbackToIntFromMethodCall: method \"{method}\" (unannotated)"
        );

        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return Sort::Int;
    }

    // Generic MethodCall receiver-propagation: when the receiver carries
    // an ExprSort annotation and the method is not handled by any rule
    // above, infer the sort from the receiver's annotation rather than
    // falling through to the HIGH-risk catch-all. This covers methods
    // like `clone()`, `into_inner()`, and other self-returning methods
    // that preserve the receiver type. Uses LOW-risk fallback since the
    // annotation provides evidence of the actual sort. (#1096)
    if receiver_annotation(receiver).is_some() {
        let sort = infer_child(receiver);
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
        return sort;
    }

    // Generic MethodCall without annotation: the receiver has no
    // ExprSort annotation but the method is unrecognized. Use LOW-risk
    // fallback (SortFallbackToIntFromMethodCall) instead of the demoting
    // HIGH-risk catch-all, since these are still method calls where
    // Int is the overwhelmingly common return type. (#1096)
    unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromMethodCall);
    Sort::Int
}
