// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parity audit: `infer_expr_sort` vs `encode_method_call_impl` sort agreement.
//!
//! The `infer_expr_sort` function in `sort_context.rs` classifies method call
//! return sorts based on the method name. The `encode_method_call_impl` function
//! in `method_call/mod.rs` dispatches to specialized encoders that produce terms of
//! specific sorts. These two must agree: if `encode_method_call_impl` produces a
//! Bool-sorted term, `infer_expr_sort` must return `Sort::Bool` for the same
//! `MethodCall` expression.
//!
//! When they disagree, downstream consumers (e.g., `Ite` branch sort inference,
//! equality sort propagation, `mk_not` application) use the wrong sort, causing
//! ay sort-mismatch panics that are caught by `catch_ay_sort_panics` — or worse,
//! silently produce unsound encodings.
//!
//! Findings:
//! - `is_empty` is encoded as Bool (len == 0) but inferred as Int (Gap 1)

use ay_dpll::api::Sort;
use ntest::timeout;

use super::{super::encoder::sort_context::infer_expr_sort, helpers::*};
use crate::ExprSort;

// =============================================================================
// Bool-returning methods: parity between infer_expr_sort and encode_method_call_impl
// =============================================================================

/// Methods that `encode_method_call_impl` encodes as Bool predicates.
/// `infer_expr_sort` must return `Sort::Bool` for each of these.
#[test]
#[timeout(30000)]
fn parity_closure_spec_methods_return_bool() {
    for method in &[
        "precondition",
        "postcondition",
        "postcondition_once",
        "postcondition_mut",
    ] {
        let expr = method_call(var("self"), method, vec![var("arg")]);
        assert_eq!(
            infer_expr_sort(&expr),
            Sort::Bool,
            "infer_expr_sort should return Bool for closure-spec method `{method}`"
        );
    }
}

#[test]
#[timeout(30000)]
fn parity_datatype_tester_methods_return_bool() {
    for method in &["is_some", "is_none", "is_ok", "is_err"] {
        let expr = method_call(var("x"), method, vec![]);
        assert_eq!(
            infer_expr_sort(&expr),
            Sort::Bool,
            "infer_expr_sort should return Bool for datatype tester `{method}`"
        );
    }
}

#[test]
#[timeout(30000)]
fn parity_iterator_completed_returns_bool() {
    let expr = method_call(var("iter"), "completed", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "infer_expr_sort should return Bool for `completed`"
    );
}

#[test]
#[timeout(30000)]
fn parity_contains_returns_bool() {
    let expr = method_call(var("s"), "contains", vec![var("x")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "infer_expr_sort should return Bool for `contains`"
    );
}

#[test]
#[timeout(30000)]
fn parity_produces_returns_bool() {
    let expr = method_call(var("iter"), "produces", vec![var("visited"), var("next")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "infer_expr_sort should return Bool for `produces`"
    );
}

#[test]
#[timeout(30000)]
fn parity_ext_eq_returns_bool() {
    let expr = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "infer_expr_sort should return Bool for `ext_eq`"
    );
}

#[test]
#[timeout(30000)]
fn parity_invariant_method_returns_bool() {
    let expr = method_call(var("x"), "invariant", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "infer_expr_sort should return Bool for invariant methods"
    );
}

// =============================================================================
// Value-returning accessors: current parity contract
// =============================================================================

/// `public()` is the invariant public-state accessor, not a predicate.
/// The current encoding routes it through the generic value-UF lane, so
/// `infer_expr_sort` must stay aligned with that Int fallback until the
/// encoder learns associated-type-aware return sorts. (#994)
#[test]
#[timeout(30000)]
fn parity_public_method_uses_value_fallback() {
    let expr = method_call(var("self"), "public", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "`public` should stay aligned with the value-UF fallback lane"
    );
}

// =============================================================================
// GAP 1: `is_empty` — Bool in encode_method_call_impl, Int in infer_expr_sort
// =============================================================================

/// `encode_method_call_impl` dispatches `is_empty` (when args is empty) to
/// either FSet encoding or Seq encoding (len == 0), both producing Bool.
/// `infer_expr_sort` falls through to `_ => Sort::Int` because `is_empty` is
/// not in its Bool method list.
///
/// Impact: `if v@.is_empty() { ... } else { ... }` — the condition is
/// correctly encoded as Bool, but `infer_expr_sort` says Int. If Ite branch
/// sort propagation uses `infer_expr_sort` on the condition, it won't
/// propagate Bool hints to the branches.
#[test]
#[timeout(30000)]
fn gap_is_empty_method_should_infer_as_bool() {
    let expr = method_call(view(var("v")), "is_empty", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "BUG: `is_empty` is encoded as Bool (len == 0) in encode_method_call_impl \
         but infer_expr_sort returns Int. Add `is_empty` to the Bool method list \
         in sort_context.rs infer_expr_sort."
    );
}

/// Same gap for bare-var receiver (FSet dispatch path).
#[test]
#[timeout(30000)]
fn gap_is_empty_bare_var_should_infer_as_bool() {
    let expr = method_call(var("s"), "is_empty", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "BUG: `is_empty` on bare var (FSet path) should also infer as Bool"
    );
}

// =============================================================================
// Seq-returning methods: parity check
// =============================================================================

/// Methods that `encode_method_call_impl` routes to `encode_seq_operation_impl`
/// (which returns Seq-sorted terms). `infer_expr_sort` should return Seq sort.
#[test]
#[timeout(30000)]
fn parity_seq_returning_methods_return_seq() {
    for method in &[
        "push_back",
        "push_front",
        "push_front_ghost",
        "pop_front",
        "tail",
        "reverse",
        "to_owned_seq",
        "concat",
        "subsequence",
    ] {
        let expr = method_call(view(var("v")), method, vec![var("arg1"), var("arg2")]);
        assert_eq!(
            infer_expr_sort(&expr),
            Sort::seq(Sort::Int),
            "infer_expr_sort should return Seq for `{method}`"
        );
    }
}

/// `set` on Seq receiver returns Seq.
#[test]
#[timeout(30000)]
fn parity_set_on_seq_receiver_returns_seq() {
    let expr = method_call(view(var("v")), "set", vec![int(0), int(1)]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "infer_expr_sort should return Seq for `set` on View receiver"
    );
}

// =============================================================================
// Int-returning methods: parity check
// =============================================================================

/// Methods that `encode_method_call_impl` routes to `encode_int_method_uf`
/// should be inferred as Int.
#[test]
#[timeout(30000)]
fn parity_int_uf_methods_return_int() {
    for method in &[
        "deep_model",
        "capacity",
        "namespace",
        "id",
        "addr_logic",
        "discriminant",
    ] {
        let expr = method_call(var("x"), method, vec![]);
        assert_eq!(
            infer_expr_sort(&expr),
            Sort::Int,
            "infer_expr_sort should return Int for UF method `{method}`"
        );
    }
}

/// `map` and `filter` are encoded as Int-returning UFs.
#[test]
#[timeout(30000)]
fn parity_map_filter_return_int() {
    for method in &["map", "filter"] {
        let expr = method_call(var("s"), method, vec![var("f")]);
        assert_eq!(
            infer_expr_sort(&expr),
            Sort::Int,
            "infer_expr_sort should return Int for collection method `{method}`"
        );
    }
}

// =============================================================================
// Datatype accessor methods: sort consistency
// =============================================================================

/// `unwrap` and `unwrap_err` are encoded as datatype accessors.
/// They return Int in the default case (accessor is declared as Int-returning UF).
/// `infer_expr_sort` should NOT return Bool for these — they are value extractors.
#[test]
#[timeout(30000)]
fn parity_unwrap_methods_not_bool() {
    // unwrap/unwrap_err are dispatched to encode_datatype_spec_method
    // which creates UF accessors, not Bool predicates.
    // infer_expr_sort correctly falls through to _ => Sort::Int.
    for method in &["unwrap", "unwrap_err"] {
        let expr = method_call(var("opt"), method, vec![]);
        // These should NOT be Bool — they extract values.
        assert_ne!(
            infer_expr_sort(&expr),
            Sort::Bool,
            "`{method}` is a value extractor, not a Bool predicate"
        );
    }
}

// =============================================================================
// Unsoundness category classification (#2204)
// =============================================================================

/// Element-access methods (`get`, `index_logic`, `unwrap`, `lookup`) now use the
/// LOW-risk `SortFallbackToIntFromMethodCall` category. The method name itself
/// provides sufficient evidence — Int is correct for the dominant case, and
/// Bool element cases are caught by sort hints. Reclassified per #2231.
#[test]
#[timeout(30000)]
fn element_access_methods_use_low_risk_category() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    for method in &["get", "index_logic", "unwrap", "lookup"] {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        let expr = method_call(var("v"), method, vec![]);
        let _ = infer_expr_sort(&expr);
        let d = unsoundness::delta(&before, &unsoundness::snapshot());

        assert!(
            !d.contains_key(&UnsoundnessCategory::SortFallbackToInt),
            "`{method}` should NOT use HIGH-risk SortFallbackToInt, got delta: {d:?}"
        );
        assert!(
            d.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
            "`{method}` should use LOW-risk SortFallbackToIntFromMethodCall, got delta: {d:?}"
        );
        unsoundness::reset();
    }
}

/// Seq receivers are the one intentional exception from #2230: for `index_logic`
/// the encoder records the LOW-risk method-call fallback when the receiver is
/// already known to be Seq-like.
///
/// `get` on Seq-like receivers now correctly returns OptionInt Datatype sort
/// (Seq::get returns Option<T>), so it fires no fallback at all. (#2207)
#[test]
#[timeout(30000)]
fn seq_receiver_element_access_methods_use_low_risk_category() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    // index_logic on Seq-like receiver: LOW-risk fallback (element access)
    #[allow(clippy::single_element_loop)]
    // loop retained for consistency with similar multi-method tests
    for method in &["index_logic"] {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        let expr = method_call(view(var("v")), method, vec![int(0)]);
        let _ = infer_expr_sort(&expr);
        let d = unsoundness::delta(&before, &unsoundness::snapshot());

        assert!(
            d.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
            "Seq receiver `{method}` should use LOW-risk SortFallbackToIntFromMethodCall, got delta: {d:?}"
        );
        assert!(
            !d.contains_key(&UnsoundnessCategory::SortFallbackToInt),
            "Seq receiver `{method}` should not use HIGH-risk SortFallbackToInt, got delta: {d:?}"
        );
        unsoundness::reset();
    }

    // get on Seq-like receiver: returns OptionInt sort directly (no fallback). (#2207)
    {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        let expr = method_call(view(var("v")), "get", vec![int(0)]);
        let sort = infer_expr_sort(&expr);
        let d = unsoundness::delta(&before, &unsoundness::snapshot());

        assert_eq!(
            sort,
            Sort::Uninterpreted("OptionInt".to_string()),
            "Seq.get() should return OptionInt sort, got {sort:?}"
        );
        assert!(
            !d.contains_key(&UnsoundnessCategory::SortFallbackToInt),
            "Seq.get() should not fire any fallback, got delta: {d:?}"
        );
        assert!(
            !d.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
            "Seq.get() should not fire any fallback, got delta: {d:?}"
        );
        unsoundness::reset();
    }
}

/// FMap receivers use the same LOW-risk method-call lane because the current
/// `fmap_lookup` encoding fixes values to `Int`. This avoids demoting Int-only
/// ghost-map proofs through the generic element-access fallback. (#2209)
#[test]
#[timeout(30000)]
fn fmap_receiver_element_access_methods_use_low_risk_category() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    for method in &["get", "index", "index_logic", "lookup"] {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        let expr = method_call(var_with_sort("m", ExprSort::FMap), method, vec![int(0)]);
        let _ = infer_expr_sort(&expr);
        let d = unsoundness::delta(&before, &unsoundness::snapshot());

        assert!(
            d.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
            "FMap receiver `{method}` should use LOW-risk SortFallbackToIntFromMethodCall, got delta: {d:?}"
        );
        assert!(
            !d.contains_key(&UnsoundnessCategory::SortFallbackToInt),
            "FMap receiver `{method}` should not use HIGH-risk SortFallbackToInt, got delta: {d:?}"
        );
        unsoundness::reset();
    }
}

/// Mapping receivers use LOW-risk `SortFallbackToIntFromMethodCall` for all
/// element access methods (`get`, `index`, `index_logic`). The current Mapping
/// encoding fixes values to `Sort::Int` (total function `Mapping<K, Int>`), so
/// the Int fallback is correct for the dominant use case. (#2317)
///
/// Regression guard: `index` must be in the element-accessor exclusion list
/// (sort_inference.rs:320-332) to reach the Mapping element-access arm. Without
/// it, `Mapping.index` hits Datatype propagation and returns Mapping sort,
/// mismatching `encode_mapping_method` which uses `mapping_get` (Sort::Int).
#[test]
#[timeout(30000)]
fn mapping_receiver_element_access_methods_use_low_risk_category() {
    use trust_wp_core::formula::intern_sort_name;

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    let mapping_dt = ExprSort::Datatype(intern_sort_name("Mapping"));

    for method in &["get", "index", "index_logic"] {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        let expr = method_call(var_with_sort("m", mapping_dt.clone()), method, vec![int(0)]);
        let sort = infer_expr_sort(&expr);
        let d = unsoundness::delta(&before, &unsoundness::snapshot());

        assert_eq!(
            sort,
            Sort::Int,
            "Mapping receiver `{method}` should infer as Int (matching encoding)"
        );
        assert!(
            d.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
            "Mapping receiver `{method}` should use LOW-risk SortFallbackToIntFromMethodCall, got delta: {d:?}"
        );
        assert!(
            !d.contains_key(&UnsoundnessCategory::SortFallbackToInt),
            "Mapping receiver `{method}` should not use HIGH-risk SortFallbackToInt, got delta: {d:?}"
        );
        unsoundness::reset();
    }
}

/// `Mapping.set` returns Mapping sort directly — no unsoundness fallback at all.
/// This confirms set is fully resolved, unlike element access which falls back
/// to Int. (#2317)
#[test]
#[timeout(30000)]
fn mapping_set_returns_mapping_no_unsoundness() {
    use trust_wp_core::formula::intern_sort_name;

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    let mapping_dt = ExprSort::Datatype(intern_sort_name("Mapping"));
    unsoundness::reset();
    let before = unsoundness::snapshot();
    let expr = method_call(var_with_sort("m", mapping_dt), "set", vec![int(0), int(42)]);
    let sort = infer_expr_sort(&expr);
    let d = unsoundness::delta(&before, &unsoundness::snapshot());

    assert_eq!(
        sort,
        Sort::Uninterpreted("Mapping".to_string()),
        "Mapping.set should return Mapping sort"
    );
    assert!(
        !d.contains_key(&UnsoundnessCategory::SortFallbackToInt),
        "Mapping.set should not trigger any Int fallback: {d:?}"
    );
    assert!(
        !d.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
        "Mapping.set should not trigger method-call fallback: {d:?}"
    );
    unsoundness::reset();
}

/// Known Int-returning methods (`len`, `sum`, `discriminant`, `deep_model`,
/// `shallow_model`) use the LOW-risk `SortFallbackToIntFromMethodCall` category.
/// These methods provably return Int regardless of the collection's element type,
/// so the Int fallback is always correct.
#[test]
#[timeout(30000)]
fn known_int_methods_use_low_risk_category() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    for method in &[
        "len",
        "len_logic",
        "sum",
        "deep_model",
        "shallow_model",
        "discriminant",
        "namespace",
        "capacity",
    ] {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        let expr = method_call(var("v"), method, vec![]);
        let _ = infer_expr_sort(&expr);
        let d = unsoundness::delta(&before, &unsoundness::snapshot());

        assert!(
            d.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
            "`{method}` should use LOW-risk SortFallbackToIntFromMethodCall, got delta: {d:?}"
        );
        assert!(
            !d.contains_key(&UnsoundnessCategory::SortFallbackToInt),
            "`{method}` should NOT use HIGH-risk SortFallbackToInt, got delta: {d:?}"
        );
        unsoundness::reset();
    }
}

/// Permission ghost accessors use the LOW-risk method-call fallback lane.
///
/// `perm.ward()` / `perm.val()` currently erase the guarded reference sort to
/// `Int` at the AST-only inference layer, but that is still less severe than
/// the generic HIGH-risk catch-all that demotes `non_atomic_invariant_cellinv`
/// after the solver has already verified the goal. (#994)
#[test]
#[timeout(30000)]
fn permission_accessors_use_low_risk_method_category() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    let permission_tuple_field = get_field(0, var("self"));

    for expr in [
        method_call(permission_tuple_field.clone(), "ward", vec![]),
        method_call(var("perm"), "val", vec![]),
    ] {
        unsoundness::reset();
        let before = unsoundness::snapshot();
        let sort = infer_expr_sort(&expr);
        let d = unsoundness::delta(&before, &unsoundness::snapshot());

        assert_eq!(
            sort,
            Sort::Int,
            "permission accessor should still infer Int"
        );
        assert!(
            d.contains_key(&UnsoundnessCategory::SortFallbackToIntFromMethodCall),
            "permission accessor should use LOW-risk SortFallbackToIntFromMethodCall, got delta: {d:?}"
        );
        assert!(
            !d.contains_key(&UnsoundnessCategory::SortFallbackToInt),
            "permission accessor should not use HIGH-risk SortFallbackToInt, got delta: {d:?}"
        );
        unsoundness::reset();
    }
}

/// `discriminant` is provably non-Bool (enum discriminant values are integers).
#[test]
#[timeout(30000)]
fn discriminant_is_definitely_non_bool() {
    use crate::encoder::sort_context::is_definitely_non_bool;

    assert!(
        is_definitely_non_bool(&method_call(var("x"), "discriminant", vec![])),
        "discriminant should be non-bool"
    );
}

/// Element-access methods are NOT `is_definitely_non_bool` because their return
/// sort depends on the element type (e.g., `Vec<bool>.get(i)` returns Bool).
#[test]
#[timeout(30000)]
fn element_access_methods_not_definitely_non_bool() {
    use crate::encoder::sort_context::is_definitely_non_bool;

    for method in &["get", "index_logic", "unwrap", "lookup"] {
        assert!(
            !is_definitely_non_bool(&method_call(var("v"), method, vec![])),
            "`{method}` can return Bool on Bool-element collections, should not be definitely non-bool"
        );
    }
}
