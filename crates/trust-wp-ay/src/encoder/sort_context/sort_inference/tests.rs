// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

use super::*;
use crate::encoder::unsoundness::{self, UnsoundnessCategory};

/// index_logic on Var(_, Ref(Datatype(Vec))) should infer Int sort (element access)
/// and use LOW-risk fallback (not HIGH SortFallbackToInt). (#994)
#[test]
#[timeout(30000)]
fn test_index_logic_ref_datatype_vec_infers_int() {
    let id = intern_sort_name("std::vec::Vec");
    let receiver = PureExpr::Var(
        "v".to_string(),
        Some(ExprSort::Ref(Box::new(ExprSort::Datatype(id)))),
    );
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Var("i".to_string(), Some(ExprSort::Int))],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "index_logic on Ref(Vec) should return Int");
}

/// index_logic on Var(_, Datatype(Vec)) should also infer Int (direct annotation).
#[test]
#[timeout(30000)]
fn test_index_logic_datatype_vec_infers_int() {
    let id = intern_sort_name("std::vec::Vec");
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Var("i".to_string(), Some(ExprSort::Int))],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "index_logic on Vec should return Int");
}

/// __trust_wp_tuple0() must infer unit_sort(), not Sort::Int. (#2325)
///
/// Before the fix, `__trust_wp_tuple0()` fell through to the LogicFnCall
/// catch-all which returns Sort::Int and fires SortFallbackToIntFromLogicFn
/// (a demoting unsoundness category). This caused all proof_asserts in
/// functions containing ghost-block snapshot assignments to be demoted
/// from Verified to Unknown.
#[test]
#[timeout(30000)]
fn test_tuple0_logic_fn_infers_unit_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple0".to_string(),
        args: vec![],
    };
    let sort = infer_expr_sort(&expr);
    let expected = unit_sort();
    assert_eq!(
        sort, expected,
        "__trust_wp_tuple0() must infer unit_sort(), got {sort:?}"
    );
}

/// Non-zero tuple constructors should still infer their Tuple<N> sort.
#[test]
#[timeout(30000)]
fn test_tuple2_logic_fn_infers_tuple2_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple2".to_string(),
        args: vec![
            PureExpr::Var("a".to_string(), Some(ExprSort::Int)),
            PureExpr::Var("b".to_string(), Some(ExprSort::Bool)),
        ],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("Tuple2".to_string()),
        "__trust_wp_tuple2() must infer Tuple2 sort"
    );
}

/// `*tuple_get_0(self).ward()` in the non-atomic invariant protocol should use
/// the low-risk method-call fallback, not the demoting catch-all. (#994)
#[test]
#[timeout(30000)]
fn test_ward_on_structural_field_uses_low_risk_method_fallback() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let expr = PureExpr::Deref(Arc::new(PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        }),
        method: "ward".to_string(),
        args: vec![],
    }));

    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "ward fallback should still infer Int");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "ward fallback must not fire the demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        1,
        "ward fallback should use the low-risk method-call bucket: {delta:?}"
    );
}

/// Structural field accessors lose the original field annotation, but
/// `field.index_logic(0)` still denotes Int-valued sequence indexing in the
/// current encoding. Keep it on the low-risk method-call fallback rather than
/// the generic demoting catch-all. (#994, `11_array_types`)
#[test]
#[timeout(30000)]
fn test_index_logic_on_structural_field_receiver_uses_low_risk_fallback() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(0)],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "index_logic should still infer Int");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "structural field index_logic must not fire the demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        1,
        "structural field index_logic should use the low-risk method bucket: {delta:?}"
    );
}

/// `__trust_wp_fmap_iter_view(iter)` must infer FMap sort, not fall through to
/// the demoting SortFallbackToIntFromLogicFn catch-all. The view projector is
/// used in the transparent FMap produces predicate body. (#2116)
#[test]
#[timeout(30000)]
fn test_fmap_iter_view_projector_infers_fmap_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_fmap_iter_view".to_string(),
        args: vec![PureExpr::Var("iter".to_string(), None)],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        fmap_sort(),
        "__trust_wp_fmap_iter_view should infer FMap sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "__trust_wp_fmap_iter_view must not fire the demoting LogicFn fallback: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "__trust_wp_fmap_iter_view must not fire any demoting fallback: {delta:?}"
    );
}

/// `__trust_wp_iter_mut_view(iter)` must infer Seq sort, not fall through to
/// the demoting SortFallbackToIntFromLogicFn catch-all. The view projector is
/// used in the IterMut produces decomposition axiom to bridge uninterpreted
/// IterMut state to Seq. (#2238)
#[test]
#[timeout(30000)]
fn test_iter_mut_view_projector_infers_seq_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_iter_mut_view".to_string(),
        args: vec![PureExpr::Var("iter".to_string(), None)],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "__trust_wp_iter_mut_view should infer Seq sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "__trust_wp_iter_mut_view must not fire the demoting LogicFn fallback: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "__trust_wp_iter_mut_view must not fire any demoting fallback: {delta:?}"
    );
}

/// `fmap_contains(m, k)` must infer Bool, `fmap_len(m)` and `fmap_lookup(m, k)`
/// must infer Int, all without firing demoting unsoundness counters. (#2116)
#[test]
#[timeout(30000)]
fn test_fmap_accessor_logic_fns_infer_correct_sorts() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let m = PureExpr::Var("m".to_string(), None);
    let k = PureExpr::Var("k".to_string(), Some(ExprSort::Int));

    let contains = PureExpr::LogicFnCall {
        name: "fmap_contains".to_string(),
        args: vec![m.clone(), k.clone()],
    };
    assert_eq!(infer_expr_sort(&contains), Sort::Bool);

    let len = PureExpr::LogicFnCall {
        name: "fmap_len".to_string(),
        args: vec![m.clone()],
    };
    assert_eq!(infer_expr_sort(&len), Sort::Int);

    let lookup = PureExpr::LogicFnCall {
        name: "fmap_lookup".to_string(),
        args: vec![m, k],
    };
    assert_eq!(infer_expr_sort(&lookup), Sort::Int);

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "fmap accessors must not fire demoting LogicFn fallback: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "fmap accessors must not fire demoting SortFallbackToInt: {delta:?}"
    );
}

/// Hashmap/list proof logic methods can appear as bare LogicFnCall nodes during
/// loop sort planning; they must not look like unknown Int fallbacks.
#[test]
#[timeout(30000)]
fn test_hashmap_contract_logic_fns_infer_without_demoting_fallback() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let receiver = PureExpr::Var(
        "m".to_string(),
        Some(ExprSort::Datatype(
            trust_wp_core::formula::intern_sort_name("MyHashMap"),
        )),
    );
    let key = PureExpr::Var("k".to_string(), Some(ExprSort::Int));

    let get = PureExpr::LogicFnCall {
        name: "get".to_string(),
        args: vec![receiver.clone(), key.clone()],
    };
    assert_eq!(
        infer_expr_sort(&get),
        Sort::Uninterpreted("OptionInt".to_string())
    );

    let bucket_ix = PureExpr::LogicFnCall {
        name: "bucket_ix".to_string(),
        args: vec![receiver.clone(), key],
    };
    assert_eq!(infer_expr_sort(&bucket_ix), Sort::Int);

    let no_double_binding = PureExpr::LogicFnCall {
        name: "no_double_binding".to_string(),
        args: vec![receiver.clone()],
    };
    assert_eq!(infer_expr_sort(&no_double_binding), Sort::Bool);

    let good_bucket = PureExpr::LogicFnCall {
        name: "good_bucket".to_string(),
        args: vec![receiver, PureExpr::Int(0)],
    };
    assert_eq!(infer_expr_sort(&good_bucket), Sort::Bool);

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "hashmap contract logic functions must not fire demoting fallback: {delta:?}"
    );
}

/// `final_value(x)` (the ^expr prophecy operator) must infer the same sort as
/// its argument without firing demoting counters. (#2116)
#[test]
#[timeout(30000)]
fn test_final_value_infers_arg_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let int_final = PureExpr::LogicFnCall {
        name: "final_value".to_string(),
        args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
    };
    assert_eq!(infer_expr_sort(&int_final), Sort::Int);

    let bool_final = PureExpr::LogicFnCall {
        name: "final_value".to_string(),
        args: vec![PureExpr::Var("b".to_string(), Some(ExprSort::Bool))],
    };
    assert_eq!(infer_expr_sort(&bool_final), Sort::Bool);

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "final_value must not fire demoting LogicFn fallback: {delta:?}"
    );
}

/// `option_var.unwrap()` with an Option-annotated receiver must use the
/// LOW-risk method-call fallback, not the demoting catch-all. (#2207)
#[test]
#[timeout(30000)]
fn test_unwrap_on_option_receiver_uses_low_risk_fallback() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "unwrap".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "unwrap on Option should return Int");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "unwrap on Option must not fire the demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        1,
        "unwrap on Option should use the low-risk method bucket: {delta:?}"
    );
}

/// `result_var.unwrap()` with a Result-annotated receiver must use the
/// LOW-risk method-call fallback. (#2207)
#[test]
#[timeout(30000)]
fn test_unwrap_on_result_receiver_uses_low_risk_fallback() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "unwrap".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "unwrap on Result should return Int");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "unwrap on Result must not fire the demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        1,
        "unwrap on Result should use the low-risk method bucket: {delta:?}"
    );
}

/// `result_var.unwrap_err()` with a Result-annotated receiver must use the
/// LOW-risk method-call fallback. (#2207)
#[test]
#[timeout(30000)]
fn test_unwrap_err_on_result_receiver_uses_low_risk_fallback() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "unwrap_err".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "unwrap_err on Result should return Int");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "unwrap_err on Result must not fire the demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        1,
        "unwrap_err on Result should use the low-risk method bucket: {delta:?}"
    );
}

/// `seq_var.get(i)` with a Seq-annotated receiver must infer OptionInt
/// Datatype sort, not Int. Seq::get() returns Option<T>. (#2207)
#[test]
#[timeout(30000)]
fn test_get_on_seq_receiver_infers_option_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let receiver = PureExpr::Var("s".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "get".to_string(),
        args: vec![PureExpr::Var("i".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "get on Seq should return OptionInt sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "get on Seq must not fire any demoting fallback: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        0,
        "get on Seq returning OptionInt should not fire any fallback: {delta:?}"
    );
}

/// `vec_var.get(i)` with a Vec (Datatype) annotation should also infer OptionInt,
/// since Vec is a Seq-model type. (#2207)
#[test]
#[timeout(30000)]
fn test_get_on_vec_receiver_infers_option_sort() {
    let id = intern_sort_name("std::vec::Vec");
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "get".to_string(),
        args: vec![PureExpr::Var("i".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "get on Vec should return OptionInt sort, got {sort:?}"
    );
}

/// `unwrap` on an unannotated receiver (no Option/Result evidence) now uses
/// the LOW-risk method-call fallback instead of the HIGH-risk catch-all.
/// The method name `unwrap` is known, and Int is correct for the dominant
/// case. Reclassified per #2231.
#[test]
#[timeout(30000)]
fn test_unwrap_on_unannotated_receiver_uses_low_risk() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let receiver = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "unwrap".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "unwrap on unannotated should still return Int"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "unwrap on unannotated receiver must not fire HIGH-risk catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        1,
        "unwrap on unannotated receiver should use LOW-risk method bucket: {delta:?}"
    );
}

/// `Deref(Option_var).unwrap()` should also route through the LOW-risk path
/// since receiver annotation peels through Deref wrappers. (#2207)
#[test]
#[timeout(30000)]
fn test_unwrap_on_deref_option_receiver_uses_low_risk() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("Option");
    let inner = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let receiver = PureExpr::Deref(Arc::new(inner));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "unwrap".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "unwrap on Deref(Option) should return Int");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "unwrap on Deref(Option) must not fire the demoting catch-all: {delta:?}"
    );
}

/// `FMap::empty()` must infer FMap sort, not fall through to the Int catch-all.
/// Without this, FMap::empty() used in FMap operations (insert, contains)
/// causes sort mismatches: the receiver has FMap sort but the empty constant
/// infers as Int. (#2207)
#[test]
#[timeout(30000)]
fn test_fmap_empty_method_infers_fmap_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("FMap".to_string(), None)),
        method: "empty".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        fmap_sort(),
        "FMap::empty() must infer FMap sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "FMap::empty() must not fire any demoting fallback: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        0,
        "FMap::empty() must not fire method-call fallback: {delta:?}"
    );
}

/// `contains_key` is a Bool-returning method (HashMap synonym for `contains`).
/// It must infer Sort::Bool without firing any demoting fallback. (#2207)
#[test]
#[timeout(30000)]
fn test_contains_key_infers_bool() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("HashMap");
    let receiver = PureExpr::Var("m".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "contains_key".to_string(),
        args: vec![PureExpr::Var("k".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "contains_key must infer Bool sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "contains_key must not fire any demoting fallback: {delta:?}"
    );
}

/// `FMap::empty()` is not Bool (it's FMap sort). Verify `is_definitely_non_bool`
/// correctly identifies it. (#2207)
#[test]
#[timeout(30000)]
fn test_fmap_empty_is_definitely_non_bool() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("FMap".to_string(), None)),
        method: "empty".to_string(),
        args: vec![],
    };
    assert!(
        is_definitely_non_bool(&expr),
        "FMap::empty() must be non-Bool"
    );
}

/// `fmap.insert(k, v)` on an FMap-annotated receiver must infer FMap sort.
/// Verified existing rule from #994 Phase 2c. (#2207)
#[test]
#[timeout(30000)]
fn test_fmap_insert_on_annotated_receiver_infers_fmap_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("FMap");
    let receiver = PureExpr::Var("m".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "insert".to_string(),
        args: vec![
            PureExpr::Var("k".to_string(), Some(ExprSort::Int)),
            PureExpr::Var("v".to_string(), Some(ExprSort::Int)),
        ],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        fmap_sort(),
        "FMap::insert on FMap receiver must infer FMap sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "FMap::insert must not fire demoting fallback: {delta:?}"
    );
}

/// `fmap.merge(other, resolver)` on an FMap-annotated receiver must infer
/// FMap sort. Verified existing rule from #994 Phase 2c. (#2207)
#[test]
#[timeout(30000)]
fn test_fmap_merge_on_annotated_receiver_infers_fmap_sort() {
    let id = intern_sort_name("FMap");
    let receiver = PureExpr::Var("m".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "merge".to_string(),
        args: vec![
            PureExpr::Var("other".to_string(), Some(ExprSort::FMap)),
            PureExpr::Var("resolver".to_string(), None),
        ],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        fmap_sort(),
        "FMap::merge on FMap receiver must infer FMap sort, got {sort:?}"
    );
}

/// `fmap.into_seq()` on an FMap-annotated receiver must infer Seq sort.
#[test]
#[timeout(30000)]
fn test_fmap_into_seq_on_annotated_receiver_infers_seq_sort() {
    let id = intern_sort_name("FMap");
    let receiver = PureExpr::Var("m".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "into_seq".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "FMap::into_seq on FMap receiver must infer Seq sort, got {sort:?}"
    );
}

// === View expression sort inference tests (#1096) ===

/// `vec@` where vec has a Vec (Datatype) annotation must infer Seq sort.
/// Vec<T>::view() returns Seq<T>, so View on a collection receiver should
/// produce Seq sort instead of falling through to identity inference. (#1096)
#[test]
#[timeout(30000)]
fn test_view_on_vec_receiver_infers_seq_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("std::vec::Vec");
    let inner = PureExpr::Var("v".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::View(Arc::new(inner));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "View on Vec should return Seq sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "View on Vec must not fire any demoting fallback: {delta:?}"
    );
}

/// `seq@` where seq has Seq annotation must infer Seq sort. (#1096)
#[test]
#[timeout(30000)]
fn test_view_on_seq_receiver_infers_seq_sort() {
    let inner = PureExpr::Var("s".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::View(Arc::new(inner));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "View on Seq should return Seq sort, got {sort:?}"
    );
}

/// `x@` where x is a scalar (Int-annotated) should still return Int.
/// View is identity for scalars — only collection types get Seq. (#1096)
#[test]
#[timeout(30000)]
fn test_view_on_scalar_receiver_preserves_int_sort() {
    let inner = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::View(Arc::new(inner));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "View on scalar Int should return Int sort, got {sort:?}"
    );
}

/// `b@` where b is Bool-annotated should return Bool.
/// View on Bool is identity. (#1096)
#[test]
#[timeout(30000)]
fn test_view_on_bool_receiver_preserves_bool_sort() {
    let inner = PureExpr::Var("b".to_string(), Some(ExprSort::Bool));
    let expr = PureExpr::View(Arc::new(inner));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "View on Bool should return Bool sort, got {sort:?}"
    );
}

/// `deque@` where deque has a VecDeque Datatype annotation must infer
/// Seq sort, since VecDeque is a Seq-model type. (#1096)
#[test]
#[timeout(30000)]
fn test_view_on_vecdeque_receiver_infers_seq_sort() {
    let id = intern_sort_name("std::collections::VecDeque");
    let inner = PureExpr::Var("d".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::View(Arc::new(inner));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "View on VecDeque should return Seq sort, got {sort:?}"
    );
}

/// `old(opt)@` where `opt` has a non-collection Datatype annotation should
/// preserve the ADT sort through the view wrapper. (#2699)
#[test]
#[timeout(30000)]
fn test_view_on_wrapped_option_receiver_preserves_datatype_sort() {
    let id = intern_sort_name("Option");
    let inner = PureExpr::Old(Arc::new(PureExpr::Var(
        "opt".to_string(),
        Some(ExprSort::Datatype(id)),
    )));
    let expr = PureExpr::View(Arc::new(inner));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("Option".to_string()),
        "View on wrapped Option receiver should preserve Option sort, got {sort:?}"
    );
}

// === UnaryOp sort inference tests (#1096) ===

/// `!true` (Not on Bool literal) must infer Bool sort. (#1096)
#[test]
#[timeout(30000)]
fn test_unop_not_on_bool_infers_bool() {
    let expr = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::Bool(true)),
    );

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "Not on Bool should return Bool, got {sort:?}"
    );
}

/// `!x` where x is Int-annotated must infer Int sort (bitwise NOT). (#1096)
#[test]
#[timeout(30000)]
fn test_unop_not_on_int_infers_int() {
    let operand = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, Arc::new(operand));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "Not on Int should return Int (bitwise NOT), got {sort:?}"
    );
}

/// `-x` where x is Int-annotated must infer Int sort (arithmetic negation). (#1096)
#[test]
#[timeout(30000)]
fn test_unop_neg_on_int_infers_int() {
    let operand = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Neg, Arc::new(operand));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "Neg on Int should return Int, got {sort:?}"
    );
}

/// `-b` where b is Bool-annotated must propagate Bool sort. (#1096)
#[test]
#[timeout(30000)]
fn test_unop_neg_on_bool_infers_bool() {
    let operand = PureExpr::Var("b".to_string(), Some(ExprSort::Bool));
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Neg, Arc::new(operand));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "Neg on Bool should propagate Bool, got {sort:?}"
    );
}

/// `!(x > 0)` (Not on a comparison) must infer Bool. (#1096)
#[test]
#[timeout(30000)]
fn test_unop_not_on_comparison_infers_bool() {
    let cmp = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, Arc::new(cmp));

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "Not on (x > 0) should return Bool, got {sort:?}"
    );
}

// === MethodCall sort inference verification tests (#1096) ===

/// `v.len()` must infer Int sort for any receiver. (#1096)
#[test]
#[timeout(30000)]
fn test_method_len_infers_int() {
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "len".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "len() must return Int sort, got {sort:?}");
}

/// `v.is_empty()` must infer Bool sort. (#1096)
#[test]
#[timeout(30000)]
fn test_method_is_empty_infers_bool() {
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "is_empty".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "is_empty() must return Bool sort, got {sort:?}"
    );
}

/// `v.contains(x)` must infer Bool sort. (#1096)
#[test]
#[timeout(30000)]
fn test_method_contains_infers_bool() {
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "contains".to_string(),
        args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "contains() must return Bool sort, got {sort:?}"
    );
}

/// `opt.is_some()` must infer Bool sort. (#1096)
#[test]
#[timeout(30000)]
fn test_method_is_some_infers_bool() {
    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "is_some".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "is_some() must return Bool sort, got {sort:?}"
    );
}

/// `res.is_ok()` must infer Bool sort. (#1096)
#[test]
#[timeout(30000)]
fn test_method_is_ok_infers_bool() {
    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "is_ok".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "is_ok() must return Bool sort, got {sort:?}"
    );
}

/// `a.ext_eq(b)` must infer Bool sort. (#1096)
#[test]
#[timeout(30000)]
fn test_method_ext_eq_infers_bool() {
    let receiver = PureExpr::Var("a".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "ext_eq".to_string(),
        args: vec![PureExpr::Var("b".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "ext_eq() must return Bool sort, got {sort:?}"
    );
}

// === Result constructor sort inference tests (#2207) ===

/// `Ok(x)` as a LogicFnCall must infer ResultIntInt Datatype sort, not Int.
/// Before the fix, Ok/Err constructors fell through to the LogicFnCall
/// catch-all which returns Sort::Int and fires SortFallbackToIntFromLogicFn.
/// This caused sort mismatches when Ok(x) expressions were used in Result
/// match contexts (is_ok tester expects Datatype, not Int). (#2207)
#[test]
#[timeout(30000)]
fn test_ok_logic_fn_infers_result_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let expr = PureExpr::LogicFnCall {
        name: "Ok".to_string(),
        args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "Ok(x) must infer ResultIntInt sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "Ok(x) must not fire demoting LogicFn fallback: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "Ok(x) must not fire any demoting fallback: {delta:?}"
    );
}

/// `Err(e)` as a LogicFnCall must infer ResultIntInt Datatype sort. (#2207)
#[test]
#[timeout(30000)]
fn test_err_logic_fn_infers_result_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let expr = PureExpr::LogicFnCall {
        name: "Err".to_string(),
        args: vec![PureExpr::Var("e".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "Err(e) must infer ResultIntInt sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "Err(e) must not fire demoting LogicFn fallback: {delta:?}"
    );
}

/// Qualified `Result::Ok(x)` must also infer ResultIntInt sort. (#2207)
#[test]
#[timeout(30000)]
fn test_qualified_result_ok_logic_fn_infers_result_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "Result::Ok".to_string(),
        args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "Result::Ok(x) must infer ResultIntInt sort, got {sort:?}"
    );
}

/// Qualified `Result::Err(e)` must also infer ResultIntInt sort. (#2207)
#[test]
#[timeout(30000)]
fn test_qualified_result_err_logic_fn_infers_result_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "Result::Err".to_string(),
        args: vec![PureExpr::Var("e".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "Result::Err(e) must infer ResultIntInt sort, got {sort:?}"
    );
}

/// `Ok(x)` and `Err(e)` are definitely not Bool (they produce Datatype sort).
/// This ensures `!Ok(x)` is correctly identified as bitwise NOT (not logical NOT). (#2207)
#[test]
#[timeout(30000)]
fn test_result_constructors_are_definitely_non_bool() {
    let ok_expr = PureExpr::LogicFnCall {
        name: "Ok".to_string(),
        args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
    };
    assert!(is_definitely_non_bool(&ok_expr), "Ok(x) must be non-Bool");

    let err_expr = PureExpr::LogicFnCall {
        name: "Err".to_string(),
        args: vec![PureExpr::Var("e".to_string(), Some(ExprSort::Int))],
    };
    assert!(is_definitely_non_bool(&err_expr), "Err(e) must be non-Bool");

    let some_expr = PureExpr::LogicFnCall {
        name: "Some".to_string(),
        args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
    };
    assert!(
        is_definitely_non_bool(&some_expr),
        "Some(x) must be non-Bool"
    );

    let none_expr = PureExpr::LogicFnCall {
        name: "None".to_string(),
        args: vec![],
    };
    assert!(is_definitely_non_bool(&none_expr), "None must be non-Bool");
}

// === Generic MethodCall fallback tests (#1096) ===

/// An unrecognized method on an Int-annotated receiver must propagate the
/// receiver's sort (Int) and use the LOW-risk `SortFallbackToIntFromMethodCall`
/// instead of the demoting HIGH-risk `SortFallbackToInt` catch-all.
/// This covers methods like `clone()` on typed receivers that don't match
/// any specific MethodCall pattern. (#1096)
///
/// Note: Datatype-annotated receivers are caught by the earlier Datatype
/// receiver-propagation arm (line 252) and don't reach the new generic arm.
/// We use Int annotation here to test the generic fallback path.
#[test]
#[timeout(30000)]
fn test_unrecognized_method_on_annotated_receiver_propagates_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "some_unknown_method".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "unrecognized method on Int receiver should propagate Int, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "unrecognized method on annotated receiver must not fire HIGH-risk catch-all: {delta:?}"
    );
    assert!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0)
            >= 1,
        "unrecognized method on annotated receiver should use LOW-risk method bucket: {delta:?}"
    );
}

/// An unrecognized method on an unannotated receiver must use the LOW-risk
/// `SortFallbackToIntFromMethodCall` (not the HIGH-risk `SortFallbackToInt`).
/// Previously, all unrecognized methods fell through to the demoting catch-all
/// regardless of context. (#1096)
#[test]
#[timeout(30000)]
fn test_unrecognized_method_on_unannotated_receiver_uses_low_risk() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let receiver = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "some_unknown_method".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "unrecognized method on unannotated receiver should return Int"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "unrecognized method must not fire HIGH-risk catch-all: {delta:?}"
    );
    assert!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0)
            >= 1,
        "unrecognized method should use LOW-risk method bucket: {delta:?}"
    );
}

/// An unrecognized method on a Bool-annotated receiver should propagate
/// Bool sort, not default to Int. (#1096)
#[test]
#[timeout(30000)]
fn test_unrecognized_method_on_bool_receiver_propagates_bool() {
    let receiver = PureExpr::Var("b".to_string(), Some(ExprSort::Bool));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "some_bool_method".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "unrecognized method on Bool receiver should propagate Bool, got {sort:?}"
    );
}

// === Additional Bool-returning method tests (#2663) ===

/// `v.all(...)` must infer Bool sort (iterator predicate). (#2663)
#[test]
#[timeout(30000)]
fn test_method_all_infers_bool() {
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "all".to_string(),
        args: vec![PureExpr::Var("pred".to_string(), None)],
    };
    assert_eq!(infer_expr_sort(&expr), Sort::Bool, "all() must return Bool");
}

/// `v.any(...)` must infer Bool sort (iterator predicate). (#2663)
#[test]
#[timeout(30000)]
fn test_method_any_infers_bool() {
    let receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "any".to_string(),
        args: vec![PureExpr::Var("pred".to_string(), None)],
    };
    assert_eq!(infer_expr_sort(&expr), Sort::Bool, "any() must return Bool");
}

/// `v.starts_with(...)` must infer Bool sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_starts_with_infers_bool() {
    let receiver = PureExpr::Var("s".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "starts_with".to_string(),
        args: vec![PureExpr::Var("prefix".to_string(), None)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "starts_with() must return Bool"
    );
}

/// `v.ends_with(...)` must infer Bool sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_ends_with_infers_bool() {
    let receiver = PureExpr::Var("s".to_string(), Some(ExprSort::Seq));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "ends_with".to_string(),
        args: vec![PureExpr::Var("suffix".to_string(), None)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "ends_with() must return Bool"
    );
}

/// `ix.in_bounds(seq)` must infer Bool sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_in_bounds_infers_bool() {
    let receiver = PureExpr::Var("ix".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "in_bounds".to_string(),
        args: vec![PureExpr::Var("seq".to_string(), Some(ExprSort::Seq))],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "in_bounds() must return Bool"
    );
}

// === Int-returning arithmetic method tests (#2663) ===

/// `x.abs()` must infer Int sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_abs_infers_int() {
    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "abs".to_string(),
        args: vec![],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "abs() must return Int, got {sort:?}");
}

/// `x.min(y)` must infer Int sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_min_infers_int() {
    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "min".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "min() must return Int, got {sort:?}");
}

/// `x.max(y)` must infer Int sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_max_infers_int() {
    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "max".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "max() must return Int, got {sort:?}");
}

/// `x.saturating_add(y)` must infer Int sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_saturating_add_infers_int() {
    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "saturating_add".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "saturating_add() must return Int, got {sort:?}"
    );
}

/// `opt.unwrap_or(default)` must infer Int sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_unwrap_or_infers_int() {
    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "unwrap_or".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    unsoundness::reset();
    let before = unsoundness::snapshot();
    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "unwrap_or() must return Int, got {sort:?}");
    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "unwrap_or must not fire HIGH-risk catch-all: {delta:?}"
    );
}

/// `opt.unwrap_or_default()` must infer Int sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_unwrap_or_default_infers_int() {
    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "unwrap_or_default".to_string(),
        args: vec![],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "unwrap_or_default() must return Int, got {sort:?}"
    );
}

// === Option-returning method tests (#2663) ===

/// `opt.map(f)` on Option receiver must infer OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_map_on_option_infers_option_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "map".to_string(),
        args: vec![PureExpr::Var("f".to_string(), None)],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "map on Option must return OptionInt, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "map on Option must not fire demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        0,
        "map on Option must not fire method-call fallback: {delta:?}"
    );
}

/// `opt.and_then(f)` on Option receiver must infer OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_and_then_on_option_infers_option_sort() {
    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "and_then".to_string(),
        args: vec![PureExpr::Var("f".to_string(), None)],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "and_then on Option must return OptionInt, got {sort:?}"
    );
}

/// `opt.filter(pred)` on Option receiver must infer OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_filter_on_option_infers_option_sort() {
    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "filter".to_string(),
        args: vec![PureExpr::Var("pred".to_string(), None)],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "filter on Option must return OptionInt, got {sort:?}"
    );
}

/// `opt.or_else(f)` on Option receiver must infer OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_or_else_on_option_infers_option_sort() {
    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "or_else".to_string(),
        args: vec![PureExpr::Var("f".to_string(), None)],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "or_else on Option must return OptionInt, got {sort:?}"
    );
}

// === Result-returning method tests (#2663) ===

/// `res.map(f)` on Result receiver must infer ResultIntInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_map_on_result_infers_result_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "map".to_string(),
        args: vec![PureExpr::Var("f".to_string(), None)],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "map on Result must return ResultIntInt, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "map on Result must not fire demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        0,
        "map on Result must not fire method-call fallback: {delta:?}"
    );
}

/// `res.map_err(f)` on Result receiver must infer ResultIntInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_map_err_on_result_infers_result_sort() {
    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "map_err".to_string(),
        args: vec![PureExpr::Var("f".to_string(), None)],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "map_err on Result must return ResultIntInt, got {sort:?}"
    );
}

/// `res.and_then(f)` on Result receiver must infer ResultIntInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_and_then_on_result_infers_result_sort() {
    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "and_then".to_string(),
        args: vec![PureExpr::Var("f".to_string(), None)],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "and_then on Result must return ResultIntInt, got {sort:?}"
    );
}

// === Cross-type conversion method tests (#2663) ===

/// `opt.ok_or(err)` on Option must infer ResultIntInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_ok_or_on_option_infers_result_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "ok_or".to_string(),
        args: vec![PureExpr::Var("err".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "ok_or on Option must return ResultIntInt, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "ok_or on Option must not fire demoting catch-all: {delta:?}"
    );
}

/// `opt.ok_or_else(f)` on Option must infer ResultIntInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_ok_or_else_on_option_infers_result_sort() {
    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "ok_or_else".to_string(),
        args: vec![PureExpr::Var("f".to_string(), None)],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "ok_or_else on Option must return ResultIntInt, got {sort:?}"
    );
}

/// `res.ok()` on Result must infer OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_ok_on_result_infers_option_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "ok".to_string(),
        args: vec![],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "ok() on Result must return OptionInt, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "ok() on Result must not fire demoting catch-all: {delta:?}"
    );
}

/// `res.err()` on Result must infer OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_err_on_result_infers_option_sort() {
    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "err".to_string(),
        args: vec![],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "err() on Result must return OptionInt, got {sort:?}"
    );
}

// === checked_* method tests (#2663) ===

/// `x.checked_add(y)` must infer OptionInt sort (returns Option<T>). (#2663)
#[test]
#[timeout(30000)]
fn test_method_checked_add_infers_option_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "checked_add".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "checked_add must return OptionInt, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "checked_add must not fire demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        0,
        "checked_add must not fire method-call fallback: {delta:?}"
    );
}

/// `x.checked_div(y)` must infer OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_checked_div_infers_option_sort() {
    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "checked_div".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "checked_div must return OptionInt, got {sort:?}"
    );
}

/// `x.checked_mul(y)` must infer OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_checked_mul_infers_option_sort() {
    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "checked_mul".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "checked_mul must return OptionInt, got {sort:?}"
    );
}

// === overflowing_* method tests (#2663) ===

/// `x.overflowing_add(y)` must infer Tuple2 sort (returns (T, bool)). (#2663)
#[test]
#[timeout(30000)]
fn test_method_overflowing_add_infers_tuple2_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let receiver = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "overflowing_add".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("Tuple2".to_string()),
        "overflowing_add must return Tuple2, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToInt)
            .copied()
            .unwrap_or(0),
        0,
        "overflowing_add must not fire demoting catch-all: {delta:?}"
    );
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromMethodCall)
            .copied()
            .unwrap_or(0),
        0,
        "overflowing_add must not fire method-call fallback: {delta:?}"
    );
}

// === Mapping logic function sort inference tests (#2663) ===

/// `mapping_cst(v)` must infer Mapping sort. (#2663)
#[test]
#[timeout(30000)]
fn test_mapping_cst_logic_fn_infers_mapping_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let expr = PureExpr::LogicFnCall {
        name: "mapping_cst".to_string(),
        args: vec![PureExpr::Var("v".to_string(), Some(ExprSort::Int))],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        mapping_sort(),
        "mapping_cst must infer Mapping sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "mapping_cst must not fire demoting LogicFn fallback: {delta:?}"
    );
}

/// `mapping_set(m, k, v)` must infer Mapping sort. (#2663)
#[test]
#[timeout(30000)]
fn test_mapping_set_logic_fn_infers_mapping_sort() {
    let m = PureExpr::Var("m".to_string(), None);
    let k = PureExpr::Var("k".to_string(), Some(ExprSort::Int));
    let v = PureExpr::Var("v".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::LogicFnCall {
        name: "mapping_set".to_string(),
        args: vec![m, k, v],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        mapping_sort(),
        "mapping_set must infer Mapping sort, got {sort:?}"
    );
}

/// `mapping_get(m, k)` must infer Int sort. (#2663)
#[test]
#[timeout(30000)]
fn test_mapping_get_logic_fn_infers_int_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let m = PureExpr::Var("m".to_string(), None);
    let k = PureExpr::Var("k".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::LogicFnCall {
        name: "mapping_get".to_string(),
        args: vec![m, k],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Int,
        "mapping_get must infer Int sort, got {sort:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "mapping_get must not fire demoting LogicFn fallback: {delta:?}"
    );
}

/// `mapping_contains(m, k)` must infer Bool sort. (#2663)
#[test]
#[timeout(30000)]
fn test_mapping_contains_logic_fn_infers_bool_sort() {
    let m = PureExpr::Var("m".to_string(), None);
    let k = PureExpr::Var("k".to_string(), Some(ExprSort::Int));
    let expr = PureExpr::LogicFnCall {
        name: "mapping_contains".to_string(),
        args: vec![m, k],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Bool,
        "mapping_contains must infer Bool sort, got {sort:?}"
    );
}

/// `Mapping::cst(v)` must infer Mapping sort (qualified name). (#2663)
#[test]
#[timeout(30000)]
fn test_mapping_cst_qualified_logic_fn_infers_mapping_sort() {
    let expr = PureExpr::LogicFnCall {
        name: "Mapping::cst".to_string(),
        args: vec![PureExpr::Int(0)],
    };

    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        mapping_sort(),
        "Mapping::cst must infer Mapping sort, got {sort:?}"
    );
}

// === is_definitely_non_bool tests for new patterns (#2663) ===

/// `x.abs()` is definitely non-Bool (Int). (#2663)
#[test]
#[timeout(30000)]
fn test_abs_is_definitely_non_bool() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        method: "abs".to_string(),
        args: vec![],
    };
    assert!(is_definitely_non_bool(&expr), "abs() must be non-Bool");
}

/// `x.checked_add(y)` is definitely non-Bool (returns OptionInt). (#2663)
#[test]
#[timeout(30000)]
fn test_checked_add_is_definitely_non_bool() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        method: "checked_add".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };
    assert!(
        is_definitely_non_bool(&expr),
        "checked_add() must be non-Bool"
    );
}

/// `x.overflowing_add(y)` is definitely non-Bool (returns Tuple2). (#2663)
#[test]
#[timeout(30000)]
fn test_overflowing_add_is_definitely_non_bool() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        method: "overflowing_add".to_string(),
        args: vec![PureExpr::Var("y".to_string(), Some(ExprSort::Int))],
    };
    assert!(
        is_definitely_non_bool(&expr),
        "overflowing_add() must be non-Bool"
    );
}

/// `mapping_cst(v)` is definitely non-Bool (returns Mapping). (#2663)
#[test]
#[timeout(30000)]
fn test_mapping_cst_is_definitely_non_bool() {
    let expr = PureExpr::LogicFnCall {
        name: "mapping_cst".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    assert!(
        is_definitely_non_bool(&expr),
        "mapping_cst must be non-Bool"
    );
}

/// `mapping_get(m, k)` is definitely non-Bool (returns Int). (#2663)
#[test]
#[timeout(30000)]
fn test_mapping_get_is_definitely_non_bool() {
    let expr = PureExpr::LogicFnCall {
        name: "mapping_get".to_string(),
        args: vec![
            PureExpr::Var("m".to_string(), None),
            PureExpr::Var("k".to_string(), Some(ExprSort::Int)),
        ],
    };
    assert!(
        is_definitely_non_bool(&expr),
        "mapping_get must be non-Bool"
    );
}

/// `opt.transpose()` on Option receiver infers ResultIntInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_transpose_on_option_infers_result_sort() {
    let id = intern_sort_name("Option");
    let receiver = PureExpr::Var("opt".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "transpose".to_string(),
        args: vec![],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "transpose on Option must return ResultIntInt, got {sort:?}"
    );
}

/// `res.transpose()` on Result receiver infers OptionInt sort. (#2663)
#[test]
#[timeout(30000)]
fn test_method_transpose_on_result_infers_option_sort() {
    let id = intern_sort_name("Result");
    let receiver = PureExpr::Var("res".to_string(), Some(ExprSort::Datatype(id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "transpose".to_string(),
        args: vec![],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "transpose on Result must return OptionInt, got {sort:?}"
    );
}

// --- Ite same-family sort resolution (#2675) ---

/// Ite with OptionInt (then) and Option (else) should resolve to OptionInt.
/// This handles the try operator `Ite(is_some(x), Some(unwrap(x)), x)` where
/// the success branch infers OptionInt and the failure branch infers Option.
#[test]
#[timeout(30000)]
fn test_ite_option_int_vs_option_prefers_option_int() {
    // then branch: a LogicFnCall that returns OptionInt
    let id = intern_sort_name("Option");
    let then_expr = PureExpr::LogicFnCall {
        name: "Some".to_string(),
        args: vec![PureExpr::Var("v".to_string(), Some(ExprSort::Int))],
    };
    // else branch: a Var annotated as Option (generic)
    let else_expr = PureExpr::Var("x".to_string(), Some(ExprSort::Datatype(id)));
    let cond = PureExpr::Var("c".to_string(), Some(ExprSort::Bool));
    let ite = PureExpr::Ite(Arc::new(cond), Arc::new(then_expr), Arc::new(else_expr));
    let sort = infer_expr_sort(&ite);
    assert_eq!(
        sort,
        Sort::Uninterpreted("OptionInt".to_string()),
        "Ite with OptionInt/Option branches should resolve to OptionInt, got {sort:?}"
    );
}

/// Ite with ResultIntInt (then) and Result (else) should resolve to ResultIntInt.
#[test]
#[timeout(30000)]
fn test_ite_result_int_int_vs_result_prefers_result_int_int() {
    let id = intern_sort_name("Result");
    let then_expr = PureExpr::LogicFnCall {
        name: "Ok".to_string(),
        args: vec![PureExpr::Var("v".to_string(), Some(ExprSort::Int))],
    };
    let else_expr = PureExpr::Var("x".to_string(), Some(ExprSort::Datatype(id)));
    let cond = PureExpr::Var("c".to_string(), Some(ExprSort::Bool));
    let ite = PureExpr::Ite(Arc::new(cond), Arc::new(then_expr), Arc::new(else_expr));
    let sort = infer_expr_sort(&ite);
    assert_eq!(
        sort,
        Sort::Uninterpreted("ResultIntInt".to_string()),
        "Ite with ResultIntInt/Result branches should resolve to ResultIntInt, got {sort:?}"
    );
}

/// resolve_same_family_sorts returns None for unrelated sorts.
#[test]
#[timeout(30000)]
fn test_resolve_same_family_sorts_unrelated_returns_none() {
    let a = Sort::Uninterpreted("OptionInt".to_string());
    let b = Sort::Uninterpreted("ResultIntInt".to_string());
    assert!(
        super::resolve_same_family_sorts(&a, &b).is_none(),
        "OptionInt and ResultIntInt are in different families"
    );
}

/// resolve_same_family_sorts returns None when one is Int.
#[test]
#[timeout(30000)]
fn test_resolve_same_family_sorts_int_returns_none() {
    let a = Sort::Int;
    let b = Sort::Uninterpreted("OptionInt".to_string());
    assert!(
        super::resolve_same_family_sorts(&a, &b).is_none(),
        "Int is not an Uninterpreted sort"
    );
}

/// resolve_same_family_sorts should prefer a concrete sort over a TypeParam
/// placeholder when only one side is `__trust_wp_typaram::*`. (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_sorts_typeparam_vs_concrete_prefers_concrete() {
    use ay_dpll::api::DatatypeSort;

    let typaram = Sort::Uninterpreted("__trust_wp_typaram::T".to_string());
    let dt = Sort::Datatype(DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![],
    });

    assert_eq!(
        super::resolve_same_family_sorts(&typaram, &dt),
        Some(dt.clone()),
        "TypeParam should yield to the concrete datatype sort"
    );
    assert_eq!(
        super::resolve_same_family_sorts(&dt, &typaram),
        Some(dt),
        "Concrete datatype sort should win over TypeParam in reversed order"
    );
}

/// resolve_same_family_sorts returns the more specific sort.
#[test]
#[timeout(30000)]
fn test_resolve_same_family_sorts_option_family() {
    let opt = Sort::Uninterpreted("Option".to_string());
    let opt_int = Sort::Uninterpreted("OptionInt".to_string());
    assert_eq!(
        super::resolve_same_family_sorts(&opt, &opt_int),
        Some(opt_int.clone()),
        "Should prefer OptionInt over Option"
    );
    assert_eq!(
        super::resolve_same_family_sorts(&opt_int, &opt),
        Some(opt_int),
        "Should prefer OptionInt over Option (reversed order)"
    );
}

// --- Cross-sort-type family resolution tests (#2699) ---

/// resolve_same_family_sorts handles Datatype vs Uninterpreted in the same
/// Option family. Datatype should be preferred because it carries constructor
/// information that the solver needs for match encoding. (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_datatype_vs_uninterpreted_option() {
    use ay_dpll::api::DatatypeSort;
    let dt = Sort::Datatype(DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![],
    });
    let uninterp = Sort::Uninterpreted("Option".to_string());
    assert_eq!(
        super::resolve_same_family_sorts(&dt, &uninterp),
        Some(dt.clone()),
        "Datatype(OptionInt) should be preferred over Uninterpreted(Option)"
    );
    assert_eq!(
        super::resolve_same_family_sorts(&uninterp, &dt),
        Some(dt),
        "Datatype(OptionInt) should be preferred over Uninterpreted(Option) (reversed)"
    );
}

/// resolve_same_family_sorts handles Seq vs Uninterpreted("Vec").
/// The native Seq sort should be preferred as the canonical encoding. (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_seq_vs_uninterpreted_vec() {
    let seq = Sort::seq(Sort::Int);
    let vec_uninterp = Sort::Uninterpreted("Vec".to_string());
    assert_eq!(
        super::resolve_same_family_sorts(&seq, &vec_uninterp),
        Some(seq.clone()),
        "Seq(Int) should be preferred over Uninterpreted(Vec)"
    );
    assert_eq!(
        super::resolve_same_family_sorts(&vec_uninterp, &seq),
        Some(seq),
        "Seq(Int) should be preferred over Uninterpreted(Vec) (reversed)"
    );
}

/// resolve_same_family_sorts handles Seq vs Uninterpreted("LinkedList").
/// Both are in the Seq family. (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_seq_vs_uninterpreted_linkedlist() {
    let seq = Sort::seq(Sort::Int);
    let ll = Sort::Uninterpreted("LinkedList".to_string());
    assert_eq!(
        super::resolve_same_family_sorts(&seq, &ll),
        Some(seq.clone()),
        "Seq(Int) should be preferred over Uninterpreted(LinkedList)"
    );
}

/// resolve_same_family_sorts handles two Datatype sorts in the same family.
/// (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_two_datatypes_option() {
    use ay_dpll::api::DatatypeSort;
    let dt_opt = Sort::Datatype(DatatypeSort {
        name: "Option".to_string(),
        constructors: vec![],
    });
    let dt_opt_int = Sort::Datatype(DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![],
    });
    assert_eq!(
        super::resolve_same_family_sorts(&dt_opt, &dt_opt_int),
        Some(dt_opt_int.clone()),
        "Datatype(OptionInt) should be preferred over Datatype(Option) (more specific)"
    );
    assert_eq!(
        super::resolve_same_family_sorts(&dt_opt_int, &dt_opt),
        Some(dt_opt_int),
        "Datatype(OptionInt) should be preferred (reversed)"
    );
}

/// resolve_same_family_sorts handles Adt_ prefixed datatype names.
/// Synthesized ADT names like "Adt_Some_None" should map to the Option family.
/// (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_adt_prefix_option() {
    use ay_dpll::api::DatatypeSort;
    let adt = Sort::Datatype(DatatypeSort {
        name: "Adt_Some_None".to_string(),
        constructors: vec![],
    });
    let uninterp = Sort::Uninterpreted("OptionInt".to_string());
    assert_eq!(
        super::resolve_same_family_sorts(&adt, &uninterp),
        Some(adt.clone()),
        "Datatype(Adt_Some_None) should be preferred over Uninterpreted(OptionInt)"
    );
}

#[test]
#[timeout(30000)]
fn test_resolve_same_family_cons_nil_uninterpreted_list() {
    use ay_dpll::api::DatatypeSort;
    let adt = Sort::Datatype(DatatypeSort {
        name: "Adt_Cons_Nil".to_string(),
        constructors: vec![],
    });
    let uninterp = Sort::Uninterpreted("List".to_string());
    assert_eq!(
        super::resolve_same_family_sorts(&adt, &uninterp),
        Some(adt.clone()),
        "Datatype(Adt_Cons_Nil) should resolve with Uninterpreted(List) before aliases are registered"
    );
}

/// resolve_same_family_sorts returns None for unrelated cross-sort-type pairs.
/// (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_cross_type_unrelated_returns_none() {
    use ay_dpll::api::DatatypeSort;
    let dt = Sort::Datatype(DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![],
    });
    let uninterp = Sort::Uninterpreted("ResultIntInt".to_string());
    assert!(
        super::resolve_same_family_sorts(&dt, &uninterp).is_none(),
        "Datatype(OptionInt) and Uninterpreted(ResultIntInt) are in different families"
    );
}

/// Seq vs non-Seq-family Uninterpreted returns None. (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_seq_vs_unrelated_uninterpreted_returns_none() {
    let seq = Sort::seq(Sort::Int);
    let uninterp = Sort::Uninterpreted("OptionInt".to_string());
    assert!(
        super::resolve_same_family_sorts(&seq, &uninterp).is_none(),
        "Seq(Int) and Uninterpreted(OptionInt) are in different families"
    );
}

/// Ite with Seq vs Uninterpreted("Vec") branches should resolve to Seq via
/// the cross-sort-type family resolution. (#2699)
#[test]
#[timeout(30000)]
fn test_ite_seq_vs_uninterpreted_vec_resolves_to_seq() {
    // Build Ite(true, Seq::empty(), vec_var@)
    let cond = PureExpr::Bool(true);
    let then_expr = PureExpr::LogicFnCall {
        name: "Seq::empty".to_string(),
        args: vec![],
    };
    let vec_id = intern_sort_name("Vec");
    let else_expr = PureExpr::View(Arc::new(PureExpr::Var(
        "v".to_string(),
        Some(ExprSort::Datatype(vec_id)),
    )));
    let ite = PureExpr::Ite(Arc::new(cond), Arc::new(then_expr), Arc::new(else_expr));
    let sort = infer_expr_sort(&ite);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "Ite with Seq and Vec view branches should resolve to Seq(Int), got {sort:?}"
    );
}

/// Match with Datatype(OptionInt) and Uninterpreted("Option") arms should
/// resolve to the more specific sort. (#2699)
#[test]
#[timeout(30000)]
fn test_match_cross_type_option_family_resolution() {
    use trust_wp_core::formula::{MatchArm, Pattern};
    let opt_int_id = intern_sort_name("OptionInt");
    // Arm 1: Some(x) => checked_add(1, 2) → OptionInt
    let arm1_body = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        method: "checked_add".to_string(),
        args: vec![PureExpr::Int(1)],
    };
    // Arm 2: None => None → Option (generic via Var annotation)
    let arm2_body = PureExpr::Var(
        "none_val".to_string(),
        Some(ExprSort::Datatype(intern_sort_name("Option"))),
    );
    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var(
            "opt".to_string(),
            Some(ExprSort::Datatype(opt_int_id)),
        )),
        arms: vec![
            MatchArm {
                pattern: Pattern::Wildcard,
                body: arm1_body,
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: arm2_body,
            },
        ],
    };
    let sort = infer_expr_sort(&match_expr);
    // First arm infers as Uninterpreted("OptionInt") from checked_add.
    // Second arm infers as Uninterpreted("Option") from the annotation.
    // resolve_same_family_sorts should pick OptionInt (more specific).
    assert!(
        sort != Sort::Int,
        "Match with Option family arms should not fall back to Int, got {sort:?}"
    );
}

/// Seq(Int) vs Datatype(Vec) ITE resolution should prefer native Seq. (#2699)
///
/// When one ITE branch infers Seq(Int) (the canonical encoding sort) and the
/// other infers as a Datatype from the Seq family (e.g., Vec from struct layout),
/// resolve_same_family_sorts should prefer the native Seq sort because it is
/// the canonical encoding representation post-#2080.
#[test]
#[timeout(30000)]
fn test_ite_seq_vs_datatype_vec_prefers_seq() {
    use ay_dpll::api::DatatypeSort;

    let seq_sort = Sort::seq(Sort::Int);
    let dt_sort = Sort::Datatype(DatatypeSort {
        name: "Vec".to_string(),
        constructors: vec![],
    });

    let result = resolve_same_family_sorts(&seq_sort, &dt_sort);
    assert_eq!(
        result,
        Some(Sort::seq(Sort::Int)),
        "Seq(Int) vs Datatype(Vec) should prefer native Seq sort"
    );

    // Also test reversed argument order
    let result_rev = resolve_same_family_sorts(&dt_sort, &seq_sort);
    assert_eq!(
        result_rev,
        Some(Sort::seq(Sort::Int)),
        "Datatype(Vec) vs Seq(Int) should prefer native Seq sort"
    );
}

/// Seq(Int) vs Datatype(LinkedList) should also prefer native Seq. (#2699)
#[test]
#[timeout(30000)]
fn test_ite_seq_vs_datatype_linked_list_prefers_seq() {
    use ay_dpll::api::DatatypeSort;

    let seq_sort = Sort::seq(Sort::Int);
    let dt_sort = Sort::Datatype(DatatypeSort {
        name: "LinkedList".to_string(),
        constructors: vec![],
    });

    let result = resolve_same_family_sorts(&seq_sort, &dt_sort);
    assert_eq!(
        result,
        Some(Sort::seq(Sort::Int)),
        "Seq(Int) vs Datatype(LinkedList) should prefer native Seq sort"
    );
}

/// Datatype(OptionInt) vs Datatype(Adt_Some_None) should resolve via family. (#2699)
#[test]
#[timeout(30000)]
fn test_ite_two_datatypes_same_option_family() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeSort};

    let opt_int = Sort::Datatype(DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    });
    let adt_sort = Sort::Datatype(DatatypeSort {
        name: "Adt_Some_None".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    });

    let result = resolve_same_family_sorts(&opt_int, &adt_sort);
    assert!(
        result.is_some(),
        "Two Datatype sorts in the Option family should resolve, got None"
    );
}

/// Seq(Int) vs Uninterpreted("Vec") should prefer native Seq. (#2699)
///
/// This was already handled before #2699 (Case 3), but verify it still works
/// alongside the new Datatype cases.
#[test]
#[timeout(30000)]
fn test_ite_seq_vs_uninterpreted_vec_prefers_seq() {
    let seq_sort = Sort::seq(Sort::Int);
    let uninterp = Sort::Uninterpreted("Vec".to_string());

    let result = resolve_same_family_sorts(&seq_sort, &uninterp);
    assert_eq!(
        result,
        Some(Sort::seq(Sort::Int)),
        "Seq(Int) vs Uninterpreted(Vec) should prefer native Seq sort"
    );
}

/// Ite with Seq(Int) then-branch and Int else-branch should infer Seq(Int),
/// not Int. The Int else-branch is from sort inference fallback and should
/// not override the concrete Seq sort from the then-branch. (#2699)
#[test]
#[timeout(30000)]
fn test_ite_seq_then_int_else_infers_seq() {
    let id = intern_sort_name("std::vec::Vec");
    let seq_receiver = PureExpr::Var("v".to_string(), Some(ExprSort::Datatype(id)));
    let then_expr = PureExpr::View(Arc::new(seq_receiver));
    let else_expr = PureExpr::Var("fallback".to_string(), None); // infers Int
    let ite = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(then_expr),
        Arc::new(else_expr),
    );

    let sort = infer_expr_sort(&ite);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "Ite with Seq then and Int else should prefer Seq sort, got {sort:?}"
    );
}

/// Match expression with mixed Datatype and Int arm sorts should prefer
/// the Datatype sort. Int arms are from inference fallback. (#2699)
#[test]
#[timeout(30000)]
fn test_match_mixed_datatype_int_arms_prefers_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let _dt = Sort::Datatype(DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    });

    // The infer_expr_sort for a Var with Datatype annotation returns the ay sort
    // from expr_sort_to_ay_sort, which for "OptionInt" returns
    // Uninterpreted("OptionInt"). Verify that when one match arm returns
    // Uninterpreted("OptionInt") and another returns Int (fallback), the match
    // overall prefers the non-Int sort.
    let opt_id = intern_sort_name("OptionInt");
    let arm1_body = PureExpr::Var("some_val".to_string(), Some(ExprSort::Datatype(opt_id)));
    let arm2_body = PureExpr::Var("default".to_string(), None); // infers Int

    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: trust_wp_core::formula::Pattern::Wildcard,
                body: arm1_body,
            },
            trust_wp_core::formula::MatchArm {
                pattern: trust_wp_core::formula::Pattern::Wildcard,
                body: arm2_body,
            },
        ],
    };

    let sort = infer_expr_sort(&match_expr);
    // The first arm infers OptionInt (Uninterpreted), second infers Int.
    // Since first is non-Int, it should be used.
    assert_ne!(
        sort,
        Sort::Int,
        "Match with OptionInt and Int arms should prefer OptionInt, got {sort:?}"
    );
}

// --- Tuple family sort resolution tests (#2699) ---

/// Two Uninterpreted Tuple2 sorts from different encoding paths should resolve
/// in the same family. (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_tuple2_uninterpreted() {
    let a = Sort::Uninterpreted("Tuple2".to_string());
    let b = Sort::Uninterpreted("Tuple2".to_string());
    assert_eq!(
        super::resolve_same_family_sorts(&a, &b),
        Some(a.clone()),
        "Two identical Tuple2 sorts should resolve to Tuple2"
    );
}

/// Datatype(Tuple2) vs Uninterpreted("Tuple2") should resolve via family. (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_datatype_vs_uninterpreted_tuple2() {
    use ay_dpll::api::DatatypeSort;
    let dt = Sort::Datatype(DatatypeSort {
        name: "Tuple2".to_string(),
        constructors: vec![],
    });
    let uninterp = Sort::Uninterpreted("Tuple2".to_string());
    let result = super::resolve_same_family_sorts(&dt, &uninterp);
    assert!(
        result.is_some(),
        "Datatype(Tuple2) and Uninterpreted(Tuple2) should be in the same family"
    );
    // Prefer Datatype since it carries constructor info
    assert_eq!(
        result,
        Some(dt),
        "Should prefer Datatype(Tuple2) over Uninterpreted(Tuple2)"
    );
}

/// ite_sort_family should classify Vec and LinkedList into the Seq family,
/// so Uninterpreted("Vec") and Uninterpreted("LinkedList") resolve as
/// same-family in Ite/Match contexts. (#2699)
#[test]
#[timeout(30000)]
fn test_ite_sort_family_vec_and_linkedlist_are_seq_family() {
    let vec_family = super::ite_sort_family("Vec");
    let ll_family = super::ite_sort_family("LinkedList");
    let seq_family = super::ite_sort_family("Seq");
    assert_eq!(vec_family, "Seq", "Vec should map to Seq family");
    assert_eq!(ll_family, "Seq", "LinkedList should map to Seq family");
    assert_eq!(seq_family, "Seq", "Seq should map to Seq family");
}

/// ite_sort_family should classify HashMap and GhostMap into FMap family. (#2699)
#[test]
#[timeout(30000)]
fn test_ite_sort_family_hashmap_and_ghostmap_are_fmap_family() {
    let hm_family = super::ite_sort_family("HashMap");
    let gm_family = super::ite_sort_family("GhostMap");
    let fmap_family = super::ite_sort_family("FMap");
    assert_eq!(hm_family, "FMap", "HashMap should map to FMap family");
    assert_eq!(gm_family, "FMap", "GhostMap should map to FMap family");
    assert_eq!(fmap_family, "FMap", "FMap should map to FMap family");
}

/// Uninterpreted("Vec") vs Uninterpreted("LinkedList") should now resolve as
/// same-family (both Seq) in resolve_same_family_sorts. (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_vec_vs_linkedlist_both_seq() {
    let vec = Sort::Uninterpreted("Vec".to_string());
    let ll = Sort::Uninterpreted("LinkedList".to_string());
    let result = super::resolve_same_family_sorts(&vec, &ll);
    assert!(
        result.is_some(),
        "Vec and LinkedList should resolve as same Seq family"
    );
}

/// Uninterpreted("HashMap") vs Uninterpreted("FMap") should resolve as
/// same-family (both FMap). (#2699)
#[test]
#[timeout(30000)]
fn test_resolve_same_family_hashmap_vs_fmap() {
    let hm = Sort::Uninterpreted("HashMap".to_string());
    let fmap = Sort::Uninterpreted("FMap".to_string());
    let result = super::resolve_same_family_sorts(&hm, &fmap);
    assert!(
        result.is_some(),
        "HashMap and FMap should resolve as same family"
    );
    // Both are Uninterpreted in the same family; the longer name is
    // preferred by the resolution heuristic ("HashMap" > "FMap").
    assert_eq!(
        result,
        Some(hm),
        "Longer name (HashMap) should be preferred over FMap by length heuristic"
    );
}

/// `declare_namespace!` functions (zero-arg, all-uppercase) must infer Int
/// without incrementing the SortFallbackToIntFromLogicFn demotion counter.
/// These are namespace ID functions returning `usize` = `Int`. (#2701)
#[test]
#[timeout(30000)]
fn test_declare_namespace_fn_returns_int_without_demotion() {
    let before = unsoundness::snapshot();

    // PERMCELL matches the declare_namespace! pattern
    let expr = PureExpr::LogicFnCall {
        name: "PERMCELL".to_string(),
        args: vec![],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "PERMCELL should return Int");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "declare_namespace! fns must not fire demoting LogicFn fallback: {delta:?}"
    );
}

/// All-uppercase logic function with underscore (e.g., MY_NS) also matches
/// the `declare_namespace!` pattern and should not trigger demotion. (#2701)
#[test]
#[timeout(30000)]
fn test_declare_namespace_fn_with_underscore_no_demotion() {
    let before = unsoundness::snapshot();

    let expr = PureExpr::LogicFnCall {
        name: "MY_NAMESPACE".to_string(),
        args: vec![],
    };
    let sort = infer_expr_sort(&expr);
    assert_eq!(sort, Sort::Int, "MY_NAMESPACE should return Int");

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "all-uppercase namespace fns must not fire demoting LogicFn fallback: {delta:?}"
    );
}

/// Driver-emitted Int cast/truncation logic functions are exact Int terms in
/// pure encoding and must not be treated as unknown user logic functions.
#[test]
#[timeout(30000)]
fn test_synthetic_int_cast_logic_fns_return_int_without_demotion() {
    let before = unsoundness::snapshot();

    for name in [
        "__trust_wp_int_truncate_u8",
        "__trust_wp_int_truncate_s16",
        "__trust_wp_int_cast_u64_to_s64",
    ] {
        let expr = PureExpr::LogicFnCall {
            name: name.to_string(),
            args: vec![PureExpr::Int(300)],
        };
        let sort = infer_expr_sort(&expr);
        assert_eq!(sort, Sort::Int, "{name} should return Int");
    }

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "synthetic Int cast/truncation fns must not fire demoting LogicFn fallback: {delta:?}"
    );
}

/// A non-namespace function (lowercase, with args) should still trigger
/// the SortFallbackToIntFromLogicFn demotion when unrecognized. (#2701)
#[test]
#[timeout(30000)]
fn test_unknown_logic_fn_still_demotes() {
    let before = unsoundness::snapshot();

    let expr = PureExpr::LogicFnCall {
        name: "unknown_fn".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let _sort = infer_expr_sort(&expr);

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0)
            > 0,
        "unknown logic fns with args must still fire demoting fallback: {delta:?}"
    );
}

/// Ite with Datatype(OptionInt) vs Uninterpreted("Option") should resolve to
/// the more specific sort in the same ADT family. (#2699)
#[test]
#[timeout(30000)]
fn test_ite_datatype_vs_uninterpreted_same_family_prefers_specific() {
    let option_id = intern_sort_name("OptionInt");
    let option_bare_id = intern_sort_name("Option");

    // Datatype-annotated var: infers to Uninterpreted("OptionInt")
    let a = PureExpr::Var("a".to_string(), Some(ExprSort::Datatype(option_id)));
    // Bare-annotated var: infers to Uninterpreted("Option")
    let b = PureExpr::Var("b".to_string(), Some(ExprSort::Datatype(option_bare_id)));
    let cond = PureExpr::Bool(true);
    let ite = PureExpr::Ite(Arc::new(cond), Arc::new(a), Arc::new(b));

    let sort = infer_expr_sort(&ite);
    // Both map to Uninterpreted sorts in the Option family; OptionInt is longer
    // and more specific, so resolve_same_family_sorts should prefer it.
    assert!(
        matches!(sort, Sort::Uninterpreted(ref name) if name == "OptionInt"),
        "Ite with OptionInt vs Option should resolve to OptionInt, got {sort:?}"
    );
}

/// Match arms with Seq-annotated and Vec-Datatype-annotated vars should
/// both resolve to the Seq family. (#2699)
#[test]
#[timeout(30000)]
fn test_match_seq_vs_vec_datatype_resolves_to_seq() {
    use trust_wp_core::formula::MatchArm;
    let vec_id = intern_sort_name("Vec");
    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: trust_wp_core::formula::Pattern::Wildcard,
                body: PureExpr::Var("s".to_string(), Some(ExprSort::Seq)),
            },
            MatchArm {
                pattern: trust_wp_core::formula::Pattern::Wildcard,
                body: PureExpr::Var("v".to_string(), Some(ExprSort::Datatype(vec_id))),
            },
        ],
    };

    let sort = infer_expr_sort(&expr);
    // ExprSort::Seq → Sort::seq(Sort::Int), ExprSort::Datatype(Vec) → Sort::seq(Sort::Int)
    // Both resolve to the same Seq(Int) sort — no mismatch at this level.
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "Match with Seq vs Vec should resolve to Seq(Int), got {sort:?}"
    );
}
