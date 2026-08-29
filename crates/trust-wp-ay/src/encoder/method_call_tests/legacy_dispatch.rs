// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Tests moved from method_call/mod.rs as part of #1584 ---

fn iter_mut_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "IterMut".to_string(),
        constructors: vec![],
    }
}

#[test]
#[timeout(30000)]
fn get_or_declare_method_func_reuses_matching_signature() {
    let mut encoder = AYEncoder::new();
    let decl1 = encoder.get_or_declare_method_func(
        "method_completed_1_u497465724d7574",
        &[Sort::Uninterpreted("IterMut".to_string())],
        Sort::Bool,
    );
    let decl2 = encoder.get_or_declare_method_func(
        "method_completed_1_u497465724d7574",
        &[Sort::Uninterpreted("IterMut".to_string())],
        Sort::Bool,
    );

    assert_eq!(
        decl1.name(),
        decl2.name(),
        "matching signatures should reuse the same UF"
    );
}

#[test]
#[timeout(30000)]
fn get_or_declare_method_func_breaks_signature_collisions() {
    let mut encoder = AYEncoder::new();
    let base_name = "method_completed_1_u497465724d7574";

    let uninterpreted = encoder.get_or_declare_method_func(
        base_name,
        &[Sort::Uninterpreted("IterMut".to_string())],
        Sort::Bool,
    );
    let datatype = encoder.get_or_declare_method_func(
        base_name,
        &[Sort::Datatype(iter_mut_datatype())],
        Sort::Bool,
    );

    assert_eq!(
        uninterpreted.name(),
        base_name,
        "the first declaration should keep the canonical symbol name"
    );
    assert_ne!(
        uninterpreted.name(),
        datatype.name(),
        "a mismatched signature must not silently reuse the first declaration"
    );
    assert_eq!(
        datatype.name(),
        "method_completed_1_u497465724d7574__sig_d497465724d7574__ret_b"
    );
    assert_eq!(
        datatype.domain(),
        &[Sort::Datatype(iter_mut_datatype())],
        "collision-broken declaration should preserve the requested datatype domain"
    );
}

/// Custom-type receiver `.contains()` must route to Bool UF, not FSet. (#2330)
#[test]
#[timeout(30000)]
fn custom_type_contains_dispatches_to_bool_uf_not_fset() {
    let mut encoder = AYEncoder::new();

    let id = intern_sort_name("Tokens");
    let receiver = PureExpr::Var("tokens".to_string(), Some(ExprSort::Datatype(id)));
    let contains_expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "contains".to_string(),
        args: vec![PureExpr::Var("ns".to_string(), Some(ExprSort::Int))],
    };

    let result = encoder.encode_pure(&contains_expr);
    assert!(
        result.is_ok(),
        "custom-type .contains() must not crash: {result:?}"
    );
    assert!(
        !encoder.decls.has_spec_func("fset_contains"),
        "custom-type .contains() must NOT declare fset_contains"
    );
}

/// Namespace token membership is true in the bounded Tokens model.
#[test]
#[timeout(30000)]
fn namespace_token_contains_encodes_true() {
    let mut encoder = AYEncoder::new();

    let contains_expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("tokens".to_string(), None)),
        method: "contains".to_string(),
        args: vec![PureExpr::LogicFnCall {
            name: "MESSAGE_PASSING".to_string(),
            args: vec![],
        }],
    };

    let term = encoder
        .encode_pure(&contains_expr)
        .expect("namespace token contains should encode");
    assert_eq!(term, encoder.solver.bool_const(true));
    assert!(
        !encoder.decls.has_spec_func("fset_contains"),
        "namespace token membership must not route through FSet contains"
    );
}

/// Ordinary same-named locals are not rewritten unless the argument is a namespace.
#[test]
#[timeout(30000)]
fn tokens_named_collection_contains_non_namespace_stays_collection_dispatch() {
    let mut encoder = AYEncoder::new();

    let contains_expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("tokens".to_string(), None)),
        method: "contains".to_string(),
        args: vec![PureExpr::Var("x".to_string(), Some(ExprSort::Int))],
    };

    let term = encoder
        .encode_pure(&contains_expr)
        .expect("ordinary contains should encode");
    assert_ne!(term, encoder.solver.bool_const(true));
    assert!(
        encoder.decls.has_spec_func("fset_contains"),
        "ordinary untyped contains should keep the existing FSet fallback"
    );
}

/// FSet receiver `.contains()` must still route to fset_contains. (#2330 regression guard)
#[test]
#[timeout(30000)]
fn fset_receiver_contains_still_routes_to_fset() {
    let mut encoder = AYEncoder::new();

    // Bare var("s") with no annotation infers Sort::Int, which is the FSet sort.
    let contains_expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
        method: "contains".to_string(),
        args: vec![PureExpr::Int(7)],
    };

    let result = encoder.encode_pure(&contains_expr);
    assert!(result.is_ok(), "FSet .contains() must encode: {result:?}");
    assert!(
        encoder.decls.has_spec_func("fset_contains"),
        "FSet .contains() must declare fset_contains UF"
    );
}

/// Quantifier-bound Seq receivers must keep their scoped sort during method
/// dispatch so `contains` stays on the Seq path instead of falling through
/// to the FSet encoder. Regression for #2116.
#[test]
#[timeout(30000)]
fn quantified_seq_receiver_contains_uses_seq_dispatch() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let quantified = exists_with_sort(
        "prod",
        ExprSort::Seq,
        method_call(var("prod"), "contains", vec![int(7)]),
    );

    encoder.register_sort_hints(std::slice::from_ref(&quantified));
    assert!(
        encoder.is_seq_receiver(&var("prod"), None),
        "prescan should classify the quantified `prod` receiver as Seq before encoding"
    );

    let result = encoder.encode_pure(&quantified);

    assert!(
        result.is_ok(),
        "quantified Seq .contains() must encode through the Seq path: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "quantified Seq .contains() should initialize the Seq theory"
    );
    assert!(
        !encoder.decls.has_spec_func("fset_contains"),
        "quantified Seq .contains() must not declare fset_contains"
    );
}

/// Regression for the negated `cc/collections.rs` HashMap iterator
/// proof-assert: the existential `prod: Seq` receiver inside
/// `prod.contains(__trust_wp_tuple2(...))` must stay on the Seq path while
/// encoding the negated postcondition. Part of #2116 / #994.
#[test]
#[timeout(30000)]
fn negated_hashmap_tuple2_membership_keeps_quantified_seq_dispatch() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("call_7_view".to_string(), ExprSort::FMap);

    let k_sort = ExprSort::TypeParam(intern_sort_name("K"));
    let v_sort = ExprSort::TypeParam(intern_sort_name("V"));
    let tuple_elem = logic_fn_call("__trust_wp_tuple2", vec![var("k1"), var("v")]);
    let rhs = exists_with_sort(
        "k1",
        k_sort.clone(),
        and(
            eq(method_call(var("k1"), "deep_model", vec![]), var("k")),
            method_call(var("prod"), "contains", vec![tuple_elem]),
        ),
    );
    let ensure = exists_with_sort(
        "prod",
        ExprSort::Seq,
        forall_with_sort(
            "k",
            k_sort,
            forall_with_sort(
                "v",
                v_sort,
                eq(
                    eq(
                        method_call(view(var("call_7")), "get", vec![var("k")]),
                        logic_fn_call("Some", vec![var("v")]),
                    ),
                    rhs,
                ),
            ),
        ),
    );

    let negated = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        encode_negated_postcondition(&mut encoder, &ensure, None, None)
    }));

    assert!(
        matches!(negated, Ok(Ok(_))),
        "negated HashMap proof_assert should encode without falling into fset_contains: {negated:?}"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_len_key_stays_on_seq_dispatch() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    let seq_empty = logic_fn_call("seq_empty", vec![]);
    let len_call = method_call(seq_empty.clone(), "len", vec![]);
    let indexed = method_call(final_expr(seq_empty.clone()), "index_logic", vec![len_call]);
    let quantified = forall_with_sort(
        "i",
        ExprSort::Int,
        eq(
            method_call(final_expr(seq_empty.clone()), "index_logic", vec![var("i")]),
            method_call(seq_empty, "index_logic", vec![var("i")]),
        ),
    );

    encoder.register_sort_hints(&[indexed.clone(), quantified]);
    let result = encoder.encode_pure(&indexed);

    assert!(
        result.is_ok(),
        "seq.index_logic(seq.len()) should encode through the Seq path: {result:?}"
    );
    assert!(
        encoder.seq_state.funcs_is_some(),
        "Seq dispatch should initialize the Seq theory"
    );
    assert!(
        !encoder
            .decls
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_")),
        "Seq indexing with a len() key must not create a generic method_index_logic UF"
    );
    let eq_zero = eq(indexed, int(0));
    let eq_zero_term = encoder
        .encode_pure(&eq_zero)
        .expect("equality over Seq index expression should encode");
    let _ = eq_zero_term;
}
