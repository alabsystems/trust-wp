// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for view encoding helpers, extracted from the inline module.

use ay_dpll::api::{DatatypeSort, SolveResult, Sort};
use trust_wp_core::{
    formula::{intern_sort_name, ExprSort, PureExpr},
    logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind, LogicFnDef},
};

use super::{
    collection_iterator_view_return_sort, direct_view_owner_type_candidates,
    expr_annotation_is_predcell_slice, indexed_predcell_slice_view_parts, sort_display_key,
};
use crate::{
    encoder::{sort_context::is_seq_family_sort, AYEncoder},
    tests::helpers::{
        deref, final_expr, get_field, logic_fn_call, method_call, old, var, var_with_sort, view,
    },
};

// ── sort_display_key ──

#[test]
fn test_sort_display_key_int() {
    assert_eq!(sort_display_key(&Sort::Int), "Int");
}

#[test]
fn test_sort_display_key_bool() {
    assert_eq!(sort_display_key(&Sort::Bool), "Bool");
}

#[test]
fn test_sort_display_key_uninterpreted() {
    assert_eq!(
        sort_display_key(&Sort::Uninterpreted("MyType".to_string())),
        "MyType"
    );
}

#[test]
fn test_sort_display_key_uninterpreted_colons_replaced() {
    assert_eq!(
        sort_display_key(&Sort::Uninterpreted("std::vec::Vec".to_string())),
        "std_vec_Vec"
    );
}

#[test]
fn test_sort_display_key_datatype() {
    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![],
    };
    assert_eq!(sort_display_key(&Sort::Datatype(dt)), "OptionInt");
}

#[test]
fn test_sort_display_key_datatype_colons_replaced() {
    let dt = DatatypeSort {
        name: "my::ns::Pair".to_string(),
        constructors: vec![],
    };
    assert_eq!(sort_display_key(&Sort::Datatype(dt)), "my_ns_Pair");
}

#[test]
fn test_direct_view_owner_type_candidates_trait_impl_path() {
    let candidates = direct_view_owner_type_candidates(
        "creusot_test::<implementation::PersistentArray<T> as creusot_std::View>::view",
    );
    assert!(
        candidates.contains(&"implementation::PersistentArray".to_string()),
        "trait impl owner should recover the concrete self type: {candidates:?}"
    );
    assert!(
        candidates.contains(&"PersistentArray".to_string()),
        "owner lookup should include the bare ADT name: {candidates:?}"
    );
}

#[test]
fn hash_map_iterator_view_has_fmap_return_sort() {
    let iter_sort = ExprSort::MutRef(Box::new(ExprSort::Datatype(intern_sort_name(
        "std::collections::hash_map::IntoIter",
    ))));
    let it = var_with_sort("it", iter_sort);
    assert_eq!(
        collection_iterator_view_return_sort(&it),
        Some(Sort::Uninterpreted("FMap".to_string()))
    );
    assert_eq!(
        collection_iterator_view_return_sort(&deref(it)),
        Some(Sort::Uninterpreted("FMap".to_string()))
    );
}

#[test]
fn hash_set_iterator_view_has_fset_return_sort() {
    for sort_name in [
        "std::collections::hash_set::IntoIter",
        "std::collections::hash_set::Iter",
        "Intersection",
        "Difference",
        "std::collections::hash_set::Intersection",
        "std::collections::hash_set::Difference",
        "std::collections::hash::set::Intersection",
        "std::collections::hash::set::Difference",
    ] {
        let iter_sort = ExprSort::Datatype(intern_sort_name(sort_name));
        let it = var_with_sort("it", iter_sort);
        assert_eq!(collection_iterator_view_return_sort(&it), Some(Sort::Int));
    }
}

#[test]
fn seq_view_identity_reasserts_component_equalities_after_scope_pop() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);
    encoder.record_sort_hint("s_view".to_string(), ExprSort::Seq);

    let s = var_with_sort("s", ExprSort::Seq);
    let s_view = view(s.clone());
    encoder.push_scope().expect("push temporary scope");
    encoder
        .encode_pure(&s_view)
        .expect("encode view in temporary scope");
    encoder.pop_scope().expect("pop temporary scope");

    let base_len = encoder
        .encode_pure(&method_call(s, "len", vec![]))
        .expect("encode base len");
    let view_len = encoder
        .encode_pure(&method_call(s_view, "len", vec![]))
        .expect("encode view len");
    let len_neq = encoder.solver.neq(base_len, view_len);
    encoder.assert_term(len_neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Seq view identity must be reasserted after popped scopes so len proxies stay linked; got {result:?}"
    );
}

#[test]
fn directly_declared_seq_view_name_asserts_component_identity() {
    let mut encoder = AYEncoder::new();
    let seq_sort = Sort::seq(Sort::Int);

    let s = encoder
        .get_or_declare_var("s", seq_sort.clone())
        .expect("declare base seq");
    let s_view = encoder
        .get_or_declare_var("s_view", seq_sort)
        .expect("declare view seq");

    let base_len = encoder.seq_len_term(s).expect("base len");
    let view_len = encoder.seq_len_term(s_view).expect("view len");
    let len_neq = encoder.solver.neq(base_len, view_len);
    encoder.assert_term(len_neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "directly declared Seq view names must bridge len proxies; got {result:?}"
    );
}

#[test]
fn directly_declared_uninterpreted_seq_view_name_asserts_component_identity() {
    let mut encoder = AYEncoder::new();
    encoder.force_uninterpreted_seq_sort_for_mixed_datatype();
    let seq_sort = Sort::Uninterpreted("Seq".to_string());

    let s = encoder
        .get_or_declare_var("s", seq_sort.clone())
        .expect("declare base seq");
    let s_view = encoder
        .get_or_declare_var("s_view", seq_sort)
        .expect("declare view seq");

    let base_len = encoder.seq_len_term(s).expect("base len");
    let view_len = encoder.seq_len_term(s_view).expect("view len");
    let len_neq = encoder.solver.neq(base_len, view_len);
    encoder.assert_term(len_neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "directly declared uninterpreted Seq view names must bridge len proxies; got {result:?}"
    );
}

// ── expr_annotation_is_predcell_slice ──

#[test]
fn test_predcell_slice_no_annotation() {
    let expr = var("x");
    assert!(!expr_annotation_is_predcell_slice(&expr));
}

#[test]
fn test_predcell_slice_wrong_datatype() {
    let id = intern_sort_name("Vec");
    let expr = var_with_sort("x", ExprSort::Datatype(id));
    assert!(!expr_annotation_is_predcell_slice(&expr));
}

#[test]
fn test_predcell_slice_correct_type() {
    let id = intern_sort_name("PredCellSlice");
    let expr = var_with_sort("x", ExprSort::Datatype(id));
    assert!(expr_annotation_is_predcell_slice(&expr));
}

#[test]
fn test_predcell_slice_qualified_name() {
    let id = intern_sort_name("my::module::PredCellSlice");
    let expr = var_with_sort("x", ExprSort::Datatype(id));
    assert!(expr_annotation_is_predcell_slice(&expr));
}

#[test]
fn test_predcell_slice_through_ref() {
    let id = intern_sort_name("PredCellSlice");
    let expr = var_with_sort("x", ExprSort::Ref(Box::new(ExprSort::Datatype(id))));
    assert!(expr_annotation_is_predcell_slice(&expr));
}

#[test]
fn test_predcell_slice_through_mutref() {
    let id = intern_sort_name("PredCellSlice");
    let expr = var_with_sort("x", ExprSort::MutRef(Box::new(ExprSort::Datatype(id))));
    assert!(expr_annotation_is_predcell_slice(&expr));
}

#[test]
fn test_predcell_slice_through_deref() {
    let id = intern_sort_name("PredCellSlice");
    let inner = var_with_sort("x", ExprSort::Datatype(id));
    let expr = deref(inner);
    assert!(expr_annotation_is_predcell_slice(&expr));
}

#[test]
fn test_predcell_slice_through_view() {
    let id = intern_sort_name("PredCellSlice");
    let inner = var_with_sort("x", ExprSort::Datatype(id));
    let expr = view(inner);
    assert!(expr_annotation_is_predcell_slice(&expr));
}

#[test]
fn test_predcell_slice_non_var_returns_false() {
    // Int literal has no annotation
    assert!(!expr_annotation_is_predcell_slice(&PureExpr::Int(0)));
}

// ── indexed_predcell_slice_view_parts ──

#[test]
fn test_indexed_predcell_slice_view_parts_index_method() {
    let id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("pcs", ExprSort::Datatype(id));
    let index_arg = PureExpr::Int(0);
    let expr = method_call(receiver, "index", vec![index_arg]);
    let result = indexed_predcell_slice_view_parts(&expr);
    assert!(result.is_some());
    let (recv, idx) = result.unwrap();
    assert_eq!(recv, &var_with_sort("pcs", ExprSort::Datatype(id)));
    assert_eq!(idx, &PureExpr::Int(0));
}

#[test]
fn test_indexed_predcell_slice_view_parts_index_logic_method() {
    let id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("pcs", ExprSort::Datatype(id));
    let index_arg = PureExpr::Int(1);
    let expr = method_call(receiver, "index_logic", vec![index_arg]);
    assert!(indexed_predcell_slice_view_parts(&expr).is_some());
}

#[test]
fn test_indexed_predcell_slice_view_parts_wrong_method() {
    let id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("pcs", ExprSort::Datatype(id));
    let expr = method_call(receiver, "len", vec![PureExpr::Int(0)]);
    assert!(indexed_predcell_slice_view_parts(&expr).is_none());
}

#[test]
fn test_indexed_predcell_slice_view_parts_wrong_arity() {
    let id = intern_sort_name("PredCellSlice");
    let receiver = var_with_sort("pcs", ExprSort::Datatype(id));
    // Two args instead of one
    let expr = method_call(receiver, "index", vec![PureExpr::Int(0), PureExpr::Int(1)]);
    assert!(indexed_predcell_slice_view_parts(&expr).is_none());
}

#[test]
fn test_indexed_predcell_slice_view_parts_non_predcell_receiver() {
    // Receiver is not PredCellSlice-annotated
    let receiver = var("plain_vec");
    let expr = method_call(receiver, "index", vec![PureExpr::Int(0)]);
    assert!(indexed_predcell_slice_view_parts(&expr).is_none());
}

#[test]
fn test_indexed_predcell_slice_view_parts_non_method_call() {
    let expr = var("x");
    assert!(indexed_predcell_slice_view_parts(&expr).is_none());
}

// ── View encoding via AYEncoder ──

#[test]
fn test_encode_view_var_declares_view_variable() {
    // View(Var("x")) should declare x_view and assert x = x_view
    let mut encoder = AYEncoder::new();
    let expr = view(var("x"));
    let result = encoder.encode_pure(&expr);
    assert!(result.is_ok(), "encoding View(Var(x)) should succeed");
}

#[test]
fn test_encode_nested_view_collapses() {
    // View(View(Var("x"))) should collapse to View(Var("x"))
    // Both should produce the same term
    let mut encoder = AYEncoder::new();
    let single_view = view(var("y"));
    let nested_view = view(view(var("y")));
    let t1 = encoder
        .encode_pure(&single_view)
        .expect("single view should encode");
    let t2 = encoder
        .encode_pure(&nested_view)
        .expect("nested view should encode");
    assert_eq!(t1, t2, "View(View(x)) should collapse to View(x)");
}

#[test]
fn test_encode_triple_nested_view_collapses() {
    // View(View(View(Var("z")))) should also collapse all the way down
    let mut encoder = AYEncoder::new();
    let single = view(var("z"));
    let triple = view(view(view(var("z"))));
    let t1 = encoder.encode_pure(&single).expect("single");
    let t2 = encoder.encode_pure(&triple).expect("triple");
    assert_eq!(t1, t2, "View(View(View(x))) should collapse to View(x)");
}

#[test]
fn test_encode_view_on_deref_expression() {
    // View(Deref(Var("ptr"))) should produce a view variable
    let mut encoder = AYEncoder::new();
    let expr = view(deref(var("ptr")));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "encoding View(Deref(Var(ptr))) should succeed"
    );
}

#[test]
fn test_encode_view_on_int_literal_is_identity() {
    // View on a scalar literal should return the literal itself
    // (Int sort is identity for view)
    let mut encoder = AYEncoder::new();
    let plain_int = PureExpr::Int(42);
    let viewed_int = view(PureExpr::Int(42));
    let t_plain = encoder.encode_pure(&plain_int).expect("plain int");
    let t_viewed = encoder.encode_pure(&viewed_int).expect("viewed int");
    assert_eq!(t_plain, t_viewed, "View on Int literal should be identity");
}

#[test]
fn test_encode_view_on_bool_literal_is_identity() {
    // View on a Bool expression should return the expression itself
    let mut encoder = AYEncoder::new();
    let plain_bool = PureExpr::Bool(true);
    let viewed_bool = view(PureExpr::Bool(true));
    let t_plain = encoder.encode_pure(&plain_bool).expect("plain bool");
    let t_viewed = encoder.encode_pure(&viewed_bool).expect("viewed bool");
    assert_eq!(t_plain, t_viewed, "View on Bool literal should be identity");
}

#[test]
fn test_encode_view_on_fset_intersection_preserves_bridge() {
    // `intersection` returns an FSet deep-model term. `view(...)` should not
    // collapse it to the raw inner term, or the set-adapter relation is lost.
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("xs"), "intersection", vec![var("ys")]);
    let viewed = view(expr.clone());

    let raw_term = encoder.encode_pure(&expr).expect("raw intersection");
    let viewed_term = encoder.encode_pure(&viewed).expect("viewed intersection");

    assert_ne!(
        raw_term, viewed_term,
        "View(intersection(...)) should remain distinct from the raw FSet term"
    );
}

#[test]
fn test_encode_view_on_copied_adapter_collapses_to_inner_view() {
    // Copied/Cloned adapters are transparent in view space: `view(copied(x))`
    // should collapse to the same inner iterator/view term as `x` so adapter
    // wrappers do not leak into downstream postconditions.
    let mut encoder = AYEncoder::new();
    let inner = method_call(var("xs"), "intersection", vec![var("ys")]);
    let copied = logic_fn_call("Copied", vec![inner.clone()]);

    let inner_term = encoder.encode_pure(&inner).expect("inner term");
    let copied_view = encoder.encode_pure(&view(copied)).expect("copied view");

    assert_eq!(
        inner_term, copied_view,
        "view(Copied(inner)) should collapse to the inner term"
    );
}

#[test]
fn test_encode_view_mutref_var_redirects_to_deref_path() {
    // View(Var("x", MutRef(Datatype(Vec)))) should produce the same term as
    // View(Deref(Var("x", MutRef(Datatype(Vec))))), because viewing a &mut T
    // is semantically viewing its current value. Both `x@` and `(*x)@` must
    // resolve to the same ay variable (`x_current_view`). (#2670)
    let mut encoder = AYEncoder::new();
    let dt_id = intern_sort_name("Vec");
    let mutref_sort = ExprSort::MutRef(Box::new(ExprSort::Datatype(dt_id)));
    let var_expr = var_with_sort("x", mutref_sort.clone());

    // View(Var("x", MutRef(Datatype(Vec))))
    let view_var = view(var_expr.clone());
    // View(Deref(Var("x", MutRef(Datatype(Vec)))))
    let view_deref = view(deref(var_expr));

    let t1 = encoder
        .encode_pure(&view_var)
        .expect("View(Var) with MutRef should succeed");
    let t2 = encoder
        .encode_pure(&view_deref)
        .expect("View(Deref(Var)) should succeed");
    assert_eq!(
        t1, t2,
        "View(Var(x, MutRef(_))) and View(Deref(Var(x, MutRef(_)))) must produce same term"
    );
}

#[test]
fn test_encode_view_wrapped_mutref_redirects_to_deref_path() {
    // split_first_mut call-site facts can produce View(Old(Deref(self_))) where
    // the wrapped expression still has MutRef(Seq) type. Viewing that reference
    // must mean viewing its pointee, so it should share the **self_ view carrier.
    let mut encoder = AYEncoder::new();
    let self_sort = ExprSort::MutRef(Box::new(ExprSort::MutRef(Box::new(ExprSort::Seq))));
    let self_expr = var_with_sort("self_", self_sort);

    let wrapped_ref_view = view(old(deref(self_expr.clone())));
    let pointee_view = view(deref(old(deref(self_expr))));

    let t1 = encoder
        .encode_pure(&wrapped_ref_view)
        .expect("View(Old(Deref(mutref))) should encode");
    let t2 = encoder
        .encode_pure(&pointee_view)
        .expect("View(Deref(Old(Deref(mutref)))) should encode");

    assert_eq!(
        t1, t2,
        "wrapped MutRef views should redirect through one more deref to the pointee view"
    );
}

#[test]
fn test_encode_view_mutref_int_is_identity() {
    // View(Var("y", MutRef(Int))) should redirect through deref and produce
    // identity on Int (scalar view is a no-op).
    let mut encoder = AYEncoder::new();
    let mutref_int = ExprSort::MutRef(Box::new(ExprSort::Int));
    let var_expr = var_with_sort("y", mutref_int);

    let view_var = view(var_expr);
    let result = encoder.encode_pure(&view_var);
    assert!(
        result.is_ok(),
        "View(Var(y, MutRef(Int))) should succeed: {:?}",
        result.err()
    );
}

#[test]
fn test_seq_view_body_instantiates_directly_for_result_without_quantified_axiom() {
    let mut encoder = AYEncoder::new();
    let tuple_sort = Sort::Uninterpreted("Tuple3".to_string());
    encoder
        .get_or_declare_var("result", tuple_sort.clone())
        .expect("result var");

    let model_name = trust_wp_core::logic::logic_fn_smt_name("model");
    let model_decl =
        encoder
            .solver_mut()
            .declare_fun(&model_name, &[tuple_sort], Sort::seq(Sort::Int));
    encoder
        .decls_for_test_mut()
        .insert_logic_func(model_name, model_decl);

    let view_def = LogicFnDef::new(
        "view".to_string(),
        "crate::PersistentArray::view".to_string(),
        vec!["self".to_string()],
        logic_fn_call("model", vec![var("self")]),
    )
    .with_param_sorts(vec![Some(ExprSort::Tuple(3))])
    .with_return_sort(Some(ExprSort::Seq));

    encoder
        .register_logic_fn(&view_def)
        .expect("direct view registration should succeed");
    let term = encoder
        .encode_pure(&view(var("result")))
        .expect("result@ should encode through direct body");

    assert!(
        encoder.solver().get_sort(term).is_seq(),
        "result@ should use the Seq model body instead of inheriting Tuple3"
    );
    assert!(
        encoder.var_term("result_view").is_none(),
        "direct result@ encoding should not synthesize a structural result_view"
    );
    assert_eq!(
        encoder.ground_pool_for_test().axiom_count(),
        0,
        "direct view registration must not add a quantified logic_view axiom"
    );
}

#[test]
fn test_direct_view_first_field_projection_can_use_seq_return_sort() {
    let mut encoder = AYEncoder::new();
    let tuple_sort = Sort::Uninterpreted("Tuple3".to_string());
    encoder
        .get_or_declare_var("result", tuple_sort.clone())
        .expect("result var");

    let option_payload_name = trust_wp_core::logic::logic_fn_smt_name("option_payload");
    let option_payload_decl =
        encoder
            .solver_mut()
            .declare_fun(&option_payload_name, &[tuple_sort], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(option_payload_name, option_payload_decl);

    let view_body = get_field(
        0,
        method_call(
            logic_fn_call("option_payload", vec![var("self")]),
            "unwrap_logic",
            vec![],
        ),
    );
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "crate::PersistentArray::view".to_string(),
        vec!["self".to_string()],
        view_body,
    )
    .with_param_sorts(vec![Some(ExprSort::Tuple(3))])
    .with_return_sort(Some(ExprSort::Seq));

    encoder
        .register_logic_fn(&view_def)
        .expect("direct view registration should succeed");
    let term = encoder
        .encode_pure(&view(var("result")))
        .expect("result@ should encode through direct body");

    assert!(
        encoder.solver().get_sort(term).is_seq(),
        "first-field direct view projection should keep the semantic Seq sort"
    );
    assert!(
        encoder.var_term("result_view").is_none(),
        "direct projection fallback should not synthesize a structural result_view"
    );
    let tuple_get_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let stale_int_projection_decls = encoder
        .logic_func_names()
        .into_iter()
        .filter(|name| name.starts_with(&tuple_get_smt) && name.contains("__placeholder_i__ret_i"))
        .collect::<Vec<_>>();
    assert!(
        stale_int_projection_decls.is_empty(),
        "direct Seq view projection should not first declare an Int-return tuple getter: {stale_int_projection_decls:?}"
    );
}

#[test]
fn view_final_tuple_projection_uses_final_root_name() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_sort = ExprSort::Tuple(2);
    let expr = view(final_expr(logic_fn_call(
        &tuple_get_0,
        vec![var_with_sort("call_3", tuple_sort.clone())],
    )));
    let expected = logic_fn_call(
        &tuple_get_0,
        vec![var_with_sort("call_3_final", tuple_sort)],
    );
    let mut encoder = AYEncoder::new();

    let term = encoder
        .encode_pure(&expr)
        .expect("View(Final(tuple_get_0(call_3))) should encode");
    let expected_term = encoder
        .encode_pure(&expected)
        .expect("tuple_get_0(call_3_final) should encode");

    assert_eq!(
        term, expected_term,
        "viewing a final tuple projection must read the final root, not the entry root"
    );
}

#[test]
fn test_direct_view_batch_registration_does_not_capture_generic_tuple_projection_view() {
    let mut encoder = AYEncoder::new();
    let pa_sort = intern_sort_name("PersistentArray");
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "creusot_test::<implementation::PersistentArray<T> as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        view(logic_fn_call("__trust_wp_field_frag", vec![var("self")])),
    )
    .with_param_sorts(vec![Some(ExprSort::Datatype(pa_sort))])
    .with_return_sort(Some(ExprSort::Seq));

    encoder
        .register_logic_fns(&[view_def])
        .expect("batch direct view registration should succeed");

    let raw_view_name = trust_wp_core::logic::logic_fn_smt_name("view");
    assert!(
        !encoder.has_logic_func_decl(&raw_view_name),
        "direct View::view bodies must not leave a monomorphic raw logic_view decl"
    );

    let inner_value = logic_fn_call("Inner::Direct", vec![var_with_sort("v", ExprSort::Seq)]);
    let tuple = logic_fn_call("__trust_wp_tuple2", vec![inner_value, var("perm")]);
    let projected_inner = get_field(0, tuple);
    let term = encoder
        .encode_pure(&view(projected_inner))
        .expect("View(tuple_get_0(tuple2(Inner, perm))) should encode");

    assert_eq!(
        encoder.solver().get_sort(term),
        Sort::Uninterpreted("Inner".to_string()),
        "generic view over an Inner projection should stay on the projection sort"
    );
}

#[test]
fn test_direct_view_beta_reduces_named_field_over_constructor_result() {
    let mut encoder = AYEncoder::new();
    let pa_sort = intern_sort_name("PersistentArray");
    let adt = AdtDecl::new(
        "crate::PersistentArray".to_string(),
        "PersistentArray".to_string(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "PersistentArray".to_string(),
            "PersistentArray".to_string(),
            vec![
                AdtFieldDecl::new("permcell".to_string(), ExprSort::Int),
                AdtFieldDecl::new("frag".to_string(), ExprSort::Seq),
                AdtFieldDecl::new("inv".to_string(), ExprSort::Int),
            ],
        )],
    );
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "PersistentArray".to_string(),
        adt,
    )]));

    let view_body = view(logic_fn_call("__trust_wp_field_frag", vec![var("self")]));
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "crate::PersistentArray::view".to_string(),
        vec!["self".to_string()],
        view_body,
    )
    .with_param_sorts(vec![Some(ExprSort::Datatype(pa_sort))])
    .with_return_sort(Some(ExprSort::Seq));

    encoder
        .register_logic_fn(&view_def)
        .expect("direct view registration should succeed");
    let constructor = logic_fn_call(
        "__trust_wp_tuple3",
        vec![var("pc"), var_with_sort("frag", ExprSort::Seq), var("inv")],
    );
    let term = encoder
        .try_encode_direct_view_body(&constructor, None)
        .expect("constructor result view should encode")
        .expect("constructor result should use direct view body");
    let term_sort = encoder.solver().get_sort(term);

    assert!(
        is_seq_family_sort(&term_sort),
        "direct view should use the constructor's Seq frag field, got {term_sort:?}"
    );
    assert!(
        !encoder.decls().has_spec_func("__trust_wp_field_frag"),
        "named field over direct constructor result should not become an Int UF"
    );
}

#[test]
fn test_direct_view_beta_uses_rebound_result_constructor_alias_without_param_sort() {
    let mut encoder = AYEncoder::new();
    let pa_sort = intern_sort_name("PersistentArray");
    let adt = AdtDecl::new(
        "implementation::PersistentArray".to_string(),
        "PersistentArray".to_string(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "PersistentArray".to_string(),
            "PersistentArray".to_string(),
            vec![
                AdtFieldDecl::new("permcell".to_string(), ExprSort::Int),
                AdtFieldDecl::new("frag".to_string(), ExprSort::Seq),
                AdtFieldDecl::new("inv".to_string(), ExprSort::Int),
            ],
        )],
    );
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "PersistentArray".to_string(),
        adt,
    )]));

    let view_body = view(logic_fn_call("__trust_wp_field_frag", vec![var("self")]));
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "creusot_test::<implementation::PersistentArray<T> as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        view_body,
    )
    .with_return_sort(Some(ExprSort::Seq));

    encoder
        .register_logic_fn(&view_def)
        .expect("direct view registration should succeed");
    let constructor = logic_fn_call(
        "__trust_wp_tuple3",
        vec![var("pc"), var_with_sort("frag", ExprSort::Seq), var("inv")],
    );
    let ctor_term = encoder
        .encode_pure(&constructor)
        .expect("constructor should encode");
    encoder.rebind_var(
        "result",
        ctor_term,
        Sort::Uninterpreted("Tuple3".to_string()),
    );
    encoder.record_var_expr_alias("result", constructor);

    let term = encoder
        .encode_pure(&view(var_with_sort("result", ExprSort::Datatype(pa_sort))))
        .expect("result@ should encode through the direct view body");
    let term_sort = encoder.solver().get_sort(term);

    assert!(
        is_seq_family_sort(&term_sort),
        "rebound result@ should use the constructor's Seq frag field, got {term_sort:?}"
    );
    assert!(
        !encoder.decls().has_spec_func("__trust_wp_field_frag"),
        "named field over rebound constructor result should not become an Int UF"
    );
    assert!(
        encoder.var_term("result_view").is_none(),
        "direct result@ encoding should not synthesize result_view"
    );
}

#[test]
fn test_view_uses_recorded_nameable_alias_before_declaring_view_var() {
    let mut encoder = AYEncoder::new();
    encoder.record_var_expr_alias("x_current", var_with_sort("target", ExprSort::Int));

    let rc_sort = intern_sort_name("alloc::rc::Rc");
    let term = encoder
        .encode_pure(&view(deref(var_with_sort(
            "x",
            ExprSort::Datatype(rc_sort),
        ))))
        .expect("view of aliased deref should encode through the alias target");

    let target_view = encoder
        .var_term("target_view")
        .expect("alias target view should be declared");
    assert_eq!(
        term, target_view,
        "View(Deref(x)) should reuse the recorded source alias"
    );
    assert!(
        encoder.var_term("x_current_view").is_none(),
        "alias substitution should avoid declaring a disconnected derived view"
    );
}

#[test]
fn test_direct_view_with_owner_metadata_rejects_unrelated_unannotated_inner() {
    let mut encoder = AYEncoder::new();
    let adt = AdtDecl::new(
        "implementation::PersistentArray".to_string(),
        "PersistentArray".to_string(),
        AdtKind::Struct,
        vec![AdtConstructorDecl::new(
            "PersistentArray".to_string(),
            "PersistentArray".to_string(),
            vec![
                AdtFieldDecl::new("permcell".to_string(), ExprSort::Int),
                AdtFieldDecl::new("frag".to_string(), ExprSort::Seq),
                AdtFieldDecl::new("inv".to_string(), ExprSort::Int),
            ],
        )],
    );
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "PersistentArray".to_string(),
        adt,
    )]));
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "creusot_test::<implementation::PersistentArray<T> as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        view(logic_fn_call("__trust_wp_field_frag", vec![var("self")])),
    )
    .with_return_sort(Some(ExprSort::Seq));
    encoder
        .register_logic_fn(&view_def)
        .expect("direct view registration should succeed");
    encoder
        .get_or_declare_var("frag", Sort::Uninterpreted("Fragment".to_string()))
        .expect("frag var");

    assert!(
        encoder
            .try_encode_direct_view_body(&var("frag"), None)
            .expect("direct view probe should not error")
            .is_none(),
        "PersistentArray direct view must not apply to an unrelated Fragment value"
    );
}

#[test]
fn test_opaque_view_uses_declared_mapping_return_sort() {
    let mut encoder = AYEncoder::new();
    let t_sort = intern_sort_name("T");
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "creusot_test::<T as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        var("self"),
    )
    .with_opaque(true)
    .with_param_sorts(vec![Some(ExprSort::Datatype(t_sort))])
    .with_return_sort(Some(ExprSort::Datatype(intern_sort_name("Mapping"))));

    encoder
        .register_logic_fn(&view_def)
        .expect("opaque view registration should keep return-sort metadata");
    let term = encoder
        .encode_pure(&view(var_with_sort("t", ExprSort::Datatype(t_sort))))
        .expect("t@ should encode");

    assert_eq!(
        encoder.solver().get_sort(term),
        Sort::Uninterpreted("Mapping".to_string()),
        "opaque custom View::view should use its declared Mapping carrier"
    );
}

#[test]
fn test_opaque_view_final_uses_declared_mapping_return_sort() {
    let mut encoder = AYEncoder::new();
    let t_sort = intern_sort_name("T");
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "creusot_test::<T as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        var("self"),
    )
    .with_opaque(true)
    .with_param_sorts(vec![Some(ExprSort::Datatype(t_sort))])
    .with_return_sort(Some(ExprSort::Datatype(intern_sort_name("Mapping"))));

    encoder
        .register_logic_fn(&view_def)
        .expect("opaque view registration should keep return-sort metadata");
    let term = encoder
        .encode_pure(&view(PureExpr::Final(std::sync::Arc::new(var_with_sort(
            "t",
            ExprSort::Datatype(t_sort),
        )))))
        .expect("^t@ should encode");

    assert_eq!(
        encoder.solver().get_sort(term),
        Sort::Uninterpreted("Mapping".to_string()),
        "opaque custom View::view should type final-state views as Mapping"
    );
}

#[test]
fn test_opaque_view_return_sort_ignores_untyped_candidates() {
    let mut encoder = AYEncoder::new();
    let t_sort = intern_sort_name("T");
    let untyped_view_def = LogicFnDef::new(
        "view".to_string(),
        "creusot_std::<U as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        var("self"),
    )
    .with_opaque(true)
    .with_return_sort(Some(ExprSort::Int));
    let mapping_view_def = LogicFnDef::new(
        "view".to_string(),
        "creusot_test::<T as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        var("self"),
    )
    .with_opaque(true)
    .with_param_sorts(vec![Some(ExprSort::Datatype(t_sort))])
    .with_return_sort(Some(ExprSort::Datatype(intern_sort_name("Mapping"))));

    encoder
        .register_logic_fns(&[untyped_view_def, mapping_view_def])
        .expect("view registrations should succeed");
    let term = encoder
        .encode_pure(&view(var_with_sort("t", ExprSort::Datatype(t_sort))))
        .expect("t@ should encode");

    assert_eq!(
        encoder.solver().get_sort(term),
        Sort::Uninterpreted("Mapping".to_string()),
        "untyped view metadata must not make typed custom-view selection ambiguous"
    );
}

#[test]
fn test_opaque_view_return_sort_matches_generic_self_by_impl_owner() {
    let mut encoder = AYEncoder::new();
    let t_sort = intern_sort_name("T");
    let self_param = intern_sort_name("Self");
    let view_def = LogicFnDef::new(
        "view".to_string(),
        "creusot_test::<T as creusot_std::View>::view".to_string(),
        vec!["self".to_string()],
        var("self"),
    )
    .with_opaque(true)
    .with_param_sorts(vec![Some(ExprSort::TypeParam(self_param))])
    .with_return_sort(Some(ExprSort::Datatype(intern_sort_name("Mapping"))));

    encoder
        .register_logic_fn(&view_def)
        .expect("opaque generic-self view registration should keep metadata");
    let term = encoder
        .encode_pure(&view(var_with_sort("t", ExprSort::Datatype(t_sort))))
        .expect("t@ should encode");

    assert_eq!(
        encoder.solver().get_sort(term),
        Sort::Uninterpreted("Mapping".to_string()),
        "generic Self receiver metadata should match the impl owner type"
    );
}

#[test]
fn test_sort_display_key_seq() {
    // Seq sort uses the Debug fallback path
    let seq = Sort::Seq(Box::new(Sort::Int));
    let key = sort_display_key(&seq);
    // Should produce a Debug representation since Seq is not handled
    // by explicit match arms
    assert!(
        !key.is_empty(),
        "sort_display_key should produce non-empty string for Seq"
    );
}
