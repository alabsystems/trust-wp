// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(30000)]
fn encode_int_method_uf_declares_and_reuses_symbol() {
    let mut encoder = AYEncoder::new();

    let term1 = encoder
        .encode_int_method_uf(&var("x"), "deep_model", &[], None)
        .expect("first deep_model UF call should encode");
    assert!(
        encoder.decls.has_logic_func("method_deep_model_1_i"),
        "Int receiver should declare method_deep_model_1_i"
    );

    let decl_count = encoder.decls.logic_func_count();
    let term2 = encoder
        .encode_int_method_uf(&var("x"), "deep_model", &[], None)
        .expect("second deep_model UF call should reuse declaration");
    assert_eq!(
        encoder.decls.logic_func_count(),
        decl_count,
        "repeated int-method UF calls should not redeclare symbols"
    );

    // Same UF application must be equal to itself.
    let neq = encoder.solver.neq(term1, term2);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "identical UF applications must be equal"
    );
}

#[test]
#[timeout(30000)]
fn encode_int_method_uf_uses_sort_tags_in_symbol_name() {
    let mut encoder = AYEncoder::new();

    let term = encoder
        .encode_int_method_uf(&bool_expr(true), "id", &[int(1)], None)
        .expect("bool/int UF signature should encode");
    assert!(
        encoder.decls.has_logic_func("method_id_2_b_i"),
        "Bool receiver + Int arg should declare method_id_2_b_i"
    );

    let zero = encoder.solver.int_const(0);
    let eq_zero = encoder.solver.eq(term, zero);
    encoder.assert_term(eq_zero);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Int-returning UF result should be usable in Int equalities"
    );
}

/// Unknown methods (not in dispatch table, not registered logic functions)
/// return `EncodingError::Unsupported` outside quantifier scopes (#1820).
/// Inside quantifier scopes, they are encoded as Int UFs to support
/// abstract method calls in ghost postconditions.
#[test]
#[timeout(30000)]
fn unknown_method_returns_encoding_error() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("x"), "totally_unknown", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "unknown method should error, got: {result:?}"
    );
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("totally_unknown"),
        "error should name the method: {msg}"
    );
    assert!(
        msg.contains("unknown method"),
        "error should indicate it is an unknown method: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn infer_encoded_sort_recurses_through_wrapped_seq_annotations() {
    let encoder = AYEncoder::new();
    let expr = final_expr(var_with_sort(
        "v",
        ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name(
            "std::vec::Vec",
        )))),
    ));

    let sort = encoder.infer_encoded_sort(&expr, None);
    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "Final(Var(_, Ref(Datatype(Vec)))) should preserve Seq sort, got {sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn infer_encoded_sort_keeps_non_seq_ref_datatypes_out_of_seq_fast_path() {
    let encoder = AYEncoder::new();
    let expr = final_expr(var_with_sort(
        "v",
        ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name("MyStruct")))),
    ));

    let sort = encoder.infer_encoded_sort(&expr, None);
    assert_eq!(
        sort,
        Sort::Uninterpreted("MyStruct".to_string()),
        "non-Seq Ref(Datatype(_)) annotations must not be rewritten to Seq, got {sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn infer_encoded_sort_recognizes_registered_nullary_constructor_var() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtKind};

    let mut encoder = AYEncoder::new();
    encoder.register_adt_decls(&std::collections::HashMap::from([(
        "State".to_string(),
        AdtDecl::new(
            "crate::State".to_string(),
            "State".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new("On".to_string(), "On".to_string(), vec![]),
                AdtConstructorDecl::new("Off".to_string(), "Off".to_string(), vec![]),
            ],
        ),
    )]));

    let sort = encoder.infer_encoded_sort(&var("On"), None);
    assert!(
        matches!(sort, Sort::Datatype(ref dt) if dt.name == "State"),
        "bare registered nullary constructor should infer as State datatype, got {sort:?}"
    );
}

#[test]
#[timeout(30000)]
fn infer_encoded_sort_composes_final_old_view_fallbacks() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v_view".to_string(), ExprSort::Seq);

    let expr = old(view(final_expr(var("v"))));
    let sort = encoder.infer_encoded_sort(&expr, None);

    assert_eq!(
        sort,
        Sort::seq(Sort::Int),
        "final_old_v_view should fall back through old_v_view to v_view"
    );
}

#[test]
#[timeout(30000)]
fn old_tuple_get_on_registered_struct_uses_native_selector_fallback() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_point_adt_decls());

    let point_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::Point")));
    encoder
        .var_sorts_mut_for_test()
        .insert("p".to_string(), point_sort);

    let tuple_get_expr = old(logic_fn_call("__trust_wp_tuple_get_0", vec![var("p")]));
    let tuple_get_term = encoder
        .encode_pure(&tuple_get_expr)
        .expect("old tuple_get_0 on Point should encode through a native selector");

    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "old tuple_get_0(Point) should not declare the bare tuple-get UF"
    );

    let old_p = *encoder
        .vars_for_test()
        .get("old_p")
        .expect("old_p should be declared in the old() context");
    let receiver_sort = encoder.solver.get_sort(old_p);
    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("field 0 on old Point should resolve to a native selector");
    let selector_term = encoder
        .solver
        .try_datatype_selector(&selector_name, old_p, selector_sort)
        .expect("native selector application should succeed");

    let eq = encoder.solver.eq(tuple_get_term, selector_term);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "old tuple_get_0(Point) should equal the native selector term"
    );
}

#[test]
#[timeout(30000)]
fn old_tuple_get_on_registered_struct_uses_sort_hint_fallback() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_point_adt_decls());
    encoder.record_sort_hint(
        "p".to_string(),
        ExprSort::Datatype(intern_sort_name("crate::Point")),
    );

    let tuple_get_expr = old(logic_fn_call("__trust_wp_tuple_get_0", vec![var("p")]));
    let tuple_get_term = encoder
        .encode_pure(&tuple_get_expr)
        .expect("old tuple_get_0 on hinted Point should encode through a native selector");

    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "old tuple_get_0(Point) with only a sort hint should not declare the bare tuple-get UF"
    );

    let old_p = *encoder
        .vars_for_test()
        .get("old_p")
        .expect("old_p should be declared in the old() context");
    let receiver_sort = encoder.solver.get_sort(old_p);
    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("field 0 on old hinted Point should resolve to a native selector");
    let selector_term = encoder
        .solver
        .try_datatype_selector(&selector_name, old_p, selector_sort)
        .expect("native selector application should succeed");

    let eq = encoder.solver.eq(tuple_get_term, selector_term);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "old tuple_get_0(Point) with only a sort hint should equal the native selector term"
    );
}

#[test]
#[timeout(30000)]
fn final_tuple_get_on_registered_struct_uses_native_selector_fallback() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_point_adt_decls());

    let point_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::Point")));
    encoder
        .var_sorts_mut_for_test()
        .insert("p_final".to_string(), point_sort);

    let tuple_get_expr = final_expr(logic_fn_call("__trust_wp_tuple_get_0", vec![var("p")]));
    let tuple_get_term = encoder
        .encode_pure(&tuple_get_expr)
        .expect("final tuple_get_0 on Point should encode through a native selector");

    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "final tuple_get_0(Point) should not declare the bare tuple-get UF"
    );

    let p_final = *encoder
        .vars_for_test()
        .get("p_final")
        .expect("p_final should be declared in the final() context");
    let receiver_sort = encoder.solver.get_sort(p_final);
    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("field 0 on final Point should resolve to a native selector");
    let selector_term = encoder
        .solver
        .try_datatype_selector(&selector_name, p_final, selector_sort)
        .expect("native selector application should succeed");

    let eq = encoder.solver.eq(tuple_get_term, selector_term);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "final tuple_get_0(Point) should equal the native selector term"
    );
}

#[test]
#[timeout(30000)]
fn annotated_tuple_get_on_registered_struct_uses_native_selector_fallback() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_point_adt_decls());

    let tuple_get_expr = logic_fn_call(
        "__trust_wp_tuple_get_0",
        vec![var_with_sort(
            "p",
            ExprSort::Datatype(intern_sort_name("crate::Point")),
        )],
    );
    let tuple_get_term = encoder
        .encode_pure(&tuple_get_expr)
        .expect("tuple_get_0 on annotated Point should encode through a native selector");

    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "annotated tuple_get_0(Point) should not declare the bare tuple-get UF"
    );

    let p = *encoder
        .vars_for_test()
        .get("p")
        .expect("p should be declared");
    let receiver_sort = encoder.solver.get_sort(p);
    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("field 0 on annotated Point should resolve to a native selector");
    let selector_term = encoder
        .solver
        .try_datatype_selector(&selector_name, p, selector_sort)
        .expect("native selector application should succeed");

    let eq = encoder.solver.eq(tuple_get_term, selector_term);
    let neq = encoder.solver.not(eq);
    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "annotated tuple_get_0(Point) should equal the native selector term"
    );
}

#[test]
#[timeout(30000)]
fn struct_field_placeholders_alias_named_and_positional_accessors() {
    let mut encoder = AYEncoder::new_all();
    let adt_decls = sample_point_adt_decls();
    encoder.register_adt_decls(&adt_decls);

    let point_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::Point")));
    let named_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_field_x");
    let tuple_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let named_key =
        AYEncoder::placeholder_smt_name(&named_smt, std::slice::from_ref(&point_sort), &Sort::Int);
    let tuple_key =
        AYEncoder::placeholder_smt_name(&tuple_smt, std::slice::from_ref(&point_sort), &Sort::Int);

    let named_decl =
        encoder.get_or_declare_logic_func(&named_key, std::slice::from_ref(&point_sort), Sort::Int);
    let tuple_decl =
        encoder.get_or_declare_logic_func(&tuple_key, std::slice::from_ref(&point_sort), Sort::Int);
    encoder.assert_tuple_axioms();

    let point = encoder.solver_mut().declare_const("p", point_sort);
    let named = encoder.solver_mut().apply(&named_decl, &[point]);
    let tuple = encoder.solver_mut().apply(&tuple_decl, &[point]);
    let eq = encoder.solver_mut().eq(named, tuple);
    let neq = encoder.solver_mut().not(eq);
    encoder.solver_mut().assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "named and positional placeholders for the same registered struct field must be aliased"
    );
}

#[test]
#[timeout(30000)]
fn struct_field_ground_aliases_link_observed_named_and_positional_accessors() {
    let mut encoder = AYEncoder::new_all();
    let adt_decls = sample_point_adt_decls();
    encoder.register_adt_decls(&adt_decls);

    let point_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::Point")));
    let named_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_field_x");
    let tuple_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let named_key =
        AYEncoder::placeholder_smt_name(&named_smt, std::slice::from_ref(&point_sort), &Sort::Int);
    let tuple_key =
        AYEncoder::placeholder_smt_name(&tuple_smt, std::slice::from_ref(&point_sort), &Sort::Int);

    let named_decl =
        encoder.get_or_declare_logic_func(&named_key, std::slice::from_ref(&point_sort), Sort::Int);
    let tuple_decl =
        encoder.get_or_declare_logic_func(&tuple_key, std::slice::from_ref(&point_sort), Sort::Int);
    let point = encoder.solver_mut().declare_const("p", point_sort);
    let named = encoder.solver_mut().apply(&named_decl, &[point]);
    let tuple = encoder.solver_mut().apply(&tuple_decl, &[point]);

    encoder
        .ground_pool_for_test_mut()
        .register(&named_smt, named, vec![point], vec![var("p")]);
    encoder
        .ground_pool_for_test_mut()
        .register(&tuple_smt, tuple, vec![point], vec![var("p")]);

    assert!(
        encoder.assert_struct_field_placeholder_ground_aliases() >= 1,
        "observed struct field placeholders should emit a ground alias"
    );

    let neq = encoder.solver_mut().neq(named, tuple);
    encoder.solver_mut().assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "ground aliases must connect named and positional placeholders"
    );
}

#[test]
#[timeout(30000)]
fn struct_field_ground_aliases_link_seq_len_proxies_for_sequence_fields() {
    let mut encoder = AYEncoder::new_all();
    let adt_decls = sample_bucket_map_adt_decls();
    encoder.register_adt_decls(&adt_decls);

    let map_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::BucketMap")));
    let seq_sort = Sort::seq(Sort::Int);
    let named_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_field_buckets");
    let tuple_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let named_key =
        AYEncoder::placeholder_smt_name(&named_smt, std::slice::from_ref(&map_sort), &seq_sort);
    let tuple_key =
        AYEncoder::placeholder_smt_name(&tuple_smt, std::slice::from_ref(&map_sort), &seq_sort);

    let named_decl = encoder.get_or_declare_logic_func(
        &named_key,
        std::slice::from_ref(&map_sort),
        seq_sort.clone(),
    );
    let tuple_decl =
        encoder.get_or_declare_logic_func(&tuple_key, std::slice::from_ref(&map_sort), seq_sort);
    let map = encoder.solver_mut().declare_const("m", map_sort);
    let named = encoder.solver_mut().apply(&named_decl, &[map]);
    let tuple = encoder.solver_mut().apply(&tuple_decl, &[map]);
    let named_len = encoder.seq_len_term(named).expect("len(named buckets)");
    let tuple_len = encoder.seq_len_term(tuple).expect("len(tuple buckets)");

    encoder
        .ground_pool_for_test_mut()
        .register(&named_smt, named, vec![map], vec![var("m")]);
    encoder
        .ground_pool_for_test_mut()
        .register(&tuple_smt, tuple, vec![map], vec![var("m")]);

    assert!(
        encoder.assert_struct_field_placeholder_ground_aliases() >= 2,
        "observed sequence field placeholders should emit value and length aliases"
    );

    let neq_len = encoder.solver_mut().neq(named_len, tuple_len);
    encoder.solver_mut().assert_term(neq_len);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "seq_len proxies for aliased struct fields must be equal"
    );
}

#[test]
#[timeout(30000)]
fn struct_field_ground_aliases_include_applications_seen_through_placeholder_encoding() {
    let mut encoder = AYEncoder::new_all();
    let adt_decls = sample_bucket_map_adt_decls();
    encoder.register_adt_decls(&adt_decls);

    let map_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::BucketMap")));
    let named_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_field_buckets");
    let tuple_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    encoder.record_sort_hint(named_smt, ExprSort::Seq);
    encoder.record_sort_hint(tuple_smt, ExprSort::Seq);
    let map = encoder.solver_mut().declare_const("m_encoded", map_sort);
    let tuple = encoder
        .apply_logic_fn(
            "__trust_wp_tuple_get_0",
            &[map],
            Some(&[var("m_encoded")]),
            None,
        )
        .expect("tuple field placeholder");
    let named = encoder
        .apply_logic_fn(
            "__trust_wp_field_buckets",
            &[map],
            Some(&[var("m_encoded")]),
            None,
        )
        .expect("named field placeholder");
    let tuple_len = encoder.seq_len_term(tuple).expect("len(tuple buckets)");
    let named_len = encoder.seq_len_term(named).expect("len(named buckets)");

    assert!(
        encoder.assert_struct_field_placeholder_ground_aliases() >= 2,
        "encoded struct field placeholders should be remembered for the final ground alias pass"
    );

    let neq = encoder.solver_mut().neq(tuple, named);
    encoder.solver_mut().assert_term(neq);
    let neq_len = encoder.solver_mut().neq(tuple_len, named_len);
    encoder.solver_mut().assert_term(neq_len);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "remembered placeholder applications should connect sequence field values and len proxies"
    );
}

#[test]
#[timeout(30000)]
fn struct_field_ground_aliases_instantiate_for_known_struct_receivers() {
    let mut encoder = AYEncoder::new_all();
    let adt_decls = sample_bucket_map_adt_decls();
    encoder.register_adt_decls(&adt_decls);

    let map_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::BucketMap")));
    let seq_sort = Sort::seq(Sort::Int);
    let named_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_field_buckets");
    let tuple_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let named_key =
        AYEncoder::placeholder_smt_name(&named_smt, std::slice::from_ref(&map_sort), &seq_sort);
    let tuple_key =
        AYEncoder::placeholder_smt_name(&tuple_smt, std::slice::from_ref(&map_sort), &seq_sort);

    let named_decl = encoder.get_or_declare_logic_func(
        &named_key,
        std::slice::from_ref(&map_sort),
        seq_sort.clone(),
    );
    let tuple_decl =
        encoder.get_or_declare_logic_func(&tuple_key, std::slice::from_ref(&map_sort), seq_sort);
    let map = encoder.solver_mut().declare_const("m_receiver", map_sort);
    encoder.insert_var("m_receiver".to_string(), map);

    assert!(
        encoder.assert_struct_field_placeholder_ground_aliases() >= 2,
        "known struct receivers should force concrete field value and length aliases"
    );

    let named = encoder.solver_mut().apply(&named_decl, &[map]);
    let tuple = encoder.solver_mut().apply(&tuple_decl, &[map]);
    let named_len = encoder.seq_len_term(named).expect("len(named buckets)");
    let tuple_len = encoder.seq_len_term(tuple).expect("len(tuple buckets)");
    let neq = encoder.solver_mut().neq(named, tuple);
    encoder.solver_mut().assert_term(neq);
    let neq_len = encoder.solver_mut().neq(named_len, tuple_len);
    encoder.solver_mut().assert_term(neq_len);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "receiver-instantiated aliases should connect field placeholders and len proxies"
    );
}

#[test]
#[timeout(30000)]
fn struct_field_ground_alias_uses_actual_receiver_sort_when_param_hint_is_stale() {
    let mut encoder = AYEncoder::new_all();
    let adt_decls = sample_point_adt_decls();
    encoder.register_adt_decls(&adt_decls);

    let point_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::Point")));
    let named_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_field_x");
    let tuple_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let named_key =
        AYEncoder::placeholder_smt_name(&named_smt, std::slice::from_ref(&point_sort), &Sort::Int);
    let tuple_key =
        AYEncoder::placeholder_smt_name(&tuple_smt, std::slice::from_ref(&point_sort), &Sort::Int);

    let named_decl =
        encoder.get_or_declare_logic_func(&named_key, std::slice::from_ref(&point_sort), Sort::Int);
    let tuple_decl =
        encoder.get_or_declare_logic_func(&tuple_key, std::slice::from_ref(&point_sort), Sort::Int);
    let point = encoder.solver_mut().declare_const("p", point_sort);
    let named = encoder.solver_mut().apply(&named_decl, &[point]);
    let tuple = encoder.solver_mut().apply(&tuple_decl, &[point]);

    encoder.assert_ground_struct_field_placeholder_aliases_for_accessor_call(
        "__trust_wp_field_x",
        &[Sort::Int],
        &[point],
        named,
    );

    let neq = encoder.solver_mut().neq(named, tuple);
    encoder.solver_mut().assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "ground aliasing must use the actual SMT receiver sort when source hints are stale"
    );
}

#[test]
#[timeout(30000)]
fn struct_field_ground_alias_uses_actual_receiver_sort_without_param_hint() {
    let mut encoder = AYEncoder::new_all();
    let adt_decls = sample_bucket_map_adt_decls();
    encoder.register_adt_decls(&adt_decls);

    let map_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::BucketMap")));
    let seq_sort = Sort::seq(Sort::Int);
    let named_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_field_buckets");
    let tuple_smt = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple_get_0");
    let named_key =
        AYEncoder::placeholder_smt_name(&named_smt, std::slice::from_ref(&map_sort), &seq_sort);
    let tuple_key =
        AYEncoder::placeholder_smt_name(&tuple_smt, std::slice::from_ref(&map_sort), &seq_sort);

    let named_decl = encoder.get_or_declare_logic_func(
        &named_key,
        std::slice::from_ref(&map_sort),
        seq_sort.clone(),
    );
    let tuple_decl =
        encoder.get_or_declare_logic_func(&tuple_key, std::slice::from_ref(&map_sort), seq_sort);
    let map = encoder.solver_mut().declare_const("m_no_hint", map_sort);
    let named = encoder.solver_mut().apply(&named_decl, &[map]);
    let tuple = encoder.solver_mut().apply(&tuple_decl, &[map]);
    let named_len = encoder.seq_len_term(named).expect("len(named buckets)");
    let tuple_len = encoder.seq_len_term(tuple).expect("len(tuple buckets)");

    encoder.assert_ground_struct_field_placeholder_aliases_for_accessor_call(
        "__trust_wp_field_buckets",
        &[],
        &[map],
        named,
    );

    let neq = encoder.solver_mut().neq(named, tuple);
    encoder.solver_mut().assert_term(neq);
    let neq_len = encoder.solver_mut().neq(named_len, tuple_len);
    encoder.solver_mut().assert_term(neq_len);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "actual receiver sort should recover struct field aliases even without source param hints"
    );
}

#[test]
#[timeout(30000)]
fn native_positional_selector_uses_declared_datatype_sort_when_adt_metadata_drifts() {
    let mut encoder = AYEncoder::new_all();

    let node_dt = DatatypeSort {
        name: "Node".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Node".to_string(),
            fields: vec![DatatypeField {
                name: "node_value".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    let list_dt = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "List".to_string(),
            fields: vec![DatatypeField {
                name: "list_head".to_string(),
                sort: Sort::Datatype(node_dt.clone()),
            }],
        }],
    };

    encoder.ensure_datatype_declared(&node_dt);
    encoder.ensure_datatype_declared(&list_dt);
    encoder.register_adt_decls(&drifted_list_adt_decls());

    let list = encoder
        .solver_mut()
        .declare_const("list", Sort::Datatype(list_dt.clone()));
    let receiver_sort = encoder.solver_mut().get_sort(list);
    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("field 0 on List should resolve to a native selector");

    assert_eq!(selector_name, "list_head");
    assert_eq!(selector_sort, Sort::Datatype(node_dt.clone()));

    encoder
        .solver_mut()
        .try_datatype_selector(&selector_name, list, selector_sort)
        .expect("selector sort must stay aligned with the declared datatype");
}

#[test]
#[timeout(30000)]
fn infer_encoded_sort_uses_declared_seq_param_logic_fn_range_without_demotion() {
    use trust_wp_core::logic::logic_fn_smt_name;

    let mut encoder = AYEncoder::new();
    let smt_name = logic_fn_smt_name("num_of_pos");
    encoder.get_or_declare_logic_func(
        &smt_name,
        &[Sort::Int, Sort::Int, Sort::seq(Sort::Int)],
        Sort::Int,
    );

    unsoundness::reset();
    let before = unsoundness::snapshot();
    let call = logic_fn_call("num_of_pos", vec![int(0), var("i"), view(var("values"))]);

    assert_eq!(encoder.infer_encoded_sort(&call, None), Sort::Int);
    let delta = unsoundness::delta(&before, &unsoundness::snapshot());
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "a declared logic function must not use the unknown-function Int fallback: {delta:?}"
    );
    unsoundness::reset();
}

#[test]
#[timeout(30000)]
fn infer_encoded_sort_uses_declared_bool_logic_fn_range_without_demotion() {
    use trust_wp_core::logic::logic_fn_smt_name;

    let mut encoder = AYEncoder::new();
    let smt_name = logic_fn_smt_name("is_sorted_pred");
    encoder.get_or_declare_logic_func(&smt_name, &[Sort::seq(Sort::Int)], Sort::Bool);

    unsoundness::reset();
    let before = unsoundness::snapshot();
    let call = logic_fn_call("is_sorted_pred", vec![view(var("values"))]);

    assert_eq!(encoder.infer_encoded_sort(&call, None), Sort::Bool);
    let delta = unsoundness::delta(&before, &unsoundness::snapshot());
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "a declared Bool function must not use the unknown-function Int fallback: {delta:?}"
    );
    unsoundness::reset();
}

/// A path-qualified opaque field type (std `std::sync::Mutex` inside the
/// user's `MutexInner`) that merely SHARES a bare name with a sibling user
/// ADT (`Mutex`) must not (a) manufacture a spurious dependency cycle in the
/// dependency-first declare order, nor (b) register the user ADT's name as an
/// opaque sort before its own declare-datatype runs. Pre-fix, both happened:
/// the Kahn order deadlocked into the name-order fallback and the user's
/// `Mutex`/`MutexGuard` declares collided with their opaque twins, killing
/// every selector lookup in the VC (#2706 residual,
/// tests/should_succeed/mutex.rs).
#[test]
#[timeout(30000)]
fn shared_bare_name_std_field_does_not_block_sibling_user_adt_declaration() {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let mut encoder = AYEncoder::new_all();

    let adt_decls: trust_wp_core::logic::AdtDecls = std::collections::HashMap::from([
        (
            "Mutex".to_string(),
            AdtDecl::new(
                "Mutex".to_string(),
                "Mutex".to_string(),
                AdtKind::Struct,
                vec![AdtConstructorDecl::new(
                    "Mutex".to_string(),
                    "Mutex".to_string(),
                    vec![AdtFieldDecl::new(
                        "0".to_string(),
                        ExprSort::Datatype(intern_sort_name("MutexInner")),
                    )],
                )],
            ),
        ),
        (
            "MutexInner".to_string(),
            AdtDecl::new(
                "MutexInner".to_string(),
                "MutexInner".to_string(),
                AdtKind::Struct,
                vec![AdtConstructorDecl::new(
                    "MutexInner".to_string(),
                    "MutexInner".to_string(),
                    vec![AdtFieldDecl::new(
                        "0".to_string(),
                        ExprSort::Datatype(intern_sort_name("std::sync::Mutex")),
                    )],
                )],
            ),
        ),
    ]);

    encoder.register_adt_decls(&adt_decls);

    assert!(
        encoder.has_datatype_decl("MutexInner"),
        "MutexInner must declare natively (its std field is a distinct opaque type)"
    );
    assert!(
        encoder.has_datatype_decl("Mutex"),
        "the user Mutex must declare natively — the std::sync::Mutex opaque \
         field inside MutexInner must not squat on its sort name"
    );

    // The user's Mutex field 0 must resolve to the declared MutexInner
    // datatype, giving native selectors.
    let mutex_dt = encoder
        .get_datatype_decl("Mutex")
        .expect("declared above")
        .clone();
    let receiver_sort = Sort::Datatype(mutex_dt);
    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&receiver_sort, 0)
        .expect("field 0 on the user Mutex should resolve to a native selector");
    assert_eq!(selector_name, "mutex_0");
    assert!(
        matches!(&selector_sort, Sort::Datatype(dt) if dt.name == "MutexInner"),
        "selector sort should be the declared MutexInner datatype, got {selector_sort:?}"
    );
}

/// `infer_encoded_sort`'s memo is keyed by the ADDRESS of the `PureExpr` node.
/// A memo that outlives the node is a use-after-free oracle: the allocator
/// hands the freed address to the next `PureExpr`, which then inherits the dead
/// node's sort. This pins that the memo cannot survive the call.
///
/// The loop allocates a Bool-inferring node, infers it (which is what would
/// populate a surviving memo), drops it, then immediately allocates an
/// Int-inferring node of the same size class — the allocator returns the same
/// block with overwhelming probability. Every iteration must still infer `Int`.
///
/// Regression: `fmap_indexing`'s pristine-main flap. An `FMap` payload `lookup`
/// inherited `Sort::Bool` from a dead node, which rerouted every later
/// `<recv>.lookup(k)` through the Bool-context operand path and replaced the
/// Int payload with `lookup(recv, k) != 0`, fabricating `payload ∈ {0, 1}`
/// premises that contradicted the faithfully encoded copy of the same frame
/// law (base UNSAT -> fail-closed "vacuous proof").
#[test]
#[timeout(30000)]
fn infer_encoded_sort_memo_never_outlives_the_expression_it_keyed_on() {
    let encoder = AYEncoder::new();

    for iteration in 0..256 {
        // Populate whatever memo exists for THIS address with `Bool`, then free
        // the node so the address becomes available for reuse.
        let poisoner: Box<PureExpr> = Box::new(bool_expr(true));
        assert_eq!(
            encoder.infer_encoded_sort(&poisoner, None),
            Sort::Bool,
            "sanity: a Bool literal infers Bool"
        );
        drop(poisoner);

        // Same size class, so the allocator very likely reuses the block.
        let reuser: Box<PureExpr> = Box::new(int(2));
        assert_eq!(
            encoder.infer_encoded_sort(&reuser, None),
            Sort::Int,
            "iteration {iteration}: an Int literal must infer Int — a stale \
             address-keyed memo entry must never answer for a different node"
        );
        drop(reuser);
    }
}
