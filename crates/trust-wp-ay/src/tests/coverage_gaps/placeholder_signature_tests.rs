// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort};

use super::*;

#[test]
#[timeout(30000)]
fn tuple_field_placeholder_reuses_name_without_domain_collision() {
    let mut encoder = AYEncoder::new();
    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);

    encoder
        .encode_pure(&logic_fn_call(&getter_name, vec![int(0)]))
        .expect("Int-domain tuple getter placeholder should encode");

    let tuple_expr = var_with_sort("pair", ExprSort::Tuple(2));
    encoder
        .encode_pure(&logic_fn_call(&getter_name, vec![tuple_expr]))
        .expect(
            "Tuple-domain tuple getter placeholder should not collide with Int-domain declaration",
        );

    let smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let matching_decl_names = encoder
        .decls()
        .logic_func_names()
        .filter(|name: &&String| name.starts_with(&format!("{smt_name}__placeholder_")))
        .collect::<Vec<_>>();
    assert_eq!(
        matching_decl_names.len(),
        2,
        "mixed-domain tuple getter placeholders should get distinct declaration keys: {matching_decl_names:?}"
    );
}

#[test]
#[timeout(30000)]
fn tuple_field_placeholder_inherits_logic_receiver_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let list_sort = ay_dpll::api::DatatypeSort {
        name: "List".to_string(),
        constructors: vec![ay_dpll::api::DatatypeConstructor {
            name: "Nil".to_string(),
            fields: vec![],
        }],
    };
    encoder.ensure_datatype_declared(&list_sort);

    let sum_name = trust_wp_core::logic::logic_fn_smt_name("sum");
    let sum_decl = encoder.solver.declare_fun(
        &sum_name,
        &[ay_dpll::api::Sort::Datatype(list_sort.clone())],
        ay_dpll::api::Sort::Int,
    );
    encoder
        .decls_for_test_mut()
        .insert_logic_func(sum_name, sum_decl);

    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);
    let receiver = logic_fn_call(
        &getter_name,
        vec![var_with_sort("pair", ExprSort::Tuple(2))],
    );
    let expr = method_call(receiver, "sum", vec![]);
    encoder
        .encode_pure(&expr)
        .expect("logic-method dispatch should encode tuple-field receiver with declared sort");

    let getter_smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let placeholder_decl = encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, _)| name.starts_with(&format!("{getter_smt_name}__placeholder_")))
        .map(|(_, decl)| decl)
        .expect("tuple getter placeholder should be declared");
    assert_eq!(
        placeholder_decl.range(),
        &ay_dpll::api::Sort::Datatype(list_sort),
        "tuple-field placeholder should inherit the outer logic fn receiver sort"
    );
}

#[test]
#[timeout(30000)]
fn registered_tuple_field_receiver_reuses_decl_without_placeholder() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let list_sort = ay_dpll::api::DatatypeSort {
        name: "List".to_string(),
        constructors: vec![ay_dpll::api::DatatypeConstructor {
            name: "Nil".to_string(),
            fields: vec![],
        }],
    };
    encoder.ensure_datatype_declared(&list_sort);

    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let getter_smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let getter_decl = encoder.solver.declare_fun(
        &getter_smt_name,
        &[ay_dpll::api::Sort::Int],
        ay_dpll::api::Sort::Datatype(list_sort.clone()),
    );
    encoder
        .decls_for_test_mut()
        .insert_logic_func(getter_smt_name.clone(), getter_decl);

    let sum_smt_name = trust_wp_core::logic::logic_fn_smt_name("sum");
    let sum_decl = encoder.solver.declare_fun(
        &sum_smt_name,
        &[ay_dpll::api::Sort::Datatype(list_sort.clone())],
        ay_dpll::api::Sort::Int,
    );
    encoder
        .decls_for_test_mut()
        .insert_logic_func(sum_smt_name, sum_decl);

    let receiver = logic_fn_call(&getter_name, vec![int(0)]);
    let method_expr = method_call(receiver.clone(), "sum", vec![]);
    let direct_expr = logic_fn_call("sum", vec![receiver]);

    let method_term = encoder
        .encode_pure(&method_expr)
        .expect("method dispatch should reuse the registered tuple-field receiver decl");
    let direct_term = encoder
        .encode_pure(&direct_expr)
        .expect("direct logic-fn call should reuse the same registered tuple-field receiver decl");

    let getter_placeholder_prefix = format!("{getter_smt_name}__placeholder_");
    assert!(
        !encoder
            .decls()
            .logic_func_names()
            .any(|name| name.starts_with(&getter_placeholder_prefix)),
        "registered tuple-field receiver should not create a placeholder decl: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );

    let neq = encoder.solver.neq(method_term, direct_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Unsat(_)),
        "method dispatch should encode the same term as a direct logic-fn call \
         when the structural receiver already has a registered declaration"
    );
}

#[test]
#[timeout(30000)]
fn tuple_field_equality_preseeds_non_int_placeholder_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);
    let token_sort = ExprSort::Datatype(intern_sort_name("crate::Token"));
    let expected_sort = encoder.sort_from_expr_sort(token_sort.clone());
    let expr = eq(
        logic_fn_call(
            &getter_name,
            vec![var_with_sort("pair", ExprSort::Tuple(2))],
        ),
        var_with_sort("token", token_sort),
    );

    let before = crate::encoder::unsoundness::snapshot();
    encoder
        .encode_pure(&expr)
        .expect("tuple-field equality should preseed a non-Int placeholder sort");
    let after = crate::encoder::unsoundness::snapshot();
    let delta = crate::encoder::unsoundness::delta(&before, &after);

    assert_eq!(
        delta.get(&crate::encoder::unsoundness::UnsoundnessCategory::SortFallbackToInt),
        None,
        "tuple-field equality should not fall back to Int when the peer sort is known: {delta:?}"
    );

    let getter_smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let placeholder_decl = encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, decl)| {
            name.starts_with(&format!("{getter_smt_name}__placeholder_"))
                && decl.domain() == [ay_dpll::api::Sort::Uninterpreted("Tuple2".to_string())]
        })
        .map(|(_, decl)| decl)
        .expect("tuple getter placeholder should be declared for Tuple2 receiver");
    assert_eq!(
        placeholder_decl.range(),
        &expected_sort,
        "tuple-field equality should seed the placeholder with the peer's non-Int sort"
    );
}

#[test]
#[timeout(30000)]
fn final_tuple_field_equality_preseeds_non_int_placeholder_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);
    let slot_sort = ExprSort::MutRef(Box::new(ExprSort::Datatype(intern_sort_name(
        "crate::Token",
    ))));
    let expected_sort = encoder.sort_from_expr_sort(slot_sort.clone());
    let expr = eq(
        final_expr(logic_fn_call(
            &getter_name,
            vec![var_with_sort("pair", ExprSort::Tuple(2))],
        )),
        var_with_sort("slot", slot_sort),
    );

    let before = crate::encoder::unsoundness::snapshot();
    encoder
        .encode_pure(&expr)
        .expect("final tuple-field equality should preseed a non-Int placeholder sort");
    let after = crate::encoder::unsoundness::snapshot();
    let delta = crate::encoder::unsoundness::delta(&before, &after);

    assert_eq!(
        delta.get(&crate::encoder::unsoundness::UnsoundnessCategory::SortFallbackToInt),
        None,
        "final tuple-field equality should not fall back to Int when the peer sort is known: {delta:?}"
    );

    let getter_smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let placeholder_decl = encoder
        .decls()
        .logic_funcs_iter()
        .find(|(name, decl)| {
            name.starts_with(&format!("{getter_smt_name}__placeholder_"))
                && decl.domain() == [ay_dpll::api::Sort::Uninterpreted("Tuple2".to_string())]
        })
        .map(|(_, decl)| decl)
        .expect("tuple getter placeholder should be declared for final Tuple2 receiver");
    assert_eq!(
        placeholder_decl.range(),
        &expected_sort,
        "final tuple-field equality should seed the placeholder with the peer's non-Int sort"
    );
}
