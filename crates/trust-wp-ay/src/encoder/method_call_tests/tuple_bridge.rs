// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn check_tuple_bridge_obligation(encoder: &mut AYEncoder) -> SolveResult {
    encoder.set_timeout(Some(std::time::Duration::from_millis(250)));
    encoder.check_sat()
}

fn unsat_or_unknown(result: &SolveResult) -> bool {
    matches!(result, SolveResult::Unsat(_) | SolveResult::Unknown)
}

#[test]
#[timeout(30000)]
fn tuple_get_on_registered_enum_uses_constructor_bridge_axioms() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_own_result_adt_decls());

    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    encoder
        .var_sorts_mut_for_test()
        .insert("self".to_string(), own_result_sort.clone());

    let tuple_get_term = encoder
        .encode_pure(&logic_fn_call("__trust_wp_tuple_get_0", vec![var("self")]))
        .expect("tuple_get_0 on registered OwnResult should encode through a constructor bridge");

    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "registered enum payload projection should not declare the bare tuple-get UF"
    );

    let self_term = *encoder
        .vars_for_test()
        .get("self")
        .expect("self should be declared");
    let datatype = match own_result_sort {
        Sort::Datatype(ref dt) => dt.clone(),
        other => panic!("expected registered OwnResult datatype sort, got {other:?}"),
    };
    let ok_payload = encoder.solver.int_const(7);
    let ok_term = encoder
        .solver
        .datatype_constructor(&datatype, "Ok", &[ok_payload]);
    let self_is_ok = encoder.solver.eq(self_term, ok_term);
    let expected_payload = encoder.solver.int_const(7);
    let not_payload = encoder.solver.neq(tuple_get_term, expected_payload);

    encoder.solver.assert_term(self_is_ok);
    encoder.solver.assert_term(not_payload);
    let result = check_tuple_bridge_obligation(&mut encoder);
    assert!(
        unsat_or_unknown(&result),
        "tuple_get_0(self) should equal the Ok payload under self == Ok(7), got {result:?}"
    );

    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_own_result_adt_decls());
    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    encoder
        .var_sorts_mut_for_test()
        .insert("self".to_string(), own_result_sort.clone());
    let tuple_get_term = encoder
        .encode_pure(&logic_fn_call("__trust_wp_tuple_get_0", vec![var("self")]))
        .expect("tuple_get_0 on registered OwnResult should encode through a constructor bridge");
    let self_term = *encoder
        .vars_for_test()
        .get("self")
        .expect("self should be declared");
    let datatype = match own_result_sort {
        Sort::Datatype(ref dt) => dt.clone(),
        other => panic!("expected registered OwnResult datatype sort, got {other:?}"),
    };
    let err_payload = encoder.solver.int_const(11);
    let err_term = encoder
        .solver
        .datatype_constructor(&datatype, "Err", &[err_payload]);
    let self_is_err = encoder.solver.eq(self_term, err_term);
    let expected_payload = encoder.solver.int_const(11);
    let not_payload = encoder.solver.neq(tuple_get_term, expected_payload);

    encoder.solver.assert_term(self_is_err);
    encoder.solver.assert_term(not_payload);
    let result = check_tuple_bridge_obligation(&mut encoder);
    assert!(
        unsat_or_unknown(&result),
        "tuple_get_0(self) should equal the Err payload under self == Err(11), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn tuple_get_on_registered_enum_reconstructs_native_constructor() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_own_result_adt_decls());

    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    encoder
        .var_sorts_mut_for_test()
        .insert("self".to_string(), own_result_sort.clone());

    let tuple_get_term = encoder
        .encode_pure(&logic_fn_call("__trust_wp_tuple_get_0", vec![var("self")]))
        .expect("tuple_get_0 on registered OwnResult should encode through a constructor bridge");

    let self_term = *encoder
        .vars_for_test()
        .get("self")
        .expect("self should be declared");
    let datatype = match own_result_sort {
        Sort::Datatype(ref dt) => dt.clone(),
        other => panic!("expected registered OwnResult datatype sort, got {other:?}"),
    };

    let is_ok = encoder
        .solver
        .try_datatype_tester("Ok", self_term)
        .expect("Ok tester should be available for OwnResult");
    let reconstructed_ok = encoder
        .solver
        .datatype_constructor(&datatype, "Ok", &[tuple_get_term]);
    let neq_ok = encoder.solver.neq(reconstructed_ok, self_term);

    encoder.solver.assert_term(is_ok);
    encoder.solver.assert_term(neq_ok);
    let result = check_tuple_bridge_obligation(&mut encoder);
    assert!(
        unsat_or_unknown(&result),
        "is_ok(self) should force Ok(tuple_get_0(self)) == self, got {result:?}"
    );

    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_own_result_adt_decls());

    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    encoder
        .var_sorts_mut_for_test()
        .insert("self".to_string(), own_result_sort.clone());

    let tuple_get_term = encoder
        .encode_pure(&logic_fn_call("__trust_wp_tuple_get_0", vec![var("self")]))
        .expect("tuple_get_0 on registered OwnResult should encode through a constructor bridge");

    let self_term = *encoder
        .vars_for_test()
        .get("self")
        .expect("self should be declared");
    let datatype = match own_result_sort {
        Sort::Datatype(ref dt) => dt.clone(),
        other => panic!("expected registered OwnResult datatype sort, got {other:?}"),
    };

    let is_err = encoder
        .solver
        .try_datatype_tester("Err", self_term)
        .expect("Err tester should be available for OwnResult");
    let reconstructed_err =
        encoder
            .solver
            .datatype_constructor(&datatype, "Err", &[tuple_get_term]);
    let neq_err = encoder.solver.neq(reconstructed_err, self_term);

    encoder.solver.assert_term(is_err);
    encoder.solver.assert_term(neq_err);
    let result = check_tuple_bridge_obligation(&mut encoder);
    assert!(
        unsat_or_unknown(&result),
        "is_err(self) should force Err(tuple_get_0(self)) == self, got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn tuple_get_uses_actual_receiver_sort_when_hint_is_stale_enum() {
    let mut encoder = AYEncoder::new_all();
    let mut adt_decls = sample_own_result_adt_decls();
    adt_decls.extend(sample_point_adt_decls());
    encoder.register_adt_decls(&adt_decls);

    let point_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::Point")));
    let stale_enum_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    let point_term = encoder
        .solver_mut()
        .declare_const("self", point_sort.clone());
    encoder
        .vars_mut_for_test()
        .insert("self".to_string(), point_term);
    encoder
        .var_sorts_mut_for_test()
        .insert("self".to_string(), stale_enum_sort);

    let tuple_get_term = encoder
        .encode_pure(&logic_fn_call("__trust_wp_tuple_get_0", vec![var("self")]))
        .expect("stale enum sort hint must not drive tuple-get projection");

    let (selector_name, selector_sort) = encoder
        .native_positional_field_selector(&point_sort, 0)
        .expect("Point field 0 should resolve to a native selector");
    let selector_term = encoder
        .solver
        .try_datatype_selector(&selector_name, point_term, selector_sort)
        .expect("Point selector should apply to the actual receiver sort");
    let neq = encoder.solver.neq(tuple_get_term, selector_term);

    encoder.solver.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "tuple_get_0 should follow the actual Point receiver sort, not the stale enum hint"
    );
}

#[test]
#[timeout(30000)]
fn tuple_get_reuses_sort_coercion_bridge_for_same_receiver() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_point_adt_decls());

    let point_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::Point")));
    let erased_term = encoder
        .solver_mut()
        .declare_const("x", Sort::Uninterpreted("Tuple1".to_string()));
    encoder
        .vars_mut_for_test()
        .insert("x".to_string(), erased_term);
    encoder
        .var_sorts_mut_for_test()
        .insert("x".to_string(), point_sort);

    let first = encoder
        .encode_pure(&logic_fn_call("__trust_wp_tuple_get_0", vec![var("x")]))
        .expect("first erased receiver projection should encode through a stable bridge");
    let second = encoder
        .encode_pure(&logic_fn_call("__trust_wp_tuple_get_0", vec![var("x")]))
        .expect("second erased receiver projection should reuse the stable bridge");

    assert_eq!(
        first, second,
        "repeated field accesses on the same erased receiver must share one datatype bridge"
    );
}

#[test]
#[timeout(30000)]
fn projected_var_on_registered_enum_receiver_uses_constructor_bridge_axioms() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_own_result_adt_decls());

    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    encoder
        .var_sorts_mut_for_test()
        .insert("self".to_string(), own_result_sort.clone());

    let projected_term = encoder
        .encode_pure(&var("self.0"))
        .expect("self.0 on registered OwnResult should encode through constructor bridge");

    assert!(
        !encoder.vars_for_test().contains_key("self.0"),
        "projected OwnResult payloads should not be declared as free vars"
    );
    assert!(
        !encoder.decls().has_spec_func("__trust_wp_tuple_get_0"),
        "projected OwnResult payloads should reuse the tuple-get bridge, not a bare UF"
    );

    let self_term = *encoder
        .vars_for_test()
        .get("self")
        .expect("self should be declared");
    let datatype = match own_result_sort {
        Sort::Datatype(ref dt) => dt.clone(),
        other => panic!("expected registered OwnResult datatype sort, got {other:?}"),
    };
    let ok_payload = encoder.solver.int_const(7);
    let ok_term = encoder
        .solver
        .datatype_constructor(&datatype, "Ok", &[ok_payload]);
    let self_is_ok = encoder.solver.eq(self_term, ok_term);
    let expected_payload = encoder.solver.int_const(7);
    let not_payload = encoder.solver.neq(projected_term, expected_payload);

    encoder.solver.assert_term(self_is_ok);
    encoder.solver.assert_term(not_payload);
    let result = check_tuple_bridge_obligation(&mut encoder);
    assert!(
        unsat_or_unknown(&result),
        "self.0 should equal the Ok payload under self == Ok(7), got {result:?}"
    );

    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_own_result_adt_decls());
    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    encoder
        .var_sorts_mut_for_test()
        .insert("self".to_string(), own_result_sort.clone());
    let projected_term = encoder
        .encode_pure(&var("self.0"))
        .expect("self.0 on registered OwnResult should encode through constructor bridge");
    let self_term = *encoder
        .vars_for_test()
        .get("self")
        .expect("self should be declared");
    let datatype = match own_result_sort {
        Sort::Datatype(ref dt) => dt.clone(),
        other => panic!("expected registered OwnResult datatype sort, got {other:?}"),
    };
    let err_payload = encoder.solver.int_const(11);
    let err_term = encoder
        .solver
        .datatype_constructor(&datatype, "Err", &[err_payload]);
    let self_is_err = encoder.solver.eq(self_term, err_term);
    let expected_payload = encoder.solver.int_const(11);
    let not_payload = encoder.solver.neq(projected_term, expected_payload);

    encoder.solver.assert_term(self_is_err);
    encoder.solver.assert_term(not_payload);
    let result = check_tuple_bridge_obligation(&mut encoder);
    assert!(
        unsat_or_unknown(&result),
        "self.0 should equal the Err payload under self == Err(11), got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn projected_var_on_registered_enum_reconstructs_native_constructor() {
    let mut encoder = AYEncoder::new_all();
    encoder.register_adt_decls(&sample_own_result_adt_decls());

    let own_result_sort =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::OwnResult")));
    encoder
        .var_sorts_mut_for_test()
        .insert("self".to_string(), own_result_sort.clone());

    let projected_term = encoder
        .encode_pure(&var("self.0"))
        .expect("self.0 on registered OwnResult should encode through constructor bridge");

    let self_term = *encoder
        .vars_for_test()
        .get("self")
        .expect("self should be declared");
    let datatype = match own_result_sort {
        Sort::Datatype(ref dt) => dt.clone(),
        other => panic!("expected registered OwnResult datatype sort, got {other:?}"),
    };
    let is_ok = encoder
        .solver
        .try_datatype_tester("Ok", self_term)
        .expect("Ok tester should be available for OwnResult");
    let reconstructed = encoder
        .solver
        .datatype_constructor(&datatype, "Ok", &[projected_term]);
    let neq = encoder.solver.neq(reconstructed, self_term);

    encoder.solver.assert_term(is_ok);
    encoder.solver.assert_term(neq);
    let result = check_tuple_bridge_obligation(&mut encoder);
    assert!(
        unsat_or_unknown(&result),
        "is_ok(self) should force Ok(self.0) == self for registered enum projections, got {result:?}"
    );
}
