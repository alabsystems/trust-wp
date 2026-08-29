// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// `*(tuple_get_0(t))` should rewrite to `tuple_get_0(*t)` so tuple axioms apply.
#[test]
#[timeout(30000)]
fn test_deref_of_logic_fn_call_pushes_deref_inward() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    let deref_outer = deref(logic_fn_call(&tuple_field_logic_fn_name(0), vec![var("t")]));
    let term = encoder
        .encode_pure(&deref_outer)
        .expect("*(tuple_get_0(t)) should encode");

    let pushed_in = logic_fn_call(&tuple_field_logic_fn_name(0), vec![deref(var("t"))]);
    let term_direct = encoder
        .encode_pure(&pushed_in)
        .expect("tuple_get_0(*t) should encode");

    let eq = encoder.solver_mut().eq(term, term_direct);
    let neg_eq = encoder.solver_mut().not(eq);
    encoder.assert_term(neg_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "*(tuple_get_0(t)) must equal tuple_get_0(*t)"
    );
}

/// `^(tuple_get_0(t))` should rewrite to `tuple_get_0(^t)`.
#[test]
#[timeout(30000)]
fn test_final_of_logic_fn_call_pushes_final_inward() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    let final_outer = final_expr(logic_fn_call(&tuple_field_logic_fn_name(0), vec![var("t")]));
    let term = encoder
        .encode_pure(&final_outer)
        .expect("^(tuple_get_0(t)) should encode");

    let pushed_in = logic_fn_call(&tuple_field_logic_fn_name(0), vec![final_expr(var("t"))]);
    let term_direct = encoder
        .encode_pure(&pushed_in)
        .expect("tuple_get_0(^t) should encode");

    let eq = encoder.solver_mut().eq(term, term_direct);
    let neg_eq = encoder.solver_mut().not(eq);
    encoder.assert_term(neg_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "^(tuple_get_0(t)) must equal tuple_get_0(^t)"
    );
}

/// `*(v.len())` should rewrite to `(*v).len()`.
#[test]
#[timeout(30000)]
fn test_deref_of_method_call_pushes_deref_into_receiver() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let deref_outer = deref(method_call(var("v"), "len", vec![]));
    let term = encoder
        .encode_pure(&deref_outer)
        .expect("*(v.len()) should encode");

    let pushed_in = method_call(deref(var("v")), "len", vec![]);
    let term_direct = encoder
        .encode_pure(&pushed_in)
        .expect("(*v).len() should encode");

    let eq = encoder.solver_mut().eq(term, term_direct);
    let neg_eq = encoder.solver_mut().not(eq);
    encoder.assert_term(neg_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "*(v.len()) must equal (*v).len()"
    );
}

/// `^(v.len())` should rewrite to `(^v).len()`.
#[test]
#[timeout(30000)]
fn test_final_of_method_call_pushes_final_into_receiver() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let final_outer = final_expr(method_call(var("v"), "len", vec![]));
    let term = encoder
        .encode_pure(&final_outer)
        .expect("^(v.len()) should encode");

    let pushed_in = method_call(final_expr(var("v")), "len", vec![]);
    let term_direct = encoder
        .encode_pure(&pushed_in)
        .expect("(^v).len() should encode");

    let eq = encoder.solver_mut().eq(term, term_direct);
    let neg_eq = encoder.solver_mut().not(eq);
    encoder.assert_term(neg_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "^(v.len()) must equal (^v).len()"
    );
}

/// `*(v@)` should rewrite to `(*v)@`.
#[test]
#[timeout(30000)]
fn test_deref_of_view_pushes_deref_inside() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let deref_view = deref(view(var("rc")));
    let term = encoder
        .encode_pure(&deref_view)
        .expect("*(rc@) should encode");

    let view_deref = view(deref(var("rc")));
    let term_direct = encoder
        .encode_pure(&view_deref)
        .expect("(*rc)@ should encode");

    let eq = encoder.solver_mut().eq(term, term_direct);
    let neg_eq = encoder.solver_mut().not(eq);
    encoder.assert_term(neg_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "*(rc@) must equal (*rc)@"
    );
}

/// `*(*(v.len()))` should push both derefs inward: `(*(*v)).len()`.
#[test]
#[timeout(30000)]
fn test_double_deref_of_method_call() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let double_deref = deref(deref(method_call(var("v"), "len", vec![])));
    let term = encoder
        .encode_pure(&double_deref)
        .expect("*(*(v.len())) should encode");

    let pushed_in = method_call(deref(deref(var("v"))), "len", vec![]);
    let term_direct = encoder
        .encode_pure(&pushed_in)
        .expect("(*(*v)).len() should encode");

    let eq = encoder.solver_mut().eq(term, term_direct);
    let neg_eq = encoder.solver_mut().not(eq);
    encoder.assert_term(neg_eq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "*(*(v.len())) must equal (*(*v)).len()"
    );
}
