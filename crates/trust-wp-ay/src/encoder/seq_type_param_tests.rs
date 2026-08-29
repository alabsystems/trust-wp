// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort};

use crate::{
    encoder::AYEncoder,
    tests::helpers::{deref, eq, int, logic_fn_call, method_call, var, var_with_sort, view},
};

/// Regression for the generic `vector/07_read_write` intermediate-state path (#2062).
///
/// The low-level `Seq::set` encoding stores through an `Array Int Int`, so
/// `TypeParam` elements must cross the same injective bridge already used by
/// `push_back`.
#[test]
#[timeout(30000)]
fn intermediate_state_set_then_read_type_param_value_verifies() {
    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));

    let intermediate = method_call(
        view(deref(var("a"))),
        "set",
        vec![int(0), var_with_sort("x", t_sort.clone())],
    );
    let read_back = method_call(intermediate, "index_logic", vec![int(0)]);
    let formula = eq(read_back, var_with_sort("x", t_sort));

    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("a_current".to_string(), ExprSort::Seq);
    encoder.record_sort_hint("a_current_view".to_string(), ExprSort::Seq);
    encoder.register_sort_hints(std::slice::from_ref(&formula));
    let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
    let negated = encoder.solver.not(formula_term);
    encoder.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "set(View(Deref(a)), 0, x:T).index_logic(0) should round-trip through the Seq element bridge, got {result:?}"
    );
}

/// Regression for `ghost/seq_iter.rs` `reverse_ghost_ref<T>` (#2116).
///
/// `push_front_ghost` shares the same Seq carrier as `push_back`, but the
/// encoder previously passed generic elements straight into `seq_push_front`
/// without bridging them to the Int carrier sort first. That caused
/// `sort mismatch in apply: expected matching domain sort, got T` when the
/// iterator yielded `&T`.
#[test]
#[timeout(30000)]
fn push_front_ghost_type_param_value_round_trips_through_seq_bridge() {
    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));

    let pushed = method_call(
        view(var("result")),
        "push_front_ghost",
        vec![var_with_sort("x", t_sort.clone())],
    );
    let read_back = method_call(pushed, "index_logic", vec![int(0)]);
    let formula = eq(read_back, var_with_sort("x", t_sort));

    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("result_view".to_string(), ExprSort::Seq);
    encoder.register_sort_hints(std::slice::from_ref(&formula));
    let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
    let negated = encoder.solver.not(formula_term);
    encoder.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "push_front_ghost(View(result), x:T).index_logic(0) should round-trip through the Seq element bridge, got {result:?}"
    );
}

/// Regression for the extracted `push_front_ghost` loop body shape in
/// `ghost/seq_iter.rs` `reverse_ghost_ref<T>` (#2116).
///
/// Loop extraction models `push_front_ghost(x)` as `seq![x].concat(result)`.
/// The singleton/literal Seq constructor must therefore bridge generic
/// elements to the Int carrier sort before applying `seq_singleton`.
#[test]
#[timeout(30000)]
fn seq_singleton_concat_type_param_value_round_trips_through_seq_bridge() {
    let t_sort = ExprSort::TypeParam(intern_sort_name("T"));

    let singleton = logic_fn_call("seq", vec![var_with_sort("x", t_sort.clone())]);
    let pushed = method_call(singleton, "concat", vec![view(var("result"))]);
    let read_back = method_call(pushed, "index_logic", vec![int(0)]);
    let formula = eq(read_back, var_with_sort("x", t_sort));

    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("result_view".to_string(), ExprSort::Seq);
    encoder.register_sort_hints(std::slice::from_ref(&formula));
    let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
    let negated = encoder.solver.not(formula_term);
    encoder.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "seq![x:T].concat(View(result)).index_logic(0) should round-trip through the Seq element bridge, got {result:?}"
    );
}
