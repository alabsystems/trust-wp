// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for tuple element range-sort inference (#994, Phase 3 Slice 1).
//!
//! Verifies that `infer_tuple_element_sort` correctly infers Bool or Int
//! range sorts from tuple sub-patterns, and that `get_or_declare_tuple_getter`
//! routes non-Int tuple patterns through signature-keyed logic getters.

use ay_dpll::api::Sort;
use ntest::timeout;

use super::helpers::{bool_expr, int, match_expr, var};
use crate::{AYEncoder, Pattern};

fn tuple_logic_getter_decl_name(encoder: &AYEncoder, index: usize) -> String {
    let getter_name =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(index);
    let smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let placeholder_prefix = format!("{smt_name}__placeholder_");
    encoder
        .decls()
        .logic_func_names()
        .find(|name| *name == &smt_name || name.starts_with(&placeholder_prefix))
        .expect("tuple logic getter should be declared")
        .clone()
}

/// Verify that a Bool literal sub-pattern in a tuple causes the getter to use
/// Bool range sort. Previously, all tuple getters were Int->Int, causing sort
/// mismatches when the element was Bool (bug/1208, or_pat).
#[test]
#[timeout(30000)]
fn tuple_element_bool_literal_gets_bool_range_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let scrutinee = encoder
        .solver
        .declare_const("pair", Sort::Uninterpreted("Tuple2".to_string()));
    encoder
        .vars_mut_for_test()
        .insert("pair".to_string(), scrutinee);
    encoder.var_sorts_mut_for_test().insert(
        "pair".to_string(),
        Sort::Uninterpreted("Tuple2".to_string()),
    );

    // Match pair against (true, x) => x where first element is Bool literal
    let expr = match_expr(
        var("pair"),
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Literal(bool_expr(true)),
                    Pattern::Binding("x".to_string()),
                ]),
                var("x"),
            ),
            (Pattern::Wildcard, int(-1)),
        ],
    );

    let _match_term = encoder
        .encode_pure(&expr)
        .expect("tuple with Bool literal element should encode");

    // The getter for element 0 should have Bool range sort (not Int).
    let getter_0_name = tuple_logic_getter_decl_name(&encoder, 0);
    let has_sort_aware = getter_0_name.contains("__placeholder_");
    assert!(
        has_sort_aware,
        "tuple getter 0 should use a signature-keyed logic declaration for Tuple2 domain, found: {getter_0_name}"
    );

    let getter_0 = encoder
        .decls()
        .get_logic_func(&getter_0_name)
        .unwrap()
        .clone();
    assert!(
        matches!(getter_0.range(), &Sort::Bool),
        "tuple getter 0 range should be Bool for Bool literal pattern"
    );
}

/// Verify that a mixed tuple (Bool, Int) correctly gets different range sorts
/// for each element getter.
#[test]
#[timeout(30000)]
fn tuple_mixed_element_sorts_bool_and_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let scrutinee = encoder
        .solver
        .declare_const("mixed", Sort::Uninterpreted("Tuple2".to_string()));
    encoder
        .vars_mut_for_test()
        .insert("mixed".to_string(), scrutinee);
    encoder.var_sorts_mut_for_test().insert(
        "mixed".to_string(),
        Sort::Uninterpreted("Tuple2".to_string()),
    );

    // Match mixed against (true, 42) => 1 — Bool literal first, Int literal second
    let expr = match_expr(
        var("mixed"),
        vec![
            (
                Pattern::Tuple(vec![
                    Pattern::Literal(bool_expr(true)),
                    Pattern::Literal(int(42)),
                ]),
                int(1),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let _match_term = encoder
        .encode_pure(&expr)
        .expect("mixed Bool/Int tuple should encode");

    // getter_0 should have Bool range, getter_1 should have Int range
    let getter_0 = tuple_logic_getter_decl_name(&encoder, 0);
    let getter_1 = tuple_logic_getter_decl_name(&encoder, 1);

    let g0 = encoder.decls().get_logic_func(&getter_0).unwrap().clone();
    let g1 = encoder.decls().get_logic_func(&getter_1).unwrap().clone();

    assert!(
        matches!(g0.range(), &Sort::Bool),
        "getter_0 range should be Bool for Bool literal: {getter_0}"
    );
    assert!(
        matches!(g1.range(), &Sort::Int),
        "getter_1 range should be Int for Int literal: {getter_1}"
    );
}
