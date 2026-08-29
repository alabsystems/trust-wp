// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `sort_queries.rs` free functions.
//!
//! Covers `expr_has_seq_sort_annotation`, `expr_is_known_int_key`, and
//! `expr_is_structural_field_receiver` — pure expression classifiers used
//! by method-call dispatch routing. (#2116, #1584)

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr, UnOp};

use super::{
    super::AYEncoder,
    sort_queries::{
        expr_has_seq_sort_annotation, expr_is_known_int_key, expr_is_structural_field_receiver,
    },
};
use crate::tests::helpers::{
    deref, final_expr, get_field, int, logic_fn_call, method_call, named_field, old, var,
    var_with_sort, view,
};

fn sample_point_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        "Point".to_string(),
        AdtDecl::new(
            "crate::Point".to_string(),
            "Point".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Point".to_string(),
                "Point".to_string(),
                vec![
                    AdtFieldDecl::new("x".to_string(), ExprSort::Int),
                    AdtFieldDecl::new("y".to_string(), ExprSort::Int),
                ],
            )],
        ),
    )])
}

// ── expr_has_seq_sort_annotation ──────────────────────────────────

#[test]
#[timeout(30000)]
fn seq_annotation_var_with_seq_sort() {
    assert!(expr_has_seq_sort_annotation(&var_with_sort(
        "v",
        ExprSort::Seq
    )));
}

#[test]
#[timeout(30000)]
fn seq_annotation_var_with_int_sort() {
    assert!(!expr_has_seq_sort_annotation(&var_with_sort(
        "x",
        ExprSort::Int
    )));
}

#[test]
#[timeout(30000)]
fn seq_annotation_var_no_sort() {
    assert!(!expr_has_seq_sort_annotation(&var("x")));
}

#[test]
#[timeout(30000)]
fn seq_annotation_datatype_vec() {
    let id = intern_sort_name("Vec");
    assert!(expr_has_seq_sort_annotation(&var_with_sort(
        "v",
        ExprSort::Datatype(id)
    )));
}

#[test]
#[timeout(30000)]
fn seq_annotation_datatype_linked_list() {
    // Note: `List` was removed from is_seq_model_type in #2231 because in
    // Creusot compat tests, `List` is a user-defined recursive enum. The
    // standard library equivalent is `LinkedList`.
    let id = intern_sort_name("alloc::collections::LinkedList");
    assert!(expr_has_seq_sort_annotation(&var_with_sort(
        "v",
        ExprSort::Datatype(id)
    )));
}

#[test]
#[timeout(30000)]
fn user_defined_list_not_seq_annotation() {
    // User-defined `List` enums (Cons | Nil) must NOT be recognized as Seq.
    // This ensures they get Datatype encoding. (#2231)
    let id = intern_sort_name("crate::List");
    assert!(!expr_has_seq_sort_annotation(&var_with_sort(
        "v",
        ExprSort::Datatype(id)
    )));
}

#[test]
#[timeout(30000)]
fn seq_annotation_datatype_vec_deque() {
    let id = intern_sort_name("VecDeque");
    assert!(expr_has_seq_sort_annotation(&var_with_sort(
        "v",
        ExprSort::Datatype(id)
    )));
}

#[test]
#[timeout(30000)]
fn seq_annotation_datatype_seq() {
    let id = intern_sort_name("creusot_contracts::Seq");
    assert!(expr_has_seq_sort_annotation(&var_with_sort(
        "v",
        ExprSort::Datatype(id)
    )));
}

#[test]
#[timeout(30000)]
fn seq_annotation_datatype_hashmap_not_seq() {
    let id = intern_sort_name("HashMap");
    assert!(!expr_has_seq_sort_annotation(&var_with_sort(
        "m",
        ExprSort::Datatype(id)
    )));
}

#[test]
#[timeout(30000)]
fn seq_annotation_ref_to_seq() {
    let sort = ExprSort::Ref(Box::new(ExprSort::Seq));
    assert!(expr_has_seq_sort_annotation(&var_with_sort("v", sort)));
}

#[test]
#[timeout(30000)]
fn seq_annotation_ref_to_int() {
    let sort = ExprSort::Ref(Box::new(ExprSort::Int));
    assert!(!expr_has_seq_sort_annotation(&var_with_sort("x", sort)));
}

#[test]
#[timeout(30000)]
fn seq_annotation_through_old_wrapper() {
    assert!(expr_has_seq_sort_annotation(&old(var_with_sort(
        "v",
        ExprSort::Seq
    ))));
}

#[test]
#[timeout(30000)]
fn seq_annotation_through_deref_wrapper() {
    assert!(expr_has_seq_sort_annotation(&deref(var_with_sort(
        "v",
        ExprSort::Seq
    ))));
}

#[test]
#[timeout(30000)]
fn seq_annotation_through_view_wrapper() {
    assert!(expr_has_seq_sort_annotation(&view(var_with_sort(
        "v",
        ExprSort::Seq
    ))));
}

#[test]
#[timeout(30000)]
fn seq_annotation_through_final_wrapper() {
    assert!(expr_has_seq_sort_annotation(&final_expr(var_with_sort(
        "v",
        ExprSort::Seq
    ))));
}

#[test]
#[timeout(30000)]
fn seq_annotation_nested_old_deref() {
    assert!(expr_has_seq_sort_annotation(&old(deref(var_with_sort(
        "v",
        ExprSort::Seq
    )))));
}

#[test]
#[timeout(30000)]
fn seq_annotation_int_literal_false() {
    assert!(!expr_has_seq_sort_annotation(&int(42)));
}

#[test]
#[timeout(30000)]
fn seq_annotation_bool_sort_false() {
    assert!(!expr_has_seq_sort_annotation(&var_with_sort(
        "b",
        ExprSort::Bool
    )));
}

#[test]
#[timeout(30000)]
fn method_param_sort_prefers_same_name_datatype_over_actual_uninterpreted() {
    let mut encoder = AYEncoder::new();
    encoder.register_adt_decls(&sample_point_adt_decls());

    let point_expr_sort = ExprSort::Datatype(intern_sort_name("crate::Point"));
    let point_sort = encoder.sort_from_expr_sort(point_expr_sort.clone());
    let Sort::Datatype(point_dt) = point_sort.clone() else {
        panic!("registered Point sort should be a native datatype");
    };

    let actual_term = encoder
        .solver
        .declare_const("p_same_name_ui", Sort::Uninterpreted("Point".to_string()));
    encoder.rebind_var("p", actual_term, point_sort.clone());

    let resolved =
        encoder.method_param_sort(&var_with_sort("p", point_expr_sort), actual_term, None);
    assert_eq!(
        resolved,
        Sort::Datatype(point_dt),
        "method_param_sort should preserve the encoder's registered datatype sort for same-name uninterpreted carriers"
    );
}

#[test]
#[timeout(30000)]
fn method_param_sort_preserves_bound_mutref_carrier_sort() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let mutref_sort = ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
    let encoded_sort = encoder.sort_from_expr_sort(mutref_sort.clone());
    let actual_term = encoder
        .get_or_declare_var("y", encoded_sort.clone())
        .expect("declare bound mutref carrier");

    let resolved = encoder.method_param_sort(&var_with_sort("y", mutref_sort), actual_term, None);
    assert_eq!(
        resolved, encoded_sort,
        "method_param_sort should preserve the bound mutable-reference carrier sort"
    );
}

// ── expr_is_known_int_key ─────────────────────────────────────────

#[test]
#[timeout(30000)]
fn known_int_key_int_literal() {
    assert!(expr_is_known_int_key(&int(42)));
}

#[test]
#[timeout(30000)]
fn known_int_key_negative_int_literal() {
    assert!(expr_is_known_int_key(&int(-1)));
}

#[test]
#[timeout(30000)]
fn known_int_key_var_with_int_sort() {
    assert!(expr_is_known_int_key(&var_with_sort("i", ExprSort::Int)));
}

#[test]
#[timeout(30000)]
fn known_int_key_var_with_seq_sort() {
    assert!(!expr_is_known_int_key(&var_with_sort("v", ExprSort::Seq)));
}

#[test]
#[timeout(30000)]
fn known_int_key_var_no_sort() {
    assert!(!expr_is_known_int_key(&var("x")));
}

#[test]
#[timeout(30000)]
fn known_int_key_old_wrapper() {
    assert!(expr_is_known_int_key(&old(int(1))));
}

#[test]
#[timeout(30000)]
fn known_int_key_deref_wrapper() {
    assert!(expr_is_known_int_key(&deref(var_with_sort(
        "i",
        ExprSort::Int
    ))));
}

#[test]
#[timeout(30000)]
fn known_int_key_final_wrapper() {
    assert!(expr_is_known_int_key(&final_expr(int(5))));
}

#[test]
#[timeout(30000)]
fn known_int_key_view_wrapper() {
    assert!(expr_is_known_int_key(&view(int(3))));
}

#[test]
#[timeout(30000)]
fn known_int_key_neg_unop() {
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(int(1)));
    assert!(expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_not_unop_false() {
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(int(1)));
    assert!(!expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_add_binop() {
    let expr = PureExpr::BinOp(Arc::new(int(1)), BinOp::Add, Arc::new(int(2)));
    assert!(expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_sub_binop() {
    let expr = PureExpr::BinOp(Arc::new(int(3)), BinOp::Sub, Arc::new(int(1)));
    assert!(expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_mul_binop() {
    let expr = PureExpr::BinOp(Arc::new(int(2)), BinOp::Mul, Arc::new(int(3)));
    assert!(expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_div_binop() {
    let expr = PureExpr::BinOp(Arc::new(int(6)), BinOp::Div, Arc::new(int(2)));
    assert!(expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_mod_binop() {
    let expr = PureExpr::BinOp(Arc::new(int(7)), BinOp::Mod, Arc::new(int(3)));
    assert!(expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_shl_binop() {
    let expr = PureExpr::BinOp(Arc::new(int(1)), BinOp::Shl, Arc::new(int(4)));
    assert!(expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_bit_and_binop() {
    let expr = PureExpr::BinOp(Arc::new(int(0xFF)), BinOp::BitAnd, Arc::new(int(0x0F)));
    assert!(expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_logical_and_false() {
    // Logical And is NOT an int-producing op
    let expr = PureExpr::BinOp(Arc::new(int(1)), BinOp::And, Arc::new(int(1)));
    assert!(!expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_binop_non_int_operand() {
    // Add with a non-int operand on one side
    let expr = PureExpr::BinOp(Arc::new(int(1)), BinOp::Add, Arc::new(var("x")));
    assert!(!expr_is_known_int_key(&expr));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_len() {
    assert!(expr_is_known_int_key(&method_call(var("v"), "len", vec![])));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_len_logic() {
    assert!(expr_is_known_int_key(&method_call(
        var("v"),
        "len_logic",
        vec![]
    )));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_pow2() {
    assert!(expr_is_known_int_key(&method_call(
        var("i"),
        "pow2",
        vec![]
    )));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_deep_model() {
    assert!(expr_is_known_int_key(&method_call(
        var("x"),
        "deep_model",
        vec![]
    )));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_shallow_model() {
    assert!(expr_is_known_int_key(&method_call(
        var("x"),
        "shallow_model",
        vec![]
    )));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_sum() {
    assert!(expr_is_known_int_key(&method_call(var("v"), "sum", vec![])));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_discriminant() {
    assert!(expr_is_known_int_key(&method_call(
        var("e"),
        "discriminant",
        vec![]
    )));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_capacity() {
    assert!(expr_is_known_int_key(&method_call(
        var("v"),
        "capacity",
        vec![]
    )));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_contains_false() {
    assert!(!expr_is_known_int_key(&method_call(
        var("v"),
        "contains",
        vec![int(1)]
    )));
}

#[test]
#[timeout(30000)]
fn known_int_key_method_get_false() {
    assert!(!expr_is_known_int_key(&method_call(
        var("m"),
        "get",
        vec![int(0)]
    )));
}

#[test]
#[timeout(30000)]
fn known_int_key_bool_literal_false() {
    assert!(!expr_is_known_int_key(&PureExpr::Bool(true)));
}

#[test]
#[timeout(30000)]
fn known_int_key_logic_fn_call_false() {
    assert!(!expr_is_known_int_key(&logic_fn_call(
        "some_fn",
        vec![int(1)]
    )));
}

// ── expr_is_structural_field_receiver ──────────────────────────────

#[test]
#[timeout(30000)]
fn structural_field_tuple_get() {
    assert!(expr_is_structural_field_receiver(&get_field(0, var("t"))));
}

#[test]
#[timeout(30000)]
fn structural_field_tuple_get_index_2() {
    assert!(expr_is_structural_field_receiver(&get_field(2, var("t"))));
}

#[test]
#[timeout(30000)]
fn structural_field_named_field() {
    assert!(expr_is_structural_field_receiver(&named_field(
        "x",
        var("s")
    )));
}

#[test]
#[timeout(30000)]
fn structural_field_named_field_nested_name() {
    assert!(expr_is_structural_field_receiver(&named_field(
        "inner_value",
        var("s")
    )));
}

#[test]
#[timeout(30000)]
fn structural_field_unrelated_logic_fn_false() {
    assert!(!expr_is_structural_field_receiver(&logic_fn_call(
        "Some",
        vec![int(1)]
    )));
}

#[test]
#[timeout(30000)]
fn structural_field_old_wrapper_tuple() {
    assert!(expr_is_structural_field_receiver(&old(get_field(
        0,
        var("t")
    ))));
}

#[test]
#[timeout(30000)]
fn structural_field_deref_wrapper_named() {
    assert!(expr_is_structural_field_receiver(&deref(named_field(
        "y",
        var("s")
    ))));
}

#[test]
#[timeout(30000)]
fn structural_field_final_wrapper() {
    assert!(expr_is_structural_field_receiver(&final_expr(get_field(
        1,
        var("t")
    ))));
}

#[test]
#[timeout(30000)]
fn structural_field_view_wrapper() {
    assert!(expr_is_structural_field_receiver(&view(named_field(
        "z",
        var("s")
    ))));
}

#[test]
#[timeout(30000)]
fn structural_field_var_false() {
    assert!(!expr_is_structural_field_receiver(&var("x")));
}

#[test]
#[timeout(30000)]
fn structural_field_int_false() {
    assert!(!expr_is_structural_field_receiver(&int(42)));
}

#[test]
#[timeout(30000)]
fn structural_field_method_call_false() {
    assert!(!expr_is_structural_field_receiver(&method_call(
        var("v"),
        "len",
        vec![]
    )));
}
