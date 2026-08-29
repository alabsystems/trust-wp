// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;

/// Parameters forwarded into already-declared Seq-domain logic functions
/// should adopt the Seq sort instead of falling through to Int. (#2002)
///
/// This tests the generalised `collect_domain_sort_targets` path for Seq.
/// A wrapper function `items_len(s)` calls `get_items(s)` where
/// `get_items` is declared with `Seq -> Int`. The parameter `s` in
/// `items_len` should inherit Seq sort from `get_items`'s domain.
#[test]
#[timeout(30000)]
fn test_cross_function_seq_passthrough_reuses_declared_domain() {
    use trust_wp_core::logic::logic_fn_smt_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare get_items: Seq -> Int directly so it's already in the
    // declared functions when items_len is registered.
    let seq_sort = Sort::seq(Sort::Int);
    let smt_name_inner = logic_fn_smt_name("get_items");
    let func_decl =
        encoder
            .solver
            .declare_fun(&smt_name_inner, std::slice::from_ref(&seq_sort), Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name_inner, func_decl);

    // items_len(s) = get_items(s) — s is only used as a passthrough arg.
    let items_len = LogicFnDef::new(
        "items_len".to_string(),
        "test::items_len".to_string(),
        vec!["s".to_string()],
        logic_fn_call("get_items", vec![var("s")]),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&items_len)
        .expect("Seq passthrough should register without error");

    let smt_name = logic_fn_smt_name("items_len");
    let decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .unwrap_or_else(|| panic!("{smt_name} should be declared"));
    assert!(
        decl.domain().first().is_some_and(ay_dpll::ApiSort::is_seq),
        "forwarded Seq param should reuse declared domain, got: {:?}",
        decl.domain()
    );
}

/// Parameters forwarded into already-declared Bool-domain logic functions
/// should adopt the Bool sort instead of falling through to Int. (#2002)
///
/// This is the specific case that was missed before the generalisation of
/// `collect_domain_sort_targets`: Bool domain positions were not collected
/// because the function only handled Seq, FMap, and Datatype.
#[test]
#[timeout(30000)]
fn test_cross_function_bool_passthrough_reuses_declared_domain() {
    use trust_wp_core::logic::logic_fn_smt_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare is_valid: Bool -> Int directly.
    let smt_name_inner = logic_fn_smt_name("is_valid");
    let func_decl = encoder
        .solver
        .declare_fun(&smt_name_inner, &[Sort::Bool], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name_inner, func_decl);

    // check_valid(b) = is_valid(b) — b is only used as a passthrough arg.
    let check_valid = LogicFnDef::new(
        "check_valid".to_string(),
        "test::check_valid".to_string(),
        vec!["b".to_string()],
        logic_fn_call("is_valid", vec![var("b")]),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&check_valid)
        .expect("Bool passthrough should register without error");

    let smt_name = logic_fn_smt_name("check_valid");
    let decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .unwrap_or_else(|| panic!("{smt_name} should be declared"));
    assert_eq!(
        decl.domain().first(),
        Some(&Sort::Bool),
        "forwarded Bool param should reuse declared domain, got: {:?}",
        decl.domain()
    );
}
