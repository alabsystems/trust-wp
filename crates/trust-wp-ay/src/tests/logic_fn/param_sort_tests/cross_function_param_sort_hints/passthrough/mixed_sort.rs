// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;

/// Multi-parameter mixed-sort passthrough: a wrapper function forwarding
/// parameters to a declared function with (Seq, Bool) domain should adopt
/// both sorts correctly. (#2002)
#[test]
#[timeout(30000)]
fn test_cross_function_mixed_sort_passthrough() {
    use trust_wp_core::logic::logic_fn_smt_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare inner_fn: (Seq, Bool) -> Int
    let seq_sort = Sort::seq(Sort::Int);
    let smt_name_inner = logic_fn_smt_name("inner_fn");
    let func_decl =
        encoder
            .solver
            .declare_fun(&smt_name_inner, &[seq_sort.clone(), Sort::Bool], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name_inner, func_decl);

    // wrapper(s, b) = inner_fn(s, b)
    let wrapper = LogicFnDef::new(
        "wrapper".to_string(),
        "test::wrapper".to_string(),
        vec!["s".to_string(), "b".to_string()],
        logic_fn_call("inner_fn", vec![var("s"), var("b")]),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&wrapper)
        .expect("mixed passthrough should register without error");

    let smt_name = logic_fn_smt_name("wrapper");
    let decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .unwrap_or_else(|| panic!("{smt_name} should be declared"));
    let domain = decl.domain();
    assert_eq!(
        domain.len(),
        2,
        "Expected 2 parameters, got {}",
        domain.len()
    );
    assert!(
        domain[0].is_seq(),
        "first param should be Seq, got: {:?}",
        domain[0]
    );
    assert_eq!(
        domain[1],
        Sort::Bool,
        "second param should be Bool, got: {:?}",
        domain[1]
    );
}
