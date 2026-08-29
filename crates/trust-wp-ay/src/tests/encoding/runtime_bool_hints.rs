// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_not_operand_runtime_hint_declares_bool_var() {
    let mut encoder = AYEncoder::new();
    let expr = not(var("flag"));

    encoder
        .encode_pure(&expr)
        .expect("not(flag) should encode without Bool/Int mismatch");

    assert_eq!(
        encoder.var_sort("flag"),
        Some(&Sort::Bool),
        "runtime Bool-context hint should declare 'flag' as Bool"
    );
}

#[test]
#[timeout(30000)]
fn test_bool_context_placeholder_logic_fn_declares_bool_return() {
    let mut encoder = AYEncoder::new();
    let expr = not(logic_fn_call("is_ready", vec![var("x")]));

    encoder
        .encode_pure(&expr)
        .expect("not(is_ready(x)) should encode with Bool placeholder return sort");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("is_ready");
    let placeholder_prefix = format!("{smt_name}__placeholder_");
    let decl = encoder
        .decls()
        .logic_funcs_iter()
        .find_map(|(name, decl)| name.starts_with(&placeholder_prefix).then_some(decl))
        .expect("placeholder declaration should be present under the signature-keyed name");
    assert_eq!(
        decl.range(),
        &Sort::Bool,
        "logic fn used in Bool context should declare Bool return sort"
    );
}
