// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(feature = "internal-bench-api")]

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_ay::AYEncoder;
use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

fn method_call(receiver: PureExpr, method: &str) -> PureExpr {
    PureExpr::MethodCall {
        receiver: std::sync::Arc::new(receiver),
        method: method.to_string(),
        args: vec![],
    }
}

fn var_with_sort(name: &str, sort: ExprSort) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(sort))
}

#[test]
#[timeout(10000)]
fn completed_retry_registers_ground_pool_under_final_symbol() {
    let mut encoder = AYEncoder::new();
    let receiver = var_with_sort("iter", ExprSort::Datatype(intern_sort_name("IterMut")));
    let pre_symbol = "method_completed_1_u497465724d7574";
    let final_symbol = "method_completed_1_u497465724d7574__sig_i__ret_b";

    encoder.bind_const_for_internal_bench("iter", Sort::Int);
    encoder
        .encode_pure(&method_call(receiver, "completed"))
        .expect("completed() retry on Int carrier should encode");

    assert_eq!(
        encoder.ground_pool_entry_count_for_internal_bench(final_symbol),
        1,
        "ground pool should register the retry application under the final declaration symbol"
    );
    assert_eq!(
        encoder.ground_pool_entry_count_for_internal_bench(pre_symbol),
        0,
        "ground pool should not keep the retry application under the pre-retry symbol"
    );
}
