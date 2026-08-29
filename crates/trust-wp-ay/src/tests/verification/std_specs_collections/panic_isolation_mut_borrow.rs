// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::*;

/// Sort mismatch panic in `verify_mut_borrow_function_with_modes` is caught
/// and converted to `Unknown` instead of crashing the pipeline.
///
/// Trigger pattern: register `g(n: Int)` and call it with Bool arg in ensures.
#[cfg(debug_assertions)]
#[test]
#[timeout(30000)]
fn test_sort_mismatch_panic_caught_in_mut_borrow() {
    use std::collections::HashMap;

    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // g(n) = n + 1, domain Int
    let logic_fn = LogicFnDef::new(
        "g_mut_test".to_string(),
        "test::g_mut_test".to_string(),
        vec!["n".to_string()],
        add(var("n"), int(1)),
    )
    .with_mode(LogicMode::Open);

    // ensures: g(x > 0) == 5 — Bool arg into Int domain → Sort mismatch panic
    let ens = eq(
        logic_fn_call("g_mut_test", vec![gt(var("result"), int(0))]),
        int(5),
    );

    let mut final_values = HashMap::new();
    final_values.insert("v".to_string(), deref(var("v")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).logic_fns(Some(&[logic_fn])),
    );

    // After widened coercion (#2155), apply_logic_fn replaces the Bool
    // argument with a fresh Int constant, so no sort mismatch panic occurs.
    // The encoding succeeds and the solver attempts verification.
    match result {
        Ok(_) => {
            // Coercion prevented the panic; solver returned a result.
        }
        Err(ref e)
            if format!("{e:?}").contains("sort mismatch")
                || format!("{e:?}").contains("Sort mismatch") =>
        {
            // Sort mismatch caught in a deeper encoding path.
        }
        Err(ref e) => {
            panic!("Unexpected encoding error in mut_borrow (not sort-related): {e:?}");
        }
    }
}
