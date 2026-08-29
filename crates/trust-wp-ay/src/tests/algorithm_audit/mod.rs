// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Algorithm audit regression tests for boundary conditions (#1245, #1246, #1247).
//!
//! Tests found during Prover algorithm_audit phase:
//! 1. `flatten_nested_existentials` trigger boundary (#1245) — FIXED
//! 2. `expr_mentions_bound_var` missing match arm shadowing (#1246) — open bug
//! 3. `substitute_vars_in_expr` lacks capture avoidance (#1247) — open bug
//!
//! Tests exercise behavior through the public `verify_function` API since the
//! affected helper functions are private to `verify/mod.rs`.

mod coercion_and_ground_instances;
mod dispatch_and_normalization;
mod frame_and_seq;
mod mapping_and_fset;
mod memory_and_sep_logic;
mod quantifier_and_closure_sort;

use ay_dpll::api::Sort;
use ntest::timeout;

use super::helpers::{int, method_call, var};
use crate::AYEncoder;

// --- Ghost permission accessor dispatch (#2507) ---

/// `ward()` dispatches to Int-returning UF, not the generic unknown-method error.
/// Sort inference already special-cases `ward` as a value accessor (#994), and now
/// method dispatch has a matching arm so the two policies are aligned. (#2507)
///
/// Guards: method_call/mod.rs — `"ward" | "val" if args.is_empty()`
#[test]
#[timeout(30000)]
fn method_call_ward_encodes_as_int_uf() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("perm"), "ward", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "ward() should encode as Int UF, got: {:?}",
        result.err()
    );

    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Int,
        "ward() must return Int (ghost permission accessor). Got {sort:?}"
    );
}

/// `val()` dispatches to Int-returning UF, symmetric with `ward()`. (#2507)
///
/// Guards: method_call/mod.rs — same arm as `ward`.
#[test]
#[timeout(30000)]
fn method_call_val_encodes_as_int_uf() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("perm"), "val", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "val() should encode as Int UF, got: {:?}",
        result.err()
    );

    let term = result.unwrap();
    let sort = encoder.solver.get_sort(term);
    assert_eq!(
        sort,
        Sort::Int,
        "val() must return Int (ghost permission accessor). Got {sort:?}"
    );
}

/// `ward` with arguments should NOT match the nullary dispatch arm.
/// It should fall through to the generic fallback (logic fn or error).
/// This ensures the dispatch is limited to the targeted accessor arity. (#2507)
#[test]
#[timeout(30000)]
fn method_call_ward_with_args_does_not_match_nullary_dispatch() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("perm"), "ward", vec![int(42)]);
    let result = encoder.encode_pure(&expr);
    // With args, `ward` should NOT match the nullary arm.
    // It will fall through to the generic fallback, which produces an error
    // (no registered logic function, no Bool hint, no quantifier scope).
    assert!(
        result.is_err(),
        "ward(42) should NOT match the nullary dispatch arm — expected error from generic fallback"
    );
}

/// `val` with arguments should NOT match the nullary dispatch arm. (#2507)
#[test]
#[timeout(30000)]
fn method_call_val_with_args_does_not_match_nullary_dispatch() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(var("perm"), "val", vec![int(42)]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_err(),
        "val(42) should NOT match the nullary dispatch arm — expected error from generic fallback"
    );
}
