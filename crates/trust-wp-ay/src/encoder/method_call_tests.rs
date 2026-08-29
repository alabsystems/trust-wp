// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for method call encoding: dispatch routing, UF declarations,
//! sort-aware FMap/FSet/Seq resolution, and logic function fallback.
//!
//! Extracted from `method_call/mod.rs` as part of #2065 structural decomposition.

use std::sync::Arc;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

use crate::{
    encoder::{
        unsoundness::{self, UnsoundnessCategory},
        AYEncoder,
    },
    tests::helpers::{
        and, bool_expr, eq, exists_with_sort, final_expr, forall_with_sort, int, logic_fn_call,
        method_call, named_field, old, var, var_with_sort, view,
    },
    verify::encode_negated_postcondition,
};

mod datatype_spec;
mod datatype_wrappers;
mod decl_and_sort;
mod defensive;
mod dispatch_routing;
mod legacy_dispatch;
mod shared;
mod tuple_bridge;

use shared::*;

/// Iterator adapter accessor methods from trust-wp-std specs must not fall
/// through to the unknown-method error path. They are opaque value
/// projections used in postconditions like `result.iter() == self`. (#2689)
#[test]
#[timeout(30000)]
fn iterator_adapter_accessors_encode_as_value_ufs() {
    let mut encoder = AYEncoder::new();

    for method in ["iter", "func", "n", "itera", "iterb", "a"] {
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("adapter".to_string(), None)),
            method: method.to_string(),
            args: vec![],
        };

        let result = encoder.encode_pure(&expr);
        assert!(
            result.is_ok(),
            "iterator adapter accessor `{method}` should encode: {result:?}"
        );
    }
}
