// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Uninterpreted function detection predicates for `PureExpr` trees.
//!
//! These predicates detect expressions that inject UF declarations during
//! encoding, used by `verify/setup.rs` to avoid assigning QF_LIA to goals
//! that need UF-capable logic.

use trust_wp_core::formula::{ExprSort, PureExpr, PureExprDepthLimitedTraversalExt as _};

use crate::encoder::MAX_ENCODING_DEPTH;

/// Checks if an expression contains method calls that inject uninterpreted functions
/// without being covered by other detection predicates.
///
/// This covers FSet/FMap operations, `ext_eq`, `produces`, `deep_model`, and
/// other spec methods that declare UFs during encoding. Without this check,
/// a contract using only these methods would be assigned QF_LIA, but the encoder
/// would inject `declare_fun` calls that require UF-capable logic. (#1923)
pub(crate) fn expr_has_uf_method_call(expr: &PureExpr) -> bool {
    // fail-closed: `on_limit = true` assumes feature exists at depth limit
    expr.any_recursive_with_depth_limit(
        MAX_ENCODING_DEPTH,
        true,
        |e| matches!(e, PureExpr::MethodCall { method, .. } if is_uf_injecting_method(method)),
    )
}

/// Returns true if the method name corresponds to an encoder path that declares
/// an uninterpreted function. This list covers methods in `method_call/` and
/// `match_enc/` that call `declare_fun` but are not caught by other detection
/// predicates (`expr_has_closure_spec_method`, `expr_has_datatype_spec_method`,
/// `expr_has_seq_method_needing_quantifiers`).
fn is_uf_injecting_method(method: &str) -> bool {
    matches!(
        method,
        // FSet operations (match_enc.rs)
        "fset_contains"
            | "fset_is_empty"
            | "fset_peek"
            | "fset_insert"
            | "fset_remove"
            | "fset_intersection"
            | "fset_difference"
            | "fset_len"
            // FMap operations (match_enc.rs)
            | "fmap_contains"
            | "fmap_lookup"
            | "fmap_len"
            | "fmap_insert"
            | "fmap_merge"
            // Seq ext_eq (method_call/) — injects inline forall quantifier
            | "ext_eq"
            // Iterator spec predicates (method_call/ + axioms.rs)
            | "produces"
            // Bool-returning UF predicates (method_call/)
            | "completed"
            // Int-returning UF methods (method_call/)
            | "deep_model"
            | "capacity"
            | "namespace"
            | "id"
            | "addr_logic"
            | "discriminant"
            | "map"
            | "filter"
    )
}

/// Checks if an expression tree contains a whole-`MutRef` carrier annotation.
///
/// These carriers trigger the internal mut-borrow constructor/accessor UFs
/// even when the surface syntax is only equality on annotated vars (no method
/// call to catch via `expr_has_uf_method_call`). Setup must therefore avoid
/// pure `QF_LIA` for such goals. (#2141, #2517)
pub(crate) fn expr_has_mut_ref_carrier(expr: &PureExpr) -> bool {
    // fail-closed: `on_limit = true` assumes carrier exists at depth limit
    expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        matches!(e, PureExpr::Var(_, Some(ExprSort::MutRef(_))))
    })
}
