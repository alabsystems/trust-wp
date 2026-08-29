// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Depth-guard polarity tests for existence-checking PureExpr walkers.
//!
//! All `expr_has_*` / `expr_mentions_*` / `expr_needs_*` functions answer
//! "does feature X exist in this expression?" At the MAX_ENCODING_DEPTH limit
//! they must conservatively return `true` (fail-closed) to avoid:
//!
//! - Missing logic escalation (QF_LIA → UF/quantifiers), causing solver Unknown
//! - Unsound quantifier elimination (skipping bound variables)
//! - Missing result_current bindings in mut_borrow verification
//!
//! These tests build expression trees deeper than MAX_ENCODING_DEPTH and verify
//! the conservative polarity. They complement the existing
//! `expr_mentions_var_survives_500_deep_tree` test in `memory_walker_depth_proofs.rs`
//! by covering all accessible existence-checking functions.
//!
//! Part of #2473 (P1 depth-guard polarity bug)
//! Phase: proof_coverage

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{BinOp, PureExpr};

use crate::encoder::MAX_ENCODING_DEPTH;

/// Build a left-recursive BinOp tree of depth `n` with `leaf` at the bottom.
#[allow(clippy::cast_possible_wrap)] // test data: small usize values safely fit i64
fn deep_binop_tree(leaf: PureExpr, n: usize) -> PureExpr {
    let mut expr = leaf;
    for i in 0..n {
        expr = PureExpr::BinOp(
            Arc::new(expr),
            BinOp::Add,
            Arc::new(PureExpr::Int(i as i64)),
        );
    }
    expr
}

/// Build a left-recursive BinOp tree of depth `n` with a plain int leaf.
/// The tree contains NO special features (no closures, quantifiers, etc.).
fn deep_plain_tree(n: usize) -> PureExpr {
    deep_binop_tree(PureExpr::Int(0), n)
}

// ========================================================================
// expr_has_closure_spec_method
// ========================================================================

/// At depth > MAX_ENCODING_DEPTH, `expr_has_closure_spec_method` must return
/// true (fail-closed) even when the tree contains no closure spec methods.
#[test]
#[timeout(30000)]
fn depth_guard_closure_spec_method_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr::expr_has_closure_spec_method(&deep),
        "expr_has_closure_spec_method must return true at depth limit (fail-closed)"
    );
}

/// Below the depth limit with no closure spec method, should return false.
#[test]
#[timeout(30000)]
fn depth_guard_closure_spec_method_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr::expr_has_closure_spec_method(&shallow),
        "expr_has_closure_spec_method should return false for plain tree below depth limit"
    );
}

// ========================================================================
// expr_needs_quantifiers
// ========================================================================

/// At depth > MAX_ENCODING_DEPTH, `expr_needs_quantifiers` must return true
/// even when no quantifiers exist in the tree.
#[test]
#[timeout(30000)]
fn depth_guard_needs_quantifiers_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr::expr_needs_quantifiers(&deep),
        "expr_needs_quantifiers must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_needs_quantifiers_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr::expr_needs_quantifiers(&shallow),
        "expr_needs_quantifiers should return false for plain tree below depth limit"
    );
}

// ========================================================================
// expr_has_datatype_spec_method
// ========================================================================

#[test]
#[timeout(30000)]
fn depth_guard_datatype_spec_method_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr::expr_has_datatype_spec_method(&deep),
        "expr_has_datatype_spec_method must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_datatype_spec_method_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr::expr_has_datatype_spec_method(&shallow),
        "expr_has_datatype_spec_method should return false for plain tree below depth limit"
    );
}

// ========================================================================
// expr_has_match_constructor_pattern
// ========================================================================

#[test]
#[timeout(30000)]
fn depth_guard_match_constructor_pattern_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr::expr_has_match_constructor_pattern(&deep),
        "expr_has_match_constructor_pattern must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_match_constructor_pattern_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr::expr_has_match_constructor_pattern(&shallow),
        "expr_has_match_constructor_pattern should return false for plain tree below depth limit"
    );
}

// ========================================================================
// expr_has_tuple_fn
// ========================================================================

#[test]
#[timeout(30000)]
fn depth_guard_tuple_fn_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr::expr_has_tuple_fn(&deep),
        "expr_has_tuple_fn must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_tuple_fn_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr::expr_has_tuple_fn(&shallow),
        "expr_has_tuple_fn should return false for plain tree below depth limit"
    );
}

// ========================================================================
// expr_has_bitwise_ops
// ========================================================================

#[test]
#[timeout(30000)]
fn depth_guard_bitwise_ops_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr::expr_has_bitwise_ops(&deep),
        "expr_has_bitwise_ops must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_bitwise_ops_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr::expr_has_bitwise_ops(&shallow),
        "expr_has_bitwise_ops should return false for plain tree below depth limit"
    );
}

// ========================================================================
// expr_has_uf_method_call
// ========================================================================

#[test]
#[timeout(30000)]
fn depth_guard_uf_method_call_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr::expr_has_uf_method_call(&deep),
        "expr_has_uf_method_call must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_uf_method_call_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr::expr_has_uf_method_call(&shallow),
        "expr_has_uf_method_call should return false for plain tree below depth limit"
    );
}

// ========================================================================
// expr_mentions_var
// ========================================================================

/// Complements `expr_mentions_var_survives_500_deep_tree` in
/// `memory_walker_depth_proofs.rs` — that test uses a 4MB stack thread,
/// this one verifies the depth-guard behavior directly with a tree
/// that hits MAX_ENCODING_DEPTH without stack concerns.
#[test]
#[timeout(30000)]
fn depth_guard_mentions_var_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr::expr_mentions_var(&deep, "nonexistent"),
        "expr_mentions_var must return true at depth limit (fail-closed), \
         even for a variable not in the tree"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_mentions_var_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr::expr_mentions_var(&shallow, "nonexistent"),
        "expr_mentions_var should return false for missing var below depth limit"
    );
}

// ========================================================================
// expr_has_seq_index_on_final
// ========================================================================

#[test]
#[timeout(30000)]
fn depth_guard_seq_index_on_final_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr_seq::expr_has_seq_index_on_final(&deep),
        "expr_has_seq_index_on_final must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_seq_index_on_final_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr_seq::expr_has_seq_index_on_final(&shallow),
        "expr_has_seq_index_on_final should return false for plain tree below depth limit"
    );
}

// ========================================================================
// expr_has_seq_method_needing_quantifiers
// ========================================================================

#[test]
#[timeout(30000)]
fn depth_guard_seq_method_needing_quantifiers_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::expr_seq::expr_has_seq_method_needing_quantifiers(&deep),
        "expr_has_seq_method_needing_quantifiers must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_seq_method_needing_quantifiers_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::expr_seq::expr_has_seq_method_needing_quantifiers(&shallow),
        "expr_has_seq_method_needing_quantifiers should return false below depth limit"
    );
}

// ========================================================================
// expr_has_result_projection (mut_borrow::helpers)
// ========================================================================

/// Highest severity per #2473 — wrong polarity here can cause false
/// verification failures by missing result_current bindings.
#[test]
#[timeout(30000)]
fn depth_guard_result_projection_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::verify::mut_borrow::helpers::expr_has_result_projection(&deep),
        "expr_has_result_projection must return true at depth limit (fail-closed); \
         wrong polarity can cause false verification failures"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_result_projection_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::verify::mut_borrow::helpers::expr_has_result_projection(&shallow),
        "expr_has_result_projection should return false for plain tree below depth limit"
    );
}

// ========================================================================
// body_has_postcondition_mut_with_var (closure_axioms::expr_walkers)
// ========================================================================

/// At depth > MAX_ENCODING_DEPTH, `body_has_postcondition_mut_with_var` must
/// return true (fail-closed) even when no `postcondition_mut` calls exist.
#[test]
#[timeout(30000)]
fn depth_guard_postcondition_mut_with_var_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::AYEncoder::body_has_postcondition_mut_with_var(&deep, "s"),
        "body_has_postcondition_mut_with_var must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_postcondition_mut_with_var_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::AYEncoder::body_has_postcondition_mut_with_var(&shallow, "s"),
        "body_has_postcondition_mut_with_var should return false for plain tree below depth limit"
    );
}

// ========================================================================
// body_has_any_postcondition_mut (closure_axioms::expr_walkers)
// ========================================================================

/// At depth > MAX_ENCODING_DEPTH, `body_has_any_postcondition_mut` must
/// return true (fail-closed) even when no `postcondition_mut` calls exist.
#[test]
#[timeout(30000)]
fn depth_guard_any_postcondition_mut_fails_closed() {
    let deep = deep_plain_tree(MAX_ENCODING_DEPTH + 10);
    assert!(
        crate::AYEncoder::body_has_any_postcondition_mut(&deep),
        "body_has_any_postcondition_mut must return true at depth limit (fail-closed)"
    );
}

#[test]
#[timeout(30000)]
fn depth_guard_any_postcondition_mut_normal_false() {
    let shallow = deep_plain_tree(10);
    assert!(
        !crate::AYEncoder::body_has_any_postcondition_mut(&shallow),
        "body_has_any_postcondition_mut should return false for plain tree below depth limit"
    );
}
