// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- is_universal_quantifier ---

#[test]
#[timeout(30000)]
fn test_universal_quantifier_forall() {
    let expr = forall("x", bool_expr(true));
    assert!(is_universal_quantifier(&expr));
}

#[test]
#[timeout(30000)]
fn test_universal_quantifier_exists_is_not_universal() {
    let expr = exists("x", bool_expr(true));
    assert!(!is_universal_quantifier(&expr));
}

#[test]
#[timeout(30000)]
fn test_universal_quantifier_plain_expr_is_not_universal() {
    assert!(!is_universal_quantifier(&bool_expr(true)));
    assert!(!is_universal_quantifier(&int(42)));
    assert!(!is_universal_quantifier(&var("x")));
}

#[test]
#[timeout(30000)]
fn test_universal_quantifier_nested_forall() {
    // Forall { body: Forall { .. } } — outer is universal
    let expr = forall("x", forall("y", bool_expr(true)));
    assert!(is_universal_quantifier(&expr));
}

#[test]
#[timeout(30000)]
fn test_universal_quantifier_forall_wrapping_exists() {
    // Forall { body: Exists { .. } } — outer is still a Forall
    let expr = forall("x", exists("y", bool_expr(true)));
    assert!(is_universal_quantifier(&expr));
}

#[test]
#[timeout(30000)]
fn test_universal_quantifier_binop_of_foralls_is_not_universal() {
    // BinOp(And, Forall{..}, Forall{..}) is NOT a universal quantifier
    let expr = PureExpr::BinOp(
        Arc::new(forall("x", bool_expr(true))),
        trust_wp_core::formula::BinOp::And,
        Arc::new(forall("y", bool_expr(true))),
    );
    assert!(!is_universal_quantifier(&expr));
}
