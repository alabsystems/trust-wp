// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use syn::{parse_quote, Expr};

use super::{ContractExpr, ContractKind};

#[test]
fn test_simple_comparison() {
    let expr: Expr = parse_quote!(x > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_arithmetic() {
    let expr: Expr = parse_quote!(x + 1 > y * 2);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_logical_and() {
    let expr: Expr = parse_quote!(x > 0 && x < 100);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_logical_or() {
    let expr: Expr = parse_quote!(x == 0 || x == 1);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_result_variable() {
    let expr: Expr = parse_quote!(result > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_result_equality() {
    let expr: Expr = parse_quote!(result == x + 1);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_old_form() {
    let expr: Expr = parse_quote!(result == old(x) + 1);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_old_with_complex_expr() {
    let expr: Expr = parse_quote!(result == old(v.len()) - 1);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_method_call() {
    let expr: Expr = parse_quote!(v.len() > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_field_access() {
    let expr: Expr = parse_quote!(self.count > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_negation() {
    let expr: Expr = parse_quote!(!flag);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_implication_pattern() {
    // Common pattern: x > 0 implies result > 0
    // Encoded as: !(x > 0) || result > 0
    let expr: Expr = parse_quote!(!(x > 0) || result > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_reject_assignment() {
    let expr: Expr = parse_quote!(x = 5);
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Ensures).unwrap_err();
    assert!(
        err.message().contains("side effects"),
        "expected side-effects error, got: {}",
        err.message()
    );
}

#[test]
fn test_accept_if() {
    let expr: Expr = parse_quote!(if x > 0 { true } else { false });
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_accept_match() {
    let expr: Expr = parse_quote!(match result {
        Some(true) => true,
        _ => false,
    });
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_accept_match_option() {
    let expr: Expr = parse_quote!(match result {
        Some(v) => v > 0,
        None => false,
    });
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_accept_match_with_guard() {
    let expr: Expr = parse_quote!(match result {
        Some(v) if v > 0 => true,
        _ => false,
    });
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_reject_loop() {
    let expr: Expr = parse_quote!(loop {
        break;
    });
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Ensures).unwrap_err();
    assert!(
        err.message().contains("control flow"),
        "expected control-flow error, got: {}",
        err.message()
    );
}

#[test]
fn test_old_wrong_arity() {
    let expr: Expr = parse_quote!(old(x, y));
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Ensures).unwrap_err();
    assert!(
        err.message().contains("exactly 1 argument"),
        "expected arity error, got: {}",
        err.message()
    );
}

#[test]
fn test_old_no_args() {
    let expr: Expr = parse_quote!(old());
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Ensures).unwrap_err();
    assert!(
        err.message().contains("exactly 1 argument"),
        "expected arity error, got: {}",
        err.message()
    );
}

// Context-aware validation tests

#[test]
fn test_result_in_requires_rejected() {
    let expr: Expr = parse_quote!(result > 0);
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Requires).unwrap_err();
    assert!(
        err.message().contains("result"),
        "expected result-rejection error, got: {}",
        err.message()
    );
}

#[test]
fn test_result_in_ensures_allowed() {
    let expr: Expr = parse_quote!(result > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_result_in_invariant_allowed() {
    let expr: Expr = parse_quote!(result > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Invariant)
        .expect("expression should validate in invariant context");
}

#[test]
fn test_result_in_variant_rejected() {
    let expr: Expr = parse_quote!(result - 1);
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Variant).unwrap_err();
    assert!(
        err.message().contains("result"),
        "expected result-rejection error, got: {}",
        err.message()
    );
}

#[test]
fn test_old_in_requires_rejected() {
    let expr: Expr = parse_quote!(old(x) > 0);
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Requires).unwrap_err();
    assert!(
        err.message().contains("old()"),
        "expected old()-rejection error, got: {}",
        err.message()
    );
}

#[test]
fn test_old_in_ensures_allowed() {
    let expr: Expr = parse_quote!(old(x) > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}

#[test]
fn test_old_in_invariant_rejected() {
    let expr: Expr = parse_quote!(old(x) > 0);
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Invariant).unwrap_err();
    assert!(
        err.message().contains("old()"),
        "expected old()-rejection error, got: {}",
        err.message()
    );
}

#[test]
fn test_old_in_variant_rejected() {
    let expr: Expr = parse_quote!(old(n) - 1);
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Variant).unwrap_err();
    assert!(
        err.message().contains("old()"),
        "expected old()-rejection error, got: {}",
        err.message()
    );
}

#[test]
fn test_requires_without_special_forms_ok() {
    let expr: Expr = parse_quote!(x > 0 && y < 100);
    ContractExpr::validate_with_kind(&expr, ContractKind::Requires)
        .expect("expression should validate in requires context");
}

#[test]
fn test_variant_without_special_forms_ok() {
    let expr: Expr = parse_quote!(n - i);
    ContractExpr::validate_with_kind(&expr, ContractKind::Variant)
        .expect("expression should validate in variant context");
}

// Edge case: old(result) is semantically invalid (#226)

#[test]
fn test_old_result_rejected() {
    // old(result) is syntactically well-formed but semantically invalid:
    // - old() captures pre-state
    // - result is post-state
    // - There is no result in pre-state to capture
    let expr: Expr = parse_quote!(old(result) > 0);
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Ensures).unwrap_err();
    assert!(
        err.message().contains("result") && err.message().contains("old"),
        "Error should mention both result and old: {}",
        err.message()
    );
}

#[test]
fn test_old_nested_result_rejected() {
    // Even deeply nested result inside old() should be rejected
    let expr: Expr = parse_quote!(old(result + x) > 0);
    let err = ContractExpr::validate_with_kind(&expr, ContractKind::Ensures).unwrap_err();
    let msg = err.message();
    assert!(
        msg.contains("result") && msg.contains("old"),
        "Error should mention both result and old: {msg}"
    );
}

#[test]
fn test_old_with_non_result_allowed() {
    // Sanity check: old(x) should still work
    let expr: Expr = parse_quote!(old(x) > 0);
    ContractExpr::validate_with_kind(&expr, ContractKind::Ensures)
        .expect("expression should validate in ensures context");
}
