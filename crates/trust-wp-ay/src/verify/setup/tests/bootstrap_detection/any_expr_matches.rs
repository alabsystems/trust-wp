// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::*;
// =============================================================================
// Tests for any_expr_matches with non-empty context_exprs
// =============================================================================

/// `any_expr_matches` should detect predicates in `context_exprs` even when
/// requires and ensures are empty.
#[test]
#[timeout(30000)]
fn any_expr_matches_context_exprs_triggers_detection() {
    use crate::expr::expr_has_uf_method_call;

    let ctx_expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".into(), None)),
        method: "ext_eq".into(),
        args: vec![PureExpr::Var("b".into(), None)],
    };

    assert!(
        any_expr_matches(&[], &[], &[&ctx_expr], expr_has_uf_method_call),
        "UF method in context_exprs should be detected"
    );
}

/// `any_expr_matches` returns false when no expression in any slice matches.
#[test]
#[timeout(30000)]
fn any_expr_matches_all_empty_returns_false() {
    use crate::expr::expr_has_uf_method_call;

    let simple = PureExpr::Int(42);
    assert!(
        !any_expr_matches(
            &[simple.clone()],
            &[simple.clone()],
            &[&simple],
            expr_has_uf_method_call
        ),
        "plain integer should not match UF method predicate"
    );
}
