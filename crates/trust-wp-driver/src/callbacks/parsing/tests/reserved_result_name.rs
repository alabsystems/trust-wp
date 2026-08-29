// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- ensures_uses_reserved_result_name tests (#2304) ---

#[test]
fn test_reserved_result_closure_tuple_binder_is_safe() {
    // `|(fst, snd)| fst == snd` — "result" is not free
    let ensures = vec![PureExpr::Closure {
        params: vec![("fst".to_string(), None), ("snd".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("fst".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("snd".to_string(), None)),
        )),
    }];
    assert!(
        !ensures_uses_reserved_result_name(&ensures),
        "closure binder with tuple pattern should not flag reserved result"
    );
}

#[test]
fn test_reserved_result_closure_shadows_result_param() {
    // `|result| result == 0` — "result" is shadowed by the closure param
    let ensures = vec![PureExpr::Closure {
        params: vec![("result".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )),
    }];
    assert!(
        !ensures_uses_reserved_result_name(&ensures),
        "closure binder named 'result' should shadow the reserved identifier"
    );
}

#[test]
fn test_reserved_result_plain_form_is_rejected() {
    // `result == result + 1` — "result" is free
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )];
    assert!(
        ensures_uses_reserved_result_name(&ensures),
        "plain-form ensures with free 'result' must be rejected"
    );
}

#[test]
fn test_format_context_extraction_warning_mentions_spanned_fallback_summary() {
    let mut diagnostics = ExtractionDiagnostics::default();
    diagnostics.record(
        "extract/block_visitor.rs",
        ExtractionDiagKind::UnsupportedTerminator,
        "unsupported MIR terminator: FalseUnwind",
        None,
    );
    diagnostics.record(
        "translate/mod.rs",
        ExtractionDiagKind::FeatureGap,
        "missing local expression for _5",
        None,
    );

    let warning = format_context_extraction_warning("crate::demo::f", &diagnostics, true)
        .expect("diagnostics should produce a warning");

    assert!(
        warning.contains("using spanned fallback after context extraction failed"),
        "warning should describe the fallback path: {warning}"
    );
    assert!(
        warning.contains("unsupported terminator"),
        "warning should include the diagnostic detail: {warning}"
    );
    assert!(
        warning.contains("(+1 more)"),
        "warning should summarize additional diagnostics: {warning}"
    );
}

#[test]
fn test_format_context_extraction_warning_returns_none_without_diagnostics() {
    assert!(
        format_context_extraction_warning(
            "crate::demo::f",
            &ExtractionDiagnostics::default(),
            false
        )
        .is_none(),
        "empty diagnostics should not emit a warning"
    );
}

#[test]
fn test_reserved_result_closure_with_free_outer_result() {
    // `|ret| ret == result` — "result" is free (not bound by closure param)
    let ensures = vec![PureExpr::Closure {
        params: vec![("ret".to_string(), None)],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("ret".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("result".to_string(), None)),
        )),
    }];
    assert!(
        ensures_uses_reserved_result_name(&ensures),
        "closure with free outer 'result' must be rejected"
    );
}
