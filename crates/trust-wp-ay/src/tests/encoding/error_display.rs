// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encoding_error_unsupported_display() {
    // Test that EncodingError::Unsupported formats correctly
    let err = EncodingError::unsupported("test construct");
    let msg = format!("{err}");
    assert!(
        msg.contains("unsupported formula"),
        "error display should contain 'unsupported formula', got: {msg}"
    );
    assert!(
        msg.contains("test construct"),
        "error display should contain construct description, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_unsupported_with_span_display() {
    // Test that span info is included in error display
    let span = SourceSpan::with_location("test.rs", 42, 10);
    let err = EncodingError::unsupported_with_span("test construct", span);
    let msg = format!("{err}");
    assert!(
        msg.contains("unsupported formula"),
        "span error should contain 'unsupported formula', got: {msg}"
    );
    assert!(
        msg.contains("test construct"),
        "span error should contain construct description, got: {msg}"
    );
    assert!(
        msg.contains("test.rs:42:10"),
        "span error should contain file:line:col location, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_unsupported_with_context_display() {
    // Test that contract text is included in error display
    let err = EncodingError::unsupported_with_context(
        "method call on view",
        None,
        Some("result@.len() == 0".to_string()),
    );
    let msg = format!("{err}");
    assert!(
        msg.contains("unsupported formula"),
        "context error should contain 'unsupported formula', got: {msg}"
    );
    assert!(
        msg.contains("method call on view"),
        "context error should contain construct description, got: {msg}"
    );
    assert!(
        msg.contains("contract: result@.len() == 0"),
        "context error should contain contract text, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_solver_error_display() {
    // Test that EncodingError::SolverError formats correctly
    let err = EncodingError::solver_error("test solver error");
    let msg = format!("{err}");
    assert!(
        msg.contains("ay error"),
        "solver error should contain 'ay error', got: {msg}"
    );
    assert!(
        msg.contains("test solver error"),
        "solver error should contain error description, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_solver_error_with_span_display() {
    // Test that span info is included in solver error display
    let span = SourceSpan::with_location("lib.rs", 100, 5);
    let err = EncodingError::solver_error_with_span("solver timeout", span);
    let msg = format!("{err}");
    assert!(
        msg.contains("ay error"),
        "span solver error should contain 'ay error', got: {msg}"
    );
    assert!(
        msg.contains("solver timeout"),
        "span solver error should contain error description, got: {msg}"
    );
    assert!(
        msg.contains("lib.rs:100:5"),
        "span solver error should contain file:line:col location, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_unsupported_with_span_attached_post_hoc_display() {
    // Driver-side error enrichment uses with_span after encoding fails.
    let err = EncodingError::unsupported("late span").with_span(SourceSpan::with_location(
        "driver.rs",
        77,
        3,
    ));
    let msg = format!("{err}");
    assert!(
        msg.contains("driver.rs:77:3"),
        "post-hoc span should appear in error display, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_solver_with_span_attached_post_hoc_display() {
    // Solver errors can also be enriched after construction.
    let err = EncodingError::solver_error("late span").with_span(SourceSpan::with_location(
        "driver.rs",
        88,
        9,
    ));
    let msg = format!("{err}");
    assert!(
        msg.contains("driver.rs:88:9"),
        "post-hoc solver span should appear in error display, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_with_byte_offset_span() {
    // Test that span with only byte offsets doesn't print location
    let span = SourceSpan::from_contract(10, 20);
    let err = EncodingError::unsupported_with_span("test construct", span);
    let msg = format!("{err}");
    assert!(
        msg.contains("unsupported formula"),
        "byte-offset error should contain 'unsupported formula', got: {msg}"
    );
    assert!(
        msg.contains("test construct"),
        "byte-offset error should contain construct description, got: {msg}"
    );
    // Should NOT contain "-->" since no file/line info
    assert!(
        !msg.contains("-->"),
        "Byte-only span should not show location"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_with_span_and_contract() {
    // Test that both span and contract text appear together
    let span = SourceSpan::with_location("test.rs", 10, 5);
    let err = EncodingError::unsupported_with_context(
        "complex expression",
        Some(span),
        Some("x@ + y@".to_string()),
    );
    let msg = format!("{err}");
    assert!(
        msg.contains("unsupported formula"),
        "combined error should contain 'unsupported formula', got: {msg}"
    );
    assert!(
        msg.contains("complex expression"),
        "combined error should contain construct description, got: {msg}"
    );
    assert!(
        msg.contains("test.rs:10:5"),
        "combined error should contain file:line:col location, got: {msg}"
    );
    assert!(
        msg.contains("contract: x@ + y@"),
        "combined error should contain contract text, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_span_without_column() {
    // Test that span with file and line but no column works
    let span = SourceSpan {
        file: Some("test.rs".to_string()),
        line: Some(42),
        column: None,
        ..Default::default()
    };
    let err = EncodingError::unsupported_with_span("test", span);
    let msg = format!("{err}");
    assert!(
        msg.contains("test.rs:42"),
        "no-column span should contain file:line, got: {msg}"
    );
    // Should NOT have ":col" at the end
    assert!(
        !msg.contains("test.rs:42:"),
        "Should not have trailing colon"
    );
}

#[test]
#[timeout(30000)]
fn test_encoding_error_sort_inference_display() {
    // Test that EncodingError::SortInference formats correctly (#1608)
    let err = EncodingError::sort_inference(
        "logic_fn_placeholder:foo",
        "no arg_exprs available to infer parameter sorts",
    );
    let msg = format!("{err}");
    assert!(
        msg.contains("sort inference failed"),
        "sort inference error should contain 'sort inference failed', got: {msg}"
    );
    assert!(
        msg.contains("logic_fn_placeholder:foo"),
        "sort inference error should contain context, got: {msg}"
    );
}

#[test]
#[timeout(30000)]
fn test_require_domain_sort_returns_error_on_out_of_bounds() {
    // require_domain_sort should return SortInference error when index
    // exceeds domain length (#1608).
    use crate::encoder::require_domain_sort;
    let domain = vec![Sort::Int, Sort::Bool];

    // In-bounds: should succeed
    assert_eq!(require_domain_sort(&domain, 0, "test").unwrap(), Sort::Int);
    assert_eq!(require_domain_sort(&domain, 1, "test").unwrap(), Sort::Bool);

    // Out-of-bounds: should fail
    let result = require_domain_sort(&domain, 2, "test");
    assert!(result.is_err());
    assert!(
        matches!(result.unwrap_err(), EncodingError::SortInference { .. }),
        "out-of-bounds domain lookup should return SortInference"
    );
}

/// Logic function with a Bool parameter must declare it as Sort::Bool in the
/// defining axiom. Before #1608, `domain.get(i).unwrap_or(Sort::Int)` would
/// silently declare Bool params as Int, making quantifiers range over all
/// integers instead of {true, false}.
#[test]
#[timeout(30000)]
fn test_logic_fn_bool_param_gets_bool_sort_not_int_fallback() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};
    let mut encoder = AYEncoder::new_with_quantifiers();

    // is_positive(flag: Bool) -> Bool = flag
    let logic_fn = LogicFnDef::new(
        "is_positive".to_string(),
        "test::is_positive".to_string(),
        vec!["flag".to_string()],
        var("flag"),
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Bool)]);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("registration should succeed");

    // The declared function should have Bool domain, not Int
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("is_positive");
    let func_decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .expect("function should be declared");
    let domain = func_decl.domain();
    assert_eq!(
        domain.len(),
        1,
        "is_positive should have exactly 1 parameter"
    );
    assert_eq!(
        domain[0],
        Sort::Bool,
        "Bool param should be Sort::Bool, not Int fallback (#1608)"
    );
}

/// Logic function with a Seq parameter must declare it as Seq sort in the
/// defining axiom. Before #1608, `domain.get(i).unwrap_or(Sort::Int)` would
/// silently declare Seq params as Int, making the Seq encoding unreachable.
#[test]
#[timeout(30000)]
fn test_logic_fn_seq_param_gets_seq_sort_not_int_fallback() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};
    let mut encoder = AYEncoder::new_with_quantifiers();

    // seq_len(s: Seq) -> Int = s.len()
    let logic_fn = LogicFnDef::new(
        "my_seq_len".to_string(),
        "test::my_seq_len".to_string(),
        vec!["s".to_string()],
        method_call(var("s"), "len", vec![]),
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Seq)]);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("registration should succeed");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("my_seq_len");
    let func_decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .expect("function should be declared");
    let domain = func_decl.domain();
    assert_eq!(
        domain.len(),
        1,
        "my_seq_len should have exactly 1 parameter"
    );
    assert!(
        domain[0].is_seq(),
        "Seq param should be Seq sort, not Int fallback (#1608), got: {:?}",
        domain[0]
    );
}
