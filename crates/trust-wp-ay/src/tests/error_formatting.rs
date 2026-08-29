// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::error::EncodingError`] constructors, Display formatting,
//! and the `with_span` combinator.
//!
//! Coverage gap: `error.rs` (212 LOC) had only 2 tests covering
//! `unsupported_with_context` and `solver_error_with_span`. Untested:
//! `unsupported` (no span), `unsupported_with_span`, `solver_error`,
//! `sort_inference`, `with_span` on all 3 variants, and no-span Display paths.

use ntest::timeout;

use crate::{EncodingError, SourceSpan};

// --- unsupported_with_context (existing coverage) ---

#[test]
#[timeout(30000)]
fn unsupported_error_formats_span_and_contract_text() {
    let err = EncodingError::unsupported_with_context(
        "quantifiers are not supported here",
        Some(SourceSpan::with_location("src/lib.rs", 12, 7)),
        Some("forall<i> xs[i] >= 0".to_string()),
    );

    let rendered = err.to_string();
    assert!(rendered.contains("unsupported formula: quantifiers are not supported here"));
    assert!(rendered.contains("\n  --> src/lib.rs:12:7"));
    assert!(rendered.contains("\n  contract: forall<i> xs[i] >= 0"));
}

// --- solver_error_with_span (existing coverage) ---

#[test]
#[timeout(30000)]
fn solver_error_formats_span_without_column_suffix() {
    let err = EncodingError::solver_error_with_span(
        "timeout",
        SourceSpan {
            file: Some("src/spec.rs".to_string()),
            start: 0,
            end: 0,
            line: Some(9),
            column: None,
        },
    );

    let rendered = err.to_string();
    assert!(rendered.contains("ay error: timeout"));
    assert!(rendered.contains("\n  --> src/spec.rs:9"));
    assert!(
        !rendered.contains("\n  --> src/spec.rs:9:"),
        "missing column should not render a trailing colon: {rendered}"
    );
}

// --- unsupported (no span, no contract) ---

#[test]
#[timeout(30000)]
fn unsupported_error_no_span() {
    let err = EncodingError::unsupported("closures not yet supported");
    let rendered = err.to_string();
    assert_eq!(rendered, "unsupported formula: closures not yet supported");
    assert!(
        !rendered.contains("-->"),
        "no-span variant should not contain span arrow"
    );
    assert!(
        !rendered.contains("contract:"),
        "no-span variant should not contain contract text"
    );
}

// --- unsupported_with_span (span but no contract) ---

#[test]
#[timeout(30000)]
fn unsupported_error_with_span_no_contract() {
    let err = EncodingError::unsupported_with_span(
        "array indexing",
        SourceSpan::with_location("src/main.rs", 42, 10),
    );
    let rendered = err.to_string();
    assert!(rendered.contains("unsupported formula: array indexing"));
    assert!(rendered.contains("\n  --> src/main.rs:42:10"));
    assert!(
        !rendered.contains("contract:"),
        "with_span variant should not contain contract text"
    );
}

// --- unsupported_with_context: span only, no contract ---

#[test]
#[timeout(30000)]
fn unsupported_error_context_span_only() {
    let err = EncodingError::unsupported_with_context(
        "trait objects",
        Some(SourceSpan::with_location("lib.rs", 1, 1)),
        None,
    );
    let rendered = err.to_string();
    assert!(rendered.contains("unsupported formula: trait objects"));
    assert!(rendered.contains("\n  --> lib.rs:1:1"));
    assert!(!rendered.contains("contract:"));
}

// --- unsupported_with_context: neither span nor contract ---

#[test]
#[timeout(30000)]
fn unsupported_error_context_neither() {
    let err = EncodingError::unsupported_with_context("generic const", None, None);
    let rendered = err.to_string();
    assert_eq!(rendered, "unsupported formula: generic const");
}

// --- solver_error (no span) ---

#[test]
#[timeout(30000)]
fn solver_error_no_span() {
    let err = EncodingError::solver_error("mk_eq sort mismatch");
    let rendered = err.to_string();
    assert_eq!(rendered, "ay error: mk_eq sort mismatch");
    assert!(!rendered.contains("-->"));
}

// --- solver_error_with_span: full span ---

#[test]
#[timeout(30000)]
fn solver_error_with_full_span() {
    let err = EncodingError::solver_error_with_span(
        "internal-error",
        SourceSpan::with_location("src/verify.rs", 100, 5),
    );
    let rendered = err.to_string();
    assert!(rendered.contains("ay error: internal-error"));
    assert!(rendered.contains("\n  --> src/verify.rs:100:5"));
}

// --- sort_inference (entirely untested before) ---

#[test]
#[timeout(30000)]
fn sort_inference_error_no_span() {
    let err = EncodingError::sort_inference("logic_fn_placeholder:foo param 0", "no domain sort");
    let rendered = err.to_string();
    assert!(rendered.contains("sort inference failed:"));
    assert!(rendered.contains("logic_fn_placeholder:foo param 0"));
    assert!(rendered.contains("no domain sort"));
    assert!(!rendered.contains("-->"));
}

// --- sort_conflict (no span) ---

#[test]
#[timeout(30000)]
fn sort_conflict_error_no_span() {
    let err = EncodingError::sort_conflict("variable 'c_final'", "Int", "ClosureEnv_conflict");
    let rendered = err.to_string();
    assert!(rendered.contains("sort conflict:"));
    assert!(rendered.contains("variable 'c_final'"));
    assert!(rendered.contains("declared as Int"));
    assert!(rendered.contains("requested as ClosureEnv_conflict"));
    assert!(!rendered.contains("-->"));
}

// --- with_span: attach span to unsupported ---

#[test]
#[timeout(30000)]
fn with_span_unsupported_attaches_location() {
    let err = EncodingError::unsupported("raw pointers");
    assert!(!err.to_string().contains("-->"));

    let err = err.with_span(SourceSpan::with_location("src/ptr.rs", 7, 3));
    let rendered = err.to_string();
    assert!(rendered.contains("unsupported formula: raw pointers"));
    assert!(rendered.contains("\n  --> src/ptr.rs:7:3"));
}

// --- with_span: attach span to solver_error ---

#[test]
#[timeout(30000)]
fn with_span_solver_error_attaches_location() {
    let err = EncodingError::solver_error("out of memory");
    assert!(!err.to_string().contains("-->"));

    let err = err.with_span(SourceSpan::with_location("src/solve.rs", 55, 1));
    let rendered = err.to_string();
    assert!(rendered.contains("ay error: out of memory"));
    assert!(rendered.contains("\n  --> src/solve.rs:55:1"));
}

// --- with_span: attach span to sort_inference ---

#[test]
#[timeout(30000)]
fn with_span_sort_inference_attaches_location() {
    let err = EncodingError::sort_inference("param 2", "ambiguous Seq/FMap");
    assert!(!err.to_string().contains("-->"));

    let err = err.with_span(SourceSpan::with_location("src/enc.rs", 300, 12));
    let rendered = err.to_string();
    assert!(rendered.contains("sort inference failed:"));
    assert!(rendered.contains("param 2"));
    assert!(rendered.contains("ambiguous Seq/FMap"));
    assert!(rendered.contains("\n  --> src/enc.rs:300:12"));
}

// --- with_span: attach span to sort_conflict ---

#[test]
#[timeout(30000)]
fn with_span_sort_conflict_attaches_location() {
    let err = EncodingError::sort_conflict("variable 'c_final'", "Int", "ClosureEnv_conflict");
    assert!(!err.to_string().contains("-->"));

    let err = err.with_span(SourceSpan::with_location("src/verify.rs", 280, 17));
    let rendered = err.to_string();
    assert!(rendered.contains("sort conflict:"));
    assert!(rendered.contains("variable 'c_final'"));
    assert!(rendered.contains("\n  --> src/verify.rs:280:17"));
}

// --- with_span: overwrites existing span ---

#[test]
#[timeout(30000)]
fn with_span_overwrites_existing_span() {
    let err = EncodingError::unsupported_with_span(
        "old pattern",
        SourceSpan::with_location("old.rs", 1, 1),
    );
    assert!(err.to_string().contains("old.rs:1:1"));

    let err = err.with_span(SourceSpan::with_location("new.rs", 99, 50));
    let rendered = err.to_string();
    assert!(
        rendered.contains("new.rs:99:50"),
        "new span should replace old"
    );
    assert!(!rendered.contains("old.rs"), "old span should be gone");
}

// --- with_span: preserves contract_text on unsupported ---

#[test]
#[timeout(30000)]
fn with_span_preserves_contract_text() {
    let err = EncodingError::unsupported_with_context(
        "advanced feature",
        None,
        Some("requires(x > 0)".to_string()),
    );
    assert!(!err.to_string().contains("-->"));
    assert!(err.to_string().contains("contract: requires(x > 0)"));

    let err = err.with_span(SourceSpan::with_location("src/lib.rs", 10, 1));
    let rendered = err.to_string();
    assert!(rendered.contains("\n  --> src/lib.rs:10:1"));
    assert!(
        rendered.contains("contract: requires(x > 0)"),
        "contract text should be preserved across with_span"
    );
}

// --- SourceSpan edge case: file=None ---

#[test]
#[timeout(30000)]
fn span_with_no_file_does_not_render_arrow() {
    let err = EncodingError::solver_error_with_span(
        "test",
        SourceSpan {
            file: None,
            start: 0,
            end: 0,
            line: Some(5),
            column: Some(3),
        },
    );
    let rendered = err.to_string();
    assert_eq!(rendered, "ay error: test");
    assert!(
        !rendered.contains("-->"),
        "no file means no span arrow should render"
    );
}

// --- SourceSpan edge case: line=None ---

#[test]
#[timeout(30000)]
fn span_with_no_line_does_not_render_arrow() {
    let err = EncodingError::solver_error_with_span(
        "test",
        SourceSpan {
            file: Some("file.rs".to_string()),
            start: 0,
            end: 0,
            line: None,
            column: None,
        },
    );
    let rendered = err.to_string();
    assert_eq!(rendered, "ay error: test");
    assert!(
        !rendered.contains("-->"),
        "no line means no span arrow should render"
    );
}

// --- Debug impl exists (thiserror generates it) ---

#[test]
#[timeout(30000)]
fn debug_impl_contains_variant_name() {
    let err = EncodingError::unsupported("test");
    let debug = format!("{err:?}");
    assert!(
        debug.contains("Unsupported"),
        "Debug should contain variant name"
    );
}

#[test]
#[timeout(30000)]
fn debug_impl_sort_inference() {
    let err = EncodingError::sort_inference("ctx", "detail");
    let debug = format!("{err:?}");
    assert!(
        debug.contains("SortInference"),
        "Debug should contain variant name"
    );
}

#[test]
#[timeout(30000)]
fn debug_impl_solver_error() {
    let err = EncodingError::solver_error("msg");
    let debug = format!("{err:?}");
    assert!(
        debug.contains("SolverError"),
        "Debug should contain variant name"
    );
}
