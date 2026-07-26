// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! pearlite! macro implementation for specification-only expressions.
//!
//! This module implements the `pearlite!` macro which allows users to write
//! specification expressions with extended syntax not available in standard Rust.
//!
//! # Design
//!
//! See `designs/2026-02-02-pearlite-dsl.md` for the full design document.
//!
//! # Current Status
//!
//! The pearlite! macro preprocesses Pearlite syntax and then validates the
//! result through the shared contract-expression path used by proc-macro
//! contracts.
//! Currently supports:
//! - `x.view()` or `x@` - View/model access
//! - Quantifiers (`forall<...>`, `exists<...>`) and implication (`==>`)
//! - Standard Rust boolean expressions (`&&`, `||`, `!`)
//! - Comparisons (`==`, `!=`, `<`, `>`, `<=`, `>=`)
//! - Method calls on spec types
//!
//! Validation uses `ContractKind::Requires`, so `result` and `old(...)` remain
//! rejected inside `pearlite!`.

use proc_macro2::TokenStream;
use quote::quote;
use syn::Expr;

use crate::{
    contract::{ContractExpr, ContractKind, ContractParseError, ContractValidationError},
    transform::preprocess_view_syntax,
};

/// Validates a pearlite expression.
///
/// Uses the same validation as contract expressions after syntax preprocessing.
/// Validation runs with `ContractKind::Requires`, so quantifiers and
/// implication are accepted while `result` and `old(...)` remain rejected.
pub(crate) fn validate_pearlite_expr(
    input: &proc_macro::TokenStream,
) -> Result<Expr, ContractParseError> {
    // Transform Creusot-style syntax (@, ^, int suffix) before parsing
    let input_to_parse: proc_macro::TokenStream = preprocess_view_syntax(input.clone());

    // Parse as expression
    let expr: Expr = syn::parse(input_to_parse).map_err(|e| {
        ContractParseError::new(
            e.span(),
            ContractValidationError::SynParseFailed {
                reason: e.to_string(),
            },
        )
    })?;

    // Validate using contract validation (supports forall, exists, etc.)
    // Use Requires kind since pearlite expressions are boolean predicates
    ContractExpr::validate_with_kind(&expr, ContractKind::Requires)?;

    Ok(expr)
}

/// Expands a pearlite! invocation.
///
/// # Verification Mode (`--cfg trust-wp`)
///
/// Emits a marked closure that the driver can detect and extract:
/// ```text
/// {
///     #[doc(hidden)]
///     #[doc = "__trust_wp_pearlite"]
///     let __pearlite_result = || -> bool { <expr> };
///     __pearlite_result()
/// }
/// ```
///
/// # Normal Compilation
///
/// Erases to a stub `true` value to satisfy type checking.
pub(crate) fn expand_pearlite(expr: &Expr) -> TokenStream {
    quote! {
        {
            #[cfg(trust_wp)]
            {
                // Marker for driver detection. The driver extracts pearlite expressions
                // by looking for this doc pattern in the AST.
                #[doc(hidden)]
                #[doc = "__trust_wp_pearlite"]
                let __pearlite_result = || -> bool { #expr };
                __pearlite_result()
            }

            #[cfg(not(trust_wp))]
            {
                // Stub value when not verifying - must return bool to match
                // the verification mode's return type
                true
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use syn::parse_quote;

    use super::*;

    // ==========================================================================
    // Validation tests (using contract validation directly since proc_macro::TokenStream
    // isn't available in unit tests)
    // ==========================================================================

    /// Helper to validate expressions as pearlite uses Requires kind
    fn validate_as_pearlite(expr: &Expr) -> Result<(), ContractParseError> {
        ContractExpr::validate_with_kind(expr, ContractKind::Requires)
    }

    #[test]
    fn test_pearlite_validate_simple_expression() {
        let expr: Expr = parse_quote!(x > 0);
        assert!(
            validate_as_pearlite(&expr).is_ok(),
            "simple comparison should be valid"
        );
    }

    #[test]
    fn test_pearlite_validate_complex_boolean() {
        let expr: Expr = parse_quote!(a && b || !c);
        assert!(
            validate_as_pearlite(&expr).is_ok(),
            "complex boolean should be valid"
        );
    }

    #[test]
    fn test_pearlite_validate_method_call() {
        let expr: Expr = parse_quote!(v.len() > 0);
        assert!(
            validate_as_pearlite(&expr).is_ok(),
            "method call should be valid"
        );
    }

    #[test]
    fn test_pearlite_validate_field_access() {
        let expr: Expr = parse_quote!(self.count >= 0);
        assert!(
            validate_as_pearlite(&expr).is_ok(),
            "field access should be valid"
        );
    }

    #[test]
    fn test_pearlite_validate_function_call() {
        // Standard function calls are valid in pearlite expressions.
        // Quantifiers and implication go through the same shared validation
        // path after syntax preprocessing.
        let expr: Expr = parse_quote!(is_valid(x));
        assert!(
            validate_as_pearlite(&expr).is_ok(),
            "function call should be valid in pearlite"
        );
    }

    #[test]
    fn test_pearlite_reject_assignment() {
        let expr: Expr = parse_quote!(x = 5);
        assert!(
            validate_as_pearlite(&expr).is_err(),
            "assignment should be rejected"
        );
    }

    #[test]
    fn test_pearlite_reject_loop() {
        let expr: Expr = parse_quote!(loop {
            break;
        });
        assert!(
            validate_as_pearlite(&expr).is_err(),
            "loop should be rejected"
        );
    }

    #[test]
    fn test_pearlite_accept_if_expression() {
        let expr: Expr = parse_quote!(if x > 0 { true } else { false });
        assert!(
            validate_as_pearlite(&expr).is_ok(),
            "if expression should be accepted (encoded as ITE in SMT)"
        );
    }

    #[test]
    fn test_pearlite_reject_result() {
        // pearlite uses Requires kind, which doesn't allow `result`
        let expr: Expr = parse_quote!(result > 0);
        assert!(
            validate_as_pearlite(&expr).is_err(),
            "result should be rejected in pearlite"
        );
    }

    #[test]
    fn test_pearlite_reject_old() {
        // pearlite uses Requires kind, which doesn't allow `old()`
        let expr: Expr = parse_quote!(old(x) > 0);
        assert!(
            validate_as_pearlite(&expr).is_err(),
            "old() should be rejected in pearlite"
        );
    }

    #[test]
    fn test_pearlite_reject_nested_old() {
        // Even deeply nested old() should be rejected
        let expr: Expr = parse_quote!((a > 0) && (b < old(c)));
        assert!(
            validate_as_pearlite(&expr).is_err(),
            "nested old() should be rejected"
        );
    }

    #[test]
    fn test_pearlite_validate_view_method() {
        // view() method calls are valid in pearlite
        let expr: Expr = parse_quote!(x.view() == y.view());
        assert!(
            validate_as_pearlite(&expr).is_ok(),
            "view() method should be valid"
        );
    }

    #[test]
    fn test_pearlite_validate_arithmetic() {
        // Arithmetic in boolean context
        let expr: Expr = parse_quote!(x + y * z > 0);
        assert!(
            validate_as_pearlite(&expr).is_ok(),
            "arithmetic should be valid"
        );
    }

    // ==========================================================================
    // Expansion tests
    // ==========================================================================

    #[test]
    fn test_expand_pearlite_basic() {
        let expr: Expr = syn::parse_quote!(x > 0);
        let expanded = expand_pearlite(&expr);
        let s = expanded.to_string();
        // Check that cfg-conditional code is emitted
        // Note: quote! uses "# [cfg (trust_wp)]" with spaces
        assert!(s.contains("cfg"), "should have cfg attribute");
        assert!(s.contains("trust_wp"), "should reference trust_wp cfg flag");
        assert!(s.contains("__trust_wp_pearlite"), "should have doc marker");
        assert!(s.contains("true"), "should have stub value");
    }

    #[test]
    fn test_expand_pearlite_with_comparison() {
        // Test that pearlite expressions with comparisons work
        // This simulates what would appear inside a #[logic] function body
        let expr: Expr = syn::parse_quote!(a >= b && b >= 0);
        let expanded = expand_pearlite(&expr);
        let s = expanded.to_string();
        // The expression should appear in the closure body
        assert!(
            s.contains("__pearlite_result"),
            "should have result binding"
        );
        assert!(s.contains("bool"), "should return bool");
    }

    #[test]
    fn test_expand_pearlite_closure_invoked() {
        // Verify the closure is invoked to return the bool value
        let expr: Expr = syn::parse_quote!(x == y);
        let expanded = expand_pearlite(&expr);
        let s = expanded.to_string();
        // The closure should be called: __pearlite_result()
        assert!(
            s.contains("__pearlite_result ()"),
            "closure should be invoked"
        );
    }
}
