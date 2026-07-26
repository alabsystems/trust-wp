// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expansion logic for `proof_assert!` and `trusted_proof_assert!` macros.

use proc_macro::TokenStream;
use quote::quote;
use syn::Expr;

use crate::{attrs, contract::ContractKind, transform::preprocess_view_syntax};

/// Check if `haystack` contains `needle` at a word boundary.
///
/// Returns true only when the character immediately before the match is
/// not an ASCII alphanumeric or underscore (or the match starts at position 0).
/// This prevents `"my_result.foo()"` from matching when `needle` is `"result."`.
pub(crate) fn has_word_boundary_match(haystack: &str, needle: &str) -> bool {
    let bytes = haystack.as_bytes();
    let needle_bytes = needle.as_bytes();
    if needle_bytes.is_empty() {
        return false;
    }
    for (i, window) in bytes.windows(needle_bytes.len()).enumerate() {
        if window == needle_bytes {
            if i == 0 {
                return true;
            }
            let prev = bytes[i - 1];
            if !prev.is_ascii_alphanumeric() && prev != b'_' {
                return true;
            }
        }
    }
    false
}

/// Expand `proof_assert!(expr)` or `proof_assert! { stmt; stmt; expr }` macro.
///
/// Supports both single-expression and multi-statement block forms. The
/// multi-statement form is used in Creusot for lemma invocation hints:
/// ```text
/// proof_assert! {
///     lemma_call();
///     assertion_expr
/// }
/// ```
pub(crate) fn expand_proof_assert(input: TokenStream) -> TokenStream {
    expand_proof_assert_with_marker(input, "trust-wp:proof_assert:")
}

/// Expand trusted proof assertion syntax used by `#[trusted] proof_assert!(...)`.
///
/// Trusted proof assertions are parsed/validated like regular proof assertions,
/// but carry a distinct marker so the driver can treat them as assumptions.
pub(crate) fn expand_trusted_proof_assert(input: TokenStream) -> TokenStream {
    expand_proof_assert_with_marker(input, "trust-wp:trusted_proof_assert:")
}

fn expand_proof_assert_with_marker(input: TokenStream, marker_prefix: &str) -> TokenStream {
    let original_input = input.clone();
    let input = preprocess_view_syntax(input);
    let expr_text = original_input.to_string();
    let expr_text_compact: String = expr_text.chars().filter(|c| !c.is_whitespace()).collect();

    // Always validate contract semantics (old/result rejection) regardless of
    // syntax path:
    // - Rust expression syntax uses syn-based validation
    // - Multi-statement/non-Rust proof_assert syntax uses contract-body parsing
    let validation_result = if syn::parse::<Expr>(input).is_ok() {
        attrs::validate_contract_attr(&original_input, ContractKind::Requires)
    } else {
        attrs::validate_contract_body_attr(&original_input, ContractKind::Requires)
    };
    if let Err(e) = validation_result {
        // Creusot compatibility: allow local variables named `result` when
        // used as method-call receivers (e.g., `result.ext_eq(...)`) inside
        // proof_assert! blocks. Keep rejecting bare `result` and `old(...)`.
        let allow_local_result_receiver =
            matches!(
                e.kind,
                crate::contract::ContractValidationError::ResultInWrongContext
            ) && has_word_boundary_match(&expr_text_compact, "result.");
        if !allow_local_result_receiver {
            return attrs::error_to_tokens("proof_assert", &e);
        }
    }

    proof_assert_expansion_with_marker(&expr_text, marker_prefix).into()
}

/// Generate the proof_assert expansion tokens from a validated expression string.
///
/// Under `cfg(trust_wp)`, emits a `#[doc = "trust-wp:proof_assert:<expr>"]` marker
/// on a dummy closure. Under `cfg(not(trust_wp))`, emits an empty block.
/// Separated from `expand_proof_assert` for unit testability.
#[cfg(test)]
pub(crate) fn proof_assert_expansion(expr_text: &str) -> proc_macro2::TokenStream {
    proof_assert_expansion_with_marker(expr_text, "trust-wp:proof_assert:")
}

pub(crate) fn proof_assert_expansion_with_marker(
    expr_text: &str,
    marker_prefix: &str,
) -> proc_macro2::TokenStream {
    let doc_marker = format!("{marker_prefix}{expr_text}");

    // The marker closure exists only so the driver can find a `Closure(def_id)`
    // aggregate statement with a `#[doc = "trust-wp:proof_assert:..."]` attribute
    // in MIR. No variable captures are needed — the driver extracts the assertion
    // text from the doc marker, not from the closure body. (#2586: the old
    // `&free_ident` captures caused borrowck failures when proof_assert! appeared
    // in code with live mutable borrows.)
    quote! {
        {
            #[cfg(trust_wp)]
            {
                let _ =
                    #[doc(hidden)]
                    #[doc = #doc_marker]
                    || -> bool {
                        true
                    };
            }

            #[cfg(not(trust_wp))]
            {}
        }
    }
}
