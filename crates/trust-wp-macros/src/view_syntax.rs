// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract syntax preprocessing
//!
//! Transforms Creusot-style syntax to valid Rust for syn parsing:
//! - `expr@` → `view(expr)` (postfix view operator)
//! - `^expr` → `final_value(expr)` (prefix final/prophecy operator)
//!
//! # Algorithm
//!
//! **@ postfix (view):**
//! Scans `TokenStream` for `@` punctuation. When found:
//! 1. Identify the preceding expression (handles grouping, method chains)
//! 2. Wrap it in `view(...)`
//! 3. Continue scanning for nested `@` occurrences
//!
//! **^ prefix (final):**
//! Scans `TokenStream` for `^` punctuation. When found:
//! 1. Identify the following expression (handles grouping)
//! 2. Replace `^expr` with `final_value(expr)`
//!
//! # Examples
//!
//! - `x@` → `view(x)`
//! - `self.data@` → `view(self.data)`
//! - `v@.len()` → `view(v).len()`
//! - `old(x)@` → `view(old(x))`
//! - `x@ + y@` → `view(x) + view(y)`
//! - `^v` → `final_value(v)`
//! - `^v == old(*v) + 1` → `final_value(v) == old(*v) + 1`
//! - `(^self)@` → `view(final_value(self))`

use proc_macro2::{Group, Span, TokenStream, TokenTree};
use quote::quote_spanned;

/// Transforms contract syntax to valid Rust for syn parsing.
///
/// Applies both transformations:
/// 1. `expr@` → `view(expr)` (postfix view operator)
/// 2. `^expr` → `final_value(expr)` (prefix final/prophecy operator)
///
/// The `final_value` transformation runs first so `(^self)@` becomes
/// `view(final_value(self))` correctly.
pub(crate) fn transform_view_syntax(input: TokenStream) -> TokenStream {
    // First transform ^ prefix to final_value()
    let after_final = transform_final_syntax(input);
    // Then transform @ postfix to view()
    let tokens: Vec<TokenTree> = after_final.into_iter().collect();
    transform_tokens(&tokens)
}

/// Transforms `^expr` to `final_value(expr)`.
///
/// Handles:
/// - `^v` → `final_value(v)`
/// - `^self` → `final_value(self)`
/// - `(^v)` → `(final_value(v))`
fn transform_final_syntax(input: TokenStream) -> TokenStream {
    let tokens: Vec<TokenTree> = input.into_iter().collect();
    transform_final_tokens(&tokens)
}

fn transform_final_tokens(tokens: &[TokenTree]) -> TokenStream {
    let mut result: Vec<TokenTree> = Vec::new();
    let mut i = 0;

    while i < tokens.len() {
        // Check if this token is `^` and followed by an expression
        if is_caret_punct(&tokens[i]) {
            if i + 1 < tokens.len() {
                // Collect the expression after ^ and wrap in final_value()
                let (expr_tokens, consumed) = collect_final_expr(&tokens[i + 1..]);
                let span = tokens[i].span();
                let wrapped = wrap_in_final_value(&expr_tokens, span);
                result.extend(wrapped);
                i += 1 + consumed; // Skip ^ and the expression
            } else {
                // Lone ^ at end - just pass through
                result.push(tokens[i].clone());
                i += 1;
            }
        } else {
            // Not ^, process normally (recursing into groups)
            result.push(transform_final_token(&tokens[i]));
            i += 1;
        }
    }

    result.into_iter().collect()
}

/// Check if a token is the `^` punctuation.
fn is_caret_punct(token: &TokenTree) -> bool {
    matches!(token, TokenTree::Punct(p) if p.as_char() == '^')
}

/// Transform a single token for final syntax, recursing into groups.
fn transform_final_token(token: &TokenTree) -> TokenTree {
    match token {
        TokenTree::Group(g) => {
            let inner = transform_final_syntax(g.stream());
            TokenTree::Group(Group::new(g.delimiter(), inner))
        }
        _ => token.clone(),
    }
}

/// Collect tokens that form the expression after `^`.
///
/// Returns (tokens, count) where count is how many tokens were consumed.
///
/// Handles:
/// - Identifiers: `^v` → `v`, consumed=1
/// - Groups: `^(expr)` → `(expr)`, consumed=1
/// - Prefix unary `*`/`&`/`!`: `^*v` → `*v`, consumed=2; `^**v` → `**v`, consumed=3
fn collect_final_expr(tokens: &[TokenTree]) -> (TokenStream, usize) {
    if tokens.is_empty() {
        return (TokenStream::new(), 0);
    }

    match &tokens[0] {
        // Single identifier: ^v
        TokenTree::Ident(_) => {
            let result: TokenStream = std::iter::once(tokens[0].clone()).collect();
            (result, 1)
        }
        // Grouped expression: ^(expr) - need to recurse into the group
        TokenTree::Group(g) => {
            let inner = transform_final_syntax(g.stream());
            let new_group = TokenTree::Group(Group::new(g.delimiter(), inner));
            let result: TokenStream = std::iter::once(new_group).collect();
            (result, 1)
        }
        // Prefix unary operators: ^*v, ^**v, ^&v, ^!v
        // Consume the operator and recurse for the inner expression.
        TokenTree::Punct(p) if matches!(p.as_char(), '*' | '&' | '!') => {
            let (inner_tokens, inner_consumed) = collect_final_expr(&tokens[1..]);
            let op_token: TokenStream = std::iter::once(tokens[0].clone()).collect();
            let result: TokenStream = op_token.into_iter().chain(inner_tokens).collect();
            (result, 1 + inner_consumed)
        }
        // Anything else - just return it
        _ => {
            let result: TokenStream = std::iter::once(tokens[0].clone()).collect();
            (result, 1)
        }
    }
}

/// Wrap tokens in a `final_value(...)` call.
fn wrap_in_final_value(expr: &TokenStream, span: Span) -> TokenStream {
    quote_spanned!(span=> final_value(#expr))
}

fn transform_tokens(tokens: &[TokenTree]) -> TokenStream {
    let mut result: Vec<TokenTree> = Vec::new();
    let mut i = 0;

    while i < tokens.len() {
        // Check if next token (if any) is `@`
        if i + 1 < tokens.len() && is_at_punct(&tokens[i + 1]) {
            // Collect the expression before `@` and wrap in view()
            let expr_tokens = collect_view_expr(&tokens[..=i]);
            let span = tokens[i + 1].span(); // Use @ span for better errors
            let wrapped = wrap_in_view(expr_tokens, span);

            // Remove previously added tokens that are part of this expression
            let expr_len = view_expr_len(&tokens[..=i]);
            let remove = expr_len.saturating_sub(1);
            if remove > 0 {
                result.truncate(result.len().saturating_sub(remove));
            }
            result.extend(wrapped);
            i += 2; // Skip past the @
        } else {
            // No @, process normally (recursing into groups)
            result.push(transform_token(&tokens[i]));
            i += 1;
        }
    }

    result.into_iter().collect()
}

/// Check if a token is the `@` punctuation.
fn is_at_punct(token: &TokenTree) -> bool {
    matches!(token, TokenTree::Punct(p) if p.as_char() == '@')
}

/// Transform a single token, recursing into groups.
fn transform_token(token: &TokenTree) -> TokenTree {
    match token {
        TokenTree::Group(g) => {
            let inner = transform_view_syntax(g.stream());
            TokenTree::Group(Group::new(g.delimiter(), inner))
        }
        _ => token.clone(),
    }
}

/// Collect tokens that form the expression before `@`.
///
/// Works backwards from position i to find the complete expression:
/// - Identifiers: `x`
/// - Field/method access: `self.data`, `v.len()`
/// - Groups: `(expr)`, `old(x)`
/// - Chained: `self.data.clone()`
fn collect_view_expr(tokens: &[TokenTree]) -> TokenStream {
    if tokens.is_empty() {
        return TokenStream::new();
    }

    let start = find_view_expr_start(tokens);
    tokens[start..].iter().cloned().collect()
}

/// Count how many tokens are in the view expression.
fn view_expr_len(tokens: &[TokenTree]) -> usize {
    if tokens.is_empty() {
        return 0;
    }

    let start = find_view_expr_start(tokens);
    tokens.len() - start
}

fn find_view_expr_start(tokens: &[TokenTree]) -> usize {
    // Start from the end and work backwards.
    let end = tokens.len();
    let mut start = end - 1;

    // If last token is a group (e.g., method args `()`), include the identifier before it
    // This handles `foo()@` → includes both `foo` and `()`
    if let TokenTree::Group(_) = &tokens[start] {
        if start > 0 {
            if let TokenTree::Ident(_) = &tokens[start - 1] {
                start -= 1;
            }
        }
    }

    // Walk backwards to find expression start
    while start > 0 {
        let prev = &tokens[start - 1];
        match prev {
            // Method/field access chain: continue backwards past `.`
            TokenTree::Punct(p) if p.as_char() == '.' => {
                if start >= 2 {
                    // Look at what's before the dot
                    let before_dot = &tokens[start - 2];
                    match before_dot {
                        // Could be `ident.` or `group.` (e.g., `foo().bar`)
                        TokenTree::Ident(_) => {
                            start -= 2;
                        }
                        TokenTree::Group(_) => {
                            start -= 2;
                            // If there's an ident before the group, include it too
                            if start > 0 {
                                if let TokenTree::Ident(_) = &tokens[start - 1] {
                                    start -= 1;
                                }
                            }
                        }
                        _ => break,
                    }
                } else {
                    break;
                }
            }
            // Reference operator: `&x@` → `view(&x)` - include the `&`
            TokenTree::Punct(p) if p.as_char() == '&' => {
                start -= 1;
            }
            // Dereference operator: `*x@` → `view(*x)` - include the `*`
            TokenTree::Punct(p) if p.as_char() == '*' => {
                start -= 1;
            }
            // Note: ^ (final) is handled by transform_final_syntax before we get here,
            // so ^x@ becomes final_value(x)@ and then view(final_value(x))
            _ => break,
        }
    }

    start
}

/// Wrap tokens in a `view(...)` call.
fn wrap_in_view(expr: TokenStream, span: Span) -> TokenStream {
    // Transform any nested @ in the expression first
    let transformed = transform_view_syntax(expr);
    quote_spanned!(span=> view(#transformed))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn transform_str(input: &str) -> String {
        let tokens: TokenStream = input.parse().unwrap();
        transform_view_syntax(tokens).to_string()
    }

    #[test]
    fn test_simple_view() {
        assert_eq!(transform_str("x@"), "view (x)");
    }

    #[test]
    fn test_field_access() {
        assert_eq!(transform_str("self.data@"), "view (self . data)");
    }

    #[test]
    fn test_method_chain() {
        // v@ followed by .len() becomes view(v).len()
        assert_eq!(transform_str("v@.len()"), "view (v) . len ()");
    }

    #[test]
    fn test_multiple_views() {
        assert_eq!(transform_str("x@ + y@"), "view (x) + view (y)");
    }

    #[test]
    fn test_comparison() {
        assert_eq!(
            transform_str("result@ == Seq::empty()"),
            "view (result) == Seq :: empty ()"
        );
    }

    #[test]
    fn test_nested_in_old() {
        // old(x@) - the @ is inside the group
        assert_eq!(transform_str("old(x@)"), "old (view (x))");
    }

    #[test]
    fn test_no_at() {
        // Pass through unchanged when no @
        assert_eq!(transform_str("x > 0"), "x > 0");
        assert_eq!(transform_str("old(x) + 1"), "old (x) + 1");
    }

    #[test]
    fn test_reference_view() {
        assert_eq!(transform_str("&x@"), "view (& x)");
    }

    #[test]
    fn test_complex_chain() {
        // self.items.len()@ - full method chain before @
        assert_eq!(
            transform_str("self.items.len()@"),
            "view (self . items . len ())"
        );
    }

    #[test]
    fn test_final_view() {
        // ^x@ - final (prophetic) value with view
        // ^ is transformed to final_value(), then @ wraps in view()
        assert_eq!(transform_str("^x@"), "view (final_value (x))");
    }

    #[test]
    fn test_deref_view() {
        // *x@ - dereference with view
        assert_eq!(transform_str("*x@"), "view (* x)");
    }

    #[test]
    fn test_grouped_final_view() {
        // (^self)@ - grouped final value with view (common Creusot pattern)
        assert_eq!(transform_str("(^self)@"), "view ((final_value (self)))");
    }

    #[test]
    fn test_full_creusot_spec() {
        // Full Creusot-style spec: (^self)@ == self@.push_back(v)
        let result = transform_str("(^self)@ == self@.push_back(v)");
        assert_eq!(
            result,
            "view ((final_value (self))) == view (self) . push_back (v)"
        );
    }

    // Tests for ^ prefix (final/prophecy) syntax
    #[test]
    fn test_final_simple() {
        // ^v becomes final_value(v)
        assert_eq!(transform_str("^v"), "final_value (v)");
    }

    #[test]
    fn test_final_comparison() {
        // ^v >= 0 - typical postcondition on final value
        assert_eq!(transform_str("^v >= 0"), "final_value (v) >= 0");
    }

    #[test]
    fn test_final_with_old() {
        // ^v == old(*v) + 1 - typical increment postcondition
        assert_eq!(
            transform_str("^v == old(*v) + 1"),
            "final_value (v) == old (* v) + 1"
        );
    }

    #[test]
    fn test_final_multiple() {
        // Multiple final values in one expression
        assert_eq!(
            transform_str("^a == old(*b) && ^b == old(*a)"),
            "final_value (a) == old (* b) && final_value (b) == old (* a)"
        );
    }

    #[test]
    fn test_final_grouped() {
        // (^v) - grouped final value
        assert_eq!(transform_str("(^v)"), "(final_value (v))");
    }

    #[test]
    fn test_no_final() {
        // Pass through unchanged when no ^
        assert_eq!(transform_str("*v == old(*v) + 1"), "* v == old (* v) + 1");
    }

    // Tests for ^* prefix chains (#1196)
    #[test]
    fn test_final_deref() {
        // ^*v — Final(Deref(v))
        assert_eq!(transform_str("^*v"), "final_value (* v)");
    }

    #[test]
    fn test_final_double_deref() {
        // ^**v — Final(Deref(Deref(v)))
        assert_eq!(transform_str("^**v"), "final_value (** v)");
    }

    #[test]
    fn test_grouped_final_deref_view() {
        // (^*bx)@ — from closures/09_fnonce_resolve.rs
        assert_eq!(transform_str("(^*bx)@"), "view ((final_value (* bx)))");
    }

    #[test]
    fn test_grouped_final_double_deref_view() {
        // (^**by)@ — from closures/09_fnonce_resolve.rs
        assert_eq!(transform_str("(^**by)@"), "view ((final_value (** by)))");
    }

    #[test]
    fn test_grouped_final_deref_view_eq() {
        // (^**by)@ == 1 — full expression from Creusot test
        assert_eq!(
            transform_str("(^**by)@ == 1"),
            "view ((final_value (** by))) == 1"
        );
    }

    #[test]
    fn test_final_ref() {
        // ^&v — Final(&v) (unusual but should work)
        assert_eq!(transform_str("^&v"), "final_value (& v)");
    }
}
