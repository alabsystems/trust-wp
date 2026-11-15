// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Marker attribute macros: `#[trusted]`, `#[erasure]`, `#[check]`, `#[opaque]`,
//! `#[bitwise_proof]`, `#[maintains]`, `#[open_inv_result]`.
//!
//! These attributes emit doc markers for driver detection without modifying
//! the item's semantics at compile time.

use proc_macro::TokenStream;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    ItemEnum, ItemFn, ItemMod, ItemStruct, ItemTrait, Macro, Token, TraitItemFn,
};

/// Extract the span of the first token from a `proc_macro::TokenStream`.
///
/// When an attribute has unexpected arguments, this points the error at the
/// first argument token rather than the macro invocation site.
pub(crate) fn first_token_span(attr: &TokenStream) -> proc_macro2::Span {
    let attr2: proc_macro2::TokenStream = attr.clone().into();
    attr2
        .into_iter()
        .next()
        .map_or_else(proc_macro2::Span::call_site, |t| t.span())
}

/// Process `#[opaque]` — hides a logic function body or type from callers.
pub(crate) fn process_opaque(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new(
            first_token_span(attr),
            format!("opaque: unexpected argument `{attr}`. #[opaque] takes no arguments"),
        )
        .to_compile_error()
        .into();
    }
    let item_tokens: proc_macro2::TokenStream = item.into();

    quote! {
        #[doc = "trust-wp:opaque:"]
        #item_tokens
    }
    .into()
}

/// Process `#[erasure(target)]` — relates a spec-enriched function to its runtime counterpart.
pub(crate) fn process_erasure(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "erasure: expected target path argument (e.g., #[erasure(target_fn)] or #[erasure(_)])",
        )
        .to_compile_error()
        .into();
    }
    let attr_text = attr.to_string();
    let item_tokens: proc_macro2::TokenStream = item.into();
    let doc_marker = format!("trust-wp:erasure:{attr_text}");

    quote! {
        #[doc = #doc_marker]
        #item_tokens
    }
    .into()
}

/// Known `#[check(mode)]` modes recognised by the driver.
const KNOWN_CHECK_MODES: &[&str] = &["terminates", "ghost"];

/// Process `#[check(mode)]` — marks a function as checked in a specific mode.
pub(crate) fn process_check(attr: &TokenStream, item: TokenStream) -> TokenStream {
    let mode = attr.to_string();
    if mode.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            format!(
                "check: expected a mode argument. Known modes: {}",
                KNOWN_CHECK_MODES.join(", ")
            ),
        )
        .to_compile_error()
        .into();
    }
    if !KNOWN_CHECK_MODES.contains(&mode.as_str()) {
        return syn::Error::new(
            first_token_span(attr),
            format!(
                "check: unknown mode `{mode}`. Known modes: {}",
                KNOWN_CHECK_MODES.join(", ")
            ),
        )
        .to_compile_error()
        .into();
    }
    let doc_marker = format!("trust-wp:check:{mode}");
    let item_tokens: proc_macro2::TokenStream = item.into();

    quote! {
        #[doc = #doc_marker]
        #[allow(dead_code)]
        #item_tokens
    }
    .into()
}

/// Emit a `trust-wp:trusted:` doc marker on a module item.
fn trusted_module(module: &ItemMod) -> TokenStream {
    let vis = &module.vis;
    let ident = &module.ident;
    let attrs = &module.attrs;
    let semi = &module.semi;

    if let Some((_brace, items)) = &module.content {
        quote! {
            #[doc = "trust-wp:trusted:"]
            #(#attrs)*
            #vis mod #ident { #(#items)* }
        }
        .into()
    } else {
        quote! {
            #[doc = "trust-wp:trusted:"]
            #(#attrs)*
            #vis mod #ident #semi
        }
        .into()
    }
}

/// Macro with optional semicolon for `#[trusted] proof_assert!(...)`.
struct MacroSemicolon {
    macro_call: Macro,
    semi: Option<Token![;]>,
}

impl Parse for MacroSemicolon {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let macro_call = input.parse::<Macro>()?;
        let semi = input.parse::<Option<Token![;]>>()?;
        Ok(Self { macro_call, semi })
    }
}

fn is_proof_assert_path(path: &syn::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.ident == "proof_assert")
}

/// Process `#[trusted]` — marks a function or module as axiomatically correct without verification.
///
/// Creusot compatibility: `#[trusted]` accepts optional hint arguments like
/// `#[trusted(terminates)]` or `#[trusted(terminates, positive(T))]` on
/// structs/enums to convey termination and positivity hints. trust-wp does not
/// yet consume these hints — they are accepted and ignored so the source
/// compiles, then the standard `trust-wp:trusted:` marker is emitted.
pub(crate) fn process_trusted(attr: &TokenStream, item: TokenStream) -> TokenStream {
    let _ = attr; // Creusot hint args accepted and ignored (see doc above).
    if let Ok(func) = syn::parse::<ItemFn>(item.clone()) {
        let vis = &func.vis;
        let sig = &func.sig;
        let block = &func.block;
        let attrs = &func.attrs;

        return quote! {
            #[doc = "trust-wp:trusted:"]
            #(#attrs)*
            #vis #sig #block
        }
        .into();
    }

    // Handle `#[trusted] default fn x(...) { ... }` — an inherent/trait impl
    // method, possibly carrying `default` (specialization). Mirror the ItemFn
    // branch but preserve `defaultness`: stripping `default` would re-trigger
    // E0520 ("matching definition is not marked default"). Axiomatizing this
    // body as trusted is sound (same as a non-default trusted method); callers
    // whose own obligations cannot be discharged still get rejected.
    if let Ok(func) = syn::parse::<syn::ImplItemFn>(item.clone()) {
        let vis = &func.vis;
        let defaultness = &func.defaultness;
        let sig = &func.sig;
        let block = &func.block;
        let attrs = &func.attrs;

        return quote! {
            #[doc = "trust-wp:trusted:"]
            #(#attrs)*
            #vis #defaultness #sig #block
        }
        .into();
    }

    // Handle `#[trusted] mod foo { ... }` — the driver's
    // `has_trusted_ancestor_module` propagates trusted status to all children.
    if let Ok(module) = syn::parse::<ItemMod>(item.clone()) {
        return trusted_module(&module);
    }

    // Handle `#[trusted(...)] struct/enum ... ` — Creusot allows trust hints
    // on types (e.g. `#[trusted(terminates, positive(T))]` for recursive
    // type definitions). trust-wp passes the type through unchanged with a
    // trust-wp:trusted: doc marker.
    if let Ok(item_struct) = syn::parse::<ItemStruct>(item.clone()) {
        return quote! {
            #[doc = "trust-wp:trusted:"]
            #item_struct
        }
        .into();
    }
    if let Ok(item_enum) = syn::parse::<ItemEnum>(item.clone()) {
        return quote! {
            #[doc = "trust-wp:trusted:"]
            #item_enum
        }
        .into();
    }

    // Handle `#[trusted] trait Foo { ... }` — Creusot allows trusting an entire
    // trait declaration. Pass through with a trust-wp:trusted: doc marker on the
    // trait item itself. The marker on the trait DefId does NOT propagate to its
    // children: `has_trusted_ancestor_module` only walks `Mod` parents, so trait
    // methods/impls are still verified normally (no spurious-trust false-accept).
    if let Ok(item_trait) = syn::parse::<ItemTrait>(item.clone()) {
        return quote! {
            #[doc = "trust-wp:trusted:"]
            #item_trait
        }
        .into();
    }

    // Creusot compatibility: allow `#[trusted] proof_assert!(...)` to pass
    // through so trusted proof assertions can be represented in source.
    if let Ok(MacroSemicolon { macro_call, semi }) = syn::parse::<MacroSemicolon>(item.clone()) {
        if is_proof_assert_path(&macro_call.path) {
            let tokens = &macro_call.tokens;
            return if semi.is_some() {
                quote! {
                    ::trust_wp::__trust_wp_trusted_proof_assert!(#tokens);
                }
                .into()
            } else {
                quote! {
                    ::trust_wp::__trust_wp_trusted_proof_assert!(#tokens)
                }
                .into()
            };
        }
    }

    match syn::parse::<TraitItemFn>(item) {
        Ok(trait_fn) => {
            let attrs = &trait_fn.attrs;
            let sig = &trait_fn.sig;
            let semi = &trait_fn.semi_token;
            let default = &trait_fn.default;

            if let Some(body) = default {
                quote! {
                    #[doc = "trust-wp:trusted:"]
                    #(#attrs)*
                    #sig #body
                }
                .into()
            } else {
                quote! {
                    #[doc = "trust-wp:trusted:"]
                    #(#attrs)*
                    #sig #semi
                }
                .into()
            }
        }
        Err(e) => syn::Error::new(
            e.span(),
            format!("trusted: expected function or module, got: {e}"),
        )
        .to_compile_error()
        .into(),
    }
}

/// Process `#[builtin("name")]` — marks an item as a built-in primitive.
///
/// Creusot compatibility: `#[builtin("name")]` tells Creusot that a function
/// or type corresponds to a built-in primitive in the target prover (e.g.,
/// a Why3 theory operator or a specific SMT theory function). In trust-wp this
/// is a pass-through marker: the attribute argument is recorded as a
/// `trust-wp:builtin:<arg-text>:` doc marker so the driver can detect the
/// annotation, and the item is emitted unchanged.
///
/// Real built-in routing (mapping the name to an SMT theory operator) is a
/// separate, deeper concern handled by the encoder. This entry point only
/// exposes the compile surface so Creusot-style source can be parsed.
///
/// Accepts `ItemFn`, `TraitItemFn`, `ItemStruct`, `ItemEnum`, and `ItemMod`
/// — mirroring `process_trusted` so the same surface coverage applies.
pub(crate) fn process_builtin(attr: &TokenStream, item: TokenStream) -> TokenStream {
    let attr_text = attr.to_string();
    if attr_text.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "builtin: expected a name argument (e.g., #[builtin(\"prim::name\")])",
        )
        .to_compile_error()
        .into();
    }
    let doc_marker = format!("trust-wp:builtin:{attr_text}:");

    if let Ok(func) = syn::parse::<ItemFn>(item.clone()) {
        let vis = &func.vis;
        let sig = &func.sig;
        let block = &func.block;
        let attrs = &func.attrs;
        return quote! {
            #[doc = #doc_marker]
            #(#attrs)*
            #vis #sig #block
        }
        .into();
    }

    if let Ok(item_struct) = syn::parse::<ItemStruct>(item.clone()) {
        return quote! {
            #[doc = #doc_marker]
            #item_struct
        }
        .into();
    }
    if let Ok(item_enum) = syn::parse::<ItemEnum>(item.clone()) {
        return quote! {
            #[doc = #doc_marker]
            #item_enum
        }
        .into();
    }

    if let Ok(module) = syn::parse::<ItemMod>(item.clone()) {
        let vis = &module.vis;
        let ident = &module.ident;
        let attrs = &module.attrs;
        let semi = &module.semi;
        if let Some((_brace, items)) = &module.content {
            return quote! {
                #[doc = #doc_marker]
                #(#attrs)*
                #vis mod #ident { #(#items)* }
            }
            .into();
        }
        return quote! {
            #[doc = #doc_marker]
            #(#attrs)*
            #vis mod #ident #semi
        }
        .into();
    }

    match syn::parse::<TraitItemFn>(item) {
        Ok(trait_fn) => {
            let attrs = &trait_fn.attrs;
            let sig = &trait_fn.sig;
            let semi = &trait_fn.semi_token;
            let default = &trait_fn.default;
            if let Some(body) = default {
                quote! {
                    #[doc = #doc_marker]
                    #(#attrs)*
                    #sig #body
                }
                .into()
            } else {
                quote! {
                    #[doc = #doc_marker]
                    #(#attrs)*
                    #sig #semi
                }
                .into()
            }
        }
        Err(e) => syn::Error::new(
            e.span(),
            format!("builtin: expected function, type, or module, got: {e}"),
        )
        .to_compile_error()
        .into(),
    }
}

/// Process `#[bitwise_proof]` — marks a function for bitvector-mode verification.
///
/// Compile-surface parity with Creusot's `#[bitwise_proof]`.
/// Currently a pass-through marker; real bitvector solver routing is a future concern.
pub(crate) fn process_bitwise_proof(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new(
            first_token_span(attr),
            format!(
                "bitwise_proof: unexpected argument `{attr}`. #[bitwise_proof] takes no arguments"
            ),
        )
        .to_compile_error()
        .into();
    }
    let item_tokens: proc_macro2::TokenStream = item.into();

    quote! {
        #[doc = "trust-wp:bitwise_proof:"]
        #item_tokens
    }
    .into()
}

/// Process `#[open_inv_result]` — suppresses result-type invariant injection.
///
/// When a function returns a type with an invariant (e.g., NonZeroU64),
/// the verifier normally adds the type invariant as a postcondition.
/// `#[open_inv_result]` suppresses this, allowing the function to return
/// a value that may not satisfy the type invariant.
pub(crate) fn process_open_inv_result(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new(
            first_token_span(attr),
            format!(
                "open_inv_result: unexpected argument `{attr}`. #[open_inv_result] takes no arguments"
            ),
        )
        .to_compile_error()
        .into();
    }
    let item_tokens: proc_macro2::TokenStream = item.into();

    quote! {
        #[doc = "trust-wp:open_inv_result:"]
        #item_tokens
    }
    .into()
}

/// Process `#[maintains(expr)]` — desugars to `#[requires(pre)] #[ensures(post)]`.
///
/// Creusot-compatible `maintains` clause desugaring:
/// - `#[maintains(P)]` → `#[requires(P)] #[ensures(P)]`
/// - `(mut x)` in receiver/args → `(* x)` in requires (deref), `(^ x)` in ensures (final value)
/// - `mut x` in args → `* x` in requires, `^ x` in ensures
///
/// This directly emits `trust-wp:requires:` and `trust-wp:ensures:` doc markers so
/// the driver's contract discovery picks them up without special-casing maintains,
/// and type-checks each clause as `#[requires]` / `#[ensures]` do.
pub(crate) fn process_maintains(attr: &TokenStream, item: TokenStream) -> TokenStream {
    let attr_text = attr.to_string();
    if attr_text.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "maintains: expected a clause argument (e.g., #[maintains(predicate())])",
        )
        .to_compile_error()
        .into();
    }
    let requires_text = maintains_transform_mut(&attr_text, "*");
    let ensures_text = maintains_transform_mut(&attr_text, "^");
    let mut item_tokens: proc_macro2::TokenStream = item.into();
    let mut helpers = proc_macro2::TokenStream::new();
    let clauses = requires_text
        .parse::<proc_macro2::TokenStream>()
        .ok()
        .zip(ensures_text.parse::<proc_macro2::TokenStream>().ok());
    // Each clause is type-checked as the `requires` / `ensures` it stands for
    // (`spec_tc`), and its marker carries the text its type-check body is
    // tagged with, so the driver reads the clause's calls as rustc resolved
    // them there (`trust-wp-driver` `logic::spec_calls`).
    let (req_marker, ens_marker) = match clauses {
        Some((requires, ensures)) => {
            for (kind, clause) in [
                (crate::spec_tc::FnClause::Requires, &requires),
                (crate::spec_tc::FnClause::Ensures, &ensures),
            ] {
                if let Some(helper) =
                    crate::spec_tc::trait_signature_helper(kind, clause, &item_tokens)
                {
                    helpers.extend(helper);
                }
                item_tokens = crate::spec_tc::insert_fn_clause(kind, clause, item_tokens);
            }
            (
                format!("trust-wp:requires:{requires}"),
                format!("trust-wp:ensures:{ensures}"),
            )
        }
        None => (
            format!("trust-wp:requires:{requires_text}"),
            format!("trust-wp:ensures:{ensures_text}"),
        ),
    };

    quote! {
        #helpers
        #[doc = #req_marker]
        #[doc = #ens_marker]
        #item_tokens
    }
    .into()
}

/// Transform `mut` keywords in a maintains clause to `*` (pre) or `^` (post).
///
/// Handles two patterns from Creusot's maintains syntax:
/// 1. `(mut X)` — parenthesized mut receiver/arg → `(op X)`
/// 2. bare `mut X` in argument positions → `op X`
///
/// The replacement is conservative: only `mut` followed by an identifier-like
/// token is replaced, avoiding accidental mutation of string literals or nested
/// expressions.
fn maintains_transform_mut(text: &str, op: &str) -> String {
    // Pattern: `(mut ` at any nesting level → `(op `
    // This handles `(mut self)`, `(mut a)`, etc.
    // The previous body mixed two different index spaces: `i` counted CHARACTERS
    // (it indexed `text.chars().collect()`), but was then used to slice `text`
    // by BYTES in `text[i..i + 4]` and `text[..i]`. Those agree only while the
    // input is ASCII; one multi-byte character and the comparison reads the
    // wrong region, or lands off a char boundary and panics. Walking the string
    // itself keeps one index space and makes every step total.
    let mut result = String::with_capacity(text.len().saturating_add(8));
    let mut rest = text;
    let mut consumed = 0usize;
    while let Some(ch) = rest.chars().next() {
        if let Some(after_mut) = rest.strip_prefix("mut ") {
            // Look back to find the preceding non-whitespace character.
            let prev_non_ws = text
                .get(..consumed)
                .and_then(|seen| seen.chars().rev().find(|c| !c.is_whitespace()));
            if matches!(prev_non_ws, Some('(' | ',') | None) {
                result.push_str(op);
                result.push(' ');
                rest = after_mut;
                consumed = consumed.saturating_add("mut ".len());
                continue;
            }
        }
        result.push(ch);
        let width = ch.len_utf8();
        rest = rest.get(width..).unwrap_or("");
        consumed = consumed.saturating_add(width);
    }
    result
}

/// Process `#[terminates]` — standalone alias for `#[check(terminates)]`.
///
/// Emits the same `trust-wp:check:terminates` doc marker as `#[check(terminates)]`
/// so the driver's `has_check_mode(attrs, "terminates")` detects it identically.
pub(crate) fn process_terminates(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new(
            first_token_span(attr),
            format!("terminates: unexpected argument `{attr}`. #[terminates] takes no arguments"),
        )
        .to_compile_error()
        .into();
    }
    let item_tokens: proc_macro2::TokenStream = item.into();

    quote! {
        #[doc = "trust-wp:check:terminates"]
        #[allow(dead_code)]
        #item_tokens
    }
    .into()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The old body indexed `text.chars().collect()` with `i` and then sliced
    /// `text[i..i + 4]` with the same `i` — character positions used as byte
    /// offsets. They agree only while the input is ASCII. With one multi-byte
    /// character ahead of the `mut`, the byte slice reads the wrong region (so
    /// the rewrite is missed) or lands off a char boundary (so it panics).
    #[test]
    fn maintains_transform_rewrites_mut_after_a_multibyte_character() {
        // `é` is two bytes: every char index after it is one less than its byte
        // offset, which is exactly the drift the old body had.
        assert_eq!(maintains_transform_mut("f(é, mut x)", "*"), "f(é, * x)");
        // A multi-byte character immediately before the delimiter, and several
        // of them, so the drift accumulates.
        assert_eq!(maintains_transform_mut("λλλ(mut s)", "^"), "λλλ(^ s)");
        // ASCII behaviour is unchanged.
        assert_eq!(maintains_transform_mut("(mut self)", "*"), "(* self)");
        // Non-delimiter context is still left alone.
        assert_eq!(maintains_transform_mut("permut ation", "*"), "permut ation");
    }

    #[test]
    fn test_maintains_transform_no_mut_unchanged() {
        assert_eq!(
            maintains_transform_mut("a.invariant(b, c)", "*"),
            "a.invariant(b, c)"
        );
        assert_eq!(
            maintains_transform_mut("a.invariant(b, c)", "^"),
            "a.invariant(b, c)"
        );
    }

    #[test]
    fn test_maintains_transform_parenthesized_mut_receiver() {
        assert_eq!(
            maintains_transform_mut("(mut self).invariants()", "*"),
            "(* self).invariants()"
        );
        assert_eq!(
            maintains_transform_mut("(mut self).invariants()", "^"),
            "(^ self).invariants()"
        );
    }

    #[test]
    fn test_maintains_transform_mut_in_args() {
        assert_eq!(
            maintains_transform_mut("(mut a).invariant(mut b, c)", "*"),
            "(* a).invariant(* b, c)"
        );
        assert_eq!(
            maintains_transform_mut("(mut a).invariant(mut b, c)", "^"),
            "(^ a).invariant(^ b, c)"
        );
    }

    #[test]
    fn test_maintains_transform_function_call_no_receiver() {
        assert_eq!(
            maintains_transform_mut("other_inv(a, b)", "*"),
            "other_inv(a, b)"
        );
    }

    #[test]
    fn test_maintains_transform_view_syntax_preserved() {
        assert_eq!(
            maintains_transform_mut("a.inv2(b@ + 0)", "*"),
            "a.inv2(b@ + 0)"
        );
    }

    #[test]
    fn test_maintains_transform_leading_mut_at_start() {
        // `mut x` at the very start of the clause (prev_non_ws is None)
        assert_eq!(maintains_transform_mut("mut x", "*"), "* x");
        assert_eq!(maintains_transform_mut("mut x", "^"), "^ x");
    }

    #[test]
    fn test_maintains_transform_multiple_mut_args() {
        assert_eq!(
            maintains_transform_mut("f(mut a, mut b, c)", "*"),
            "f(* a, * b, c)"
        );
        assert_eq!(
            maintains_transform_mut("f(mut a, mut b, c)", "^"),
            "f(^ a, ^ b, c)"
        );
    }
}
