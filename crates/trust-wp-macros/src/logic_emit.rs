// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function emission helpers.
//!
//! Shared codegen for `#[logic]`, `#[predicate]`, and `#[law]` proc macros.
//! Handles both regular functions and trait method declarations.

use proc_macro::TokenStream;
use quote::quote;
use syn::{ItemFn, TraitItemFn};

use crate::{logic, marker_attrs::first_token_span};

const LAW_DOC_MARKER: &str = "trust-wp:logic_law:";
const OPAQUE_DOC_MARKER: &str = "trust-wp:opaque:";
const SEALED_DOC_MARKER: &str = "trust-wp:logic_sealed:";
const OPEN_CRATE_DOC_MARKER: &str = "trust-wp:logic_open_crate:";
const OPEN_SUPER_DOC_MARKER: &str = "trust-wp:logic_open_super:";

fn extra_doc_markers_for_logic_attr(attr: &TokenStream, force_law: bool) -> Vec<&'static str> {
    let mut markers = Vec::new();
    if force_law || logic::logic_attr_contains_law(attr) {
        markers.push(LAW_DOC_MARKER);
    }
    if logic::logic_attr_contains_opaque(attr) {
        markers.push(OPAQUE_DOC_MARKER);
    }
    if logic::logic_attr_contains_sealed(attr) {
        markers.push(SEALED_DOC_MARKER);
    }
    if logic::logic_attr_contains_open_crate(attr) {
        markers.push(OPEN_CRATE_DOC_MARKER);
    }
    if logic::logic_attr_contains_open_super(attr) {
        markers.push(OPEN_SUPER_DOC_MARKER);
    }
    markers
}

/// Emit a logic function with doc marker and erased body.
///
/// The body is ALWAYS erased because:
/// 1. The driver reads contract/body text from doc markers, not compiled MIR
/// 2. Creusot logic bodies may use `dead` (compiler intrinsic) or other
///    Creusot-specific constructs that can't type-check in standard Rust
/// 3. Logic functions are never called at runtime
///
/// The original body text is preserved in a doc marker so the driver can
/// parse it as a contract expression.
pub(crate) fn emit_logic_function(
    func: &ItemFn,
    doc_marker: &str,
    extra_doc_markers: &[&str],
) -> TokenStream {
    let vis = &func.vis;
    let sig = &func.sig;
    let attrs = &func.attrs;
    let extra_docs = extra_doc_markers
        .iter()
        .map(|marker| quote! { #[doc = #marker] });

    let body_text = extract_block_body_text(&func.block);
    let body_marker = format!("trust-wp:logic_body:{body_text}");

    quote! {
        #[doc = #doc_marker]
        #(#extra_docs)*
        #[doc = #body_marker]
        #[allow(unused_variables, dead_code)]
        #(#attrs)*
        #vis #sig {
            unreachable!("logic functions are erased at runtime")
        }
    }
    .into()
}

/// Extract the body text from a function block for embedding in a doc marker.
///
/// For simple blocks with a single trailing expression `{ expr }`, returns just
/// the expression text. For empty blocks and single semicolon statements, it
/// emits an expression-compatible form to avoid downstream parse failures in
/// logic body extraction.
fn extract_block_body_text(block: &syn::Block) -> String {
    use syn::Stmt;

    match block.stmts.as_slice() {
        // `{}` represents unit.
        [] => "()".to_string(),
        // Common expression body: `{ expr }`
        [Stmt::Expr(expr, None)] => quote!(#expr).to_string(),
        // Statement-only body: `{ expr; }`
        [Stmt::Expr(expr, Some(_))] => quote!(#expr).to_string(),
        // Keep complex blocks intact until block parsing support is complete.
        _ => quote!(#block).to_string(),
    }
}

/// Emit a trait method declaration with a logic doc marker.
///
/// Trait method declarations have no body, so we just add the marker attribute
/// and pass the signature through unchanged. The driver discovers these via
/// doc attribute scanning on trait items.
pub(crate) fn emit_trait_logic_method(
    trait_fn: &TraitItemFn,
    doc_marker: &str,
    extra_doc_markers: &[&str],
) -> TokenStream {
    let attrs = &trait_fn.attrs;
    let sig = &trait_fn.sig;
    let default = &trait_fn.default;
    let semi = &trait_fn.semi_token;
    let extra_docs = extra_doc_markers
        .iter()
        .map(|marker| quote! { #[doc = #marker] });

    if let Some(body) = default {
        let body_text = extract_block_body_text(body);
        let body_marker = format!("trust-wp:logic_body:{body_text}");
        quote! {
            #[doc = #doc_marker]
            #(#extra_docs)*
            #[doc = #body_marker]
            #[allow(unused_variables, dead_code)]
            #(#attrs)*
            #sig {
                unreachable!("logic functions are erased at runtime")
            }
        }
        .into()
    } else {
        quote! {
            #[doc = #doc_marker]
            #(#extra_docs)*
            #(#attrs)*
            #sig #semi
        }
        .into()
    }
}

/// Process `#[logic]` attribute on a function or trait method.
pub(crate) fn process_logic(attr: &TokenStream, item: TokenStream) -> TokenStream {
    let mode = match logic::parse_logic_attr(attr) {
        Ok(m) => m,
        Err(e) => {
            return syn::Error::new(e.span, format!("logic: {}", e.message))
                .to_compile_error()
                .into();
        }
    };
    let doc_marker = format!("trust-wp:logic:{}", mode.marker_suffix());
    let extra_doc_markers = extra_doc_markers_for_logic_attr(attr, false);

    if let Ok(func) = syn::parse::<ItemFn>(item.clone()) {
        if let Err(e) = logic::validate_logic_function(&func, mode) {
            return syn::Error::new(e.span, format!("logic: {}", e.message))
                .to_compile_error()
                .into();
        }
        return emit_logic_function(&func, &doc_marker, &extra_doc_markers);
    }

    match syn::parse::<TraitItemFn>(item) {
        Ok(trait_fn) => {
            if let Err(e) = logic::validate_logic_signature(&trait_fn.sig, mode) {
                return syn::Error::new(e.span, format!("logic: {}", e.message))
                    .to_compile_error()
                    .into();
            }
            emit_trait_logic_method(&trait_fn, &doc_marker, &extra_doc_markers)
        }
        Err(e) => syn::Error::new(e.span(), format!("logic: expected function, got: {e}"))
            .to_compile_error()
            .into(),
    }
}

/// Process `#[predicate]` attribute on a function or trait method.
pub(crate) fn process_predicate(attr: &TokenStream, item: TokenStream) -> TokenStream {
    let mode = match logic::parse_logic_attr(attr) {
        Ok(m) => m,
        Err(e) => {
            return syn::Error::new(e.span, format!("predicate: {}", e.message))
                .to_compile_error()
                .into();
        }
    };
    let doc_marker = format!("trust-wp:logic:{}predicate", mode.marker_suffix());
    let extra_doc_markers = extra_doc_markers_for_logic_attr(attr, false);

    if let Ok(func) = syn::parse::<ItemFn>(item.clone()) {
        if let Err(e) = logic::validate_logic_function(&func, mode) {
            return syn::Error::new(e.span, format!("predicate: {}", e.message))
                .to_compile_error()
                .into();
        }
        if let Err(e) = logic::validate_predicate_function(&func) {
            return syn::Error::new(e.span, format!("predicate: {}", e.message))
                .to_compile_error()
                .into();
        }
        return emit_logic_function(&func, &doc_marker, &extra_doc_markers);
    }

    match syn::parse::<TraitItemFn>(item) {
        Ok(trait_fn) => {
            if let Err(e) = logic::validate_logic_signature(&trait_fn.sig, mode) {
                return syn::Error::new(e.span, format!("predicate: {}", e.message))
                    .to_compile_error()
                    .into();
            }
            if let Err(e) = logic::validate_predicate_signature(&trait_fn.sig) {
                return syn::Error::new(e.span, format!("predicate: {}", e.message))
                    .to_compile_error()
                    .into();
            }
            emit_trait_logic_method(&trait_fn, &doc_marker, &extra_doc_markers)
        }
        Err(e) => syn::Error::new(e.span(), format!("predicate: expected function, got: {e}"))
            .to_compile_error()
            .into(),
    }
}

/// Process `#[law]` attribute on a function or trait method.
pub(crate) fn process_law(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new(
            first_token_span(attr),
            format!("law: unexpected argument `{attr}`. #[law] takes no arguments"),
        )
        .to_compile_error()
        .into();
    }

    let doc_marker = format!("trust-wp:logic:{}", logic::LogicMode::Open.marker_suffix());
    let law_mode = logic::LogicMode::Open;
    let extra_doc_markers = extra_doc_markers_for_logic_attr(attr, true);

    if let Ok(func) = syn::parse::<ItemFn>(item.clone()) {
        if let Err(e) = logic::validate_logic_function(&func, law_mode) {
            return syn::Error::new(e.span, format!("law: {}", e.message))
                .to_compile_error()
                .into();
        }
        return emit_logic_function(&func, &doc_marker, &extra_doc_markers);
    }

    match syn::parse::<TraitItemFn>(item) {
        Ok(trait_fn) => {
            if let Err(e) = logic::validate_logic_signature(&trait_fn.sig, law_mode) {
                return syn::Error::new(e.span, format!("law: {}", e.message))
                    .to_compile_error()
                    .into();
            }
            emit_trait_logic_method(&trait_fn, &doc_marker, &extra_doc_markers)
        }
        Err(e) => syn::Error::new(e.span(), format!("law: expected function, got: {e}"))
            .to_compile_error()
            .into(),
    }
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod extract_block_body_text_tests {
    use quote::quote;

    use super::extract_block_body_text;

    #[test]
    fn empty_block_maps_to_unit_expression() {
        let block: syn::Block = syn::parse_quote!({});
        assert_eq!(extract_block_body_text(&block), "()");
    }

    #[test]
    fn semicolon_only_body_maps_to_expression_text() {
        let block: syn::Block = syn::parse_quote!({
            Self::f();
        });
        let body_text = extract_block_body_text(&block);
        let parsed: syn::Expr =
            syn::parse_str(&body_text).expect("extract_block_body_text should emit a valid expr");
        assert_eq!(quote!(#parsed).to_string(), quote!(Self::f()).to_string());
    }

    #[test]
    fn trailing_expression_body_is_preserved() {
        let block: syn::Block = syn::parse_quote!({ x + 1 });
        let body_text = extract_block_body_text(&block);
        let parsed: syn::Expr =
            syn::parse_str(&body_text).expect("extract_block_body_text should emit a valid expr");
        assert_eq!(quote!(#parsed).to_string(), quote!(x + 1).to_string());
    }
}
