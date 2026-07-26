// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Helper utilities for `extern_spec!` macro expansion.
//!
//! Extracted from `extern_spec.rs` to keep file size under 500 lines.

use proc_macro2::Span;
use quote::{format_ident, quote};
use syn::{
    fold::Fold,
    punctuated::Punctuated,
    token::{Colon, Comma},
    Attribute, FnArg, Ident, Pat, PatType, Path, Result, Signature, Type, TypePath,
};

/// Extract the path string from a Type for lookup purposes.
///
/// Returns `None` for unsupported type forms (qualified paths like `<T as Trait>::Assoc`,
/// references, tuples, etc.). The caller should handle this case appropriately.
pub(crate) fn type_to_path_string(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(TypePath { qself: None, path }) => {
            let segments: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
            Some(segments.join("::"))
        }
        _ => None,
    }
}

/// Extract a simple path string from a trait path for lookup purposes.
pub(crate) fn path_to_string(path: &Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

/// Extract a target name string from a Type.
///
/// Path types use their segment identifiers (`Option::<T>` -> `Option`) to
/// match the existing `extern_spec` lookup behavior. Other forms (for example,
/// tuple self types in trait impls) are compacted from tokens.
pub(crate) fn type_to_target_string(ty: &Type) -> String {
    if let Some(path) = type_to_path_string(ty) {
        return path;
    }
    let compact: String = quote!(#ty)
        .to_string()
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    compact.replace(',', ", ")
}

/// Extract requires/ensures attributes from the method's attributes.
///
/// Returns an error if a contract attribute uses a form other than `#[requires(...)]`
/// or `#[ensures(...)]` (e.g., bare `#[requires]` or `#[requires = "expr"]`), which
/// would otherwise be silently dropped (#810).
pub(crate) fn extract_contracts(attrs: &[Attribute]) -> Result<(Vec<String>, Vec<String>)> {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();

    for attr in attrs {
        if let Some(ident) = attr.path().get_ident() {
            if ident == "requires" {
                if let syn::Meta::List(meta_list) = &attr.meta {
                    requires.push(meta_list.tokens.to_string());
                } else {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "extern_spec: #[requires] must use parenthesized form: #[requires(expr)]",
                    ));
                }
            } else if ident == "ensures" {
                if let syn::Meta::List(meta_list) = &attr.meta {
                    ensures.push(meta_list.tokens.to_string());
                } else {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "extern_spec: #[ensures] must use parenthesized form: #[ensures(expr)]",
                    ));
                }
            }
        }
    }

    Ok((requires, ensures))
}

/// Generate a unique identifier for the extern spec stub function.
///
/// The type component uses injective encoding so names like `foo::bar` and
/// `foo_bar` remain distinct (#1461, #1435).
pub(crate) fn generate_stub_ident(type_name: &str, method_name: &str, span: Span) -> Ident {
    let clean_type = encode_ident_component(type_name);
    format_ident!("__extern_spec_{}_{}", clean_type, method_name, span = span)
}

pub(crate) fn encode_ident_component(name: &str) -> String {
    let mut encoded = String::with_capacity(name.len() + 16);
    for ch in name.chars() {
        match ch {
            '_' => encoded.push_str("__"),
            ch if ch.is_ascii_alphanumeric() => encoded.push(ch),
            '<' => encoded.push_str("_LT_"),
            '>' => encoded.push_str("_GT_"),
            ',' => encoded.push_str("_C_"),
            ':' => encoded.push_str("_P_"),
            ' ' => encoded.push_str("_S_"),
            '&' => encoded.push_str("_R_"),
            '*' => encoded.push_str("_D_"),
            '(' => encoded.push_str("_LP_"),
            ')' => encoded.push_str("_RP_"),
            '[' => encoded.push_str("_LB_"),
            ']' => encoded.push_str("_RB_"),
            _ => {
                use std::fmt::Write;
                let _ = write!(encoded, "_x{:02X}_", ch as u32);
            }
        }
    }
    if encoded.is_empty() {
        encoded.push('_');
    }
    encoded
}

/// Extract parameter names from a method signature for doc-marker emission.
///
/// Returns comma-separated names: `self` receivers become `"self"`, typed
/// parameters use their identifier, and unsupported patterns use `"_"`.
pub(crate) fn extract_param_names(sig: &Signature) -> Vec<String> {
    sig.inputs
        .iter()
        .map(|input| match input {
            FnArg::Receiver(_) => "self".to_string(),
            FnArg::Typed(PatType { pat, .. }) => {
                if let Pat::Ident(pat_ident) = pat.as_ref() {
                    pat_ident.ident.to_string()
                } else {
                    "_".to_string()
                }
            }
        })
        .collect()
}

/// Convert a Signature's inputs to call arguments.
/// Handles both `self` receivers and typed parameters.
///
/// Note: Complex patterns like `(a, b): (i32, i32)` are not supported.
/// External function specs should use simple identifier patterns.
pub(crate) fn sig_to_call_args(sig: &Signature) -> Punctuated<syn::Expr, Comma> {
    let mut args = Punctuated::new();

    for (idx, input) in sig.inputs.iter().enumerate() {
        let expr: syn::Expr = match input {
            FnArg::Receiver(_) => {
                // `self` receiver becomes `self_` in the call
                syn::parse_quote!(self_)
            }
            FnArg::Typed(PatType { pat, .. }) => {
                // Extract the identifier from the pattern
                if let Pat::Ident(pat_ident) = pat.as_ref() {
                    let ident = &pat_ident.ident;
                    syn::parse_quote!(#ident)
                } else {
                    // For unsupported complex patterns, generate a placeholder.
                    // This will cause a compile error if the stub is ever called,
                    // but extern_spec stubs are never called at runtime anyway.
                    let placeholder = format_ident!("__unsupported_pattern_{}", idx);
                    syn::parse_quote!(#placeholder)
                }
            }
        };
        args.push(expr);
    }

    args
}

/// Syn fold that replaces bare `Self` type references with a concrete type.
///
/// Extern spec stubs are standalone functions (not inside an `impl` block),
/// so `Self` is not in scope. This folder rewrites `Self` occurrences in
/// parameter types and return types to the concrete self type.
struct ReplaceSelf<'a> {
    self_ty: &'a Type,
}

impl Fold for ReplaceSelf<'_> {
    fn fold_type(&mut self, ty: Type) -> Type {
        match &ty {
            Type::Path(TypePath { qself: None, path }) if path.is_ident("Self") => {
                self.self_ty.clone()
            }
            _ => syn::fold::fold_type(self, ty),
        }
    }
}

/// Transform signature to replace `self` with `self_: SelfType` and `Self` with
/// the concrete type. Preserves lifetimes from the receiver (e.g., `&'a self`
/// -> `self_: &'a Type`).
pub(crate) fn transform_sig_for_stub(sig: &Signature, self_ty: &Type) -> Signature {
    let mut folder = ReplaceSelf { self_ty };
    let mut new_sig = sig.clone();
    new_sig.inputs = sig
        .inputs
        .iter()
        .map(|input| match input {
            FnArg::Receiver(recv) => {
                // Replace `self` with `self_: &Type` or `self_: Type`
                // Preserve lifetime from the reference if present
                let ty: Type = if let Some((_, lifetime)) = &recv.reference {
                    if recv.mutability.is_some() {
                        syn::parse_quote!(&#lifetime mut #self_ty)
                    } else {
                        syn::parse_quote!(&#lifetime #self_ty)
                    }
                } else {
                    self_ty.clone()
                };
                FnArg::Typed(PatType {
                    attrs: recv.attrs.clone(),
                    pat: Box::new(syn::parse_quote!(self_)),
                    colon_token: Colon::default(),
                    ty: Box::new(ty),
                })
            }
            FnArg::Typed(pat_ty) => {
                // Replace `Self` in parameter types with the concrete type
                let folded_ty = folder.fold_type((*pat_ty.ty).clone());
                FnArg::Typed(PatType {
                    attrs: pat_ty.attrs.clone(),
                    pat: pat_ty.pat.clone(),
                    colon_token: pat_ty.colon_token,
                    ty: Box::new(folded_ty),
                })
            }
        })
        .collect();
    // Also replace `Self` in the return type
    new_sig.output = folder.fold_return_type(new_sig.output);
    // Also replace `Self` in where clause predicates. Without this,
    // `where Self: Clone` would retain bare `Self` in the generated stub,
    // causing E0411 since stubs are standalone functions. (#1628)
    if let Some(ref mut where_clause) = new_sig.generics.where_clause {
        where_clause.predicates = where_clause
            .predicates
            .iter()
            .map(|p| folder.fold_where_predicate(p.clone()))
            .collect();
    }
    new_sig
}

/// Validate contract expressions for a single method.
///
/// All other macro entry points call `validate_contract_attr`; this ensures
/// `extern_spec` methods also validate expressions (#810, issue 2).
pub(crate) fn validate_contracts(
    requires: &[String],
    ensures: &[String],
    span: Span,
) -> Result<()> {
    for req_text in requires {
        let tokens: proc_macro::TokenStream = req_text.parse().map_err(|_| {
            syn::Error::new(span, format!("failed to tokenize requires: {req_text}"))
        })?;
        if let Err(e) =
            crate::attrs::validate_contract_attr(&tokens, crate::contract::ContractKind::Requires)
        {
            return Err(syn::Error::new(
                span,
                format!("extern_spec requires: {}", e.message()),
            ));
        }
    }
    for ens_text in ensures {
        let tokens: proc_macro::TokenStream = ens_text.parse().map_err(|_| {
            syn::Error::new(span, format!("failed to tokenize ensures: {ens_text}"))
        })?;
        if let Err(e) =
            crate::attrs::validate_contract_attr(&tokens, crate::contract::ContractKind::Ensures)
        {
            return Err(syn::Error::new(
                span,
                format!("extern_spec ensures: {}", e.message()),
            ));
        }
    }
    Ok(())
}
