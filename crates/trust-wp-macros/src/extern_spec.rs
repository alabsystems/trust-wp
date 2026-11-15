// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `extern_spec!` macro for specifying contracts on external functions.
//!
//! This macro allows users to attach specifications to functions they don't own
//! (e.g., standard library functions). The specs are registered at compile time
//! and discovered by trust-wp-driver during verification.
//!
//! # Syntax
//!
//! **Note:** Generic types must use turbofish syntax (`Type::<T>`) to avoid
//! parsing ambiguity where `<` could be interpreted as a comparison operator.
//!
//! ```rust,no_run
//! use trust_wp_macros::extern_spec;
//!
//! extern_spec! {
//!     // Use turbofish syntax for generic types: Option::<T> not Option<T>
//!     impl<T> core::option::Option::<T> {
//!         #[requires(self.is_some())]
//!         #[ensures(Some(result) == old(self))]
//!         fn unwrap(self) -> T;
//!     }
//! }
//! ```
//!
//! # Design
//!
//! Each method expands to a stub function carrying `trust-wp:extern_spec:*`
//! doc markers (target path, parameter names, requires, ensures) that the
//! driver reads to attach the contract to the named external item. The stubs
//! live inside a `const _: () = { .. }` block so they never enter the user's
//! namespace; a method body, when given, becomes a module-level `_body`
//! function verified against the method's own contract, as Creusot does.

use std::fmt::Write;

use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::{
    braced,
    parse::{Parse, ParseStream},
    spanned::Spanned,
    Attribute, Generics, Path, Result, Signature, Token, Type, TypePath,
};

use crate::extern_spec_helpers::{
    extract_contracts, extract_param_names, generate_stub_ident, path_to_string, sig_to_call_args,
    transform_sig_for_stub, type_to_target_string, validate_contracts,
};

/// Parsed `extern_spec`! input containing one or more impl blocks.
pub(crate) struct ExternSpecInput {
    items: Vec<ExternImplBlock>,
}

/// An impl block within `extern_spec`! containing methods with contracts.
struct ExternImplBlock {
    generics: Generics,
    trait_path: Option<Path>,
    self_ty: Type,
    methods: Vec<ExternMethod>,
}

/// A single method declaration with contracts.
struct ExternMethod {
    attrs: Vec<Attribute>,
    sig: Signature,
    /// Optional body. Creusot proves an `extern_spec!` body against the
    /// method's own contract (goal `vc_extern_spec_<..>_body`), so a body is
    /// kept and expanded into a separate, verified `_body` function.
    body: Option<syn::Block>,
}

impl Parse for ExternSpecInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(ExternSpecInput { items })
    }
}

impl Parse for ExternImplBlock {
    fn parse(input: ParseStream) -> Result<Self> {
        let _impl_token: Token![impl] = input.parse()?;

        // Parse optional generics: impl<T> Type<T> { ... }
        let generics: Generics = input.parse()?;

        // Parse either:
        //   impl<T> Type { ... }                 (inherent impl form)
        //   impl<T> TraitPath for Type { ... }   (trait impl form)
        let implemented_ty: Type = input.parse()?;
        let (trait_path, self_ty) = if input.peek(Token![for]) {
            let _for_token: Token![for] = input.parse()?;
            let self_ty: Type = input.parse()?;
            let trait_path = match implemented_ty {
                Type::Path(TypePath { qself: None, path }) => path,
                other => {
                    return Err(syn::Error::new_spanned(
                        other,
                        "extern_spec! trait impls require a trait path before `for`",
                    ));
                }
            };
            (Some(trait_path), self_ty)
        } else {
            (None, implemented_ty)
        };

        // Parse optional where clause: impl<T> Trait for Type where T: Bound { ... }
        // syn::Generics::parse does not consume the where clause — it must be
        // parsed separately after the self type is known.
        let mut generics = generics;
        generics.where_clause = input.parse()?;

        // Parse the brace-delimited method list
        let content;
        let _brace = braced!(content in input);

        let mut methods = Vec::new();
        while !content.is_empty() {
            methods.push(content.parse()?);
        }

        Ok(ExternImplBlock {
            generics,
            trait_path,
            self_ty,
            methods,
        })
    }
}

impl Parse for ExternMethod {
    fn parse(input: ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let sig: Signature = input.parse()?;
        // Accept either `;` (declaration only) or `{ ... }` (a body). Creusot
        // checks an extern_spec body against the method's contract, so the
        // body is kept and expanded into a verified `_body` function.
        let body = if input.peek(Token![;]) {
            let _semi: Token![;] = input.parse()?;
            None
        } else {
            Some(input.parse::<syn::Block>()?)
        };
        Ok(ExternMethod { attrs, sig, body })
    }
}

/// Generate the expansion for one impl block.
fn expand_impl_block(impl_block: ExternImplBlock) -> Result<(TokenStream, TokenStream)> {
    let target_owner = if let Some(trait_path) = &impl_block.trait_path {
        let self_name = type_to_target_string(&impl_block.self_ty);
        let trait_name = path_to_string(trait_path);
        format!("<{self_name} as {trait_name}>")
    } else {
        // Accept both simple paths (Option::<T>) and non-path types ([T], str).
        // Non-path types use the compact token rendering for target lookup.
        type_to_target_string(&impl_block.self_ty)
    };

    let mut output = TokenStream::new();
    let mut body_fns = TokenStream::new();

    for method in impl_block.methods {
        let (stub, body_fn) = expand_method(
            &method,
            &impl_block.generics,
            &impl_block.self_ty,
            impl_block.trait_path.as_ref(),
            &target_owner,
        )?;
        output.extend(stub);
        body_fns.extend(body_fn);
    }

    Ok((output, body_fns))
}

/// Generate the expansion for one method within an impl block: the extern
/// spec stub, and (when the method has a body) the body function to prove.
fn expand_method(
    method: &ExternMethod,
    impl_generics: &Generics,
    self_ty: &Type,
    trait_path: Option<&Path>,
    target_owner: &str,
) -> Result<(TokenStream, Option<TokenStream>)> {
    let span = method.sig.span();
    let method_name = method.sig.ident.to_string();
    let target_path = format!("{target_owner}::{method_name}");

    let (requires, ensures) = extract_contracts(&method.attrs)?;
    validate_contracts(&requires, &ensures, span)?;

    let requires_str = requires.join("; ");
    let ensures_str = ensures.join("; ");

    // Generate stub function identifier
    let stub_ident = generate_stub_ident(target_owner, &method_name, span);

    // Transform signature for standalone function
    let mut stub_sig = transform_sig_for_stub(&method.sig, self_ty);
    stub_sig.ident = stub_ident.clone();

    // Merge impl generics with method generics
    let mut merged_generics = impl_generics.clone();
    for param in &method.sig.generics.params {
        merged_generics.params.push(param.clone());
    }
    if let Some(where_clause) = method.sig.generics.where_clause.as_ref() {
        if let Some(existing) = merged_generics.where_clause.as_mut() {
            existing.predicates.extend(where_clause.predicates.clone());
        } else {
            merged_generics.where_clause = Some(where_clause.clone());
        }
    }
    stub_sig.generics = merged_generics;

    let call_args = sig_to_call_args(&method.sig);
    let method_ident = &method.sig.ident;
    let call_expr = if let Some(tp) = trait_path {
        quote_spanned!(span=> <#self_ty as #tp>::#method_ident(#call_args))
    } else {
        quote_spanned!(span=> <#self_ty>::#method_ident(#call_args))
    };

    let param_names = extract_param_names(&method.sig);
    let params_str = param_names.join(", ");

    let target_doc = format!("trust-wp:extern_spec:target={target_path}");
    let params_doc = format!("trust-wp:extern_spec:params={params_str}");
    let requires_doc = format!("trust-wp:extern_spec:requires={requires_str}");
    let ensures_doc = format!("trust-wp:extern_spec:ensures={ensures_str}");

    // Filter non-contract attributes for the stub
    let other_attrs: Vec<_> = method
        .attrs
        .iter()
        .filter(|a| {
            a.path()
                .get_ident()
                .is_none_or(|id| id != "requires" && id != "ensures")
        })
        .collect();

    let body_fn = method.body.as_ref().map(|body| {
        expand_body_fn(
            &method.attrs,
            &stub_sig,
            &body_fn_ident(impl_generics, trait_path, self_ty, &method.sig.ident),
            body,
            self_ty,
        )
    });

    let stub = quote_spanned! {span=>
        #[doc(hidden)]
        #[doc = #target_doc]
        #[doc = #params_doc]
        #[doc = #requires_doc]
        #[doc = #ensures_doc]
        #[allow(dead_code, non_snake_case, unused_variables)]
        #(#other_attrs)*
        #stub_sig {
            #call_expr
        }
    };
    Ok((stub, body_fn))
}

/// Creusot's generated name for an extern spec body,
/// `extern_spec<impl generics><trait path><self type>_<method>_body`
/// (`creusot-std-proc/src/creusot/extern_spec.rs::flatten` with
/// `doc.rs::DocItemName`). Using the same name places the obligation at the
/// same item path as Creusot's goal (`M_extern_spec_UseSelf_i32_func_body`).
fn body_fn_ident(
    impl_generics: &Generics,
    trait_path: Option<&Path>,
    self_ty: &Type,
    method: &syn::Ident,
) -> syn::Ident {
    let mut name = DocItemName(String::from("extern_spec"));
    name.add_generics(impl_generics);
    if let Some(tp) = trait_path {
        name.add_path(tp);
    }
    name.add_type(self_ty);
    name.add_ident(method);
    format_ident!("{}_body", name.0, span = method.span())
}

/// Port of Creusot's `DocItemName` (`creusot-std-proc/src/creusot/doc.rs`).
struct DocItemName(String);

impl DocItemName {
    fn add_ident(&mut self, i: &syn::Ident) {
        self.0.push('_');
        self.0.push_str(&i.to_string());
    }

    fn add_type(&mut self, ty: &Type) {
        match ty {
            Type::Array(t) => {
                self.0.push_str("__array");
                self.add_type(&t.elem);
            }
            Type::BareFn(t) => {
                self.0.push_str("__fn");
                for input in &t.inputs {
                    self.add_type(&input.ty);
                }
                self.add_return_type(&t.output);
            }
            Type::Group(t) => self.add_type(&t.elem),
            Type::ImplTrait(t) => {
                self.0.push_str("__impl");
                for bound in &t.bounds {
                    self.add_type_param_bound(bound);
                }
            }
            Type::Macro(_) => self.0.push_str("__macro"),
            Type::Never(_) => self.0.push_str("__never"),
            Type::Paren(t) => self.add_type(&t.elem),
            Type::Path(t) => {
                self.add_path(&t.path);
                if let Some(qself) = &t.qself {
                    self.add_type(&qself.ty);
                }
            }
            Type::Ptr(t) => {
                if t.mutability.is_some() {
                    self.0.push_str("__ptrmut");
                } else {
                    self.0.push_str("__ptrconst");
                }
                self.add_type(&t.elem);
            }
            Type::Reference(t) => {
                if t.mutability.is_some() {
                    self.0.push_str("__refmut");
                } else {
                    self.0.push_str("__ref");
                }
                self.add_type(&t.elem);
            }
            Type::Slice(t) => {
                self.0.push_str("__slice");
                self.add_type(&t.elem);
            }
            Type::TraitObject(t) => {
                self.0.push_str("__dyn");
                for b in &t.bounds {
                    self.add_type_param_bound(b);
                }
            }
            Type::Tuple(t) => {
                let _ = write!(self.0, "__tuple{}", t.elems.len());
                for ty in &t.elems {
                    self.add_type(ty);
                }
            }
            Type::Verbatim(tokens) => {
                let _ = write!(self.0, "__verbatim{tokens}");
            }
            _ => {}
        }
    }

    fn add_generics(&mut self, generics: &Generics) {
        for param in &generics.params {
            match param {
                syn::GenericParam::Lifetime(lt) => {
                    if !lt.bounds.is_empty() {
                        self.0.push_str("__outlives");
                    }
                }
                syn::GenericParam::Type(tp) => self.add_ident(&tp.ident),
                syn::GenericParam::Const(cp) => {
                    self.0.push_str("__const");
                    self.0.push_str(&cp.ident.to_string());
                }
            }
        }
    }

    fn add_type_param_bound(&mut self, bound: &syn::TypeParamBound) {
        match bound {
            syn::TypeParamBound::Trait(tb) => self.add_path(&tb.path),
            syn::TypeParamBound::Verbatim(tokens) => {
                let _ = write!(self.0, "__verbatim{tokens}");
            }
            _ => {}
        }
    }

    fn add_return_type(&mut self, ret: &syn::ReturnType) {
        self.0.push_str("__output");
        match ret {
            syn::ReturnType::Default => self.0.push_str("__unit"),
            syn::ReturnType::Type(_, ty) => self.add_type(ty),
        }
    }

    fn add_path(&mut self, path: &Path) {
        for segment in &path.segments {
            self.add_ident(&segment.ident);
            match &segment.arguments {
                syn::PathArguments::None => {}
                syn::PathArguments::AngleBracketed(args) => {
                    for arg in &args.args {
                        match arg {
                            syn::GenericArgument::Type(ty) => self.add_type(ty),
                            syn::GenericArgument::Const(syn::Expr::Path(ep)) => {
                                if let Some(qself) = &ep.qself {
                                    self.add_type(&qself.ty);
                                }
                                self.add_path(&ep.path);
                            }
                            syn::GenericArgument::AssocType(at) => {
                                self.add_ident(&at.ident);
                                self.add_type(&at.ty);
                            }
                            _ => {}
                        }
                    }
                }
                syn::PathArguments::Parenthesized(args) => {
                    self.0.push_str("__lpar");
                    for arg in &args.inputs {
                        self.add_type(arg);
                    }
                    self.0.push_str("__rpar");
                    self.add_return_type(&args.output);
                }
            }
        }
    }
}

/// Expand an `extern_spec!` method body into a standalone function that is
/// verified against the method's own contract.
///
/// This mirrors Creusot (`creusot-std-proc/src/creusot/extern_spec.rs`,
/// `f_with_body`): when a method is given a body, Creusot emits a separate
/// `<name>_body` function carrying the SAME attributes as the extern spec
/// (contracts, and `#[trusted]` if present, which then suppresses the goal)
/// and the user's body with `self` escaped, and translates it like any other
/// program function — producing the `vc_extern_spec_<..>_body` goal. The
/// extern spec itself (the doc-marker stub) is unaffected: the target's
/// contract is still an assumption at call sites, exactly as before; this
/// only ADDS an obligation.
///
/// The body function has no `trust-wp:extern_spec:*` doc markers, so it is
/// never registered as an extern spec entry.
fn expand_body_fn(
    attrs: &[Attribute],
    stub_sig: &Signature,
    body_ident: &syn::Ident,
    body: &syn::Block,
    self_ty: &Type,
) -> TokenStream {
    let mut sig = stub_sig.clone();
    sig.ident = body_ident.clone();
    let self_ty_tokens = self_ty.to_token_stream();
    let attrs: Vec<TokenStream> = attrs
        .iter()
        .map(|attr| escape_self_tokens(attr.to_token_stream(), &self_ty_tokens))
        .collect();
    let body = escape_self_tokens(body.to_token_stream(), &self_ty_tokens);
    quote! {
        #[allow(dead_code, non_snake_case, unused_variables)]
        #(#attrs)*
        #sig #body
    }
}

/// Rewrite the `self` receiver to the stub parameter `self_` and `Self` to the
/// concrete self type, recursively through every token group.
///
/// The stub signature already renames the receiver to `self_: <Self type>`
/// (`transform_sig_for_stub`); contract expressions and the body must use the
/// same name.
fn escape_self_tokens(tokens: TokenStream, self_ty: &TokenStream) -> TokenStream {
    use proc_macro2::{Group, TokenTree};
    let mut out = TokenStream::new();
    for tt in tokens {
        match tt {
            TokenTree::Ident(ref ident) if ident == "self" => {
                out.extend(std::iter::once(TokenTree::Ident(proc_macro2::Ident::new(
                    "self_",
                    ident.span(),
                ))));
            }
            TokenTree::Ident(ref ident) if ident == "Self" => {
                out.extend(self_ty.clone());
            }
            TokenTree::Group(group) => {
                let mut new_group = Group::new(
                    group.delimiter(),
                    escape_self_tokens(group.stream(), self_ty),
                );
                new_group.set_span(group.span());
                out.extend(std::iter::once(TokenTree::Group(new_group)));
            }
            other => out.extend(std::iter::once(other)),
        }
    }
    out
}

/// Main entry point for `extern_spec`! macro expansion.
pub(crate) fn expand_extern_spec(input: ExternSpecInput) -> Result<TokenStream> {
    let mut output = TokenStream::new();
    let mut body_fns = TokenStream::new();

    for impl_block in input.items {
        let (stubs, bodies) = expand_impl_block(impl_block)?;
        output.extend(stubs);
        body_fns.extend(bodies);
    }

    // Wrap the stubs in a const block to avoid polluting the namespace. Body
    // functions stay at module scope under Creusot's generated name, exactly
    // where Creusot places them (`extern_spec_<..>_body`).
    Ok(quote! {
        const _: () = {
            #output
        };

        #body_fns
    })
}

#[cfg(test)]
mod tests {
    use proc_macro2::Span;
    use syn::{parse_quote, Attribute, Type};

    use super::{expand_extern_spec, ExternImplBlock, ExternSpecInput};
    use crate::extern_spec_helpers::{
        encode_ident_component, extract_contracts, generate_stub_ident, path_to_string,
    };

    #[test]
    fn extract_contracts_rejects_bare_requires_attribute() {
        let attrs: Vec<Attribute> = vec![parse_quote!(#[requires])];

        let err = extract_contracts(&attrs)
            .expect_err("bare #[requires] should be rejected in extern_spec");

        assert!(
            err.to_string()
                .contains("#[requires] must use parenthesized form"),
            "unexpected error: {err}",
        );
    }

    #[test]
    fn extract_contracts_rejects_name_value_ensures_attribute() {
        let attrs: Vec<Attribute> = vec![parse_quote!(#[ensures = "x > 0"])];

        let err = extract_contracts(&attrs)
            .expect_err("name-value #[ensures = ...] should be rejected in extern_spec");

        assert!(
            err.to_string()
                .contains("#[ensures] must use parenthesized form"),
            "unexpected error: {err}",
        );
    }

    #[test]
    fn encode_ident_component_is_injective_for_colon_vs_underscore() {
        assert_ne!(
            encode_ident_component("foo::bar"),
            encode_ident_component("foo_bar")
        );
        assert_eq!(encode_ident_component("foo::bar"), "foo_P__P_bar");
        assert_eq!(encode_ident_component("foo_bar"), "foo__bar");
    }

    #[test]
    fn generate_stub_ident_avoids_generic_type_collisions() {
        let generic = generate_stub_ident("Vec<T>", "push", Span::call_site()).to_string();
        let underscored = generate_stub_ident("Vec_T_", "push", Span::call_site()).to_string();

        assert_ne!(generic, underscored);
        assert_eq!(generic, "__extern_spec_Vec_LT_T_GT__push");
        assert_eq!(underscored, "__extern_spec_Vec__T___push");
    }

    #[test]
    fn parse_trait_impl_block_records_trait_path_and_self_type() {
        let block: ExternImplBlock = parse_quote! {
            impl<U: PartialOrd<U> + DeepModel, T: PartialOrd<T> + DeepModel> core::cmp::PartialOrd for (U, T)
            where U::DeepModelTy: OrdLogic, T::DeepModelTy: OrdLogic
            {
                fn lt(&self, o: &(U, T)) -> bool;
            }
        };

        assert_eq!(
            path_to_string(block.trait_path.as_ref().expect("expected trait path")),
            "core::cmp::PartialOrd"
        );
        assert!(
            matches!(block.self_ty, Type::Tuple(_)),
            "expected tuple self type for trait impl"
        );
    }

    #[test]
    fn expand_extern_spec_accepts_trait_impl_for_tuple_self_type() {
        let input: ExternSpecInput = parse_quote! {
            impl<U: PartialOrd<U>, T: PartialOrd<T>> core::cmp::PartialOrd for (U, T) {
                fn lt(&self, o: &(U, T)) -> bool;
            }
        };

        let expanded = expand_extern_spec(input)
            .expect("trait impl extern_spec should expand successfully")
            .to_string();

        assert!(
            expanded.contains("trust-wp:extern_spec:target=<(U, T) as core::cmp::PartialOrd>::lt"),
            "missing expected target doc marker in expansion: {expanded}"
        );
    }

    #[test]
    fn parse_method_with_body_block() {
        // Body blocks should be accepted and discarded.
        // No contract attrs to avoid proc_macro API limitation in unit tests.
        let input: ExternSpecInput = syn::parse_str(
            "impl Foo for i32 {
                fn func(x: i32) -> bool {
                    x > 0
                }
            }",
        )
        .expect("should parse extern_spec with method body");

        let expanded = expand_extern_spec(input)
            .expect("extern_spec with method body should expand successfully")
            .to_string();

        assert!(
            expanded.contains("trust-wp:extern_spec:target=<i32 as Foo>::func"),
            "missing expected target doc marker in expansion: {expanded}"
        );
    }

    #[test]
    fn method_body_expands_to_separate_verified_body_fn() {
        // Creusot proves an extern_spec body against its own contract
        // (vc_extern_spec_<..>_body); trust-wp must emit that function.
        let input: ExternSpecInput = syn::parse_str(
            "impl UseSelf for i32 {
                #[trusted]
                fn func(&self, s: &Self) -> bool {
                    *self == 1 && Self::default() == 0
                }
            }",
        )
        .expect("should parse extern_spec with method body");
        let expanded = expand_extern_spec(input)
            .expect("extern_spec with body should expand")
            .to_string();
        let body_fn = expanded
            .split("fn ")
            .find(|chunk| chunk.contains("_body"))
            .unwrap_or_else(|| panic!("no _body fn in expansion: {expanded}"));
        assert!(
            body_fn.contains("self_ : & i32") && body_fn.contains("* self_ == 1"),
            "body fn must use the stub receiver name: {body_fn}"
        );
        assert!(
            body_fn.contains("i32 :: default ()"),
            "Self in body must be the concrete type: {body_fn}"
        );
        assert!(
            !body_fn.contains(" self ") && !body_fn.contains(" Self "),
            "unescaped self in body fn: {body_fn}"
        );
        // #[trusted] is copied, exactly as Creusot copies the attributes, so a
        // trusted extern_spec body is not proved.
        assert!(
            expanded.matches("# [trusted]").count() == 2,
            "trusted attr must be on both stub and body fn: {expanded}"
        );
        // The body fn carries no extern_spec marker (not a second registration).
        assert_eq!(expanded.matches("trust-wp:extern_spec:target=").count(), 1);
        // Creusot's name (goal module M_extern_spec_UseSelf_i32_func_body),
        // at module scope rather than inside the stubs' `const _` block.
        assert!(
            expanded.contains("fn extern_spec_UseSelf_i32_func_body"),
            "body fn must use Creusot's generated name: {expanded}"
        );
        let const_block_end = expanded.rfind("} ;").expect("const block");
        assert!(
            expanded
                .find("fn extern_spec_UseSelf_i32_func_body")
                .unwrap()
                > const_block_end,
            "body fn must be outside the const block: {expanded}"
        );
    }

    #[test]
    fn body_fn_name_follows_creusot_doc_item_name() {
        let input: ExternSpecInput = syn::parse_str(
            "impl<T> Clone for Vec<T> {
                fn clone(&self) -> Vec<T> { loop {} }
            }
            impl<'a, U> Foo for &'a mut [U] {
                fn f(&self) -> bool { true }
            }",
        )
        .expect("should parse");
        let expanded = expand_extern_spec(input).expect("expand").to_string();
        assert!(
            expanded.contains("fn extern_spec_T_Clone_Vec_T_clone_body"),
            "{expanded}"
        );
        assert!(
            expanded.contains("fn extern_spec_U_Foo__refmut__slice_U_f_body"),
            "{expanded}"
        );
    }

    #[test]
    fn declaration_without_body_emits_no_body_fn() {
        let input: ExternSpecInput = syn::parse_str(
            "impl UseSelf for () {
                fn func(&self, s: &Self) -> bool;
            }",
        )
        .expect("should parse");
        let expanded = expand_extern_spec(input).expect("expand").to_string();
        assert!(
            !expanded.contains("_body"),
            "unexpected body fn: {expanded}"
        );
    }

    #[test]
    fn parse_method_with_semicolon_and_body_mixed() {
        // Mix of semicolon-terminated and body-terminated methods.
        let input: ExternSpecInput = syn::parse_str(
            "impl UseSelf for () {
                fn func(x: i32) -> bool;
            }
            impl UseSelf for i32 {
                fn func(x: i32) -> bool {
                    true
                }
            }",
        )
        .expect("should parse mixed semicolon/body extern_spec");

        let expanded = expand_extern_spec(input)
            .expect("mixed semicolon/body extern_spec should expand")
            .to_string();

        assert!(
            expanded.contains("<() as UseSelf>::func"),
            "missing unit impl target: {expanded}"
        );
        assert!(
            expanded.contains("<i32 as UseSelf>::func"),
            "missing i32 impl target: {expanded}"
        );
    }

    #[test]
    fn parse_late_bound_lifetime_in_trait_impl() {
        let input: ExternSpecInput = parse_quote! {
            impl<'a> std::ops::Add<&'a u16> for u16 {
                fn add(self, a: &'a u16) -> u16;
            }
        };

        let expanded = expand_extern_spec(input)
            .expect("late-bound lifetime extern_spec should expand")
            .to_string();

        assert!(
            expanded.contains("trust-wp:extern_spec:target=<u16 as std::ops::Add>::add"),
            "missing expected target: {expanded}"
        );
    }

    #[test]
    fn replace_self_handles_nested_self_in_parameters() {
        use quote::quote;

        use crate::extern_spec_helpers::transform_sig_for_stub;

        let self_ty: Type = parse_quote!(MyStruct);
        let sig: syn::Signature = parse_quote! {
            fn merge(&self, other: Option<Self>, pairs: Vec<(Self, &Self)>) -> Self
        };
        let transformed = transform_sig_for_stub(&sig, &self_ty);
        let rendered = quote!(#transformed).to_string();

        // Self in Option<Self> should become Option<MyStruct>
        assert!(
            rendered.contains("Option < MyStruct >"),
            "nested Self in Option<Self> not replaced: {rendered}"
        );
        // Self in Vec<(Self, &Self)> should become Vec<(MyStruct, &MyStruct)>
        assert!(
            rendered.contains("MyStruct"),
            "nested Self in Vec<(Self, &Self)> not replaced: {rendered}"
        );
        // Return type Self should become MyStruct
        assert!(
            rendered.contains("-> MyStruct"),
            "return type Self not replaced: {rendered}"
        );
        // No remaining bare `Self` tokens
        assert!(
            !rendered.contains(" Self"),
            "unreplaced Self remaining in transformed signature: {rendered}"
        );
    }

    #[test]
    fn replace_self_handles_where_clause_predicates() {
        use quote::quote;

        use crate::extern_spec_helpers::transform_sig_for_stub;

        let self_ty: Type = parse_quote!(MyStruct);
        let sig: syn::Signature = parse_quote! {
            fn method(&self) -> bool where Self: Clone, Self: std::fmt::Debug
        };
        let transformed = transform_sig_for_stub(&sig, &self_ty);
        let rendered = quote!(#transformed).to_string();

        // Where clause `Self: Clone` should become `MyStruct: Clone`
        assert!(
            rendered.contains("MyStruct : Clone"),
            "Self in where clause not replaced: {rendered}"
        );
        // Where clause `Self: Debug` should become `MyStruct: Debug`
        assert!(
            rendered.contains("MyStruct : std :: fmt :: Debug"),
            "Self in where clause trait bound not replaced: {rendered}"
        );
        // No remaining bare `Self` tokens
        assert!(
            !rendered.contains(" Self"),
            "unreplaced Self remaining in transformed signature: {rendered}"
        );
    }

    // ── param_names extraction tests (#2298) ──────────────────────

    #[test]
    fn extract_param_names_self_and_typed() {
        use crate::extern_spec_helpers::extract_param_names;

        let sig: syn::Signature = parse_quote! {
            fn push(&mut self, value: T)
        };
        let names = extract_param_names(&sig);
        assert_eq!(names, vec!["self", "value"]);
    }

    #[test]
    fn extract_param_names_no_self() {
        use crate::extern_spec_helpers::extract_param_names;

        let sig: syn::Signature = parse_quote! {
            fn new() -> Self
        };
        let names = extract_param_names(&sig);
        assert!(names.is_empty());
    }

    #[test]
    fn expand_extern_spec_emits_params_marker() {
        let input: ExternSpecInput = syn::parse_str(
            "impl Option<T> {
                fn ok_or(&self, err: E) -> Result<T, E>;
            }",
        )
        .expect("should parse extern_spec");

        let expanded = expand_extern_spec(input)
            .expect("should expand successfully")
            .to_string();

        assert!(
            expanded.contains("trust-wp:extern_spec:params=self, err"),
            "missing params= doc marker in expansion: {expanded}"
        );
    }

    #[test]
    fn expand_extern_spec_accepts_inherent_slice_self_type() {
        let input: ExternSpecInput = parse_quote! {
            impl<T> [T] {
                fn len(&self) -> usize;
                fn is_empty(&self) -> bool;
            }
        };

        let expanded = expand_extern_spec(input)
            .expect("inherent [T] extern_spec should expand successfully")
            .to_string();

        assert!(
            expanded.contains("trust-wp:extern_spec:target=[T]::len"),
            "missing [T]::len target: {expanded}"
        );
        assert!(
            expanded.contains("trust-wp:extern_spec:target=[T]::is_empty"),
            "missing [T]::is_empty target: {expanded}"
        );
    }

    #[test]
    fn expand_extern_spec_accepts_inherent_str_self_type() {
        let input: ExternSpecInput = syn::parse_str(
            "impl str {
                fn len(&self) -> usize;
            }",
        )
        .expect("should parse inherent str extern_spec");

        let expanded = expand_extern_spec(input)
            .expect("inherent str extern_spec should expand successfully")
            .to_string();

        assert!(
            expanded.contains("trust-wp:extern_spec:target=str::len"),
            "missing str::len target: {expanded}"
        );
    }
}
