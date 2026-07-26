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
//! See `designs/2026-02-01-extern-spec.md` for the full design document.

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
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
        // Accept either `;` (declaration only) or `{ ... }` (body — discarded).
        // Creusot allows bodies in extern_spec methods for default/logic implementations.
        // trust-wp only uses the contract attributes; the body is ignored.
        if input.peek(Token![;]) {
            let _semi: Token![;] = input.parse()?;
        } else {
            let _body: syn::Block = input.parse()?;
        }
        Ok(ExternMethod { attrs, sig })
    }
}

/// Generate the expansion for one impl block.
fn expand_impl_block(impl_block: ExternImplBlock) -> Result<TokenStream> {
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

    for method in impl_block.methods {
        output.extend(expand_method(
            &method,
            &impl_block.generics,
            &impl_block.self_ty,
            impl_block.trait_path.as_ref(),
            &target_owner,
        )?);
    }

    Ok(output)
}

/// Generate the expansion for one method within an impl block.
fn expand_method(
    method: &ExternMethod,
    impl_generics: &Generics,
    self_ty: &Type,
    trait_path: Option<&Path>,
    target_owner: &str,
) -> Result<TokenStream> {
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

    Ok(quote_spanned! {span=>
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
    })
}

/// Main entry point for `extern_spec`! macro expansion.
pub(crate) fn expand_extern_spec(input: ExternSpecInput) -> Result<TokenStream> {
    let mut output = TokenStream::new();

    for impl_block in input.items {
        output.extend(expand_impl_block(impl_block)?);
    }

    // Wrap in a const block to avoid polluting the namespace
    Ok(quote! {
        const _: () = {
            #output
        };
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
