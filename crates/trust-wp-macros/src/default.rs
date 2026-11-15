// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Default` derive implementation for Creusot-compatible facade imports.

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DataEnum, DeriveInput, Fields,
    GenericParam, Generics, Ident, Type, Variant,
};

/// Derive `Default` with the compatibility semantics expected by Creusot tests.
pub fn derive_default(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident.clone();

    let generics = add_trait_bounds(input.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let body_code = default_body(&name, &input.data);
    let body_spec = default_spec(&name, &input.data);

    quote! {
        impl #impl_generics ::core::default::Default for #name #ty_generics #where_clause {
            #[::trust_wp_std::ensures(#body_spec)]
            fn default() -> Self {
                #body_code
            }
        }
    }
    .into()
}

/// Add `Default` bounds to all type parameters.
fn add_trait_bounds(mut generics: Generics) -> Generics {
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param
                .bounds
                .push(parse_quote!(::core::default::Default));
        }
    }
    generics
}

/// Emit the body of `default()`.
fn default_body(type_name: &Ident, data: &Data) -> TokenStream {
    match data {
        Data::Struct(data_struct) => {
            let fields = fields_set_to_default(&data_struct.fields);
            quote!(#type_name #fields)
        }
        Data::Enum(data_enum) => match default_variant(data_enum) {
            Ok(default_variant) => {
                let variant_name = &default_variant.ident;
                let fields = fields_set_to_default(&default_variant.fields);
                quote!(#type_name::#variant_name #fields)
            }
            Err(error) => error.to_compile_error(),
        },
        Data::Union(_) => {
            syn::Error::new(Span::call_site(), "this trait cannot be derived for unions")
                .to_compile_error()
        }
    }
}

/// Emit field initializers using `Default::default()`.
fn fields_set_to_default(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(fields) => {
            let fields = fields.named.iter().map(|field| {
                let name = &field.ident;
                let default_expr = default_expr_for_type(&field.ty);
                quote_spanned! { field.span() =>
                    #name: #default_expr
                }
            });
            quote!({ #(#fields),* })
        }
        Fields::Unnamed(fields) => {
            let fields = fields.unnamed.iter().map(|field| {
                let default_expr = default_expr_for_type(&field.ty);
                quote_spanned! { field.span() =>
                    #default_expr
                }
            });
            quote!(( #(#fields),* ))
        }
        Fields::Unit => quote!(),
    }
}

/// Emit the postcondition passed to `#[ensures(...)]`.
///
/// Payload-bearing defaults destructure `result` and reuse each field call's
/// `default.postcondition(...)` predicate. This keeps the generated contract
/// aligned with the call assumptions extracted from the `Default::default()`
/// invocations in the body, including generic fields.
fn default_spec(type_name: &Ident, data: &Data) -> TokenStream {
    match data {
        Data::Struct(data_struct) => struct_default_spec(type_name, &data_struct.fields),
        Data::Enum(data_enum) => match default_variant(data_enum) {
            Ok(default_variant) => {
                let variant_name = &default_variant.ident;
                if matches!(default_variant.fields, Fields::Unit) {
                    quote!(match result { #type_name::#variant_name => true, _ => false })
                } else {
                    // Creusot's derive states every payload field's default, as
                    // for a struct; a variant-only claim is weaker than the
                    // contract callers are owed.
                    let (pattern, fields_expr) =
                        constructor_default_pattern_and_expr(&default_variant.fields);
                    quote!(match result { #type_name::#variant_name #pattern => #fields_expr, _ => false })
                }
            }
            Err(error) => error.to_compile_error(),
        },
        Data::Union(_) => {
            syn::Error::new(Span::call_site(), "this trait cannot be derived for unions")
                .to_compile_error()
        }
    }
}

fn struct_default_spec(type_name: &Ident, fields: &Fields) -> TokenStream {
    match fields {
        Fields::Unit => quote!(true),
        Fields::Named(_) | Fields::Unnamed(_) => {
            let (pattern, fields_expr) = constructor_default_pattern_and_expr(fields);
            quote!(match result { #type_name #pattern => #fields_expr, _ => false })
        }
    }
}

fn default_variant(data_enum: &DataEnum) -> syn::Result<&Variant> {
    let mut default_variants = data_enum.variants.iter().filter(|variant| {
        variant
            .attrs
            .iter()
            .any(|attr| attr.path().is_ident("default"))
    });

    let Some(default_variant) = default_variants.next() else {
        return Err(syn::Error::new(Span::call_site(), "no default declared"));
    };

    if let Some(extra_variant) = default_variants.next() {
        return Err(syn::Error::new_spanned(
            extra_variant,
            "multiple default variants declared",
        ));
    }

    Ok(default_variant)
}

fn constructor_default_pattern_and_expr(fields: &Fields) -> (TokenStream, TokenStream) {
    match fields {
        Fields::Named(fields) => {
            // Bind every field by name; never place a literal in the pattern.
            // Pearlite rejects Int-literal patterns (`x: 0`), so primitive
            // defaults are asserted via equality predicates instead.
            let pattern_fields = fields.named.iter().map(|field| {
                let name = &field.ident;
                quote_spanned! { field.span() => #name }
            });
            let predicates = fields.named.iter().map(|field| {
                let name = &field.ident;
                default_field_predicate(&field.ty, quote!(#name), field.span())
            });
            (
                quote!({ #(#pattern_fields),* }),
                quote!(true #(&& #predicates)*),
            )
        }
        Fields::Unnamed(fields) => {
            let pattern_fields = fields.unnamed.iter().enumerate().map(|(index, field)| {
                let name = Ident::new(&format!("x{index}"), field.span());
                quote_spanned! { field.span() => #name }
            });
            let predicates = fields.unnamed.iter().enumerate().map(|(index, field)| {
                let name = Ident::new(&format!("x{index}"), field.span());
                default_field_predicate(&field.ty, quote!(#name), field.span())
            });
            (
                quote!(( #(#pattern_fields),* )),
                quote!(true #(&& #predicates)*),
            )
        }
        Fields::Unit => (quote!(), quote!(true)),
    }
}

/// Build the postcondition predicate for one field of a derived `Default`.
///
/// `value` is the token stream naming the (pattern-bound) field. Primitive
/// defaults assert equality with the default literal; non-primitive fields
/// reuse the inner `Default::default()` call's postcondition. Literals are
/// emitted only in expression position — never as patterns — because Pearlite
/// does not support Int-literal patterns.
fn default_field_predicate(ty: &Type, value: TokenStream, span: Span) -> TokenStream {
    match primitive_default_kind(ty) {
        Some(PrimitiveDefault::False) => quote_spanned! { span => #value == false },
        // Typed zero (`0i32`): an unsuffixed pearlite literal is `Int`.
        Some(PrimitiveDefault::Zero) => {
            let zero = primitive_type_ident(ty).map_or_else(
                || quote_spanned! { span => 0 },
                |ident| {
                    let lit = syn::LitInt::new(&format!("0{ident}"), span);
                    quote_spanned! { span => #lit }
                },
            );
            quote_spanned! { span => #value == #zero }
        }
        None => quote_spanned! { span =>
            core::default::Default::default.postcondition((), #value)
        },
    }
}

fn default_expr_for_type(ty: &Type) -> TokenStream {
    match primitive_default_kind(ty) {
        Some(PrimitiveDefault::False) => quote!(false),
        Some(PrimitiveDefault::Zero) => quote!(0),
        None => quote!(::core::default::Default::default()),
    }
}

#[derive(Clone, Copy)]
enum PrimitiveDefault {
    False,
    Zero,
}

fn primitive_type_ident(ty: &Type) -> Option<String> {
    let Type::Path(type_path) = ty else {
        return None;
    };
    if type_path.qself.is_some() || type_path.path.segments.len() != 1 {
        return None;
    }
    Some(type_path.path.segments.first()?.ident.to_string())
}

fn primitive_default_kind(ty: &Type) -> Option<PrimitiveDefault> {
    let Type::Path(type_path) = ty else {
        return None;
    };
    if type_path.qself.is_some() || type_path.path.segments.len() != 1 {
        return None;
    }
    let ident = type_path.path.segments.first()?.ident.to_string();
    match ident.as_str() {
        "bool" => Some(PrimitiveDefault::False),
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "usize" => Some(PrimitiveDefault::Zero),
        _ => None,
    }
}
