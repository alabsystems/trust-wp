// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `DeepModel` derive implementation.

use proc_macro::TokenStream;
use quote::{format_ident, quote};

pub(crate) fn derive_deep_model(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    match derive_deep_model_impl(&input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn derive_deep_model_impl(input: &syn::DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
    let name = &input.ident;
    let vis = &input.vis;
    let generics = &input.generics;

    // Check for #[DeepModelTy = "ExistingType"] helper attribute
    let custom_ty = extract_deep_model_ty_attr(input)?;

    if let Some(custom_path) = custom_ty {
        // Custom target type — just implement the trait, no companion type generated
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
        return Ok(quote! {
            impl #impl_generics ::trust_wp_std::logic::DeepModel for #name #ty_generics #where_clause {
                type DeepModelTy = #custom_path;

                #[cfg_attr(trust_wp, ::trust_wp::logic(open))]
                #[allow(unused_variables, dead_code)]
                fn deep_model(self) -> Self::DeepModelTy {
                    unreachable!("logic functions are erased at runtime")
                }
            }
        });
    }

    // Generate companion type and trait impl
    match &input.data {
        syn::Data::Struct(data) => Ok(derive_deep_model_struct(name, vis, generics, data)),
        syn::Data::Enum(data) => Ok(derive_deep_model_enum(name, vis, generics, data)),
        syn::Data::Union(_) => Err(syn::Error::new_spanned(
            name,
            "DeepModel cannot be derived for unions",
        )),
    }
}

fn extract_deep_model_ty_attr(input: &syn::DeriveInput) -> syn::Result<Option<syn::Type>> {
    for attr in &input.attrs {
        if attr.path().is_ident("DeepModelTy") {
            let value: syn::LitStr = attr.parse_args()?;
            let ty: syn::Type = syn::parse_str(&value.value()).map_err(|e| {
                syn::Error::new_spanned(&value, format!("invalid type in DeepModelTy: {e}"))
            })?;
            return Ok(Some(ty));
        }
    }
    Ok(None)
}

fn deep_model_type_name(name: &syn::Ident) -> syn::Ident {
    syn::Ident::new(&format!("{name}DeepModel"), name.span())
}

/// Add `DeepModel` bounds to all type parameters.
fn add_deep_model_bounds(generics: &syn::Generics) -> syn::Generics {
    let mut generics = generics.clone();
    for param in &mut generics.params {
        if let syn::GenericParam::Type(type_param) = param {
            type_param
                .bounds
                .push(syn::parse_quote!(::trust_wp_std::logic::DeepModel));
        }
    }
    generics
}

fn derive_deep_model_struct(
    name: &syn::Ident,
    vis: &syn::Visibility,
    generics: &syn::Generics,
    data: &syn::DataStruct,
) -> proc_macro2::TokenStream {
    let dm_name = deep_model_type_name(name);
    let bounded_generics = add_deep_model_bounds(generics);
    let (impl_generics, ty_generics, where_clause) = bounded_generics.split_for_impl();
    let dm_type_generics = bounded_generics.clone();

    let (dm_type_def, dm_body) = match &data.fields {
        syn::Fields::Named(fields) => {
            let field_defs: Vec<_> = fields
                .named
                .iter()
                .map(|f| {
                    let fname = &f.ident;
                    let fvis = &f.vis;
                    let fty = &f.ty;
                    quote! { #fvis #fname: <#fty as ::trust_wp_std::logic::DeepModel>::DeepModelTy }
                })
                .collect();
            let field_inits: Vec<_> = fields
                .named
                .iter()
                .map(|f| {
                    let fname = &f.ident;
                    quote! { #fname: self.#fname.deep_model() }
                })
                .collect();

            (
                quote! {
                    #vis struct #dm_name #dm_type_generics {
                        #(#field_defs),*
                    }
                },
                quote! { #dm_name { #(#field_inits),* } },
            )
        }
        syn::Fields::Unnamed(fields) => {
            let field_defs: Vec<_> = fields
                .unnamed
                .iter()
                .map(|f| {
                    let fvis = &f.vis;
                    let fty = &f.ty;
                    quote! { #fvis <#fty as ::trust_wp_std::logic::DeepModel>::DeepModelTy }
                })
                .collect();
            let field_inits: Vec<_> = fields
                .unnamed
                .iter()
                .enumerate()
                .map(|(i, _)| {
                    let idx = syn::Index::from(i);
                    quote! { self.#idx.deep_model() }
                })
                .collect();

            (
                quote! {
                    #vis struct #dm_name #dm_type_generics ( #(#field_defs),* );
                },
                quote! { #dm_name ( #(#field_inits),* ) },
            )
        }
        syn::Fields::Unit => (
            quote! { #vis struct #dm_name #dm_type_generics; },
            quote! { #dm_name },
        ),
    };

    quote! {
        use ::trust_wp_std::logic::DeepModel as _;

        #dm_type_def

        impl #impl_generics ::trust_wp_std::logic::DeepModel for #name #ty_generics #where_clause {
            type DeepModelTy = #dm_name #ty_generics;

            #[cfg_attr(trust_wp, ::trust_wp::logic(open))]
                #[allow(unused_variables, dead_code)]
                fn deep_model(self) -> Self::DeepModelTy {
                    #dm_body
                }
            }
    }
}

fn derive_deep_model_enum(
    name: &syn::Ident,
    vis: &syn::Visibility,
    generics: &syn::Generics,
    data: &syn::DataEnum,
) -> proc_macro2::TokenStream {
    let dm_name = deep_model_type_name(name);
    let bounded_generics = add_deep_model_bounds(generics);
    let (impl_generics, ty_generics, where_clause) = bounded_generics.split_for_impl();
    let dm_type_generics = bounded_generics.clone();

    let variant_defs: Vec<_> = data
        .variants
        .iter()
        .map(|v| {
            let vname = &v.ident;
            match &v.fields {
                syn::Fields::Named(fields) => {
                    let field_defs: Vec<_> = fields
                        .named
                        .iter()
                        .map(|f| {
                            let fname = &f.ident;
                            let fvis = &f.vis;
                            let fty = &f.ty;
                            quote! { #fvis #fname: <#fty as ::trust_wp_std::logic::DeepModel>::DeepModelTy }
                        })
                        .collect();
                    quote! { #vname { #(#field_defs),* } }
                }
                syn::Fields::Unnamed(fields) => {
                    let field_defs: Vec<_> = fields
                        .unnamed
                        .iter()
                        .map(|f| {
                            let fty = &f.ty;
                            quote! { <#fty as ::trust_wp_std::logic::DeepModel>::DeepModelTy }
                        })
                        .collect();
                    quote! { #vname ( #(#field_defs),* ) }
                }
                syn::Fields::Unit => quote! { #vname },
            }
        })
        .collect();

    let variant_arms: Vec<_> = data
        .variants
        .iter()
        .map(|v| {
            let vname = &v.ident;
            match &v.fields {
                syn::Fields::Named(fields) => {
                    let field_names: Vec<_> =
                        fields.named.iter().map(|f| f.ident.clone().unwrap()).collect();
                    let field_inits: Vec<_> = field_names
                        .iter()
                        .map(|fname| quote! { #fname: #fname.deep_model() })
                        .collect();
                    quote! {
                        #name::#vname { #(#field_names),* } => #dm_name::#vname { #(#field_inits),* }
                    }
                }
                syn::Fields::Unnamed(fields) => {
                    let binders: Vec<_> = (0..fields.unnamed.len())
                        .map(|i| format_ident!("__field_{i}"))
                        .collect();
                    let mapped: Vec<_> =
                        binders.iter().map(|binder| quote! { #binder.deep_model() }).collect();
                    quote! {
                        #name::#vname ( #(#binders),* ) => #dm_name::#vname ( #(#mapped),* )
                    }
                }
                syn::Fields::Unit => quote! {
                    #name::#vname => #dm_name::#vname
                },
            }
        })
        .collect();

    quote! {
        use ::trust_wp_std::logic::DeepModel as _;

        #vis enum #dm_name #dm_type_generics {
            #(#variant_defs),*
        }

        impl #impl_generics ::trust_wp_std::logic::DeepModel for #name #ty_generics #where_clause {
            type DeepModelTy = #dm_name #ty_generics;

            #[cfg_attr(trust_wp, ::trust_wp::logic(open))]
            #[allow(unused_variables, dead_code)]
            fn deep_model(self) -> Self::DeepModelTy {
                match self {
                    #(#variant_arms),*
                }
            }
        }
    }
}
