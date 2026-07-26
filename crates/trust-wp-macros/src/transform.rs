// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Token preprocessing transforms.
//!
//! - `transform_int_suffix_tokens`: rewrites `123int` literals to `Int::from(123)`
//! - `preprocess_view_syntax`: applies `@` and `^` rewrites plus int-suffix transform

use proc_macro::TokenStream;
use proc_macro2::{Group, TokenTree};
use quote::quote;

use crate::view_syntax::transform_view_syntax;

pub(crate) fn transform_int_suffix_tokens(
    input: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let mut output = proc_macro2::TokenStream::new();

    for token in input {
        match token {
            TokenTree::Group(group) => {
                let inner = transform_int_suffix_tokens(group.stream());
                let mut new_group = Group::new(group.delimiter(), inner);
                new_group.set_span(group.span());
                output.extend([TokenTree::Group(new_group)]);
            }
            TokenTree::Literal(lit) => {
                let text = lit.to_string();
                if let Some(base) = text.strip_suffix("int") {
                    if let Ok(base_tokens) = base.parse::<proc_macro2::TokenStream>() {
                        output.extend(quote! { ::trust_wp_std::logic::Int::from(#base_tokens) });
                    } else {
                        output.extend([TokenTree::Literal(lit)]);
                    }
                } else {
                    output.extend([TokenTree::Literal(lit)]);
                }
            }
            other => output.extend([other]),
        }
    }

    output
}

pub(crate) fn preprocess_view_syntax(input: TokenStream) -> TokenStream {
    let input2: proc_macro2::TokenStream = input.into();
    let input2 = transform_int_suffix_tokens(input2);
    let input_text = input2.to_string();
    if input_text.contains('@') || input_text.contains('^') {
        transform_view_syntax(input2).into()
    } else {
        input2.into()
    }
}
