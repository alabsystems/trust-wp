// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expansion logic for the `ghost!` macro.

use proc_macro::TokenStream;
use quote::quote;

use crate::{ghost, transform::preprocess_view_syntax};

/// Expand `ghost! { ... }` macro.
pub(crate) fn expand_ghost(input: TokenStream) -> TokenStream {
    let input2: proc_macro2::TokenStream = preprocess_view_syntax(input).into();
    let wrapped_block: proc_macro2::TokenStream = quote!({ #input2 });

    if let Err(e) = ghost::validate_ghost_block(&wrapped_block.clone().into()) {
        return syn::Error::new(e.span, format!("ghost!: {}", e.message))
            .to_compile_error()
            .into();
    }

    let block: syn::Block = match syn::parse2(wrapped_block) {
        Ok(block) => block,
        Err(e) => {
            return syn::Error::new(
                e.span(),
                format!("ghost!: failed to parse ghost block: {e}"),
            )
            .to_compile_error()
            .into();
        }
    };

    quote! {
        {
            #[cfg(trust_wp)]
            #[doc(hidden)]
            #[doc = "__trust_wp_ghost"]
            let __trust_wp_ghost_value = ::trust_wp_std::ghost::Ghost::new(#block);

            #[cfg(not(trust_wp))]
            #[doc(hidden)]
            #[doc = "__trust_wp_ghost"]
            #[allow(unreachable_code, unused_variables, dead_code)]
            let __trust_wp_ghost_value = if false {
                ::trust_wp_std::ghost::Ghost::new(#block)
            } else {
                ::trust_wp_std::ghost::Ghost::conjure()
            };

            __trust_wp_ghost_value
        }
    }
    .into()
}
