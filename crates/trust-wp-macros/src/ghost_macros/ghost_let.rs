// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expansion logic for the `ghost_let!` macro.

use quote::quote;
use syn::Expr;

use crate::transform::preprocess_view_syntax;

/// Expand `ghost_let!(var = expr)` or `ghost_let!(mut var = expr)` macro.
///
/// Declares a ghost variable bound to a ghost expression. The result is
/// always `Ghost<T>`. Under trust-wp verification, the body is preserved;
/// under normal compilation, it is erased via `Ghost::conjure()`.
///
/// Reference: Creusot `creusot-std-proc/src/dummy.rs:38-49`
pub(crate) fn expand_ghost_let(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = preprocess_view_syntax(input);
    expand_ghost_let_tokens(input.into()).into()
}

pub(crate) fn expand_ghost_let_tokens(
    input2: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    // Parse: [mut] <ident> = <expr>
    let parsed: syn::Result<GhostLetInput> = syn::parse2(input2);
    let parsed = match parsed {
        Ok(p) => p,
        Err(e) => {
            return syn::Error::new(
                e.span(),
                format!("ghost_let!: expected `[mut] var = expr`, got: {e}"),
            )
            .to_compile_error();
        }
    };

    let mutability = parsed.mutability;
    let var = parsed.var;
    let body = parsed.body;

    // The `#[doc = "__trust_wp_ghost"]` marker tells `trust-wp-driver`'s
    // ghost-block finder to treat this `let` as a ghost block. Without it,
    // the driver rejects the `Ghost::new(#body)` call (and any ghost
    // extractions inside `#body`) as "ghost variable in program context".
    // Mirrors `ghost!` (`ghost_block.rs`) and Creusot's `#[creusot::ghost_let]`
    // / `#[creusot::ghost_block]` pair in `creusot-std-proc/src/creusot/proof.rs:72`.
    quote! {
        #[cfg(trust_wp)]
        #[doc(hidden)]
        #[doc = "__trust_wp_ghost"]
        let #mutability #var = ::trust_wp_std::ghost::Ghost::new(#body);

        #[cfg(not(trust_wp))]
        #[doc(hidden)]
        #[doc = "__trust_wp_ghost"]
        #[allow(unreachable_code, unused_variables, dead_code, unused_mut)]
        let #mutability #var = if false {
            ::trust_wp_std::ghost::Ghost::new(#body)
        } else {
            ::trust_wp_std::ghost::Ghost::conjure()
        };
    }
}

/// Parsed input for `ghost_let!`.
struct GhostLetInput {
    mutability: Option<syn::Token![mut]>,
    var: syn::Ident,
    body: Expr,
}

impl syn::parse::Parse for GhostLetInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mutability: Option<syn::Token![mut]> = input.parse()?;
        let var: syn::Ident = input.parse()?;
        let _eq: syn::Token![=] = input.parse()?;
        let body: Expr = input.parse()?;
        Ok(GhostLetInput {
            mutability,
            var,
            body,
        })
    }
}
