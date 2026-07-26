// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `proof!` — the in-source authored-proof surface (design §3 L1: `proof!{ := by tac }`).
//!
//! The macro is a thin desugar: it validates the `by <tactic>` payload and emits a
//! `#[doc = "trust-wp:proof_by:<tactic>"]` marker on a dummy closure (the exact
//! mechanism `proof_assert!` uses). The marker is reserved for a future sound
//! driver integration; the production driver does not currently consume it.
//! Consequently this macro is an inert proof hint and cannot discharge an
//! obligation.

use proc_macro::TokenStream;
use proc_macro2::TokenTree;

use super::proof_assert::proof_assert_expansion_with_marker;

/// Expand `proof!(by <tactic tokens>)` into the driver marker.
///
/// Accepted forms:
/// - `proof!(by <nonempty tactic tokens>)`
/// - `proof!(assume [<axiom>, ...], by <nonempty tactic tokens>)`
///
/// Both forms preserve their full payload in the reserved marker.
pub(crate) fn expand_proof(input: TokenStream) -> TokenStream {
    let input2: proc_macro2::TokenStream = input.into();
    let text = input2.to_string();
    let compact: String = text.chars().filter(|c| !c.is_whitespace()).collect();

    let starts_by = compact.starts_with("by");
    let starts_assume = compact.starts_with("assume[");
    let has_by_payload = if starts_by {
        compact.len() > 2
    } else if starts_assume {
        // require `],by<nonempty>` after the axiom list
        compact
            .split_once("],by")
            .is_some_and(|(_, tac)| !tac.is_empty())
    } else {
        false
    };
    if !has_by_payload {
        let msg = "proof! expects `by <tactic>` or `assume [<axioms>], by <tactic>` \
                   with a non-empty tactic";
        return syn::Error::new(
            input2
                .into_iter()
                .next()
                .map_or_else(proc_macro2::Span::call_site, |t: TokenTree| t.span()),
            msg,
        )
        .to_compile_error()
        .into();
    }

    proof_assert_expansion_with_marker(&text, "trust-wp:proof_by:").into()
}

#[cfg(test)]
mod proof_by_tests {
    use super::*;

    fn expand_str(s: &str) -> String {
        // Route through the marker generator directly for unit-level checks.
        proof_assert_expansion_with_marker(s, "trust-wp:proof_by:").to_string()
    }

    #[test]
    fn marker_carries_the_tactic_payload() {
        let out = expand_str("by induction_on_n");
        assert!(out.contains("trust-wp:proof_by:by induction_on_n"), "{out}");
    }
}
