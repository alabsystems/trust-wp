// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The namespace of verifier-synthesized variable names.
//!
//! A `PureExpr::Var` name is either a source name (a parameter, a binding, the
//! last segment of a path a clause names: `S::C` and `dep::C` resolve to `C`)
//! or a name the verifier synthesizes (call results, placeholders for
//! untranslatable call arguments, anonymous parameters, havoc symbols,
//! skolem constants, borrow carriers, ...). When a synthesized name can also be
//! spelled as a Rust identifier, a source item of that name becomes the SAME
//! solver symbol, and a fact about one is a fact about the other: a `const
//! call_0` in a `requires` constrained the call result stored in MIR local 0.
//!
//! Every synthesized name that must not alias a source name therefore contains
//! [`SYNTHESIZED_NAME_SIGIL`]. Neither a Rust identifier (rustc lexes `$` as a
//! punctuation token, never inside an identifier) nor the contract parser's
//! identifier lexer (alphanumerics and `_`) can produce it, so no source name
//! can equal such a name. `$` is an SMT-LIB simple-symbol character, so the
//! names need no quoting (and `ay_core::quote_symbol` quotes whatever does).
//!
//! Spellings: `$call_N` / `$_call_N` (call results), `$fallback_argI_N`,
//! `$anon_argI`, `$havoc_local_*`, `$havoc_owner_*`, `$_N` (untranslated MIR
//! local), `$for_iter_*`, `$borrow_N`, `{carrier}$twp_mK`, `$twp_current_*` /
//! `$twp_prophecy_*` / `$twp_payload_*`, `sk${binder}` / `sk$exists_*`,
//! `{parent}$rbN` / `$reborrow_N` (plain reborrow children), `$param_N`
//! (unnamed parameter slots), `$local_N` (anonymous projected-write carriers),
//! `$iter_result_N` (for-loop `next()` results), `$stmtN` (spec block
//! statement binders), `$forall_post_state` / `$forall_post_field_N` /
//! `$unused` (closure-precondition grounding), `$inv_{variant}_*` (synthesized
//! invariant pattern binders), `{binder}$αN` (capture-avoiding renames),
//! `{name}$shadowN` / `{name}$unresolved_N` (a binding of a shadowed name, named
//! apart per MIR local, and a clause name no binding resolves; the driver's D-237).
//!
//! Not moved: names the encoder DERIVES from a source name by affixing its
//! spelling (`x_current`, `x_final`, `x_view`, `x_prime`, `old_x`, ...). They
//! are pair-refused at the source by the driver's
//! `validate_derived_name_aliases`. Functions and constants spelled
//! `__trust_wp*` / `__twp*` are refused at the source over every identifier
//! kind. Solver-level encoder constants (`heap`, `__seq_lit_N`, ...) never
//! meet source names: every source variable is declared under the
//! `trust-wp-ay` `source_symbol` identity prefix.

/// The character every alias-free synthesized variable name contains.
pub const SYNTHESIZED_NAME_SIGIL: char = '$';

/// True when `name` lies in the synthesized namespace (cannot be a source name).
#[must_use]
pub fn is_synthesized_name(name: &str) -> bool {
    name.contains(SYNTHESIZED_NAME_SIGIL)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn synthesized_names_are_not_identifiers() {
        for name in [
            "$call_0",
            "$_call_3",
            "$fallback_arg0_0",
            "sk$i",
            "x$twp_m1",
            "$_4",
        ] {
            assert!(is_synthesized_name(name));
            assert!(!name.chars().all(|c| c.is_alphanumeric() || c == '_'));
        }
        assert!(!is_synthesized_name("call_0"));
        assert!(!is_synthesized_name("__trust_wp_fallback_arg0_0"));
    }
}
