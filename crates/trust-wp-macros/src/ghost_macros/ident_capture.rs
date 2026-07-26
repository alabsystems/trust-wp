// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Identifier capture and quantifier binding analysis for `proof_assert` expressions.
//!
//! Scans token streams to extract free variable identifiers, excluding reserved
//! keywords, type names, quantifier-bound variables, field/method names, and
//! path segments.

/// Keywords and type names that should not be treated as free variable identifiers
/// when extracting captures from `proof_assert` expressions.
pub(crate) const RESERVED_IDENTS: &[&str] = &[
    // Rust keywords
    "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn", "for",
    "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return",
    "self", "Self", "static", "struct", "super", "trait", "true", "type", "unsafe", "use", "where",
    "while", "async", "await", "dyn", // Pearlite/trust-wp spec keywords
    "forall", "exists", "result", "old", // Common type names (not variables)
    "bool", "char", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128",
    "usize", "f32", "f64", "str", "String", "Vec", "Option", "Result", "Box", "Rc", "Arc",
    "HashMap", "HashSet", "Int",
];

/// Extract likely free variable identifiers from a token stream.
///
/// Scans the token stream for `Ident` tokens that are not reserved keywords,
/// type names, or quantifier-bound variables. The result is conservative (may
/// capture more than needed — extra captures don't hurt).
pub(crate) fn extract_free_identifiers(
    tokens: &proc_macro2::TokenStream,
) -> Vec<proc_macro2::Ident> {
    let mut idents = Vec::new();
    let mut seen = std::collections::HashSet::new();
    // Track quantifier-bound variables: `forall<x: T>` or `exists<y: T>` bind x, y
    let mut quantifier_bound = std::collections::HashSet::new();
    collect_idents_from_tokens(tokens, &mut idents, &mut seen, &mut quantifier_bound);
    idents
}

/// Recursively collect identifiers from a token stream.
fn collect_idents_from_tokens(
    tokens: &proc_macro2::TokenStream,
    idents: &mut Vec<proc_macro2::Ident>,
    seen: &mut std::collections::HashSet<String>,
    quantifier_bound: &mut std::collections::HashSet<String>,
) {
    fn peek_double_colon(iter: &std::iter::Peekable<proc_macro2::token_stream::IntoIter>) -> bool {
        let mut clone = iter.clone();
        matches!(
            (clone.next(), clone.next()),
            (
                Some(proc_macro2::TokenTree::Punct(first)),
                Some(proc_macro2::TokenTree::Punct(second))
            ) if first.as_char() == ':' && second.as_char() == ':'
        )
    }

    let mut iter = tokens.clone().into_iter().peekable();
    let mut after_dot = false;
    let mut after_path_sep = false;
    while let Some(tt) = iter.next() {
        match &tt {
            proc_macro2::TokenTree::Ident(id) => {
                // After `.`, the identifier is a field name or method — not a free variable
                if after_dot {
                    after_dot = false;
                    continue;
                }
                // Identifier immediately after `::` is a path segment — not a free variable.
                if after_path_sep {
                    after_path_sep = false;
                    continue;
                }
                after_dot = false;
                let name = id.to_string();
                // If this is `forall` or `exists`, the next `<...>` group binds variables
                if name == "forall" || name == "exists" {
                    if let Some(proc_macro2::TokenTree::Punct(p)) = iter.peek() {
                        if p.as_char() == '<' {
                            collect_quantifier_bindings(&mut iter, quantifier_bound);
                        }
                    }
                    continue;
                }
                // If followed by `(`, this is a function call — not a variable
                let is_call = matches!(
                    iter.peek(),
                    Some(proc_macro2::TokenTree::Group(g))
                        if g.delimiter() == proc_macro2::Delimiter::Parenthesis
                );
                if is_call {
                    continue;
                }
                // If followed by `::`, this is a path segment (module/type) — not a variable
                let is_path = peek_double_colon(&iter);
                if is_path {
                    continue;
                }
                if !RESERVED_IDENTS.contains(&name.as_str())
                    && !quantifier_bound.contains(&name)
                    && !seen.contains(&name)
                    && !name.starts_with(|c: char| c.is_uppercase())
                {
                    seen.insert(name);
                    idents.push(id.clone());
                }
            }
            proc_macro2::TokenTree::Punct(p) => {
                after_dot = p.as_char() == '.';
                if p.as_char() == ':' && peek_double_colon(&iter) {
                    // Current `:` is the first half of `::`; when the second `:`
                    // is consumed, the following identifier must be ignored.
                    after_path_sep = true;
                }
            }
            proc_macro2::TokenTree::Group(group) => {
                after_dot = false;
                after_path_sep = false;
                collect_idents_from_tokens(&group.stream(), idents, seen, quantifier_bound);
            }
            proc_macro2::TokenTree::Literal(_) => {
                after_dot = false;
                after_path_sep = false;
            }
        }
    }
}

/// Consume tokens from a quantifier binding `<x: T, y: U>` and record bound variable names.
///
/// Handles nested angle brackets in type annotations, e.g.
/// `exists<prod: Seq<(K, V)>, it1: &mut IntoIter<K, V>>` — the inner `<K, V>`
/// must not prematurely terminate the binding scan.
fn collect_quantifier_bindings(
    iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
    quantifier_bound: &mut std::collections::HashSet<String>,
) {
    // Skip the `<` punct
    iter.next();
    let mut expect_ident = true;
    let mut angle_depth: u32 = 0;
    for tt in iter.by_ref() {
        match &tt {
            proc_macro2::TokenTree::Punct(p) if p.as_char() == '<' => {
                angle_depth += 1;
            }
            proc_macro2::TokenTree::Punct(p) if p.as_char() == '>' => {
                if angle_depth == 0 {
                    break;
                }
                angle_depth -= 1;
            }
            proc_macro2::TokenTree::Punct(p) if p.as_char() == ',' && angle_depth == 0 => {
                expect_ident = true;
            }
            proc_macro2::TokenTree::Punct(p) if p.as_char() == ':' && angle_depth == 0 => {
                expect_ident = false;
            }
            proc_macro2::TokenTree::Ident(id) if expect_ident && angle_depth == 0 => {
                quantifier_bound.insert(id.to_string());
                expect_ident = false;
            }
            _ => {}
        }
    }
}
