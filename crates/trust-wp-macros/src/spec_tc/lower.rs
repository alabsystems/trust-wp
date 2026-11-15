// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Token-level lowering of pearlite-only syntax into syn-parsable Rust.
//!
//! Only for the type-check vehicle (see `super`). Rewrites:
//! - `forall<x: T, y: U> body` -> `__trust_wp_tc_forall(|x: T, y: U| -> bool { body })`
//!   (likewise `exists`); the body extends to the end of the enclosing
//!   segment, as in pearlite-syn; `#[trigger(..)]` / `#![trigger ..]` hints
//!   after the binders are dropped;
//! - `a ==> b` -> `__trust_wp_tc_implies((a), (b))` (right associative,
//!   lowest binary precedence).
//!
//! A segment is a token run between top-level `,` / `;` of one delimiter
//! group; a match-arm `pat =>` prefix and a `let pat =` prefix are kept
//! outside the implication split. `@` / `^` are rewritten afterwards by the
//! shared `transform_view_syntax`.

use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};

pub(crate) const FORALL: &str = "__trust_wp_tc_forall";
pub(crate) const EXISTS: &str = "__trust_wp_tc_exists";
pub(crate) const IMPLIES: &str = "__trust_wp_tc_implies";

pub(crate) fn lower_stream(ts: TokenStream) -> TokenStream {
    let tokens: Vec<TokenTree> = ts.into_iter().collect();
    let mut out: Vec<TokenTree> = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < tokens.len() {
        let tt = &tokens[i];
        // A quantifier binder list `forall<x: T, y: U>` is not a separator.
        if (is_ident(tt, "forall") || is_ident(tt, "exists"))
            && tokens.get(i + 1).is_some_and(|t| is_punct(t, '<'))
        {
            if let Some(close) = binder_close(&tokens, i + 1) {
                i = close + 1;
                continue;
            }
        }
        if is_punct(tt, ',') || is_punct(tt, ';') {
            out.extend(lower_segment(&tokens[start..i]));
            out.push(tt.clone());
            start = i + 1;
        }
        i += 1;
    }
    out.extend(lower_segment(&tokens[start..]));
    out.into_iter().collect()
}

fn is_punct(tt: &TokenTree, c: char) -> bool {
    matches!(tt, TokenTree::Punct(p) if p.as_char() == c)
}

fn is_joint_punct(tt: &TokenTree, c: char) -> bool {
    matches!(tt, TokenTree::Punct(p) if p.as_char() == c && p.spacing() == Spacing::Joint)
}

fn is_ident(tt: &TokenTree, name: &str) -> bool {
    matches!(tt, TokenTree::Ident(id) if id == name)
}

/// `=>` at `i` (and not the tail of `==>`, `<=>`, `>=` ...).
fn is_fat_arrow(tokens: &[TokenTree], i: usize) -> bool {
    if !(is_joint_punct(&tokens[i], '=') && tokens.get(i + 1).is_some_and(|t| is_punct(t, '>'))) {
        return false;
    }
    !(i > 0 && matches!(&tokens[i - 1], TokenTree::Punct(p) if p.spacing() == Spacing::Joint))
}

/// `==>` starting at `i`.
fn is_implies(tokens: &[TokenTree], i: usize) -> bool {
    is_joint_punct(&tokens[i], '=')
        && tokens.get(i + 1).is_some_and(|t| is_joint_punct(t, '='))
        && tokens.get(i + 2).is_some_and(|t| is_punct(t, '>'))
        && !(i > 0
            && matches!(&tokens[i - 1], TokenTree::Punct(p) if p.spacing() == Spacing::Joint))
}

/// A lone `=` (assignment / let initializer) at `i`.
fn is_single_eq(tokens: &[TokenTree], i: usize) -> bool {
    let TokenTree::Punct(p) = &tokens[i] else {
        return false;
    };
    if p.as_char() != '=' || p.spacing() == Spacing::Joint {
        return false;
    }
    !(i > 0 && matches!(&tokens[i - 1], TokenTree::Punct(q) if q.spacing() == Spacing::Joint))
}

fn lower_segment(seg: &[TokenTree]) -> Vec<TokenTree> {
    if seg.is_empty() {
        return Vec::new();
    }
    // Match arm `pat => body`.
    if let Some(i) = (0..seg.len()).find(|&i| is_fat_arrow(seg, i) && !quantifier_before(seg, i)) {
        let mut out = lower_groups(&seg[..i + 2]);
        out.extend(lower_segment(&seg[i + 2..]));
        return out;
    }
    // `let pat = init`.
    if is_ident(&seg[0], "let") {
        if let Some(i) = (1..seg.len()).find(|&i| is_single_eq(seg, i)) {
            let mut out = lower_groups(&seg[..=i]);
            out.extend(lower_segment(&seg[i + 1..]));
            return out;
        }
    }
    // Quantifier: its body extends to the end of the segment.
    for q in 0..seg.len() {
        let kind = match &seg[q] {
            TokenTree::Ident(id) if id == "forall" => FORALL,
            TokenTree::Ident(id) if id == "exists" => EXISTS,
            _ => continue,
        };
        if !seg.get(q + 1).is_some_and(|t| is_punct(t, '<')) {
            continue;
        }
        let Some(close) = binder_close(seg, q + 1) else {
            continue;
        };
        let binders: TokenStream = seg[q + 2..close].iter().cloned().collect();
        let mut body_start = close + 1;
        // Trigger hints: `#[trigger(..)]` or `#![trigger ..]`.
        while body_start < seg.len() && is_punct(&seg[body_start], '#') {
            let mut j = body_start + 1;
            if seg.get(j).is_some_and(|t| is_punct(t, '!')) {
                j += 1;
            }
            match seg.get(j) {
                Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Bracket => {
                    body_start = j + 1;
                }
                _ => break,
            }
        }
        let body: TokenStream = lower_segment(&seg[body_start..]).into_iter().collect();
        let span = seg[q].span();
        let quant = quantifier_call(kind, binders, body, span);
        return lower_implications(&seg[..q], quant);
    }
    lower_implications(seg, Vec::new())
}

/// Whether position `i` lies inside a `forall<...>` binder list (a `=>`
/// there would be a type-level token, not a match arm). Conservative.
fn quantifier_before(seg: &[TokenTree], i: usize) -> bool {
    (0..i).any(|q| {
        (is_ident(&seg[q], "forall") || is_ident(&seg[q], "exists"))
            && seg.get(q + 1).is_some_and(|t| is_punct(t, '<'))
    })
}

/// Index of the `>` closing the binder list opened by `<` at `open`.
fn binder_close(seg: &[TokenTree], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (i, tt) in seg.iter().enumerate().skip(open) {
        if is_punct(tt, '<') {
            depth += 1;
        } else if is_punct(tt, '>') {
            // `->` inside a binder type is not a closing bracket.
            if i > 0 && is_joint_punct(&seg[i - 1], '-') {
                continue;
            }
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
    }
    None
}

fn quantifier_call(
    kind: &str,
    binders: TokenStream,
    body: TokenStream,
    span: Span,
) -> Vec<TokenTree> {
    let mut closure: Vec<TokenTree> = Vec::new();
    closure.push(punct('|', Spacing::Alone, span));
    closure.extend(binders);
    closure.push(punct('|', Spacing::Alone, span));
    closure.push(punct('-', Spacing::Joint, span));
    closure.push(punct('>', Spacing::Alone, span));
    closure.push(TokenTree::Ident(Ident::new("bool", span)));
    closure.push(group(Delimiter::Brace, body, span));
    vec![
        TokenTree::Ident(Ident::new(kind, span)),
        group(Delimiter::Parenthesis, closure.into_iter().collect(), span),
    ]
}

fn punct(c: char, spacing: Spacing, span: Span) -> TokenTree {
    let mut p = Punct::new(c, spacing);
    p.set_span(span);
    TokenTree::Punct(p)
}

fn group(delim: Delimiter, ts: TokenStream, span: Span) -> TokenTree {
    let mut g = Group::new(delim, ts);
    g.set_span(span);
    TokenTree::Group(g)
}

/// Split `seg ++ tail` at top-level `==>`; `tail` (already lowered) belongs
/// to the last operand.
fn lower_implications(seg: &[TokenTree], tail: Vec<TokenTree>) -> Vec<TokenTree> {
    let mut parts: Vec<Vec<TokenTree>> = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < seg.len() {
        if is_implies(seg, i) {
            parts.push(lower_groups(&seg[start..i]));
            i += 3;
            start = i;
        } else {
            i += 1;
        }
    }
    let mut last = lower_groups(&seg[start..]);
    last.extend(tail);
    parts.push(last);
    let mut acc = parts.pop().unwrap_or_default();
    while let Some(hyp) = parts.pop() {
        let span = hyp
            .first()
            .map_or_else(Span::call_site, proc_macro2::TokenTree::span);
        let args = vec![
            group(Delimiter::Parenthesis, hyp.into_iter().collect(), span),
            punct(',', Spacing::Alone, span),
            group(Delimiter::Parenthesis, acc.into_iter().collect(), span),
        ];
        acc = vec![
            TokenTree::Ident(Ident::new(IMPLIES, span)),
            group(Delimiter::Parenthesis, args.into_iter().collect(), span),
        ];
    }
    acc
}

fn lower_groups(seg: &[TokenTree]) -> Vec<TokenTree> {
    seg.iter()
        .map(|tt| match tt {
            TokenTree::Group(g) => {
                let mut ng = Group::new(g.delimiter(), lower_stream(g.stream()));
                ng.set_span(g.span());
                TokenTree::Group(ng)
            }
            other => other.clone(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn low(s: &str) -> String {
        lower_stream(s.parse().unwrap()).to_string()
    }

    #[test]
    fn implication_right_assoc() {
        assert_eq!(
            low("a ==> b ==> c"),
            "__trust_wp_tc_implies ((a) , (__trust_wp_tc_implies ((b) , (c))))"
        );
    }

    #[test]
    fn quantifier_body_extends() {
        assert_eq!(
            low("x && forall<i: Int, j> i < j ==> p(i)"),
            "x && __trust_wp_tc_forall (| i : Int , j | -> bool { __trust_wp_tc_implies ((i < j) , (p (i))) })"
        );
    }

    #[test]
    fn hyp_before_quantifier() {
        assert_eq!(
            low("a ==> exists<s: Seq<(K, V)>> s == t"),
            "__trust_wp_tc_implies ((a) , (__trust_wp_tc_exists (| s : Seq < (K , V) >| -> bool { s == t })))"
        );
    }

    #[test]
    fn match_arms_and_let() {
        assert_eq!(
            low("match r { Some(v) => a ==> b, None => true }"),
            "match r { Some (v) => __trust_wp_tc_implies ((a) , (b)) , None => true }"
        );
        assert_eq!(
            low("{ let y = a ==> b; y }"),
            "{ let y = __trust_wp_tc_implies ((a) , (b)) ; y }"
        );
    }

    #[test]
    fn comparisons_untouched() {
        assert_eq!(low("a >= b && c <= d"), "a >= b && c <= d");
    }

    #[test]
    fn trigger_dropped() {
        assert_eq!(
            low("forall<x: Int> #[trigger(f(x))] f(x)"),
            "__trust_wp_tc_forall (| x : Int | -> bool { f (x) })"
        );
    }
}
