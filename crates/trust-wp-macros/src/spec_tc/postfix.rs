// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Token-level lowering of pearlite `x@` (view) and `^x` (final), with
//! pearlite-syn precedence (`pearlite-syn/src/term.rs` `unary_term` /
//! `trailer_helper`): `@` is a trailer like `.f`, `.0`, `[i]`, `(args)`, so
//! it binds tighter than every prefix operator; `^` is a prefix operator over
//! a unary term. Hence `^x.0` is `^(x.0)`, `*rc@` is `*(rc@)`, `u64::MAX@` is
//! `(u64::MAX)@` and `self.0@[i]@[x]` is `((self.0)@[i])@[x]`.
//!
//! Output markers (consumed by `encode`): `__trust_wp_tc_view(e)` and
//! `__trust_wp_tc_fin(e)`. A binary `^` (xor, an operand already on its
//! left) is left alone, as are the patterns of match arms (`x @ pat`).

use proc_macro2::{Delimiter, Group, Ident, Spacing, Span, TokenStream, TokenTree};

pub(crate) const VIEW: &str = "__trust_wp_tc_view";
pub(crate) const FIN: &str = "__trust_wp_tc_fin";

const KEYWORDS_OPERAND_FOLLOWS: &[&str] = &[
    "if", "match", "let", "else", "in", "return", "while", "for", "move", "break", "loop",
];

pub(crate) fn lower_postfix(ts: TokenStream) -> TokenStream {
    let tokens: Vec<TokenTree> = ts.into_iter().map(recurse).collect();
    let mut out: Vec<TokenTree> = Vec::new();
    // Split at top-level `,` / `;`; inside a segment leave a match-arm
    // pattern (everything before a top-level `=>`) untouched.
    let mut start = 0;
    for i in 0..=tokens.len() {
        let at_sep = i == tokens.len() || is_punct(&tokens[i], ',') || is_punct(&tokens[i], ';');
        if !at_sep {
            continue;
        }
        let seg = &tokens[start..i];
        match (0..seg.len()).find(|&k| is_fat_arrow(seg, k)) {
            Some(k) => {
                out.extend(seg[..k + 2].iter().cloned());
                out.extend(lower_operands(&seg[k + 2..]));
            }
            None => out.extend(lower_operands(seg)),
        }
        if i < tokens.len() {
            out.push(tokens[i].clone());
        }
        start = i + 1;
    }
    out.into_iter().collect()
}

fn recurse(tt: TokenTree) -> TokenTree {
    match tt {
        TokenTree::Group(g) => {
            let mut ng = Group::new(g.delimiter(), lower_postfix(g.stream()));
            ng.set_span(g.span());
            TokenTree::Group(ng)
        }
        other => other,
    }
}

fn is_punct(tt: &TokenTree, c: char) -> bool {
    matches!(tt, TokenTree::Punct(p) if p.as_char() == c)
}

fn is_fat_arrow(tokens: &[TokenTree], i: usize) -> bool {
    matches!(&tokens[i], TokenTree::Punct(p) if p.as_char() == '=' && p.spacing() == Spacing::Joint)
        && tokens.get(i + 1).is_some_and(|t| is_punct(t, '>'))
        && !(i > 0
            && matches!(&tokens[i - 1], TokenTree::Punct(p) if p.spacing() == Spacing::Joint))
}

fn wrap(name: &str, inner: Vec<TokenTree>, span: Span) -> Vec<TokenTree> {
    let mut g = Group::new(Delimiter::Parenthesis, inner.into_iter().collect());
    g.set_span(span);
    vec![
        TokenTree::Ident(Ident::new(name, span)),
        TokenTree::Group(g),
    ]
}

/// Whether an operand ends with this token (so a following `^` is binary).
fn ends_operand(tt: &TokenTree) -> bool {
    match tt {
        TokenTree::Ident(id) => !KEYWORDS_OPERAND_FOLLOWS.contains(&id.to_string().as_str()),
        TokenTree::Literal(_) | TokenTree::Group(_) => true,
        TokenTree::Punct(p) => matches!(p.as_char(), '?' | '@'),
    }
}

fn lower_operands(seg: &[TokenTree]) -> Vec<TokenTree> {
    let mut out: Vec<TokenTree> = Vec::new();
    let mut i = 0;
    while i < seg.len() {
        let operand_pos = out.last().is_none_or(|t| !ends_operand(t));
        // `->` (closure return type): copy verbatim.
        if matches!(&seg[i], TokenTree::Punct(p) if p.as_char() == '-' && p.spacing() == Spacing::Joint)
            && seg.get(i + 1).is_some_and(|t| is_punct(t, '>'))
        {
            out.extend(seg[i..i + 2].iter().cloned());
            i += 2;
            continue;
        }
        if operand_pos && starts_unary(seg, i) {
            let (toks, next) = parse_unary(seg, i);
            out.extend(toks);
            i = next;
            continue;
        }
        // A stray postfix `@` after something we did not parse as an operand
        // (e.g. after a closing group reached in non-operand position).
        out.push(seg[i].clone());
        i += 1;
    }
    out
}

fn starts_unary(seg: &[TokenTree], i: usize) -> bool {
    match &seg[i] {
        TokenTree::Punct(p) => matches!(p.as_char(), '^' | '*' | '!' | '-' | '&' | '<' | ':'),
        TokenTree::Ident(id) => !KEYWORDS_OPERAND_FOLLOWS.contains(&id.to_string().as_str()),
        TokenTree::Literal(_) | TokenTree::Group(_) => true,
    }
}

/// `unary := ('^' | '*' | '!' | '-' | '&' ['mut']) unary | trailer`
fn parse_unary(seg: &[TokenTree], i: usize) -> (Vec<TokenTree>, usize) {
    if let TokenTree::Punct(p) = &seg[i] {
        let c = p.as_char();
        // `&&` / `||` style joint puncts in operand position are not prefixes
        // we understand; `&` followed by `&` is a double reference.
        if matches!(c, '^' | '*' | '!' | '-' | '&') {
            let mut j = i + 1;
            let mut prefix = vec![seg[i].clone()];
            if c == '&'
                && seg
                    .get(j)
                    .is_some_and(|t| matches!(t, TokenTree::Ident(id) if id == "mut"))
            {
                prefix.push(seg[j].clone());
                j += 1;
            }
            if j >= seg.len() {
                return (prefix, j);
            }
            let (inner, next) = if starts_unary(seg, j) {
                parse_unary(seg, j)
            } else {
                (vec![seg[j].clone()], j + 1)
            };
            if c == '^' {
                return (wrap(FIN, inner, p.span()), next);
            }
            prefix.extend(inner);
            return (prefix, next);
        }
    }
    parse_trailer(seg, i)
}

/// trailer := primary ( '.' member [turbofish] [args] | '.' lit | [idx] | (args) | '@' | '?' )*
fn parse_trailer(seg: &[TokenTree], i: usize) -> (Vec<TokenTree>, usize) {
    let (mut cur, mut j) = parse_primary(seg, i);
    loop {
        match seg.get(j) {
            Some(TokenTree::Punct(p)) if p.as_char() == '@' => {
                cur = wrap(VIEW, cur, p.span());
                j += 1;
            }
            Some(TokenTree::Punct(p)) if p.as_char() == '?' => {
                cur.push(seg[j].clone());
                j += 1;
            }
            Some(TokenTree::Punct(p))
                if p.as_char() == '.'
                    && p.spacing() == Spacing::Alone
                    && !seg.get(j + 1).is_some_and(|t| is_punct(t, '.')) =>
            {
                match seg.get(j + 1) {
                    Some(TokenTree::Ident(_) | TokenTree::Literal(_)) => {
                        cur.push(seg[j].clone());
                        cur.push(seg[j + 1].clone());
                        j += 2;
                        // `::<..>` turbofish on a method.
                        if is_path_sep(seg, j) && seg.get(j + 2).is_some_and(|t| is_punct(t, '<')) {
                            let end = angle_close(seg, j + 2).unwrap_or(seg.len() - 1);
                            cur.extend(seg[j..=end].iter().cloned());
                            j = end + 1;
                        }
                    }
                    _ => break,
                }
            }
            Some(TokenTree::Group(g))
                if matches!(g.delimiter(), Delimiter::Parenthesis | Delimiter::Bracket) =>
            {
                cur.push(seg[j].clone());
                j += 1;
            }
            _ => break,
        }
    }
    (cur, j)
}

fn is_path_sep(seg: &[TokenTree], j: usize) -> bool {
    matches!(seg.get(j), Some(TokenTree::Punct(p)) if p.as_char() == ':' && p.spacing() == Spacing::Joint)
        && seg.get(j + 1).is_some_and(|t| is_punct(t, ':'))
}

fn angle_close(seg: &[TokenTree], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (k, tt) in seg.iter().enumerate().skip(open) {
        if is_punct(tt, '<') {
            depth += 1;
        } else if is_punct(tt, '>') {
            if k > 0
                && matches!(&seg[k - 1], TokenTree::Punct(p) if p.as_char() == '-' && p.spacing() == Spacing::Joint)
            {
                continue;
            }
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return Some(k);
            }
        }
    }
    None
}

/// `primary := literal | group | ['<' qself '>'] ['::'] segment ('::' (segment | '<'..'>'))* ['!' group]`
fn parse_primary(seg: &[TokenTree], i: usize) -> (Vec<TokenTree>, usize) {
    match &seg[i] {
        TokenTree::Literal(_) => (vec![seg[i].clone()], i + 1),
        TokenTree::Group(g) => {
            let mut cur = vec![seg[i].clone()];
            let mut j = i + 1;
            // `$t::MAX` from `macro_rules!`: an invisible group followed by a path tail.
            if g.delimiter() == Delimiter::None {
                let (rest, next) = parse_path_tail(seg, j);
                cur.extend(rest);
                j = next;
            }
            (cur, j)
        }
        TokenTree::Punct(p) if p.as_char() == '<' => {
            let end = angle_close(seg, i).unwrap_or(seg.len() - 1);
            let mut cur: Vec<TokenTree> = seg[i..=end].to_vec();
            let j = end + 1;
            let (rest, next) = parse_path_tail(seg, j);
            cur.extend(rest);
            (cur, next)
        }
        TokenTree::Punct(_) => {
            // Leading `::` of an absolute path.
            if is_path_sep(seg, i) {
                let (rest, next) = parse_path_tail(seg, i);
                return (rest, next);
            }
            (vec![seg[i].clone()], i + 1)
        }
        TokenTree::Ident(_) => {
            let mut cur = vec![seg[i].clone()];
            let (rest, mut j) = parse_path_tail(seg, i + 1);
            cur.extend(rest);
            // Macro invocation `path!(..)`.
            if seg.get(j).is_some_and(|t| is_punct(t, '!'))
                && matches!(seg.get(j + 1), Some(TokenTree::Group(_)))
            {
                cur.push(seg[j].clone());
                cur.push(seg[j + 1].clone());
                j += 2;
            }
            (cur, j)
        }
    }
}

/// ('::' (ident | '<'..'>'))*
fn parse_path_tail(seg: &[TokenTree], mut j: usize) -> (Vec<TokenTree>, usize) {
    let mut cur = Vec::new();
    while is_path_sep(seg, j) {
        match seg.get(j + 2) {
            Some(TokenTree::Ident(_)) => {
                cur.extend(seg[j..j + 3].iter().cloned());
                j += 3;
            }
            Some(t) if is_punct(t, '<') => {
                let end = angle_close(seg, j + 2).unwrap_or(seg.len() - 1);
                cur.extend(seg[j..=end].iter().cloned());
                j = end + 1;
            }
            _ => break,
        }
    }
    (cur, j)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn low(s: &str) -> String {
        lower_postfix(s.parse().unwrap()).to_string()
    }

    #[test]
    fn final_binds_looser_than_field() {
        assert_eq!(
            low("(^x.0)@ == 5"),
            "__trust_wp_tc_view ((__trust_wp_tc_fin (x . 0))) == 5"
        );
    }

    #[test]
    fn view_on_paths_and_chains() {
        assert_eq!(
            low("(*a)@ <= u64::MAX@ / 2"),
            "__trust_wp_tc_view ((* a)) <= __trust_wp_tc_view (u64 :: MAX) / 2"
        );
        assert_eq!(
            low("self.0@[i]@[x]"),
            "__trust_wp_tc_view (__trust_wp_tc_view (self . 0) [i]) [x]"
        );
        assert_eq!(low("*rc@ == 1i32"), "* __trust_wp_tc_view (rc) == 1i32");
        assert_eq!(
            low("<I3<T> as Nat>::VALUE@ == T::VALUE@"),
            "__trust_wp_tc_view (< I3 < T > as Nat >:: VALUE) == __trust_wp_tc_view (T :: VALUE)"
        );
        assert_eq!(low("v@.len() > 0"), "__trust_wp_tc_view (v) . len () > 0");
    }

    #[test]
    fn xor_and_patterns_untouched() {
        assert_eq!(low("a ^ b"), "a ^ b");
        assert_eq!(
            low("match x { y @ Some(_) => y@ , _ => 0 }"),
            "match x { y @ Some (_) => __trust_wp_tc_view (y) , _ => 0 }"
        );
    }

    #[test]
    fn macro_type_group_path() {
        let ty = TokenTree::Group(Group::new(Delimiter::None, "u32".parse().unwrap()));
        let mut ts: TokenStream = std::iter::once(ty).collect();
        ts.extend("::MAX@ > 0".parse::<TokenStream>().unwrap());
        let out = lower_postfix(ts).to_string();
        assert!(out.starts_with("__trust_wp_tc_view ("), "{out}");
        assert!(out.contains("MAX)"), "{out}");
    }

    #[test]
    fn prefix_chain() {
        assert_eq!(
            low("^*x == -y@"),
            "__trust_wp_tc_fin (* x) == - __trust_wp_tc_view (y)"
        );
        assert_eq!(low("old(x)@"), "__trust_wp_tc_view (old (x))");
    }
}
