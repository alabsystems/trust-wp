// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specification type-check vehicle.
//!
//! trust-wp reads every contract clause as TEXT from `trust-wp:` doc markers,
//! so without this module rustc never type-checks a clause and an ill-typed
//! specification (`{ let _y: bool = 5u32; true }`) verifies. Creusot's
//! attribute expansion instead places the clause, lowered by `pretyping`,
//! inside a closure rustc type-checks. This module does the same:
//!
//! ```text
//! #[cfg(trust_wp)]
//! #[allow(..)]
//! let _ = #[doc(hidden)] #[doc = "__trust_wp_spec_tc"]
//!     |result: Ret| -> bool { use ..; <encoded clause> };
//! ```
//!
//! * `cfg(trust_wp)`: only the trust-wp driver sets it, so plain builds (and
//!   dependency crates under `cargo trust-wp`) never contain the closure;
//! * the driver's `mir_built` override (`callbacks::spec_typecheck`) turns the
//!   closure's construction into `Nop`s and replaces the body of every
//!   `__trust_wp_spec_tc` closure (and closures nested in it) with a bare
//!   return, so it creates no MIR, no borrows, no runtime obligations and is
//!   never borrow-checked (pearlite is not subject to Rust ownership);
//! * the clause TEXT recorded in the doc marker is untouched, so the
//!   specification the driver parses is unchanged.
//!
//! A clause the lowering cannot parse as Rust (e.g. chained comparisons that
//! trust-wp-core accepts) is simply not type-checked here — the vehicle only
//! ever adds rejections.

mod encode;
pub(crate) mod lower;
mod postfix;

use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned};
use syn::{ReturnType, Type};

/// Doc marker carried by every type-check closure. Deliberately NOT a
/// `trust-wp:` marker: no driver pass that scans `trust-wp:` doc attributes
/// may ever mistake it for a specification.
pub(crate) const SPEC_TC_MARKER: &str = "__trust_wp_spec_tc";

/// The marker value the type-check closure of a LOGIC BODY carries in place
/// of `SPEC_TC_MARKER` (`logic_body_statement`). Every pass that honours the
/// marker honours both; the driver reads this one to tell the body's closure
/// from its contract clauses' (`logic::call_resolution`).
pub(crate) const SPEC_TC_LOGIC_BODY_MARKER: &str = "__trust_wp_spec_tc:logic_body";

/// Prefix of the doc attribute naming the clause a type-check body checks
/// (`clause_tag_attr`). The driver reads a clause's calls in that clause's
/// own body (`trust-wp-driver` `logic::spec_calls`), so the tag carries the
/// clause's `trust-wp:` marker kind and exactly the text that marker carries.
pub(crate) const SPEC_TC_CLAUSE_TAG: &str = "__trust_wp_spec_tc_clause:";

/// Pearlite-only syntax -> Rust tokens (quantifiers, `==>`, `@`, `^`).
pub(crate) fn lower_tokens(ts: TokenStream) -> TokenStream {
    postfix::lower_postfix(lower::lower_stream(unpreprocess_final(ts)))
}

/// `ghost!`/`snapshot!`/`pearlite!` run `preprocess_view_syntax` over their
/// whole input, so a contract attribute nested inside them (e.g. a loop
/// `#[invariant]` in a `ghost!` block) arrives with `^x` already rewritten
/// to `final_value(x)`. Restore the prophecy operator so the clause is
/// type-checked as Creusot's `^` (`*Fin::fin(x)`); `x@` arrives as
/// `view(x)`, a real `trust_wp_std` function, and needs nothing.
fn unpreprocess_final(ts: TokenStream) -> TokenStream {
    let tokens: Vec<TokenTree> = ts.into_iter().collect();
    let mut out = Vec::with_capacity(tokens.len());
    let mut i = 0;
    while i < tokens.len() {
        match (&tokens[i], tokens.get(i + 1)) {
            (TokenTree::Ident(id), Some(TokenTree::Group(g)))
                if id == "final_value" && g.delimiter() == Delimiter::Parenthesis =>
            {
                let mut caret = proc_macro2::Punct::new('^', proc_macro2::Spacing::Alone);
                caret.set_span(id.span());
                out.push(TokenTree::Punct(caret));
                let mut inner = Group::new(Delimiter::Parenthesis, unpreprocess_final(g.stream()));
                inner.set_span(g.span());
                out.push(TokenTree::Group(inner));
                i += 2;
            }
            (TokenTree::Group(g), _) => {
                let mut inner = Group::new(g.delimiter(), unpreprocess_final(g.stream()));
                inner.set_span(g.span());
                out.push(TokenTree::Group(inner));
                i += 1;
            }
            (t, _) => {
                out.push(t.clone());
                i += 1;
            }
        }
    }
    out.into_iter().collect()
}

pub(crate) fn lower_and_parse_block(ts: TokenStream) -> Option<syn::Block> {
    let lowered = lower_tokens(ts);
    let braced = TokenTree::Group(Group::new(Delimiter::Brace, lowered));
    syn::parse2::<syn::Block>(std::iter::once(braced).collect()).ok()
}

fn span_of(ts: &TokenStream) -> Span {
    ts.clone()
        .into_iter()
        .next()
        .map_or_else(Span::call_site, |t| t.span())
}

fn uses_prelude(sp: Span) -> TokenStream {
    quote_spanned! {sp=>
        #[allow(unused_imports)]
        use ::trust_wp_std::__spec_tc::{ExtEqTc as _, IndexPaTc as _, IndexTc as _, ViewTc as _};
        #[allow(unused_imports)]
        use ::trust_wp_std::std::ops::{FnExt as _, FnMutExt as _, FnOnceExt as _};
        #[allow(unused_imports)]
        use ::trust_wp_std::__spec_tc::{
            FMapLogicTc as _, FSetLogicTc as _, IntLogicTc as _, MappingLogicTc as _,
            SeqLogicTc as _, SeqSeqLogicTc as _, SeqRefLogicTc as _, FSetIntLogicTc as _, RaLogicTc as _,
        };
    }
}

/// Encode a clause given as attribute/macro tokens into a block expression
/// of the clause's own value, or `None` when it does not parse as Rust.
pub(crate) fn encode_clause(clause: &TokenStream) -> Option<TokenStream> {
    encode_clause_mode(clause, false)
}

fn encode_clause_mode(clause: &TokenStream, proof_assert_mode: bool) -> Option<TokenStream> {
    let block = lower_and_parse_block(clause.clone())?;
    let sp = span_of(clause);
    let uses = uses_prelude(sp);
    let body = encode::encode_block(&block, proof_assert_mode);
    Some(quote_spanned! {sp=> { #uses #body } })
}

/// Whether trust-wp's driver will PARSE `clause` as a contract clause —
/// `boolean` for `requires`/`ensures`/`invariant`, which must be predicates;
/// a `variant` is any term.
///
/// A clause the driver's own parser refuses (`callbacks::parsing::clauses`:
/// `parse_contract` fails, or a boolean clause is structurally non-boolean —
/// `#[requires('a')]` parses as `Int(97)`) is a PARSE error of the
/// specification: the driver reports `failed to parse <kind>`, verifies
/// nothing of the function (`has unparseable .. clause(s) — skipping
/// verification to prevent unsound results`) and the front door exits 3,
/// the documented parse/CLI-error code. Type-checking such a clause here
/// would put rustc's E0308 (`expected bool, found char`) first and end the
/// run as a compile error instead, so the vehicle leaves it to the driver.
///
/// This never widens acceptance: every clause skipped here is one the
/// driver refuses outright. The text parsed is exactly the clause text the
/// `trust-wp:<kind>:` doc marker carries (`attrs::emit_tool_attr`), so the
/// two parsers see the same string.
pub(crate) fn driver_parses(boolean: bool, clause: &TokenStream) -> bool {
    let Ok(expr) = trust_wp_core::contract_parser::parse_contract(&clause.to_string()) else {
        return false;
    };
    // The SHARED refusal predicate, not a copy of it: the driver's
    // `parse_boolean_clause` calls the same `trust_wp_core` method, so this
    // vehicle cannot skip a type-check for a clause the driver would accept.
    !(boolean && expr.is_refused_as_boolean_clause())
}

/// The `#[doc = "<marker>"]` marker attribute (`SPEC_TC_MARKER`, or
/// `SPEC_TC_LOGIC_BODY_MARKER` on a logic body's closure), every token (and
/// so the attribute's span) at `Span::call_site()`. The driver honours the
/// marker only when its span comes from this crate's macro expansion
/// (`trust-wp-driver` `spec_typecheck::marker_is_from_trust_wp_macros`); a
/// marker written in user source keeps the user's span and is refused.
/// Never build it with a span taken from user tokens.
fn marker_attr(marker: &str) -> TokenStream {
    quote! { #[doc = #marker] }
}

/// The tag naming the clause a type-check body checks: its `trust-wp:`
/// marker `kind` and the clause text, spelled as `attrs::emit_tool_attr`
/// spells the marker (the tokens' `Display`). Built at `Span::call_site()`,
/// as `marker_attr` is.
fn clause_tag_attr(kind: &str, clause: &TokenStream) -> TokenStream {
    let tag = format!("{SPEC_TC_CLAUSE_TAG}{kind}:{clause}");
    quote! { #[doc = #tag] }
}

/// The type-check statement for a clause, tagged `tag`
/// (`clause_tag_attr`): `let _ = |<params>| -> <ret> <body>;`.
fn tc_statement(
    sp: Span,
    tag: TokenStream,
    params: TokenStream,
    ret: TokenStream,
    body: TokenStream,
) -> TokenStream {
    tc_statement_marked(sp, tag, params, ret, body, SPEC_TC_MARKER)
}

/// `tc_statement` with the closure marked `marker`.
fn tc_statement_marked(
    sp: Span,
    tag: TokenStream,
    params: TokenStream,
    ret: TokenStream,
    body: TokenStream,
    marker: &str,
) -> TokenStream {
    let marker = marker_attr(marker);
    quote_spanned! {sp=>
        #[cfg(trust_wp)]
        #[allow(let_underscore_drop, unused_variables, unused_braces, unused_parens,
                clippy::all, unreachable_code, non_shorthand_field_patterns)]
        let _ = #[doc(hidden)] #marker #tag |#params| -> #ret #body;
    }
}

/// Whether `ty` mentions `impl Trait` (cannot annotate a closure parameter).
fn type_has_impl_trait(ty: &Type) -> bool {
    quote!(#ty)
        .to_string()
        .split_whitespace()
        .any(|t| t == "impl")
}

/// Result binding type for an `ensures` closure, or `None` when it cannot be
/// written as a closure parameter type.
fn result_type(output: &ReturnType) -> Option<TokenStream> {
    match output {
        ReturnType::Default => Some(quote! { () }),
        ReturnType::Type(_, ty) if type_has_impl_trait(ty) || is_never(ty) => None,
        ReturnType::Type(_, ty) => Some(quote! { #ty }),
    }
}

/// `-> !`: the never type cannot be written as a closure parameter type on
/// stable (E0658) and a diverging function has no result to bind.
fn is_never(ty: &Type) -> bool {
    match ty {
        Type::Never(_) => true,
        Type::Paren(p) => is_never(&p.elem),
        _ => false,
    }
}

enum EnsuresResultParam {
    Omitted,
    Bound(TokenStream),
}

/// The `result` parameter of an `ensures` type-check closure. A diverging
/// function omits it when the clause does not mention `result`; `None`
/// declines a clause that cannot be type-checked here.
fn ensures_result_param(output: &ReturnType, clause: &TokenStream) -> Option<EnsuresResultParam> {
    if let ReturnType::Type(_, ty) = output {
        if is_never(ty) {
            return if mentions_ident(clause, "result") {
                None
            } else {
                Some(EnsuresResultParam::Omitted)
            };
        }
    }
    let ret = result_type(output)?;
    Some(EnsuresResultParam::Bound(quote! { result: #ret }))
}

/// The kind of fn-level clause being type-checked.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum FnClause {
    Requires,
    Ensures,
    Variant,
}

impl FnClause {
    /// The `trust-wp:` marker kind `attrs::emit_tool_attr` writes the clause
    /// under.
    fn marker_kind(self) -> &'static str {
        match self {
            Self::Requires => "requires",
            Self::Ensures => "ensures",
            Self::Variant => "variant",
        }
    }
}

/// Parse the signature part of a function item (everything before its body
/// brace group). Returns the return type.
fn fn_signature_output(prefix: &[TokenTree]) -> Option<ReturnType> {
    let mut ts: TokenStream = prefix.iter().cloned().collect();
    ts.extend(quote! { {} });
    if let Ok(f) = syn::parse2::<syn::ItemFn>(ts.clone()) {
        return Some(f.sig.output);
    }
    if let Ok(f) = syn::parse2::<syn::ImplItemFn>(ts.clone()) {
        return Some(f.sig.output);
    }
    syn::parse2::<syn::TraitItemFn>(ts)
        .ok()
        .map(|f| f.sig.output)
}

/// Insert the type-check closure for `clause` at the start of the body of
/// the function item `item`; for a bodyless trait method, emit a sibling
/// helper (`trait_signature_helper`). Other items (closures, `extern_spec!`
/// shapes) are returned unchanged: they are not type-checked by this vehicle.
pub(crate) fn insert_fn_clause(
    kind: FnClause,
    clause: &TokenStream,
    item: TokenStream,
) -> TokenStream {
    let tokens: Vec<TokenTree> = item.clone().into_iter().collect();
    if matches!(tokens.last(), Some(TokenTree::Punct(p)) if p.as_char() == ';') {
        // Bodyless trait method: the helper is a SIBLING item, emitted by the
        // caller before the `trust-wp:` marker (`trait_signature_helper`).
        return item;
    }
    let Some(TokenTree::Group(body)) = tokens.last() else {
        return item;
    };
    if body.delimiter() != Delimiter::Brace {
        return item;
    }
    let Some(output) = fn_signature_output(&tokens[..tokens.len() - 1]) else {
        return item;
    };
    if kind == FnClause::Ensures && is_closure_clause(clause) {
        return item;
    }
    if !driver_parses(kind != FnClause::Variant, clause) {
        return item;
    }
    let Some(encoded) = encode_clause(clause) else {
        return item;
    };
    let sp = span_of(clause);
    let tag = clause_tag_attr(kind.marker_kind(), clause);
    let stmt = match kind {
        FnClause::Requires => tc_statement(sp, tag, quote! {}, quote! { bool }, encoded),
        FnClause::Ensures => {
            let Some(param) = ensures_result_param(&output, clause) else {
                return item;
            };
            let params = match param {
                EnsuresResultParam::Omitted => TokenStream::new(),
                EnsuresResultParam::Bound(p) => quote_spanned! {sp=> #p },
            };
            tc_statement(sp, tag, params, quote! { bool }, encoded)
        }
        FnClause::Variant => {
            let check = quote_spanned! {sp=> ::trust_wp_std::__spec_tc::variant_check };
            tc_statement(
                sp,
                tag,
                quote! {},
                quote! { bool },
                quote_spanned! {sp=> { let _ = #check(#encoded); true } },
            )
        }
    };
    if kind == FnClause::Variant {
        // A fn-level `#[variant]` is trust-wp's spelling of a LOOP variant
        // (`demo/03_loops.rs`: "#[variant] strictly decreases"), so it names
        // the loop's counter — a binding of the function BODY, not a
        // parameter. Type-checking it at the top of the body puts it where
        // that binding does not exist yet (`error[E0425]: cannot find value
        // `i` in this scope`), which rejects a specification trust-wp proves.
        // Placing the statement immediately before the loop gives the clause
        // the same scope a loop `#[invariant]`/`#[variant]` gets. A recursive
        // function's variant names only parameters, so the move costs it
        // nothing; with no loop to find, the statement stays at the top.
        if let Some(at) = first_loop_statement_start(body) {
            return splice_into_body(&tokens, body, at, stmt);
        }
    }
    prepend_to_body(&tokens, body, stmt)
}

/// Index, in the token list of a function body, where the first top-level
/// loop statement starts — its label when it has one.
///
/// Token-level on purpose: the body is re-emitted unchanged apart from the
/// splice. A loop nested inside another statement (`let x = loop { .. }`, a
/// loop inside an inner block) is deliberately not matched: the position
/// must be one where a `let` statement is legal, which is why the keyword
/// has to open a statement (nothing before it, a `;`, or a closing brace).
fn first_loop_statement_start(body: &Group) -> Option<usize> {
    let toks: Vec<TokenTree> = body.stream().into_iter().collect();
    for (i, tok) in toks.iter().enumerate() {
        let TokenTree::Ident(id) = tok else { continue };
        if !matches!(id.to_string().as_str(), "while" | "for" | "loop") {
            continue;
        }
        // `'label: while ..` — the statement starts at the lifetime.
        let start = if i >= 3
            && matches!(&toks[i - 1], TokenTree::Punct(p) if p.as_char() == ':')
            && matches!(&toks[i - 2], TokenTree::Ident(_))
            && matches!(&toks[i - 3], TokenTree::Punct(p) if p.as_char() == '\'')
        {
            i - 3
        } else {
            i
        };
        let opens_statement = match start.checked_sub(1).map(|j| &toks[j]) {
            None => true,
            Some(TokenTree::Punct(p)) => p.as_char() == ';',
            Some(TokenTree::Group(g)) => g.delimiter() == Delimiter::Brace,
            _ => false,
        };
        if opens_statement {
            return Some(start);
        }
    }
    None
}

/// Re-emit the item with `stmt` inserted into its body at token index `at`.
fn splice_into_body(
    tokens: &[TokenTree],
    body: &Group,
    at: usize,
    stmt: TokenStream,
) -> TokenStream {
    let body_toks: Vec<TokenTree> = body.stream().into_iter().collect();
    let mut inner: TokenStream = body_toks[..at].iter().cloned().collect();
    inner.extend(stmt);
    inner.extend(body_toks[at..].iter().cloned());
    let mut new_body = Group::new(Delimiter::Brace, inner);
    new_body.set_span(body.span());
    let mut out: TokenStream = tokens[..tokens.len() - 1].iter().cloned().collect();
    out.extend(std::iter::once(TokenTree::Group(new_body)));
    out
}

/// The kind of loop clause being type-checked.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LoopClause {
    Invariant,
    Variant,
}

/// Type-check statement for a loop `#[invariant]`/`#[variant]`, placed as
/// the statement right BEFORE the loop statement `item`.
///
/// Scope follows Creusot's desugaring (`creusot-std-proc` `invariant.rs`):
/// the clause sees the variables in scope before the loop — never the loop
/// pattern bindings of `for`/`while let` — plus, on a `for` loop, `iter`
/// (the `IntoIterator::into_iter` value) and `produced`
/// (`Snapshot<Seq<Item>>`). Returns `None` when `item` is not a
/// `while`/`for`/`loop` expression or the clause does not parse as Rust.
pub(crate) fn loop_clause_statement(
    kind: LoopClause,
    clause: &TokenStream,
    item: &TokenStream,
) -> Option<TokenStream> {
    let tokens: Vec<TokenTree> = item.clone().into_iter().collect();
    let mut i = 0;
    // Outer attributes (`#[..]`, including the remaining contract attributes).
    while matches!(tokens.get(i), Some(TokenTree::Punct(p)) if p.as_char() == '#')
        && matches!(tokens.get(i + 1), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Bracket)
    {
        i += 2;
    }
    // Optional label `'name:`.
    if matches!(tokens.get(i), Some(TokenTree::Punct(p)) if p.as_char() == '\'') {
        if !matches!(tokens.get(i + 1), Some(TokenTree::Ident(_))) {
            return None;
        }
        if !matches!(tokens.get(i + 2), Some(TokenTree::Punct(p)) if p.as_char() == ':') {
            return None;
        }
        i += 3;
    }
    let Some(TokenTree::Ident(head)) = tokens.get(i) else {
        return None;
    };
    let head = head.to_string();
    if !matches!(head.as_str(), "while" | "for" | "loop") {
        return None;
    }
    let Some(TokenTree::Group(body)) = tokens.last() else {
        return None;
    };
    if body.delimiter() != Delimiter::Brace || tokens.len() <= i + 1 {
        return None;
    }
    if !driver_parses(kind == LoopClause::Invariant, clause) {
        return None;
    }
    let encoded = encode_clause(clause)?;
    let sp = span_of(clause);
    let value = match kind {
        LoopClause::Invariant => encoded,
        LoopClause::Variant => {
            let check = quote_spanned! {sp=> ::trust_wp_std::__spec_tc::variant_check };
            quote_spanned! {sp=> { let _ = #check(#encoded); true } }
        }
    };
    let body = if head == "for" {
        // `for <pat> in <expr> { body }`: `in` is the first top-level `in`
        // after the pattern (a pattern never contains a bare `in`).
        let rest = &tokens[i + 1..tokens.len() - 1];
        let pos = rest
            .iter()
            .position(|t| matches!(t, TokenTree::Ident(id) if id == "in"))?;
        let iter_expr: TokenStream = rest[pos + 1..].iter().cloned().collect();
        if iter_expr.is_empty() {
            return None;
        }
        let helper = quote_spanned! {sp=> ::trust_wp_std::__spec_tc::for_loop_tc };
        quote_spanned! {sp=> {
            #helper((#iter_expr), |iter, produced| -> bool { let _ = (&iter, &produced); #value })
        } }
    } else {
        value
    };
    let kind = match kind {
        LoopClause::Invariant => "invariant",
        LoopClause::Variant => "variant",
    };
    Some(tc_statement(
        sp,
        clause_tag_attr(kind, clause),
        quote! {},
        quote! { bool },
        body,
    ))
}

/// Bodyless trait method (`fn f(..) -> R;`): Creusot emits a sibling trait
/// item `fn <unique>(<sig inputs>, result: R) -> bool { <clause> }`
/// (`creusot-std-proc` `sig_spec_item`). trust-wp does the same, with
/// `where Self: Sized` (the helper never makes a trait non dyn-compatible)
/// and the `__trust_wp_spec_tc` marker on the helper fn, which the driver
/// never verifies and whose MIR it erases. Returns only the helper: the
/// caller emits it BEFORE the method's `trust-wp:` marker, so the marker
/// stays on the method (a marker on the helper would drop the contract).
pub(crate) fn trait_signature_helper(
    kind: FnClause,
    clause: &TokenStream,
    item: &TokenStream,
) -> Option<TokenStream> {
    if kind == FnClause::Variant
        || !matches!(item.clone().into_iter().last(), Some(TokenTree::Punct(p)) if p.as_char() == ';')
    {
        return None;
    }
    let Ok(method) = syn::parse2::<syn::TraitItemFn>(item.clone()) else {
        return None;
    };
    if method.default.is_some() {
        return None;
    }
    if kind == FnClause::Ensures && is_closure_clause(clause) {
        return None;
    }
    if !driver_parses(true, clause) {
        return None;
    }
    let mut sig = method.sig.clone();
    if sig.variadic.is_some() {
        return None;
    }
    let result_param = match kind {
        FnClause::Ensures => ensures_result_param(&sig.output, clause)?,
        _ => EnsuresResultParam::Omitted,
    };
    let encoded = encode_clause(clause)?;
    let sp = span_of(clause);
    static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    sig.ident = syn::Ident::new(
        &format!("__trust_wp_spec_tc_{}_{n}", method.sig.ident),
        method.sig.ident.span(),
    );
    sig.constness = None;
    sig.asyncness = None;
    if let EnsuresResultParam::Bound(result_param) = result_param {
        let Ok(arg) = syn::parse2::<syn::FnArg>(result_param) else {
            return None;
        };
        sig.inputs.push(arg);
    }
    sig.output = syn::parse_quote! { -> bool };
    sig.generics
        .make_where_clause()
        .predicates
        .push(syn::parse_quote! { Self: ::core::marker::Sized });
    let marker = marker_attr(SPEC_TC_MARKER);
    let tag = clause_tag_attr(kind.marker_kind(), clause);
    let helper = quote_spanned! {sp=>
        #[cfg(trust_wp)]
        #[doc(hidden)]
        #marker
        #tag
        #[allow(unused_variables, unused_braces, unused_parens, non_snake_case,
                clippy::all, unreachable_code, non_shorthand_field_patterns)]
        #sig #encoded
    };
    Some(helper)
}

/// Type-check statement for a `requires`/`ensures` on a closure expression,
/// placed BEFORE the closure inside a wrapping block (the caller emits
/// `{ <statement> <marked closure> }`).
///
/// Nothing is inserted into the user's closure: its body, MIR and captures
/// are unchanged (a type-check closure inside it would add upvars). The
/// type-check closure lives in the enclosing body instead and re-declares
/// the closure's parameters, so this applies only when every parameter has
/// a type annotation, and — when the clause mentions `result` — the closure
/// has an explicit `-> T`. Other closures (and the `|r| ..` ensures form)
/// are not type-checked here.
pub(crate) fn closure_clause_statement(
    kind: FnClause,
    clause: &TokenStream,
    item: &TokenStream,
) -> Option<TokenStream> {
    if kind == FnClause::Variant || (kind == FnClause::Ensures && is_closure_clause(clause)) {
        return None;
    }
    if !driver_parses(true, clause) {
        return None;
    }
    let closure = syn::parse2::<syn::ExprClosure>(item.clone()).ok()?;
    let mut params = Vec::new();
    for input in &closure.inputs {
        let syn::Pat::Type(pt) = input else {
            return None;
        };
        if type_has_impl_trait(&pt.ty) {
            return None;
        }
        params.push(quote! { #pt });
    }
    if kind == FnClause::Ensures && mentions_ident(clause, "result") {
        let ReturnType::Type(_, ty) = &closure.output else {
            return None;
        };
        if type_has_impl_trait(ty) || is_never(ty) {
            return None;
        }
        params.push(quote! { result: #ty });
    }
    let encoded = encode_clause(clause)?;
    let sp = span_of(clause);
    Some(tc_statement(
        sp,
        clause_tag_attr(kind.marker_kind(), clause),
        quote! { #(#params),* },
        quote! { bool },
        encoded,
    ))
}

fn mentions_ident(ts: &TokenStream, name: &str) -> bool {
    ts.clone().into_iter().any(|t| match t {
        TokenTree::Ident(id) => id == name,
        TokenTree::Group(g) => mentions_ident(&g.stream(), name),
        _ => false,
    })
}

/// `#[ensures(|r| ..)]`: Creusot's named-result form. Not type-checked here.
fn is_closure_clause(clause: &TokenStream) -> bool {
    matches!(clause.clone().into_iter().next(), Some(TokenTree::Punct(p)) if p.as_char() == '|')
}

fn prepend_to_body(tokens: &[TokenTree], body: &Group, stmt: TokenStream) -> TokenStream {
    let mut inner = stmt;
    inner.extend(body.stream());
    let mut new_body = Group::new(Delimiter::Brace, inner);
    new_body.set_span(body.span());
    let mut out: TokenStream = tokens[..tokens.len() - 1].iter().cloned().collect();
    out.extend(std::iter::once(TokenTree::Group(new_body)));
    out
}

/// Type-check statement for a logic function body of return type `output`.
pub(crate) fn logic_body_statement(block: &syn::Block, output: &ReturnType) -> Option<TokenStream> {
    let ret = result_type(output)?;
    let body_tokens: TokenStream = block
        .stmts
        .iter()
        .filter(|s| !is_spec_tc_stmt(s))
        .map(quote::ToTokens::to_token_stream)
        .collect();
    let encoded = encode_clause(&body_tokens)?;
    let sp = block.brace_token.span.join();
    Some(tc_statement_marked(
        sp,
        TokenStream::new(),
        quote! {},
        ret,
        encoded,
        SPEC_TC_LOGIC_BODY_MARKER,
    ))
}

/// Type-check statement for a `proof_assert!` body.
///
/// Literals stay `Int`, but `==`/`!=` and indexing also relate `Int` with a
/// machine integer: a `proof_assert!` may mention values built by
/// `snapshot!`/ghost code, whose nested literals trust-wp types as Rust
/// integers where Creusot's pearlite lowering of the snapshot body gives
/// `Int` (e.g. `snapshot!(map.insert(1, 3))` then `map[1] == 3`).
///
/// `kind` is the assertion's `trust-wp:` marker kind (`proof_assert`,
/// `trusted_proof_assert`), for the body's tag.
pub(crate) fn proof_assert_statement(kind: &str, input: &TokenStream) -> Option<TokenStream> {
    let encoded = encode_clause_mode(input, true)?;
    Some(tc_statement(
        span_of(input),
        clause_tag_attr(kind, input),
        quote! {},
        quote! { bool },
        encoded,
    ))
}

/// Whether `stmt` is a type-check statement emitted by this module (so that
/// body-text markers never include it).
pub(crate) fn is_spec_tc_stmt(stmt: &syn::Stmt) -> bool {
    let syn::Stmt::Local(local) = stmt else {
        return false;
    };
    let Some(init) = &local.init else {
        return false;
    };
    let syn::Expr::Closure(clos) = init.expr.as_ref() else {
        return false;
    };
    clos.attrs.iter().any(|a| match &a.meta {
        syn::Meta::NameValue(nv) if nv.path.is_ident("doc") => matches!(
            &nv.value,
            syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. })
                if s.value() == SPEC_TC_MARKER || s.value() == SPEC_TC_LOGIC_BODY_MARKER
        ),
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn enc(s: &str) -> String {
        encode_clause(&s.parse().unwrap())
            .expect("encodes")
            .to_string()
    }

    #[test]
    fn equality_relates_one_type_or_an_int_with_a_machine_integer() {
        let e = enc("result == 5u32");
        assert!(
            e.contains("__spec_tc :: equal_pa ((* & result) , 5u32)"),
            "{e}"
        );
    }

    #[test]
    fn the_flat_fn_contract_predicate_spelling_is_typed_against_the_signature() {
        // trust-wp's driver reads `f.precondition(x)` with a flat argument
        // list; trust-wp-std's signature takes Creusot's tuple. A single
        // argument is ambiguous — `a: A` with `A: Tuple` is Creusot's own
        // spelling (`closures/06_fn_specs.rs`) — so it goes through
        // `fn_args_of`, which unifies with the signature's `Args` either
        // way; the binders of `exists<st, r> f.postcondition_mut(x, st, r)`
        // still get their types from the signature (untyped, they are E0282
        // and rustc's borrowck ICEs on the closure).
        let e = enc("f.precondition(x) && n > 0");
        assert!(
            e.contains("precondition (:: trust_wp_std :: __spec_tc :: fn_args_of (& (* & x)))"),
            "{e}"
        );
        assert!(!e.contains("dead"), "{e}");
        assert!(e.contains("gt_lit"), "{e}");
        let e = enc("exists<st, r> (*f).postcondition_mut(arg, st, r)");
        assert!(
            e.contains("fn_args_of (& (* & arg)) , (* st) , (* r))"),
            "{e}"
        );
        assert!(!e.contains("dead"), "{e}");

        // Two or more flat arguments are unambiguous and re-tupled.
        let e = enc("f.precondition(x, y)");
        assert!(e.contains("precondition (((* & x) , (* & y)))"), "{e}");
        assert!(!e.contains("fn_args_of"), "{e}");

        // A call with no argument before the trailing ones is not a `Fn`
        // predicate but a user's own method of that name
        // (`should_succeed/mutex.rs`: `self.postcondition(result)`) and
        // stays untyped.
        let e = enc("self.postcondition(result)");
        assert!(e.contains("dead"), "{e}");

        // Creusot's tupled spelling keeps its typing untouched.
        let e = enc("f.postcondition_mut((1i32,), f2, result)");
        assert!(e.contains("postcondition_mut ((1i32 ,) ,"), "{e}");
        assert!(!e.contains("dead"), "{e}");
    }

    #[test]
    fn equality_falls_back_to_unification_against_an_untyped_operand() {
        // `[0, 1, 2, 3]` is not type-checked (Creusot rejects array terms in
        // pearlite), so it encodes to a value of unconstrained type. Relating
        // that by trait would leave the variable unresolved (E0283); the
        // same-type `equal` unifies it with the other operand.
        let e = enc("[0, 1, 2, 3] == x");
        assert!(e.contains("__spec_tc :: equal ("), "{e}");
        assert!(!e.contains("equal_pa"), "{e}");
    }

    #[test]
    fn a_literal_operand_takes_the_other_operand_s_type() {
        // `x@` is an `Int`, `x` on an `i32` is an `i32`: one encoding, and
        // the literal contributes no type of its own to either.
        let e = enc("x@ == 5");
        assert!(e.contains("eq_lit"), "{e}");
        assert!(e.contains("5u128"), "{e}");
        assert!(e.contains("__trust_wp_tc_view"), "{e}");
        assert!(!e.contains("int_lit"), "{e}");

        let e = enc("x > 0");
        assert!(e.contains("__spec_tc :: gt_lit ((* & x) , 0u128)"), "{e}");
        let e = enc("result == x + 1");
        assert!(e.contains("__spec_tc :: add_lit ((* & x) , 1u128)"), "{e}");
        // Either operand order, and a negated literal keeps its sign.
        let e = enc("100 > n");
        assert!(e.contains("gt_lit_left (100u128 , (* & n))"), "{e}");
        let e = enc("x >= -1");
        assert!(e.contains("ge_lit ((* & x) , - 1i128)"), "{e}");
    }

    #[test]
    fn literal_binary_vehicles_preserve_operator_and_physical_operand_order() {
        for (op, stem) in [
            ("==", "eq"),
            ("!=", "ne"),
            ("<", "lt"),
            ("<=", "le"),
            (">", "gt"),
            (">=", "ge"),
            ("+", "add"),
            ("-", "sub"),
            ("*", "mul"),
            ("/", "div"),
            ("%", "rem"),
        ] {
            let right = enc(&format!("x {op} 7"));
            assert!(
                right.contains(&format!("__spec_tc :: {stem}_lit ((* & x) , 7u128)")),
                "{right}"
            );
            let left = enc(&format!("7 {op} x"));
            assert!(
                left.contains(&format!("__spec_tc :: {stem}_lit_left (7u128 , (* & x))")),
                "{left}"
            );
        }
        let negative_left = enc("-7 >= x");
        assert!(
            negative_left.contains("ge_lit_left (- 7i128 , (* & x))"),
            "{negative_left}"
        );
        let negative_right = enc("x >= -7");
        assert!(
            negative_right.contains("ge_lit ((* & x) , - 7i128)"),
            "{negative_right}"
        );
    }

    #[test]
    fn literal_vehicle_does_not_change_suffixed_or_both_literal_typing() {
        for op in ["==", "!=", "<", "<=", ">", ">="] {
            let right = enc(&format!("x {op} 7u64"));
            let left = enc(&format!("7u64 {op} x"));
            assert!(right.contains("7u64") && left.contains("7u64"));
            for stem in ["eq", "ne", "lt", "le", "gt", "ge"] {
                assert!(!right.contains(&format!("{stem}_lit")), "{right}");
                assert!(!left.contains(&format!("{stem}_lit")), "{left}");
            }
        }
        let bare = enc("1 >= 0");
        assert!(bare.contains("ge_log"), "{bare}");
        assert!(!bare.contains("ge_lit"), "{bare}");
    }

    #[test]
    fn the_int_constructor_over_a_bare_literal_is_the_int_literal() {
        // trust-wp's `Int(0)` spelling of Creusot's bare `0`: the literal is
        // typed as `Int`, not as an `Int` built from an `Int`.
        let e = enc("result == Int(0)");
        assert!(e.contains("int_lit (0u128)"), "{e}");
        assert!(!e.contains("Int ("), "{e}");
        let e = enc("Int(-1) < x");
        assert!(e.contains("neg_tc"), "{e}");
        assert!(!e.contains("Int ("), "{e}");
        let e = enc("::trust_wp::logic::Int(3) == x");
        assert!(!e.contains("Int ("), "{e}");
        // Any other argument is typed against the constructor's `i128` field.
        let e = enc("Int(n as i128) == x");
        assert!(e.contains("Int ((* & n) as i128)"), "{e}");
    }

    #[test]
    fn a_literal_facing_a_literal_stays_an_int() {
        // Nothing constrains the type, so Creusot's `Int` typing stands
        // rather than an inference failure.
        let e = enc("1 + 1 == 2");
        assert!(e.contains("int_lit (1u128)"), "{e}");
        assert!(e.contains("AddTc :: add_tc"), "{e}");
        // A suffixed literal carries its own type and is left alone.
        let e = enc("x == 5u32");
        assert!(!e.contains("eq_lit"), "{e}");
        assert!(e.contains("5u32"), "{e}");
    }

    #[test]
    fn statements_are_kept_as_statements() {
        let e = enc("{ let _y: bool = 5u32; true }");
        assert!(e.contains("let _y : bool = 5u32 ;"), "{e}");
        let e = enc("{ if true { false } else { false } true }");
        assert!(e.contains("if true { false } else { false } true"), "{e}");
    }

    #[test]
    fn quantifier_and_implication() {
        let e = enc("forall<i: Int> 0 <= i ==> p(i)");
        assert!(
            e.contains("__spec_tc :: forall (| i : & Int | -> bool"),
            "{e}"
        );
        assert!(e.contains("__spec_tc :: implication"), "{e}");
    }

    fn loop_stmt(kind: LoopClause, clause: &str, item: &str) -> Option<String> {
        loop_clause_statement(kind, &clause.parse().unwrap(), &item.parse().unwrap())
            .map(|t| t.to_string())
    }

    #[test]
    fn loop_invariant_on_while_is_type_checked_before_the_loop() {
        let s = loop_stmt(LoopClause::Invariant, "i@ <= 10", "while i > 0 { i -= 1; }")
            .expect("while loop");
        assert!(s.contains("__trust_wp_spec_tc"), "{s}");
        assert!(
            !s.contains("while"),
            "the loop itself is not part of the statement: {s}"
        );
    }

    #[test]
    fn loop_invariant_on_for_binds_iter_and_produced_not_the_pattern() {
        let s = loop_stmt(
            LoopClause::Invariant,
            "produced.len() <= 3",
            "#[invariant(true)] 'outer: for x in 0..n { let _ = x; }",
        )
        .expect("labelled for loop");
        assert!(
            s.contains("for_loop_tc ((0 .. n) , | iter , produced |"),
            "{s}"
        );
        assert!(!s.contains("| x"), "{s}");
    }

    #[test]
    fn loop_variant_goes_through_variant_check() {
        let s = loop_stmt(LoopClause::Variant, "i@", "loop { break; }").expect("loop");
        assert!(s.contains("variant_check"), "{s}");
    }

    #[test]
    fn non_loop_items_get_no_loop_statement() {
        assert!(loop_stmt(LoopClause::Invariant, "true", "let x = 5;").is_none());
        assert!(loop_stmt(LoopClause::Invariant, "true", "fn f() {}").is_none());
    }

    fn trait_helper(kind: FnClause, clause: &str, item: &str) -> Option<String> {
        trait_signature_helper(kind, &clause.parse().unwrap(), &item.parse().unwrap())
            .map(|t| t.to_string())
    }

    #[test]
    fn bodyless_trait_method_gets_a_sized_marked_sibling_helper() {
        let s = trait_helper(
            FnClause::Ensures,
            "result == true",
            "#[requires(x@ < 3)] fn is_true(&self, x: u32) -> bool;",
        )
        .expect("trait signature");
        assert!(s.contains("fn __trust_wp_spec_tc_is_true_"), "{s}");
        assert!(s.contains("result : bool"), "{s}");
        assert!(s.contains("Self : :: core :: marker :: Sized"), "{s}");
        assert!(s.contains("__trust_wp_spec_tc\""), "{s}");
        assert!(
            !s.contains("requires"),
            "other contract attributes are not copied: {s}"
        );
    }

    #[test]
    fn methods_with_bodies_get_no_sibling_helper() {
        assert!(trait_helper(FnClause::Requires, "true", "fn f(&self) {}").is_none());
        assert!(trait_helper(FnClause::Variant, "x", "fn f(x: u32);").is_none());
    }

    #[test]
    fn fn_level_variant_is_checked_where_the_loop_bindings_exist() {
        let item: TokenStream =
            "pub fn sum(n: i32) -> i32 { let mut i = 0; while i < n { i += 1; } i }"
                .parse()
                .unwrap();
        let out = insert_fn_clause(FnClause::Variant, &"n - i".parse().unwrap(), item).to_string();
        let tc = out
            .find("__trust_wp_spec_tc")
            .expect("type-check statement");
        let loop_kw = out.find("while").expect("loop");
        let binding = out.find("let mut i").expect("loop counter");
        assert!(binding < tc && tc < loop_kw, "{out}");
    }

    #[test]
    fn a_variant_with_no_loop_to_find_stays_at_the_top_of_the_body() {
        let item: TokenStream = "pub fn fact(n: i32) -> i32 { let m = n; f(m) }"
            .parse()
            .unwrap();
        let out = insert_fn_clause(FnClause::Variant, &"n".parse().unwrap(), item).to_string();
        let tc = out
            .find("__trust_wp_spec_tc")
            .expect("type-check statement");
        assert!(tc < out.find("let m").expect("body"), "{out}");
    }

    #[test]
    fn a_loop_that_is_not_a_statement_does_not_move_the_variant() {
        // `loop` here opens an initialiser, not a statement: a `let` cannot
        // be spliced in front of it.
        let item: TokenStream = "pub fn f(n: i32) -> i32 { let x = loop { break 1; }; x }"
            .parse()
            .unwrap();
        let out = insert_fn_clause(FnClause::Variant, &"n".parse().unwrap(), item).to_string();
        let tc = out
            .find("__trust_wp_spec_tc")
            .expect("type-check statement");
        assert!(tc < out.find("let x").expect("body"), "{out}");
    }

    #[test]
    fn diverging_fn_ensures_has_no_never_typed_result() {
        let item: TokenStream = "pub fn die() -> ! { panic!() }".parse().unwrap();
        let out =
            insert_fn_clause(FnClause::Ensures, &"true".parse().unwrap(), item.clone()).to_string();
        assert!(out.contains("__trust_wp_spec_tc"), "{out}");
        assert!(!out.contains("result : !"), "{out}");
        let out = insert_fn_clause(
            FnClause::Ensures,
            &"result == result".parse().unwrap(),
            item,
        )
        .to_string();
        assert!(!out.contains("__trust_wp_spec_tc"), "{out}");
    }

    #[test]
    fn a_clause_the_driver_cannot_parse_is_left_to_the_driver() {
        // `'a'` parses (as `Int(97)`) but is not a boolean predicate;
        // `result == "a"` does not parse at all. The driver reports both as
        // parse errors (exit 3), so neither gets a type-check closure that
        // would pre-empt that report with an E0308.
        let item: TokenStream = "fn f(x: i32) -> i32 { x }".parse().unwrap();
        for clause in ["'a'", "result == \"a\""] {
            let out = insert_fn_clause(FnClause::Ensures, &clause.parse().unwrap(), item.clone())
                .to_string();
            assert!(!out.contains("__trust_wp_spec_tc"), "{clause}: {out}");
        }
        assert!(loop_stmt(LoopClause::Invariant, "'a'", "while i > 0 { i -= 1; }").is_none());
        assert!(trait_helper(FnClause::Requires, "'a'", "fn f(&self);").is_none());
        assert!(closure_clause_statement(
            FnClause::Requires,
            &"'a'".parse().unwrap(),
            &"|x: i32| -> i32 { x }".parse().unwrap()
        )
        .is_none());

        // A variant is any term: the driver parses `'a'` (as `Int(97)`), so
        // it IS type-checked and the type error (`char: WellFounded`) is the
        // rejection, as in Creusot.
        let out =
            insert_fn_clause(FnClause::Variant, &"'a'".parse().unwrap(), item.clone()).to_string();
        assert!(out.contains("__trust_wp_spec_tc"), "{out}");
        // A well-formed clause is still type-checked.
        let out =
            insert_fn_clause(FnClause::Ensures, &"result == x".parse().unwrap(), item).to_string();
        assert!(out.contains("__trust_wp_spec_tc"), "{out}");
    }

    #[test]
    fn preprocessed_final_value_is_the_prophecy_operator() {
        let e = enc("produced.len() == 0 || final_value(snap_k) == 1usize");
        assert!(!e.contains("final_value"), "{e}");
        assert!(e.contains("Fin"), "{e}");
    }

    #[test]
    fn tc_statement_detected() {
        let stmt = tc_statement(
            Span::call_site(),
            clause_tag_attr("requires", &quote! { true }),
            quote! {},
            quote! { bool },
            quote! { { true } },
        );
        let block: syn::Block = syn::parse2(quote! { { #stmt } }).unwrap();
        assert!(is_spec_tc_stmt(&block.stmts[0]));
    }

    /// Each clause's type-check body names that clause: its marker kind and
    /// the text `attrs::emit_tool_attr` writes the marker with, so the driver
    /// reads the clause's calls in its own body.
    #[test]
    fn a_clause_body_is_tagged_with_its_marker_kind_and_text() {
        let item: TokenStream = "fn f(x: u32) -> u32 { x }".parse().unwrap();
        let clause: TokenStream = "x . holds ()".parse().unwrap();
        let tag = |kind: &str| format!("{SPEC_TC_CLAUSE_TAG}{kind}:{clause}");
        for (kind, name) in [
            (FnClause::Requires, "requires"),
            (FnClause::Ensures, "ensures"),
            (FnClause::Variant, "variant"),
        ] {
            let out = insert_fn_clause(kind, &clause, item.clone()).to_string();
            assert!(out.contains(&tag(name)), "{out}");
        }
        let helper = trait_signature_helper(
            FnClause::Ensures,
            &clause,
            &"fn f(x: u32) -> u32;".parse().unwrap(),
        )
        .expect("a bodyless trait method gets a helper")
        .to_string();
        assert!(helper.contains(&tag("ensures")), "{helper}");
        let invariant = loop_clause_statement(
            LoopClause::Invariant,
            &clause,
            &"loop { break }".parse().unwrap(),
        )
        .expect("a loop gets a statement")
        .to_string();
        assert!(invariant.contains(&tag("invariant")), "{invariant}");
        let assertion = proof_assert_statement("proof_assert", &clause)
            .expect("an assertion gets a statement")
            .to_string();
        assert!(assertion.contains(&tag("proof_assert")), "{assertion}");
    }
}
