// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! syn-level encoding of a lowered clause onto `trust_wp_std::__spec_tc`.
//!
//! Mirrors Creusot's `encode_term_` (`creusot-std-proc/src/creusot/pretyping.rs`):
//! `==`/`!=` become `equal`/`neq` (same type on both sides, no `PartialEq`),
//! `<`.. become `OrdLogic`, `+ - * / %` and unary `-` become the logical
//! operator traits, unsuffixed and `int`-suffixed integer literals are `Int`,
//! `x@` is `View`, `^x` is `Fin`, `a[i]` is `IndexLogic`, `old(x)` is
//! `*old(x)`, `dead` is `*dead()`, pearlite closures are `Mapping`s,
//! `seq![..]` is a `Seq`, and quantifier/implication markers from `lower`
//! become `forall`/`exists`/`implication`. Everything else is re-emitted as
//! plain Rust, so rustc applies Rust typing to it.

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::{spanned::Spanned, BinOp, Expr, Lit, Stmt, UnOp};

use super::{
    lower::{EXISTS, FORALL, IMPLIES},
    postfix::{FIN, VIEW},
};

const TC: &str = "::trust_wp_std::__spec_tc";

fn tc_path(sp: Span, name: &str) -> TokenStream {
    let path: TokenStream = format!("{TC}::{name}").parse().expect("static path");
    respan(path, sp)
}

fn respan(ts: TokenStream, sp: Span) -> TokenStream {
    ts.into_iter()
        .map(|mut tt| {
            tt.set_span(sp);
            tt
        })
        .collect()
}

fn single_ident(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(p) if p.qself.is_none() => p.path.get_ident().map(ToString::to_string),
        _ => None,
    }
}

/// Creusot `Locals`: variables bound by reference (quantifier binders and
/// pearlite closure parameters, whose Rust binder type is `&T` so unsized
/// `T` is allowed). Their occurrences are emitted as `(*x)`; every other
/// plain variable is emitted as `(*&x)` so a closure never captures an
/// unsized value by value.
#[derive(Default, Clone)]
pub(crate) struct Locals {
    refvars: Vec<String>,
    /// `proof_assert!` mode: `==`/`!=` and `a[i]` also relate `Int` with
    /// machine integers (see `__spec_tc::equal_pa` / `IndexPaTc`).
    pub(crate) proof_assert_mode: bool,
}

fn encode_expr_in(expr: &Expr, locals: &mut Locals) -> TokenStream {
    let sp = expr.span();
    match expr {
        Expr::Binary(b) => encode_binary(b, sp, locals),
        Expr::Unary(u) => {
            let inner = encode_expr_in(&u.expr, locals);
            if let UnOp::Neg(_) = u.op {
                let f = tc_path(sp, "NegTc::neg_tc");
                quote_spanned! {sp=> #f(#inner) }
            } else {
                let op = &u.op;
                quote! { #op #inner }
            }
        }
        Expr::Lit(l) => match &l.lit {
            Lit::Int(i) if i.suffix().is_empty() || i.suffix() == "int" => {
                let digits = syn::LitInt::new(&format!("{}u128", i.base10_digits()), i.span());
                let f = tc_path(sp, "int_lit");
                quote_spanned! {sp=> #f(#digits) }
            }
            _ => l.to_token_stream(),
        },
        Expr::Call(c) => encode_call(c, sp, locals),
        // A `Fn` contract predicate in trust-wp's FLAT spelling. Creusot
        // passes the call's arguments as a TUPLE — `f.precondition((x,))`,
        // which is what trust-wp-std's `precondition(self, args: Args)`
        // types — while trust-wp's driver reads these from the clause TEXT
        // with the arguments flat: `f.precondition(x)`,
        // `f.postcondition(x, result)`, `f.postcondition_mut(x, st, r)`,
        // `f.postcondition_once(x, r)` (`closure_enrichment`,
        // `proof_assert_wiring`: the LAST arguments are the result state
        // and/or the result, everything before them is the call's argument
        // list). The flat spelling is typed against Creusot's signature, so
        // `exists<st, r> f.postcondition_mut(x, st, r)` gives the
        // unannotated binders their types exactly as the tupled spelling
        // does (an untyped binder is otherwise E0282, and rustc's borrowck
        // ICEs on such a closure). Two or more call arguments are re-tupled;
        // a SINGLE one is ambiguous — `f.precondition(a)` is Creusot's own
        // spelling when `a: A` with `A: Tuple`
        // (`should_succeed/closures/06_fn_specs.rs`) — so it is type-checked
        // on its own and passed through `__spec_tc::fn_args_of`, which
        // unifies with the `Fn` bound's `Args` either way.
        //
        // A call with NO argument before the trailing ones is not touched:
        // it is not the flat spelling of a `Fn` predicate (which always has
        // the call's arguments) but a user's own method of that name —
        // `should_succeed/mutex.rs` writes `self.postcondition(result)` on
        // its own trait — and stays untyped as before.
        Expr::MethodCall(m) if is_flat_fn_spec_call(m) => encode_flat_fn_spec(m, sp, locals),
        Expr::MethodCall(m)
            if m.method == "ext_eq" && m.args.len() == 1 && m.turbofish.is_none() =>
        {
            let recv = encode_expr_in(&m.receiver, locals);
            let arg = encode_expr_in(&m.args[0], locals);
            // A method call, not a free call: the receiver may be a `Snapshot`
            // wrapper, which is transparent in pearlite and reachable only
            // through method-call autoderef.
            quote_spanned! {sp=> (#recv).__trust_wp_tc_ext_eq(#arg) }
        }
        Expr::MethodCall(m) => {
            let recv = encode_expr_in(&m.receiver, locals);
            let method = &m.method;
            let turbofish = &m.turbofish;
            let args: Vec<TokenStream> = m.args.iter().map(|a| encode_expr_in(a, locals)).collect();
            quote! { #recv . #method #turbofish (#(#args),*) }
        }
        Expr::Index(ix) => encode_index(ix, sp, locals),
        Expr::Paren(p) => {
            let inner = encode_expr_in(&p.expr, locals);
            quote_spanned! {sp=> (#inner) }
        }
        Expr::Group(g) => {
            let inner = encode_expr_in(&g.expr, locals);
            quote_spanned! {sp=> (#inner) }
        }
        Expr::Field(f) => {
            let base = encode_expr_in(&f.base, locals);
            let member = &f.member;
            quote! { #base . #member }
        }
        Expr::Cast(c) => {
            let inner = encode_expr_in(&c.expr, locals);
            let ty = &c.ty;
            quote! { #inner as #ty }
        }
        Expr::Reference(r) => {
            let inner = encode_expr_in(&r.expr, locals);
            let m = &r.mutability;
            quote! { & #m #inner }
        }
        Expr::Tuple(t) => encode_tuple(t, sp, locals),
        // Creusot: `Unsupported expression: Array`. trust-wp's frontend has its
        // own refusal, so the vehicle stays silent here.
        Expr::Array(_) => unconstrained(sp),
        Expr::If(i) => encode_if(i, sp, locals),
        Expr::Let(l) => {
            let pat = &l.pat;
            let init = encode_expr_in(&l.expr, locals);
            quote! { let #pat = #init }
        }
        // Creusot: `Pattern matching literals on Int are unsupported by
        // Pearlite` (pretyping `PatEncoder`, #1827). trust-wp's frontend emits
        // that refusal itself, so the vehicle stays silent on such a match.
        Expr::Match(m) if m.arms.iter().any(|arm| pat_has_int_literal(&arm.pat)) => {
            unconstrained(sp)
        }
        Expr::Match(m) => encode_match(m, sp, locals),
        Expr::Block(b) => {
            let label = &b.label;
            let block = encode_block_in(&b.block, locals);
            quote! { #label #block }
        }
        Expr::Closure(clos) => encode_closure(clos, sp, locals),
        Expr::Struct(s) => encode_struct(s, locals),
        Expr::Range(r) => {
            let start = r.start.as_ref().map(|e| encode_expr_in(e, locals));
            let end = r.end.as_ref().map(|e| encode_expr_in(e, locals));
            let limits = &r.limits;
            quote_spanned! {sp=> (#start #limits #end) }
        }
        Expr::Path(_) if single_ident(expr).as_deref() == Some("dead") => {
            let f = tc_path(sp, "dead");
            quote_spanned! {sp=> (*#f()) }
        }
        Expr::Path(_) if single_ident(expr).is_some_and(|n| locals.refvars.contains(&n)) => {
            quote_spanned! {sp=> (*#expr) }
        }
        Expr::Path(_) if single_ident(expr).is_some_and(|n| is_variable_like(&n)) => {
            quote_spanned! {sp=> (*&#expr) }
        }
        Expr::Macro(m) => encode_macro(m, locals).unwrap_or_else(|| macro_fallback(m)),
        _ => expr.to_token_stream(),
    }
}

/// The digits of a bare (unsuffixed or `int`-suffixed) pearlite integer
/// literal, as the carrier the `*_lit` functions take: `123u128`, or
/// `-123i128` when the literal is negated. `None` for anything else —
/// a suffixed literal (`5u32`) already carries its own type and is emitted
/// unchanged.
fn int_literal_carrier(expr: &Expr) -> Option<TokenStream> {
    fn peel(e: &Expr) -> &Expr {
        match e {
            Expr::Paren(p) => peel(&p.expr),
            Expr::Group(g) => peel(&g.expr),
            _ => e,
        }
    }
    let (neg, inner) = match peel(expr) {
        Expr::Unary(u) if matches!(u.op, UnOp::Neg(_)) => (true, peel(&u.expr)),
        other => (false, other),
    };
    let Expr::Lit(l) = inner else { return None };
    let Lit::Int(i) = &l.lit else { return None };
    if !(i.suffix().is_empty() || i.suffix() == "int") {
        return None;
    }
    let digits = i.base10_digits();
    let sp = i.span();
    let carrier = if neg {
        let lit = syn::LitInt::new(&format!("{digits}i128"), sp);
        quote_spanned! {sp=> -#lit }
    } else {
        let lit = syn::LitInt::new(&format!("{digits}u128"), sp);
        quote_spanned! {sp=> #lit }
    };
    Some(carrier)
}

/// `a <op> <literal>` / `<literal> <op> a`, for an operator whose logical
/// meaning is fixed by the non-literal operand's type. `None` when neither
/// side is a bare literal, when BOTH are (nothing constrains the type, so
/// Creusot's `Int` typing stands), or for an operator with no `*_lit` form.
fn encode_literal_binop(b: &syn::ExprBinary, locals: &mut Locals) -> Option<TokenStream> {
    let (right_name, left_name) = match b.op {
        BinOp::Eq(_) => ("eq_lit", "eq_lit_left"),
        BinOp::Ne(_) => ("ne_lit", "ne_lit_left"),
        BinOp::Lt(_) => ("lt_lit", "lt_lit_left"),
        BinOp::Le(_) => ("le_lit", "le_lit_left"),
        BinOp::Gt(_) => ("gt_lit", "gt_lit_left"),
        BinOp::Ge(_) => ("ge_lit", "ge_lit_left"),
        BinOp::Add(_) => ("add_lit", "add_lit_left"),
        BinOp::Sub(_) => ("sub_lit", "sub_lit_left"),
        BinOp::Mul(_) => ("mul_lit", "mul_lit_left"),
        BinOp::Div(_) => ("div_lit", "div_lit_left"),
        BinOp::Rem(_) => ("rem_lit", "rem_lit_left"),
        _ => return None,
    };
    let sp = b.span();
    // Retain both the operator's identity and the physical operand order.
    // Normalizing literal-left subtraction/division into value-first calls
    // would erase information a THIR frontend needs for its actual semantics.
    let (name, left, right) = match (int_literal_carrier(&b.left), int_literal_carrier(&b.right)) {
        (None, Some(carrier)) => (
            right_name,
            encode_expr_in(strip_paren(&b.left), locals),
            carrier,
        ),
        (Some(carrier), None) => (
            left_name,
            carrier,
            encode_expr_in(strip_paren(&b.right), locals),
        ),
        _ => return None,
    };
    let f = tc_path(sp, name);
    Some(quote_spanned! {sp=> #f(#left, #right) })
}

/// A call of a `Fn`/`FnMut`/`FnOnce` contract predicate (`trust-wp-std`
/// `std::ops`) whose arguments are NOT Creusot's tuple: the spelling
/// trust-wp's driver reads and trust-wp-std's signature refuses.
fn is_flat_fn_spec_call(m: &syn::ExprMethodCall) -> bool {
    let named = matches!(
        m.method.to_string().as_str(),
        "precondition" | "postcondition" | "postcondition_mut" | "postcondition_once"
    );
    named && !matches!(m.args.first().map(strip_paren), Some(Expr::Tuple(_)) | None)
}

/// Number of arguments AFTER the call's argument list in a `Fn` contract
/// predicate: `postcondition(args, result)`, `postcondition_once(args,
/// result)`, `postcondition_mut(args, result_state, result)`.
fn flat_fn_spec_trailing_args(method: &str) -> usize {
    match method {
        "postcondition" | "postcondition_once" => 1,
        "postcondition_mut" => 2,
        _ => 0,
    }
}

/// A flat `Fn` predicate call the vehicle does NOT re-tuple (see
/// `encode_expr_in`): no argument precedes the trailing ones.
fn is_untyped_flat_fn_spec_call(m: &syn::ExprMethodCall) -> bool {
    is_flat_fn_spec_call(m) && m.args.len() <= flat_fn_spec_trailing_args(&m.method.to_string())
}

/// A call of one of trust-wp's reserved internal names (`__trust_wp_*`):
/// the driver's own spelling of a projection, not a Rust item. The
/// vehicle's own lowering markers (`lower`, `postfix`) share the prefix and
/// are encoded by their own arms, so they are not "internal" here.
fn is_internal_spelling(name: &str) -> bool {
    name.starts_with("__trust_wp_") && !matches!(name, FORALL | EXISTS | IMPLIES | VIEW | FIN)
}

/// The callee of an `Int(..)` constructor call: a path whose last segment is
/// the bare identifier `Int` (`Int`, `trust_wp::Int`, `::trust_wp::logic::Int`).
fn is_int_ctor(func: &Expr) -> bool {
    let Expr::Path(p) = func else { return false };
    p.qself.is_none()
        && p.path.segments.last().is_some_and(|seg| {
            seg.ident == "Int" && matches!(seg.arguments, syn::PathArguments::None)
        })
}

/// Whether encoding `expr` yields an UNCONSTRAINED value (`__spec_tc`'s
/// `dead`) rather than a term of the clause's own type — the places the
/// vehicle deliberately declines to type.
///
/// Such a value carries a fresh inference variable, so an operator that
/// relates it to the other operand by a TRAIT (`EqPaTc`) leaves that
/// variable unresolved (`error[E0283]: type annotations needed`) where the
/// same-type `equal` would have unified it. Equality therefore falls back to
/// `equal`/`neq` whenever either side is one of these.
fn encodes_unconstrained(expr: &Expr) -> bool {
    match strip_paren(expr) {
        Expr::Array(_) => true,
        Expr::Match(m) => m.arms.iter().any(|arm| pat_has_int_literal(&arm.pat)),
        Expr::MethodCall(m) => is_untyped_flat_fn_spec_call(m),
        Expr::Call(c) => single_ident(&c.func).is_some_and(|n| is_internal_spelling(&n)),
        Expr::Path(_) => single_ident(expr).as_deref() == Some("dead"),
        Expr::Macro(m) => {
            m.mac
                .path
                .segments
                .last()
                .is_some_and(|seg| seg.ident == "pearlite")
                && super::lower_and_parse_block(m.mac.tokens.clone()).is_none()
        }
        _ => false,
    }
}

fn strip_paren(e: &Expr) -> &Expr {
    match e {
        Expr::Paren(p) => &p.expr,
        _ => e,
    }
}

fn encode_macro(m: &syn::ExprMacro, locals: &mut Locals) -> Option<TokenStream> {
    let name = m.mac.path.segments.last()?.ident.to_string();
    match name.as_str() {
        // Nested pearlite (logic bodies): lower and encode inline.
        "pearlite" => {
            let block = super::lower_and_parse_block(m.mac.tokens.clone())?;
            Some(encode_block_in(&block, locals))
        }
        "seq" => {
            let parser = syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated;
            let elems =
                syn::parse::Parser::parse2(parser, super::lower_tokens(m.mac.tokens.clone()))
                    .ok()?;
            let elems: Vec<TokenStream> = elems.iter().map(|e| encode_expr_in(e, locals)).collect();
            let sp = m.span();
            let f = tc_path(sp, "seq_literal");
            Some(quote_spanned! {sp=> #f(&[#(#elems),*]) })
        }
        _ => None,
    }
}

pub(crate) fn encode_block(block: &syn::Block, proof_assert_mode: bool) -> TokenStream {
    encode_block_in(
        block,
        &mut Locals {
            proof_assert_mode,
            ..Locals::default()
        },
    )
}

fn encode_block_in(block: &syn::Block, locals: &mut Locals) -> TokenStream {
    let mut inner = locals.clone();
    let stmts: Vec<TokenStream> = block
        .stmts
        .iter()
        .map(|s| encode_stmt(s, &mut inner))
        .collect();
    let sp = block.brace_token.span.join();
    quote_spanned! {sp=> { #(#stmts)* } }
}

fn encode_stmt(stmt: &Stmt, locals: &mut Locals) -> TokenStream {
    match stmt {
        Stmt::Local(local) => {
            let attrs = &local.attrs;
            let pat = &local.pat;
            if let Some(init) = &local.init {
                let e = encode_expr_in(&init.expr, locals);
                let diverge = init.diverge.as_ref().map(|(_, d)| {
                    let d = encode_expr_in(d, locals);
                    quote! { else #d }
                });
                quote! { #(#attrs)* let #pat = #e #diverge; }
            } else {
                quote! { #(#attrs)* let #pat; }
            }
        }
        Stmt::Expr(e, semi) => {
            let e = encode_expr_in(e, locals);
            quote! { #e #semi }
        }
        Stmt::Macro(m) => {
            let name = m.mac.path.segments.last().map(|s| s.ident.to_string());
            let as_expr = syn::ExprMacro {
                attrs: m.attrs.clone(),
                mac: m.mac.clone(),
            };
            let semi = &m.semi_token;
            match encode_macro(&as_expr, locals) {
                Some(ts) => quote! { #ts #semi },
                None if name.as_deref() == Some("pearlite") => {
                    let fallback = macro_fallback(&as_expr);
                    quote! { #fallback #semi }
                }
                None => m.to_token_stream(),
            }
        }
        Stmt::Item(i) => i.to_token_stream(),
    }
}

/// Parameter list of a quantifier / pearlite closure with Creusot's
/// reference binding: `x: T` becomes `x: &T`, `x` becomes `x: &_`; the bound
/// names are returned so their occurrences are emitted as `(*x)`. Other
/// patterns become `&pat: &T` and bind nothing by reference.
fn ref_bound_inputs(
    inputs: &syn::punctuated::Punctuated<syn::Pat, syn::Token![,]>,
) -> (TokenStream, Vec<String>) {
    let mut bound = Vec::new();
    let params = inputs.iter().map(|pat| match pat {
        syn::Pat::Type(pt) => match pt.pat.as_ref() {
            syn::Pat::Ident(pi)
                if pi.by_ref.is_none() && pi.mutability.is_none() && pi.subpat.is_none() =>
            {
                bound.push(pi.ident.to_string());
                let ident = &pi.ident;
                let ty = &pt.ty;
                quote! { #ident: &#ty }
            }
            other => {
                let ty = &pt.ty;
                quote! { &#other: &#ty }
            }
        },
        syn::Pat::Ident(pi)
            if pi.by_ref.is_none() && pi.mutability.is_none() && pi.subpat.is_none() =>
        {
            bound.push(pi.ident.to_string());
            let ident = &pi.ident;
            quote! { #ident: &_ }
        }
        other => quote! { &#other },
    });
    let params: Vec<TokenStream> = params.collect();
    (quote! { #(#params),* }, bound)
}

/// A single-segment path that denotes a variable (not a constant, unit
/// struct or enum variant): starts lowercase or `_`, or is `self`.
fn is_variable_like(name: &str) -> bool {
    name == "self" || name.starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
}

/// An unencodable nested `pearlite!` must not be expanded by the program-side
/// `pearlite!` macro (whose parser rejects pearlite syntax); it is typed as
/// an unconstrained value instead (the vehicle only ever adds rejections).
fn macro_fallback(m: &syn::ExprMacro) -> TokenStream {
    let is_pearlite = m
        .mac
        .path
        .segments
        .last()
        .is_some_and(|s| s.ident == "pearlite");
    if is_pearlite {
        let sp = m.span();
        let f = tc_path(sp, "dead");
        quote_spanned! {sp=> (*#f()) }
    } else {
        m.to_token_stream()
    }
}

/// A value of any type, used where the vehicle deliberately does not
/// type-check a sub-term (it never adds an acceptance: the clause text is
/// still verified, and trust-wp's frontend refusal for the construct runs).
fn unconstrained(sp: Span) -> TokenStream {
    let f = tc_path(sp, "dead");
    quote_spanned! {sp=> (*#f()) }
}

fn pat_has_int_literal(pat: &syn::Pat) -> bool {
    struct Finder(bool);
    impl<'ast> syn::visit::Visit<'ast> for Finder {
        fn visit_pat(&mut self, pat: &'ast syn::Pat) {
            if let syn::Pat::Lit(syn::ExprLit {
                lit: Lit::Int(_), ..
            }) = pat
            {
                self.0 = true;
            }
            syn::visit::visit_pat(self, pat);
        }
        fn visit_expr_lit(&mut self, lit: &'ast syn::ExprLit) {
            if matches!(lit.lit, Lit::Int(_)) {
                self.0 = true;
            }
        }
    }
    let mut finder = Finder(false);
    syn::visit::Visit::visit_pat(&mut finder, pat);
    finder.0
}

fn encode_binary(b: &syn::ExprBinary, sp: Span, locals: &mut Locals) -> TokenStream {
    let unconstrained_side = encodes_unconstrained(&b.left) || encodes_unconstrained(&b.right);
    // A bare integer literal facing a non-literal operand takes that
    // operand's type (see `__spec_tc`'s `*_lit` functions) — unless
    // that operand is one the vehicle declines to type: the `*_lit`
    // functions relate the literal to the operand by TRAIT, which
    // leaves an unconstrained operand unresolved (E0283) where the
    // same-type operators below unify it.
    if !unconstrained_side {
        if let Some(ts) = encode_literal_binop(b, locals) {
            return ts;
        }
    }
    let l = encode_expr_in(strip_paren(&b.left), locals);
    let r = encode_expr_in(strip_paren(&b.right), locals);
    let op = &b.op;
    let call = |name: &str| {
        let f = tc_path(sp, name);
        quote_spanned! {sp=> #f(#l, #r) }
    };
    let ord = |m: &str| {
        let m = syn::Ident::new(m, sp);
        quote_spanned! {sp=> ::trust_wp_std::logic::OrdLogic::#m(#l, #r) }
    };
    let arith = |tr: &str, m: &str| {
        let f = tc_path(sp, &format!("{tr}::{m}"));
        quote_spanned! {sp=> #f(#l, #r) }
    };
    match op {
        // `equal_pa`/`neq_pa`, not `equal`/`neq`: same type on both
        // sides, OR an `Int` against a machine integer. trust-wp's
        // surface compares the two directly —
        // `#[ensures(result == old(v@.len()) + 1)]` on a `usize`
        // result is one of the repo's own documented examples — and
        // its verifier discharges that obligation over the clause
        // text, where a machine integer is its `Int` model. The
        // relation is still a PAIR of integer types: `x == 5u64`
        // with `x: u32` has no impl and stays refused.
        BinOp::Eq(_) => call(if unconstrained_side {
            "equal"
        } else {
            "equal_pa"
        }),
        BinOp::Ne(_) => call(if unconstrained_side { "neq" } else { "neq_pa" }),
        // The operator traits select their impl by BOTH operand
        // types; with one side unconstrained the selection is
        // ambiguous (E0283), so the operands are checked and the
        // result stays unconstrained.
        BinOp::Add(_) | BinOp::Sub(_) | BinOp::Mul(_) | BinOp::Div(_) | BinOp::Rem(_)
            if unconstrained_side =>
        {
            let d = tc_path(sp, "dead");
            quote_spanned! {sp=> { let _ = (#l, #r); (*#d()) } }
        }
        BinOp::Lt(_) => ord("lt_log"),
        BinOp::Le(_) => ord("le_log"),
        BinOp::Gt(_) => ord("gt_log"),
        BinOp::Ge(_) => ord("ge_log"),
        BinOp::Add(_) => arith("AddTc", "add_tc"),
        BinOp::Sub(_) => arith("SubTc", "sub_tc"),
        BinOp::Mul(_) => arith("MulTc", "mul_tc"),
        BinOp::Div(_) => arith("DivTc", "div_tc"),
        BinOp::Rem(_) => arith("RemTc", "rem_tc"),
        _ => {
            let l = encode_expr_in(&b.left, locals);
            let r = encode_expr_in(&b.right, locals);
            quote! { #l #op #r }
        }
    }
}

fn encode_call(c: &syn::ExprCall, sp: Span, locals: &mut Locals) -> TokenStream {
    let args: Vec<TokenStream> = c.args.iter().map(|a| encode_expr_in(a, locals)).collect();
    match single_ident(&c.func).as_deref() {
        Some(name) if (name == FORALL || name == EXISTS) && c.args.len() == 1 => {
            let f = tc_path(sp, if name == FORALL { "forall" } else { "exists" });
            let Expr::Closure(clos) = &c.args[0] else {
                return quote! { #f(#(#args),*) };
            };
            let (inputs, bound) = ref_bound_inputs(&clos.inputs);
            let mut inner = locals.clone();
            inner.refvars.extend(bound);
            let body = encode_expr_in(&clos.body, &mut inner);
            quote_spanned! {sp=> #f(|#inputs| -> bool { #body }) }
        }
        Some(IMPLIES) if c.args.len() == 2 => {
            let f = tc_path(sp, "implication");
            quote_spanned! {sp=> #f(#(#args),*) }
        }
        Some("inv") if c.args.len() == 1 => {
            let f = tc_path(sp, "inv");
            quote_spanned! {sp=> #f(#(#args),*) }
        }
        Some("old") if c.args.len() == 1 => {
            let f = tc_path(sp, "old");
            quote_spanned! {sp=> (*#f(#(#args),*)) }
        }
        Some(VIEW) if c.args.len() == 1 => {
            let a = &args[0];
            quote_spanned! {sp=> ((#a).__trust_wp_tc_view()) }
        }
        Some(FIN) if c.args.len() == 1 => {
            let a = &args[0];
            quote_spanned! {sp=> (*::trust_wp_std::logic::ops::Fin::fin(#a)) }
        }
        // trust-wp's `Int` LITERAL spelling. trust-wp-std's `Int` is
        // `pub struct Int(pub i128)` and the repo's specifications
        // write the constructor around a bare literal (`Int(0)`,
        // `Int(-1)`); Creusot has no such spelling — its `Int`
        // literal is the bare `0` — so the constructor over a bare
        // literal IS the literal and is typed as one (`Int`), not as
        // `Int(Int)`. Any other argument is typed against the `i128`
        // field.
        _ if is_int_ctor(&c.func)
            && c.args.len() == 1
            && int_literal_carrier(&c.args[0]).is_some() =>
        {
            args[0].clone()
        }
        // A call spelled in trust-wp's reserved `__trust_wp_*`
        // namespace (`__trust_wp_tuple_get_0(p)` is the driver's own
        // MIR-extracted form of a field access, not a Rust item). The
        // driver refuses every such identifier in specification text
        // (`creusot_frontend_checks::validate_reserved_binding_names`,
        // exit 2, no credit); the vehicle checks the arguments and
        // leaves the value unconstrained so THAT refusal, which names
        // the reason, is the one reported rather than an E0425.
        Some(name) if is_internal_spelling(name) => {
            let d = tc_path(sp, "dead");
            quote_spanned! {sp=> { let _ = (#(#args),*,); (*#d()) } }
        }
        _ => {
            let func = match c.func.as_ref() {
                Expr::Path(_) => c.func.to_token_stream(),
                other => encode_expr_in(other, locals),
            };
            quote! { #func(#(#args),*) }
        }
    }
}

fn encode_flat_fn_spec(m: &syn::ExprMethodCall, sp: Span, locals: &mut Locals) -> TokenStream {
    let trailing = flat_fn_spec_trailing_args(&m.method.to_string());
    if m.args.len() <= trailing {
        return unconstrained(sp);
    }
    let split = m.args.len() - trailing;
    let recv = encode_expr_in(&m.receiver, locals);
    let method = &m.method;
    let call_args: Vec<TokenStream> = m
        .args
        .iter()
        .take(split)
        .map(|a| encode_expr_in(a, locals))
        .collect();
    let args = if split == 1 {
        let f = tc_path(sp, "fn_args_of");
        let a = &call_args[0];
        quote_spanned! {sp=> #f(&#a) }
    } else {
        quote_spanned! {sp=> (#(#call_args),*) }
    };
    let rest: Vec<TokenStream> = m
        .args
        .iter()
        .skip(split)
        .map(|a| encode_expr_in(a, locals))
        .collect();
    quote_spanned! {sp=> #recv . #method (#args #(, #rest)*) }
}

fn encode_match(m: &syn::ExprMatch, sp: Span, locals: &mut Locals) -> TokenStream {
    let scrut = encode_expr_in(&m.expr, locals);
    let arms = m.arms.iter().map(|arm| {
        let pat = &arm.pat;
        let guard = arm.guard.as_ref().map(|(_, g)| {
            let g = encode_expr_in(g, locals);
            quote! { if #g }
        });
        let body = encode_expr_in(&arm.body, locals);
        quote! { #pat #guard => { #body }, }
    });
    quote_spanned! {sp=> match #scrut { #(#arms)* } }
}

fn encode_index(ix: &syn::ExprIndex, sp: Span, locals: &mut Locals) -> TokenStream {
    let base = encode_expr_in(strip_paren(&ix.expr), locals);
    let idx = encode_expr_in(&ix.index, locals);
    if locals.proof_assert_mode {
        quote_spanned! {sp=> (#base).__trust_wp_tc_index_pa(#idx) }
    } else {
        quote_spanned! {sp=> (#base).__trust_wp_tc_index(#idx) }
    }
}

fn encode_tuple(t: &syn::ExprTuple, sp: Span, locals: &mut Locals) -> TokenStream {
    let elems: Vec<TokenStream> = t.elems.iter().map(|e| encode_expr_in(e, locals)).collect();
    if elems.len() == 1 {
        quote_spanned! {sp=> (#(#elems),*,) }
    } else {
        quote_spanned! {sp=> (#(#elems),*) }
    }
}

fn encode_if(i: &syn::ExprIf, sp: Span, locals: &mut Locals) -> TokenStream {
    let cond = encode_expr_in(&i.cond, locals);
    let then = encode_block_in(&i.then_branch, locals);
    let els = i.else_branch.as_ref().map(|(_, e)| {
        let e = encode_expr_in(e, locals);
        quote! { else #e }
    });
    quote_spanned! {sp=> if #cond #then #els }
}

fn encode_closure(clos: &syn::ExprClosure, sp: Span, locals: &mut Locals) -> TokenStream {
    let (inputs, bound) = ref_bound_inputs(&clos.inputs);
    let output = &clos.output;
    let mut inner = locals.clone();
    inner.refvars.extend(bound);
    let body = encode_expr_in(&clos.body, &mut inner);
    let f = tc_path(sp, "mapping_from_fn");
    quote_spanned! {sp=> #f(|#inputs| #output { #body }) }
}

fn encode_struct(s: &syn::ExprStruct, locals: &mut Locals) -> TokenStream {
    let path = &s.path;
    let mut fields = Vec::new();
    for fv in &s.fields {
        let member = &fv.member;
        let e = encode_expr_in(&fv.expr, locals);
        fields.push(quote! { #member: #e });
    }
    let rest = match &s.rest {
        Some(r) => {
            let r = encode_expr_in(r, locals);
            quote! { .. #r }
        }
        None if s.dot2_token.is_some() => quote! { .. },
        None => quote! {},
    };
    quote! { #path { #(#fields,)* #rest } }
}
