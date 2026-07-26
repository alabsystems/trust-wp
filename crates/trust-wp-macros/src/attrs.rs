// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract attribute macro helpers.

use proc_macro::TokenStream;
use quote::quote;
use syn::{spanned::Spanned, Expr, ReturnType, Type};
use trust_wp_core::{
    contract_parser::{parse_contract, parse_contract_body},
    formula::PureExpr,
};

use crate::{
    contract::{ContractExpr, ContractKind, ContractParseError, ContractValidationError},
    transform::preprocess_view_syntax,
};

pub(crate) fn requires(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if let Err(e) = validate_contract_attr(attr, ContractKind::Requires) {
        return error_to_tokens("requires", &e);
    }
    // Re-emit as tool attribute so rustc preserves it for the driver.
    emit_tool_attr("requires", attr, item)
}

pub(crate) fn ensures(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if let Err(e) = validate_contract_attr(attr, ContractKind::Ensures) {
        return error_to_tokens("ensures", &e);
    }
    if let Err(e) = ensures_result_requires_non_unit_return(attr, &item) {
        return error_to_tokens("ensures", &e);
    }
    // Re-emit as tool attribute so rustc preserves it for the driver.
    emit_tool_attr("ensures", attr, item)
}

pub(crate) fn invariant(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if let Err(e) = validate_contract_attr(attr, ContractKind::Invariant) {
        return error_to_tokens("invariant", &e);
    }
    // Re-emit as tool attribute so rustc preserves it for the driver.
    emit_tool_attr("invariant", attr, item)
}

pub(crate) fn variant(attr: &TokenStream, item: TokenStream) -> TokenStream {
    if let Err(e) = validate_contract_attr(attr, ContractKind::Variant) {
        return error_to_tokens("variant", &e);
    }
    // Re-emit as tool attribute so rustc preserves it for the driver.
    emit_tool_attr("variant", attr, item)
}

/// Validates a contract attribute, returning a parse error if invalid.
///
/// Preprocesses Creusot-style syntax before parsing:
/// - `expr@` -> `view(expr)` (postfix view operator)
/// - `^expr` -> `final_value(expr)` (prefix final/prophecy operator)
/// - `123int` -> `Int::from(123)` (int suffix literals)
///
/// This preprocessing allows syn to parse contracts with non-standard Rust syntax.
pub(crate) fn validate_contract_attr(
    attr: &TokenStream,
    kind: ContractKind,
) -> Result<(), ContractParseError> {
    let contract_text = attr.to_string();

    // Transform Creusot-style syntax to valid Rust for syn parsing:
    // - `^expr` -> `final_value(expr)` (final/prophecy value)
    // - `expr@` -> `view(expr)` (view postfix)
    // - `123int` -> `Int::from(123)` (int suffix literals)
    let attr_to_parse: TokenStream = preprocess_view_syntax(attr.clone());

    match syn::parse::<Expr>(attr_to_parse) {
        Ok(contract_expr) => ContractExpr::validate_with_kind(&contract_expr, kind),
        Err(syn_err) => {
            // Fallback for Creusot contract syntax that is not valid Rust syntax
            // (`a < b < c`, etc.). If trust-wp-core can parse it, keep compile-time
            // validation for result/old restrictions and defer full semantics to
            // driver-side verification.
            let parsed = parse_contract(&contract_text).map_err(|core_err| {
                ContractParseError::new(
                    syn_err.span(),
                    ContractValidationError::CoreParseFailed {
                        reason: core_err.to_string(),
                    },
                )
            })?;
            validate_special_forms_in_core_expr(&parsed, kind)
                .map_err(|kind| ContractParseError::new(syn_err.span(), kind))
        }
    }
}

/// Validates a contract body (used by `proof_assert!` block syntax), returning
/// a parse error if invalid.
///
/// Unlike `validate_contract_attr`, this accepts multi-statement bodies such as
/// `lemma_call(); assertion_expr` and validates special forms (`result`, `old`)
/// on the trailing assertion expression.
pub(crate) fn validate_contract_body_attr(
    attr: &TokenStream,
    kind: ContractKind,
) -> Result<(), ContractParseError> {
    let contract_text = attr.to_string();
    let parsed = parse_contract_body(&contract_text).map_err(|core_err| {
        ContractParseError::new(
            proc_macro2::Span::call_site(),
            ContractValidationError::CoreParseFailed {
                reason: core_err.to_string(),
            },
        )
    })?;
    validate_special_forms_in_core_expr(&parsed, kind)
        .map_err(|kind| ContractParseError::new(proc_macro2::Span::call_site(), kind))
}

fn validate_special_forms_in_core_expr(
    expr: &PureExpr,
    kind: ContractKind,
) -> Result<(), ContractValidationError> {
    validate_special_forms_in_core_expr_inner(expr, kind, false)
}

fn validate_special_forms_in_core_expr_inner(
    expr: &PureExpr,
    kind: ContractKind,
    inside_old: bool,
) -> Result<(), ContractValidationError> {
    match expr {
        PureExpr::Var(name, _) if name == "result" => {
            if inside_old {
                return Err(ContractValidationError::ResultInsideOld);
            }
            if !matches!(kind, ContractKind::Ensures | ContractKind::Invariant) {
                return Err(ContractValidationError::ResultInWrongContext);
            }
        }
        PureExpr::Old(inner) => {
            if !matches!(kind, ContractKind::Ensures) {
                return Err(ContractValidationError::OldInWrongContext);
            }
            validate_special_forms_in_core_expr_inner(inner, kind, true)?;
            return Ok(());
        }
        PureExpr::BinOp(left, _, right) => {
            validate_special_forms_in_core_expr_inner(left, kind, inside_old)?;
            validate_special_forms_in_core_expr_inner(right, kind, inside_old)?;
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            validate_special_forms_in_core_expr_inner(inner, kind, inside_old)?;
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            validate_special_forms_in_core_expr_inner(cond, kind, inside_old)?;
            validate_special_forms_in_core_expr_inner(then_expr, kind, inside_old)?;
            validate_special_forms_in_core_expr_inner(else_expr, kind, inside_old)?;
        }
        PureExpr::MethodCall {
            receiver,
            method: _,
            args,
        } => {
            validate_special_forms_in_core_expr_inner(receiver, kind, inside_old)?;
            for arg in args {
                validate_special_forms_in_core_expr_inner(arg, kind, inside_old)?;
            }
        }
        PureExpr::Forall {
            var: _,
            var_sort: _,
            body,
            triggers,
        }
        | PureExpr::Exists {
            var: _,
            var_sort: _,
            body,
            triggers,
        } => {
            validate_special_forms_in_core_expr_inner(body, kind, inside_old)?;
            for trigger_group in triggers {
                for trigger_expr in trigger_group {
                    validate_special_forms_in_core_expr_inner(trigger_expr, kind, inside_old)?;
                }
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            validate_special_forms_in_core_expr_inner(scrutinee, kind, inside_old)?;
            for arm in arms {
                validate_special_forms_in_core_expr_inner(&arm.body, kind, inside_old)?;
            }
        }
        PureExpr::LogicFnCall { name: _, args } => {
            for arg in args {
                validate_special_forms_in_core_expr_inner(arg, kind, inside_old)?;
            }
        }
        PureExpr::Let { value, body, .. } => {
            validate_special_forms_in_core_expr_inner(value, kind, inside_old)?;
            validate_special_forms_in_core_expr_inner(body, kind, inside_old)?;
        }
        PureExpr::LetAssume { assumption, body } => {
            validate_special_forms_in_core_expr_inner(assumption, kind, inside_old)?;
            validate_special_forms_in_core_expr_inner(body, kind, inside_old)?;
        }
        PureExpr::LetObligation { obligation, body } => {
            validate_special_forms_in_core_expr_inner(obligation, kind, inside_old)?;
            validate_special_forms_in_core_expr_inner(body, kind, inside_old)?;
        }
        PureExpr::Closure { body, .. } => {
            validate_special_forms_in_core_expr_inner(body, kind, inside_old)?;
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(_, _) => {}
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {}
    }
    Ok(())
}

pub(crate) fn error_to_tokens(macro_name: &str, e: &ContractParseError) -> TokenStream {
    syn::Error::new(e.span, format!("{macro_name}: {}", e.message()))
        .to_compile_error()
        .into()
}

fn ensures_result_requires_non_unit_return(
    attr: &TokenStream,
    item: &TokenStream,
) -> Result<(), ContractParseError> {
    let Ok(parsed) = parse_contract(&attr.to_string()) else {
        return Ok(());
    };
    if !expr_uses_free_result(&parsed) {
        return Ok(());
    }

    let item = strip_trailing_comma(item.clone());
    if annotated_surface_returns_unit(&item) == Some(true) {
        return Err(ContractParseError::new(
            attr_expr_span(attr),
            ContractValidationError::ResultOnUnitReturn,
        ));
    }

    Ok(())
}

fn expr_uses_free_result(expr: &PureExpr) -> bool {
    expr.free_vars().contains("result")
}

fn annotated_surface_returns_unit(item: &TokenStream) -> Option<bool> {
    if let Ok(item_fn) = syn::parse::<syn::ItemFn>(item.clone()) {
        return Some(return_type_is_unit(&item_fn.sig.output));
    }
    if let Ok(item_fn) = syn::parse::<syn::ImplItemFn>(item.clone()) {
        return Some(return_type_is_unit(&item_fn.sig.output));
    }
    if let Ok(item_fn) = syn::parse::<syn::TraitItemFn>(item.clone()) {
        return Some(return_type_is_unit(&item_fn.sig.output));
    }
    if let Ok(closure) = syn::parse::<syn::ExprClosure>(item.clone()) {
        return Some(closure_definitely_returns_unit(&closure));
    }
    None
}

/// Determine whether a closure definitely returns unit.
///
/// For closures with explicit `-> ()` or `-> (())`, use the return type directly.
/// For closures with inferred return types (`ReturnType::Default`), inspect the
/// body to avoid rejecting valid inferred-value closures like `|| x` (#2542).
fn closure_definitely_returns_unit(closure: &syn::ExprClosure) -> bool {
    match &closure.output {
        ReturnType::Type(_, ty) => type_is_unit(ty),
        ReturnType::Default => expr_definitely_unit(&closure.body),
    }
}

/// Syntactic check: does this expression definitely evaluate to `()`?
///
/// Returns `true` only when the syntax proves the expression is unit-valued:
/// - A block whose last statement is semicolon-terminated (no tail expression)
/// - An empty tuple `()`
/// - A parenthesized/grouped wrapper around a definitely-unit expression
///
/// Returns `false` for anything uncertain — including blocks with tail
/// expressions, literals, paths, method calls, etc. This is a conservative
/// check: false negatives are safe (they just skip the `result` guard).
fn expr_definitely_unit(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Block(block) => block_is_definitely_unit(&block.block),
        syn::Expr::Tuple(tuple) => tuple.elems.is_empty(),
        syn::Expr::Paren(paren) => expr_definitely_unit(&paren.expr),
        syn::Expr::Group(group) => expr_definitely_unit(&group.expr),
        _ => false,
    }
}

/// A block is definitely unit when it has no tail expression — its last
/// statement is semicolon-terminated (or it's empty).
fn block_is_definitely_unit(block: &syn::Block) -> bool {
    match block.stmts.last() {
        None => true,
        Some(syn::Stmt::Expr(_, Some(_))) => true, // trailing semicolon
        Some(syn::Stmt::Expr(_, None)) => false,   // tail expression (value)
        Some(syn::Stmt::Local(_)) => true,         // `let x = ...;`
        Some(syn::Stmt::Item(_)) => true,          // item definition
        Some(syn::Stmt::Macro(m)) => m.semi_token.is_some(),
    }
}

fn return_type_is_unit(return_type: &ReturnType) -> bool {
    match return_type {
        ReturnType::Default => true,
        ReturnType::Type(_, ty) => type_is_unit(ty),
    }
}

fn type_is_unit(ty: &Type) -> bool {
    match ty {
        Type::Tuple(tuple) => tuple.elems.is_empty(),
        Type::Paren(paren) => type_is_unit(&paren.elem),
        Type::Group(group) => type_is_unit(&group.elem),
        _ => false,
    }
}

fn attr_expr_span(attr: &TokenStream) -> proc_macro2::Span {
    let attr_to_parse: TokenStream = preprocess_view_syntax(attr.clone());
    syn::parse::<Expr>(attr_to_parse).map_or_else(
        |_| {
            attr.clone()
                .into_iter()
                .next()
                .map_or_else(proc_macro2::Span::call_site, |token| {
                    proc_macro2::Span::from(token.span())
                })
        },
        |expr| expr.span(),
    )
}

fn emit_tool_attr(name: &str, attr: &TokenStream, item: TokenStream) -> TokenStream {
    // When a contract attribute is applied to a closure in expression position
    // (e.g., `.filter(#[ensures(...)] |x| ...)`), rustc includes the trailing
    // comma in the item tokens. We must strip it or the expansion produces
    // "macro expansion ignores `,` and any tokens following" errors.
    let item = strip_trailing_comma(item);

    let item_tokens: proc_macro2::TokenStream = item.into();
    let attr_text = attr.to_string();
    // Embed contract in doc attribute to avoid key-value syntax issues.
    // Format: #[doc = "trust-wp:{name}:{contract}"]
    // The driver extracts contracts from doc attributes with this prefix.
    let doc_marker = format!("trust-wp:{name}:{attr_text}");
    let expanded = quote! {
        #[doc = #doc_marker]
        #item_tokens
    };
    expanded.into()
}

/// Strip a trailing comma from a token stream.
///
/// When `#[ensures]` or other contract attributes are applied to closures in
/// function call argument position, rustc includes the trailing comma separator
/// in the item tokens passed to the proc macro. If we return it, rustc emits
/// "macro expansion ignores `,` and any tokens following" because the comma
/// from the original source is also present, resulting in a double comma.
fn strip_trailing_comma(item: TokenStream) -> TokenStream {
    use proc_macro::TokenTree;
    let mut tokens: Vec<TokenTree> = item.into_iter().collect();
    if let Some(TokenTree::Punct(p)) = tokens.last() {
        if p.as_char() == ',' {
            tokens.pop();
        }
    }
    tokens.into_iter().collect()
}
