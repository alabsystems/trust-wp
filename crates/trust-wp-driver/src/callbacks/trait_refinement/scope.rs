// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Scope closure of refinement clauses.
//!
//! Specification clauses reach the refinement check as unscoped strings: a
//! name in the trait's clause is written in the trait's module and a name in
//! the impl's clause in the impl's module, but the parser and the encoder
//! resolve both textually. `x > K` in the trait and `x > K` in the impl may
//! denote different constants (or logic functions, or constructors) and would
//! still be compared as equal terms.
//!
//! Only logic-function calls are resolved through rustc (the identity
//! resolver, each side in its own scope). Otherwise the refinement check only runs on
//! clauses whose every name has a scope-independent meaning, and everything
//! else is refused. The accepted vocabulary is deliberately small:
//!
//! - the method's own parameters, `result`, and names bound inside the clause
//!   (quantifier, `let`, closure and match-arm binders);
//! - literals and the fixed pearlite operators (arithmetic, comparison,
//!   logical connectives, `@`, `*`, `^`, `old`, `if`, `match` over
//!   binding/tuple/literal patterns);
//! - quantifier binders and closure parameters written with the type `Int`
//!   or `bool`, the only written types whose sort the AST records faithfully
//!   (and only while no local item or import shadows those names; see
//!   `prepare.rs`).
//! - the parser's own synthetic accessors: tuple construction, tuple field
//!   `.N` and named field `.f` (a field of a parameter's type, which is the
//!   same type on both sides of the refinement).
//!
//! - a call the identity resolver bound to one local definition that is not a
//!   trait declaration (its unique id): the trait's clause is resolved in the
//!   trait's scope with its declaration calls instantiated at the impl, and
//!   the impl's in its own scope, before this check, so equal ids are the
//!   same definition on both sides.
//!
//! Refused: every other identifier or path (constants, statics, `Self::X`,
//! `<T as Tr>::X`), every other logic-function or function call, every method
//! call left unresolved (method resolution depends on the traits in scope),
//! constructor patterns and struct literals, and every type the parser drops
//! from the AST.
//!
//! Written types are checked on the clause text (see
//! [`first_unrecorded_written_type`]), because the parser erases most of
//! them: `(e : T)` keeps at most the sort of `T` (for an integer type or
//! `bool`) and otherwise parses to `e`, `let y: T = ..` likewise, a cast to a
//! fixed-width integer type is lowered to Rust's `as` and any other cast does
//! not parse at all, and `forall<v: Wd>` (a type alias whose meaning is
//! scope-dependent), a
//! tuple or pointer annotation, and `forall<v>` all parse to a binder with no
//! sort. Machine-integer annotations (`forall<v: u8>`) parse to the `Int`
//! sort with the type's range stated on the body (D-203), which names no type. Every cast, ascription,
//! `let` annotation and literal type suffix is refused (`255u8` keeps only
//! the value, but the suffix fixes the machine type of the operators around
//! it: `255u8 + 1u8 == 0u8` holds, `255u16 + 1u16 == 0u16` does not), as is every binder or closure parameter
//! whose written type is not exactly `Int` or `bool`. After that, two clauses
//! whose ASTs are equal are equal including every written type, which is
//! what the verbatim shortcut in `mod.rs` relies on.

use std::collections::HashSet;

use trust_wp_core::{
    contract_parser::{WrittenType, WrittenTypeSite},
    formula::{ExprSort, Pattern, PureExpr},
};

/// Written binder and closure-parameter types whose sort the AST records
/// faithfully: `Int` parses to [`ExprSort::Int`], `bool` to [`ExprSort::Bool`].
pub(super) const FAITHFUL_WRITTEN_TYPES: [&str; 2] = ["Int", "bool"];

/// Prefixes of the parser's synthetic logic-function names (see
/// `trust_wp_core::formula::types`). Any user logic function registered
/// under one of these names makes the accessors ambiguous, and the check
/// refuses.
pub(super) const SYNTHETIC_LOGIC_FN_PREFIX: &str = "__trust_wp_";
const TUPLE_LOGIC_FN_PREFIX: &str = "__trust_wp_tuple";
const TUPLE_FIELD_LOGIC_FN_PREFIX: &str = "__trust_wp_tuple_get_";
const NAMED_FIELD_LOGIC_FN_PREFIX: &str = "__trust_wp_field_";

fn is_decimal(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())
}

/// Whether `name` is one of the parser's synthetic accessors.
fn is_synthetic_accessor(name: &str) -> bool {
    if let Some(index) = name.strip_prefix(TUPLE_FIELD_LOGIC_FN_PREFIX) {
        return is_decimal(index);
    }
    if let Some(arity) = name.strip_prefix(TUPLE_LOGIC_FN_PREFIX) {
        return is_decimal(arity);
    }
    if let Some(field) = name.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
        return !field.is_empty()
            && field
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_');
    }
    false
}

/// Whether `name` is the unique id the identity resolver gave ONE local
/// definition that is not a trait declaration: it means that definition in
/// every scope. A declaration's id is the method at an abstract `Self`, which
/// the two sides of a refinement need not read at the same type.
fn names_one_concrete_definition(name: &str) -> bool {
    use trust_wp_core::logic::identity::{logic_fn_identity_registry, LogicFnOwnerKind};
    logic_fn_identity_registry().is_some_and(|registry| {
        registry
            .member(name)
            .is_some_and(|member| member.kind != LogicFnOwnerKind::TraitDecl)
    })
}

/// A binder sort the AST records faithfully. A binder with no sort was
/// written with a type the parser dropped (an alias, a tuple, a pointer) or
/// with none at all, and its domain is unknown.
fn is_scope_free_sort(sort: Option<&ExprSort>) -> bool {
    matches!(sort, Some(ExprSort::Int | ExprSort::Bool))
}

/// The first type written (or elided) in a clause's text that the clause's
/// AST does not record faithfully, described for the refusal message. `None`
/// when every written type is a binder or closure parameter of type `Int` or
/// `bool`.
pub(super) fn first_unrecorded_written_type(written: &[WrittenType]) -> Option<String> {
    written.iter().find_map(|written| {
        let text = written.text.as_deref();
        match (written.site, text) {
            (WrittenTypeSite::Cast, text) => Some(format!("cast `as {}`", text.unwrap_or("_"))),
            (WrittenTypeSite::Ascription, text) => {
                Some(format!("type ascription `: {}`", text.unwrap_or("_")))
            }
            (WrittenTypeSite::LiteralSuffix, text) => {
                Some(format!("literal type suffix `{}`", text.unwrap_or("_")))
            }
            (WrittenTypeSite::LetBinding, text) => {
                Some(format!("`let` annotation `: {}`", text.unwrap_or("_")))
            }
            (WrittenTypeSite::QuantifierBinder, None) => {
                Some("a quantifier binder with no written type".to_string())
            }
            (WrittenTypeSite::ClosureParam, None) => {
                Some("a closure parameter with no written type".to_string())
            }
            (WrittenTypeSite::QuantifierBinder | WrittenTypeSite::ClosureParam, Some(text)) => {
                (!FAITHFUL_WRITTEN_TYPES.contains(&text)).then(|| format!("type `{text}`"))
            }
        }
    })
}

/// The first name in `expr` whose meaning depends on the scope the clause
/// was written in, described for the refusal message. `None` when every name
/// is a parameter, `result`, a binder, or fixed pearlite vocabulary.
pub(super) fn first_scope_dependent_name(
    expr: &PureExpr,
    params: &HashSet<&str>,
    clause_kind: ClauseKind,
) -> Option<String> {
    let mut bound: Vec<String> = Vec::new();
    let found = walk(expr, params, &mut bound);
    if found.is_some() || clause_kind == ClauseKind::Ensures {
        return found;
    }
    // `result` names the return value only in a postcondition; in a
    // precondition it resolves to nothing (the body path rejects it), so it
    // must not be accepted as a free name there.
    expr.free_vars()
        .contains("result")
        .then(|| "`result` outside a postcondition".to_string())
}

/// Which clause list a clause comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ClauseKind {
    Requires,
    Ensures,
}

/// Prefix of every name the refinement check and the parser synthesize
/// (positional parameter names, anonymous parameters, accessors). A user
/// identifier or binder in this namespace could alias a synthesized name.
pub(super) const RESERVED_NAME_PREFIX: &str = "__trust_wp_";

fn reserved_binder(names: &[String]) -> Option<String> {
    names
        .iter()
        .find(|name| name.starts_with(RESERVED_NAME_PREFIX) || name.as_str() == "result")
        .map(|name| format!("binder `{name}`, which shadows a reserved or synthesized name"))
}

fn walk_all(exprs: &[PureExpr], params: &HashSet<&str>, bound: &mut Vec<String>) -> Option<String> {
    exprs.iter().find_map(|expr| walk(expr, params, bound))
}

fn with_binders(
    names: &[String],
    bound: &mut Vec<String>,
    f: impl FnOnce(&mut Vec<String>) -> Option<String>,
) -> Option<String> {
    if let Some(found) = reserved_binder(names) {
        return Some(found);
    }
    let depth = bound.len();
    bound.extend(names.iter().cloned());
    let found = f(bound);
    bound.truncate(depth);
    found
}

#[allow(clippy::too_many_lines)]
fn walk(expr: &PureExpr, params: &HashSet<&str>, bound: &mut Vec<String>) -> Option<String> {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => None,
        PureExpr::Var(name, _) => {
            if name.starts_with(RESERVED_NAME_PREFIX) {
                return Some(format!(
                    "identifier `{name}` in the reserved `{RESERVED_NAME_PREFIX}` namespace"
                ));
            }
            let is_resolved = bound.iter().any(|b| b == name)
                || params.contains(name.as_str())
                || name == "result";
            (!is_resolved).then(|| format!("identifier `{name}`"))
        }
        PureExpr::BinOp(left, _, right) => {
            walk(left, params, bound).or_else(|| walk(right, params, bound))
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => walk(inner, params, bound),
        PureExpr::Ite(cond, then_expr, else_expr) => walk(cond, params, bound)
            .or_else(|| walk(then_expr, params, bound))
            .or_else(|| walk(else_expr, params, bound)),
        PureExpr::MethodCall { method, .. } => Some(format!("method call `.{method}(..)`")),
        PureExpr::LogicFnCall { name, args } => {
            if is_synthetic_accessor(name) || names_one_concrete_definition(name) {
                walk_all(args, params, bound)
            } else {
                Some(format!("call `{name}(..)`"))
            }
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        }
        | PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            if !is_scope_free_sort(var_sort.as_ref()) {
                return Some(format!("binder `{var}` whose type has no faithful sort"));
            }
            with_binders(std::slice::from_ref(var), bound, |bound| {
                walk(body, params, bound).or_else(|| {
                    triggers
                        .iter()
                        .find_map(|trigger| walk_all(trigger, params, bound))
                })
            })
        }
        PureExpr::Match { scrutinee, arms } => {
            if let Some(found) = walk(scrutinee, params, bound) {
                return Some(found);
            }
            arms.iter().find_map(|arm| {
                let mut names = Vec::new();
                if let Some(found) = pattern_binders(&arm.pattern, params, bound, &mut names) {
                    return Some(found);
                }
                with_binders(&names, bound, |bound| walk(&arm.body, params, bound))
            })
        }
        PureExpr::Let { var, value, body } => walk(value, params, bound).or_else(|| {
            with_binders(std::slice::from_ref(var), bound, |bound| {
                walk(body, params, bound)
            })
        }),
        PureExpr::Closure {
            params: binders,
            body,
        } => {
            if let Some((name, _)) = binders
                .iter()
                .find(|(_, sort)| !is_scope_free_sort(sort.as_ref()))
            {
                return Some(format!(
                    "closure parameter `{name}` whose type has no faithful sort"
                ));
            }
            let names: Vec<String> = binders.iter().map(|(name, _)| name.clone()).collect();
            with_binders(&names, bound, |bound| walk(body, params, bound))
        }
        // Driver-internal forms never produced by the clause parser, and any
        // variant added later: refuse rather than guess.
        _ => Some("an internal expression form".to_string()),
    }
}

/// Collect the names a pattern binds; refuse constructor patterns (a variant
/// name is resolved in the clause's scope).
fn pattern_binders(
    pattern: &Pattern,
    params: &HashSet<&str>,
    bound: &mut Vec<String>,
    names: &mut Vec<String>,
) -> Option<String> {
    match pattern {
        Pattern::Wildcard => None,
        Pattern::Binding(name) => {
            names.push(name.clone());
            None
        }
        Pattern::Literal(literal) => walk(literal, params, bound),
        Pattern::Alias { alias, pattern } => {
            names.push(alias.clone());
            pattern_binders(pattern, params, bound, names)
        }
        Pattern::Tuple(items) => items
            .iter()
            .find_map(|item| pattern_binders(item, params, bound, names)),
        Pattern::Constructor { name, .. } => Some(format!("constructor pattern `{name}`")),
        _ => Some("an unsupported pattern form".to_string()),
    }
}
