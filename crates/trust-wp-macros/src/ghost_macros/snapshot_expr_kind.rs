// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Syntactic classification of the expression `snapshot!` was handed.
//!
//! Both predicates here are pure functions of the parsed expression: they
//! decide which capture strategy `snapshot::expand_snapshot` may use, and they
//! hold no expansion state. They live beside the expander rather than inside
//! it so `snapshot.rs` stays within its anti-regrowth LOC budget (see
//! `ghost_macros/tests/loc_budget.rs`), which is the module's own answer to
//! regrowth: split by concern, keep every part budgeted.

use syn::Expr;

use crate::expr_walk::any_expr;

/// Check if an expression contains a call to a spec-only function
/// (`such_that`, `dead`, `unreachable`) that cannot be evaluated at runtime.
pub(super) fn contains_spec_only_call(expr: &Expr) -> bool {
    any_expr(expr, &mut |e| {
        matches!(e,
            Expr::Call(call) if matches!(
                call.func.as_ref(),
                Expr::Path(path) if path.path.segments.last()
                    .is_some_and(|seg| {
                        seg.ident == "such_that"
                            || seg.ident == "dead"
                            || seg.ident == "unreachable"
                    })
            )
        )
    })
}

/// Whether `expr` is a place expression or a reference expression — the only
/// syntactic forms that can have `&mut` type and thus need the loan-decoupling
/// snapshot-capture dispatch. Place/reference expressions also always have a
/// fully-known type at macro-expansion time, which the type-directed dispatch
/// requires (a not-yet-inferred type would poison its `&mut` selection). (bug/869)
pub(super) fn is_place_or_reference_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Path(_) => true,
        Expr::Field(_) => true,
        Expr::Index(_) => true,
        Expr::Reference(_) => true,
        Expr::Unary(u) => matches!(u.op, syn::UnOp::Deref(_)),
        Expr::Paren(p) => is_place_or_reference_expr(&p.expr),
        Expr::Group(g) => is_place_or_reference_expr(&g.expr),
        _ => false,
    }
}
