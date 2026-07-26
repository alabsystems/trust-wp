// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic `syn::Expr` traversal helpers for snapshot macro expansion.
//!
//! Consolidates the recurring bottom-up ownership rewrite and short-circuit
//! visitor patterns that were previously hand-written per walker. (#2530)

use syn::{Expr, Stmt};

/// Bottom-up ownership rewrite: recurse into children first, then apply `f`.
///
/// Covers 14 common Expr variants. Unknown variants pass through unchanged.
pub(crate) fn rewrite_expr_bottom_up(expr: Expr, f: &mut impl FnMut(Expr) -> Expr) -> Expr {
    let recursed = match expr {
        Expr::Call(mut call) => {
            *call.func = rewrite_expr_bottom_up(*call.func, f);
            call.args = call
                .args
                .into_iter()
                .map(|a| rewrite_expr_bottom_up(a, f))
                .collect();
            Expr::Call(call)
        }
        Expr::MethodCall(mut mc) => {
            *mc.receiver = rewrite_expr_bottom_up(*mc.receiver, f);
            mc.args = mc
                .args
                .into_iter()
                .map(|a| rewrite_expr_bottom_up(a, f))
                .collect();
            Expr::MethodCall(mc)
        }
        Expr::Binary(mut bin) => {
            *bin.left = rewrite_expr_bottom_up(*bin.left, f);
            *bin.right = rewrite_expr_bottom_up(*bin.right, f);
            Expr::Binary(bin)
        }
        Expr::Unary(mut unary) => {
            *unary.expr = rewrite_expr_bottom_up(*unary.expr, f);
            Expr::Unary(unary)
        }
        Expr::Paren(mut paren) => {
            *paren.expr = rewrite_expr_bottom_up(*paren.expr, f);
            Expr::Paren(paren)
        }
        Expr::Reference(mut r) => {
            *r.expr = rewrite_expr_bottom_up(*r.expr, f);
            Expr::Reference(r)
        }
        Expr::Closure(mut c) => {
            *c.body = rewrite_expr_bottom_up(*c.body, f);
            Expr::Closure(c)
        }
        Expr::Tuple(mut t) => {
            t.elems = t
                .elems
                .into_iter()
                .map(|e| rewrite_expr_bottom_up(e, f))
                .collect();
            Expr::Tuple(t)
        }
        Expr::Field(mut field) => {
            *field.base = rewrite_expr_bottom_up(*field.base, f);
            Expr::Field(field)
        }
        Expr::Index(mut idx) => {
            *idx.expr = rewrite_expr_bottom_up(*idx.expr, f);
            *idx.index = rewrite_expr_bottom_up(*idx.index, f);
            Expr::Index(idx)
        }
        Expr::Cast(mut cast) => {
            *cast.expr = rewrite_expr_bottom_up(*cast.expr, f);
            Expr::Cast(cast)
        }
        Expr::Group(mut group) => {
            *group.expr = rewrite_expr_bottom_up(*group.expr, f);
            Expr::Group(group)
        }
        Expr::If(mut if_expr) => {
            *if_expr.cond = rewrite_expr_bottom_up(*if_expr.cond, f);
            if let Some((tok, else_expr)) = if_expr.else_branch {
                if_expr.else_branch = Some((tok, Box::new(rewrite_expr_bottom_up(*else_expr, f))));
            }
            Expr::If(if_expr)
        }
        other => other,
    };
    f(recursed)
}

/// Short-circuit visitor: return true if any node satisfies `f`.
///
/// Same variant coverage as `rewrite_expr_bottom_up` plus Block (via stmts).
pub(crate) fn any_expr(expr: &Expr, f: &mut impl FnMut(&Expr) -> bool) -> bool {
    if f(expr) {
        return true;
    }
    match expr {
        Expr::Call(call) => any_expr(&call.func, f) || call.args.iter().any(|a| any_expr(a, f)),
        Expr::MethodCall(mc) => any_expr(&mc.receiver, f) || mc.args.iter().any(|a| any_expr(a, f)),
        Expr::Binary(bin) => any_expr(&bin.left, f) || any_expr(&bin.right, f),
        Expr::Unary(unary) => any_expr(&unary.expr, f),
        Expr::Paren(paren) => any_expr(&paren.expr, f),
        Expr::Reference(r) => any_expr(&r.expr, f),
        Expr::Closure(c) => any_expr(&c.body, f),
        Expr::Field(field) => any_expr(&field.base, f),
        Expr::Index(idx) => any_expr(&idx.expr, f) || any_expr(&idx.index, f),
        Expr::Cast(cast) => any_expr(&cast.expr, f),
        Expr::Group(group) => any_expr(&group.expr, f),
        Expr::Tuple(t) => t.elems.iter().any(|e| any_expr(e, f)),
        Expr::If(if_expr) => {
            any_expr(&if_expr.cond, f)
                || if_expr.then_branch.stmts.iter().any(|s| any_stmt(s, f))
                || if_expr
                    .else_branch
                    .as_ref()
                    .is_some_and(|(_, e)| any_expr(e, f))
        }
        Expr::Block(block) => block.block.stmts.iter().any(|s| any_stmt(s, f)),
        _ => false,
    }
}

fn any_stmt(stmt: &Stmt, f: &mut impl FnMut(&Expr) -> bool) -> bool {
    match stmt {
        Stmt::Expr(e, _) => any_expr(e, f),
        Stmt::Local(local) => local
            .init
            .as_ref()
            .is_some_and(|init| any_expr(&init.expr, f)),
        _ => false,
    }
}
