// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AST rewriting passes for `snapshot!` macro expansion.
//!
//! These transforms run on the parsed expression before the snapshot macro
//! generates its final expansion. They handle Creusot compatibility patterns:
//! - Deref argument rewriting (`*x` → `x.into_inner()`)
//! - Unit-block call argument capture (`x` → `Snapshot::capture(&x).into_inner()`)
//! - Closure parameter type annotation (untyped params → `Int`)

use syn::{Expr, ExprBlock, Stmt};

use crate::expr_walk::rewrite_expr_bottom_up;

/// Rewrite call/method arguments of the form `*x` into `x.into_inner()`.
///
/// Intentionally shallow: only descends into Call and MethodCall functor
/// positions, not all children. This is correct because deref arguments only
/// need rewriting at call sites, not in arbitrary sub-expressions.
pub(crate) fn rewrite_snapshot_call_arg_derefs(expr: Expr) -> Expr {
    match expr {
        Expr::Call(mut call) => {
            *call.func = rewrite_snapshot_call_arg_derefs(*call.func);
            call.args = call.args.into_iter().map(rewrite_snapshot_arg).collect();
            Expr::Call(call)
        }
        Expr::MethodCall(mut method_call) => {
            *method_call.receiver = rewrite_snapshot_call_arg_derefs(*method_call.receiver);
            method_call.args = method_call
                .args
                .into_iter()
                .map(rewrite_snapshot_arg)
                .collect();
            Expr::MethodCall(method_call)
        }
        other => other,
    }
}

fn rewrite_snapshot_arg(arg: Expr) -> Expr {
    let arg = rewrite_snapshot_call_arg_derefs(arg);
    if let Expr::Unary(unary) = arg {
        if matches!(unary.op, syn::UnOp::Deref(_)) {
            if let Expr::Path(path) = *unary.expr {
                return syn::parse_quote!((#path).into_inner());
            }
        }
        Expr::Unary(unary)
    } else {
        arg
    }
}

/// Rewrite bare path arguments inside unit snapshot blocks to borrow/capture
/// instead of moving the original runtime value.
///
/// Creusot programs use patterns like `snapshot! { logi_drop(x); }; x.push(...)`
/// where the call inside the ghost snapshot block should observe `x` logically
/// without consuming the runtime variable. Wrap simple by-value path arguments
/// so the verifier still sees the logical value while Rust keeps ownership of
/// the original local.
pub(crate) fn rewrite_unit_block_call_path_args(block_expr: &ExprBlock) -> ExprBlock {
    let mut rewritten = block_expr.clone();
    for stmt in &mut rewritten.block.stmts {
        rewrite_unit_block_stmt(stmt);
    }
    rewritten
}

fn rewrite_unit_block_stmt(stmt: &mut Stmt) {
    match stmt {
        Stmt::Expr(expr, _) => rewrite_unit_block_expr(expr),
        Stmt::Local(local) => {
            if let Some(init) = &mut local.init {
                rewrite_unit_block_expr(&mut init.expr);
            }
        }
        _ => {}
    }
}

/// Mutable in-place rewriter for unit block expressions. Uses `&mut Expr`
/// pattern with statement-level logic (Stmt::Local, Stmt::Expr). Not converted
/// to `rewrite_expr_bottom_up` because the ownership-based helper cannot thread
/// mutable references and the Call-specific path-arg capture logic is unique to
/// this walker. Deferred per designs/2026-03-19-2530. (#2530)
fn rewrite_unit_block_expr(expr: &mut Expr) {
    match expr {
        Expr::Call(call) => {
            rewrite_unit_block_expr(&mut call.func);
            for arg in &mut call.args {
                rewrite_unit_block_expr(arg);
                if let Expr::Path(path) = arg {
                    let path = path.clone();
                    *arg = syn::parse_quote! {
                        (::trust_wp_std::ghost::Snapshot::capture(&(#path)).into_inner())
                    };
                }
            }
        }
        Expr::MethodCall(method_call) => {
            rewrite_unit_block_expr(&mut method_call.receiver);
            for arg in &mut method_call.args {
                rewrite_unit_block_expr(arg);
            }
        }
        Expr::Block(block) => {
            for stmt in &mut block.block.stmts {
                rewrite_unit_block_stmt(stmt);
            }
        }
        Expr::If(if_expr) => {
            rewrite_unit_block_expr(&mut if_expr.cond);
            for stmt in &mut if_expr.then_branch.stmts {
                rewrite_unit_block_stmt(stmt);
            }
            if let Some((_, else_expr)) = &mut if_expr.else_branch {
                rewrite_unit_block_expr(else_expr);
            }
        }
        Expr::Match(match_expr) => {
            rewrite_unit_block_expr(&mut match_expr.expr);
            for arm in &mut match_expr.arms {
                rewrite_unit_block_expr(&mut arm.body);
                if let Some((_, guard)) = &mut arm.guard {
                    rewrite_unit_block_expr(guard);
                }
            }
        }
        Expr::Paren(paren) => rewrite_unit_block_expr(&mut paren.expr),
        Expr::Reference(reference) => rewrite_unit_block_expr(&mut reference.expr),
        Expr::Unary(unary) => rewrite_unit_block_expr(&mut unary.expr),
        Expr::Binary(binary) => {
            rewrite_unit_block_expr(&mut binary.left);
            rewrite_unit_block_expr(&mut binary.right);
        }
        Expr::Assign(assign) => {
            rewrite_unit_block_expr(&mut assign.left);
            rewrite_unit_block_expr(&mut assign.right);
        }
        Expr::Tuple(tuple) => {
            for elem in &mut tuple.elems {
                rewrite_unit_block_expr(elem);
            }
        }
        _ => {}
    }
}

/// Annotate untyped closure parameters with `::trust_wp_std::logic::Int`.
///
/// In Creusot's pearlite, untyped closure parameters in logical context default
/// to `Int`. This function recursively walks an expression tree and annotates
/// any closure parameter that lacks a type annotation with `Int`.
///
/// This fixes type inference failures like:
/// Annotate only wildcard `_` closure params with `Int`.
///
/// For top-level closures in `snapshot!` that become `Mapping::from_closure`,
/// named params (even `_a`) should inherit types from calling context rather
/// than being forced to `Int`.
pub(crate) fn annotate_closure_wildcards_only(expr: Expr) -> Expr {
    if let Expr::Closure(mut closure) = expr {
        closure.inputs = closure
            .inputs
            .into_iter()
            .map(|pat| {
                if matches!(&pat, syn::Pat::Wild(_)) {
                    syn::Pat::Type(syn::PatType {
                        attrs: Vec::new(),
                        pat: Box::new(pat),
                        colon_token: syn::token::Colon::default(),
                        ty: Box::new(syn::parse_quote!(::trust_wp_std::logic::Int)),
                    })
                } else {
                    pat
                }
            })
            .collect();
        Expr::Closure(closure)
    } else {
        expr
    }
}

/// Annotate ALL untyped closure parameters with `Int` (Creusot pearlite default).
///
/// - `snapshot!(|_| 42)` → `snapshot!(|_: Int| 42)` (`mapping_indexing.rs` E0282)
/// - `snapshot!(such_that(|x| x + 1 == 42))` → annotated closure (`such_that.rs` E0282)
pub(crate) fn annotate_closure_params_with_int(expr: Expr) -> Expr {
    rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Closure(mut closure) = e {
            closure.inputs = closure
                .inputs
                .into_iter()
                .map(annotate_untyped_param_with_int)
                .collect();
            Expr::Closure(closure)
        } else {
            e
        }
    })
}

fn annotate_untyped_param_with_int(pat: syn::Pat) -> syn::Pat {
    if matches!(&pat, syn::Pat::Ident(_) | syn::Pat::Wild(_)) {
        syn::Pat::Type(syn::PatType {
            attrs: Vec::new(),
            pat: Box::new(pat),
            colon_token: syn::token::Colon::default(),
            ty: Box::new(syn::parse_quote!(::trust_wp_std::logic::Int)),
        })
    } else {
        pat
    }
}

/// Rewrite `such_that(|x| ...)` closure arguments into
/// `such_that(Mapping::from_closure(|x| ...))`.
///
/// This normalizes direct-closure `such_that` calls so the driver sees an
/// explicit `Mapping` argument matching the std-spec shape `p.get(result)`.
/// Without this rewrite, the closure is an opaque argument with no `.get()`
/// method, and the `such_that` postcondition cannot connect the witness to
/// the predicate body. (#2245)
///
/// Only applied inside `snapshot!` expansion — does not affect general
/// `such_that` calls in the language.
pub(crate) fn rewrite_such_that_closure_to_mapping(expr: Expr) -> Expr {
    rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Call(mut call) = e {
            let is_such_that = matches!(
                call.func.as_ref(),
                Expr::Path(path) if path.path.segments.last()
                    .is_some_and(|seg| seg.ident == "such_that")
            );
            if is_such_that {
                call.args = call
                    .args
                    .into_iter()
                    .map(|arg| {
                        if matches!(&arg, Expr::Closure(_)) {
                            syn::parse_quote! {
                                ::trust_wp_std::logic::Mapping::<_, _>::from_closure(#arg)
                            }
                        } else {
                            arg
                        }
                    })
                    .collect();
            }
            Expr::Call(call)
        } else {
            e
        }
    })
}
