// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `expr_walk` traversal helpers.

use quote::quote;
use syn::Expr;

use crate::expr_walk::{any_expr, rewrite_expr_bottom_up};

fn parse_expr(tokens: proc_macro2::TokenStream) -> Expr {
    syn::parse2(tokens).expect("valid expression")
}

// ── rewrite_expr_bottom_up ──

#[test]
fn rewrite_bottom_up_literal_unchanged() {
    let expr = parse_expr(quote!(42));
    let result = rewrite_expr_bottom_up(expr.clone(), &mut |e| e);
    assert_eq!(quote!(#result).to_string(), quote!(#expr).to_string());
}

#[test]
fn rewrite_bottom_up_visits_binary_children() {
    let expr = parse_expr(quote!(1 + 1));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Lit(lit) = &e {
            if let syn::Lit::Int(int) = &lit.lit {
                if int.base10_digits() == "1" {
                    return parse_expr(quote!(2));
                }
            }
        }
        e
    });
    assert_eq!(quote!(#result).to_string(), quote!(2 + 2).to_string());
}

#[test]
fn rewrite_bottom_up_order_children_before_parent() {
    let expr = parse_expr(quote!(a + b));
    let mut saw_rewritten_child = false;
    let _ = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Binary(bin) = &e {
            if let Expr::Lit(_) = bin.left.as_ref() {
                saw_rewritten_child = true;
            }
        }
        if matches!(&e, Expr::Path(_)) {
            return parse_expr(quote!(0));
        }
        e
    });
    assert!(
        saw_rewritten_child,
        "parent should see rewritten children (bottom-up order)"
    );
}

#[test]
fn rewrite_bottom_up_call_args() {
    let expr = parse_expr(quote!(f(a, b)));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Path(p) = &e {
            if p.path.is_ident("a") {
                return parse_expr(quote!(1));
            }
        }
        e
    });
    assert_eq!(quote!(#result).to_string(), quote!(f(1, b)).to_string());
}

#[test]
fn rewrite_bottom_up_method_call_receiver_and_args() {
    let expr = parse_expr(quote!(x.foo(y)));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Path(p) = &e {
            if p.path.is_ident("x") {
                return parse_expr(quote!(z));
            }
        }
        e
    });
    assert_eq!(quote!(#result).to_string(), quote!(z.foo(y)).to_string());
}

#[test]
fn rewrite_bottom_up_nested_unary_paren_ref() {
    let expr = parse_expr(quote!(&(!x)));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Path(p) = &e {
            if p.path.is_ident("x") {
                return parse_expr(quote!(y));
            }
        }
        e
    });
    assert_eq!(quote!(#result).to_string(), quote!(&(!y)).to_string());
}

#[test]
fn rewrite_bottom_up_tuple() {
    let expr = parse_expr(quote!((a, b, c)));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Path(p) = &e {
            if p.path.is_ident("b") {
                return parse_expr(quote!(42));
            }
        }
        e
    });
    assert_eq!(quote!(#result).to_string(), quote!((a, 42, c)).to_string());
}

#[test]
fn rewrite_bottom_up_field_access() {
    let expr = parse_expr(quote!(x.field));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Path(p) = &e {
            if p.path.is_ident("x") {
                return parse_expr(quote!(y));
            }
        }
        e
    });
    assert_eq!(quote!(#result).to_string(), quote!(y.field).to_string());
}

#[test]
fn rewrite_bottom_up_index() {
    let expr = parse_expr(quote!(arr[i]));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Path(p) = &e {
            if p.path.is_ident("i") {
                return parse_expr(quote!(0));
            }
        }
        e
    });
    assert_eq!(quote!(#result).to_string(), quote!(arr[0]).to_string());
}

#[test]
fn rewrite_bottom_up_if_cond_and_else() {
    let expr = parse_expr(quote!(if a { b } else { c }));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Path(p) = &e {
            if p.path.is_ident("a") {
                return parse_expr(quote!(true));
            }
        }
        e
    });
    let s = quote!(#result).to_string();
    assert!(s.contains("true"), "if-cond should be rewritten: {s}");
}

#[test]
fn rewrite_bottom_up_closure_body() {
    let expr = parse_expr(quote!(|x| x + 1));
    let result = rewrite_expr_bottom_up(expr, &mut |e| {
        if let Expr::Lit(lit) = &e {
            if let syn::Lit::Int(int) = &lit.lit {
                if int.base10_digits() == "1" {
                    return parse_expr(quote!(2));
                }
            }
        }
        e
    });
    let s = quote!(#result).to_string();
    assert!(s.contains('2'), "closure body should be rewritten: {s}");
    assert!(!s.contains("+ 1"), "original literal should be gone: {s}");
}

#[test]
fn rewrite_bottom_up_unknown_variant_passthrough() {
    let expr = parse_expr(quote!("hello"));
    let mut visited = false;
    let result = rewrite_expr_bottom_up(expr.clone(), &mut |e| {
        visited = true;
        e
    });
    assert!(visited, "even unknown variants get visited by f");
    assert_eq!(quote!(#result).to_string(), quote!(#expr).to_string());
}

// ── any_expr ──

#[test]
fn any_expr_root_match() {
    let expr = parse_expr(quote!(42));
    assert!(any_expr(&expr, &mut |e| matches!(e, Expr::Lit(_))));
}

#[test]
fn any_expr_nested_in_binary() {
    let expr = parse_expr(quote!(a + 42));
    assert!(any_expr(&expr, &mut |e| matches!(e, Expr::Lit(_))));
}

#[test]
fn any_expr_no_match() {
    let expr = parse_expr(quote!(a + b));
    assert!(!any_expr(&expr, &mut |e| matches!(e, Expr::Lit(_))));
}

#[test]
fn any_expr_in_method_call_args() {
    let expr = parse_expr(quote!(x.foo(42)));
    assert!(any_expr(&expr, &mut |e| matches!(e, Expr::Lit(_))));
}

#[test]
fn any_expr_in_call_func_position() {
    let expr = parse_expr(quote!(f(a)));
    assert!(any_expr(&expr, &mut |e| {
        matches!(e, Expr::Path(p) if p.path.is_ident("f"))
    }));
}

#[test]
fn any_expr_short_circuits_on_first_match() {
    let expr = parse_expr(quote!(a + b));
    let mut visit_count = 0;
    let found = any_expr(&expr, &mut |e| {
        visit_count += 1;
        matches!(e, Expr::Binary(_))
    });
    assert!(found);
    assert_eq!(visit_count, 1, "should short-circuit after root match");
}

#[test]
fn any_expr_if_then_branch() {
    let expr = parse_expr(quote!(if cond { 42 } else { a }));
    assert!(
        any_expr(&expr, &mut |e| matches!(e, Expr::Lit(_))),
        "should find literal in then-branch"
    );
}

#[test]
fn any_expr_if_else_branch() {
    let expr = parse_expr(quote!(if cond { a } else { 99 }));
    assert!(
        any_expr(&expr, &mut |e| {
            if let Expr::Lit(lit) = e {
                matches!(&lit.lit, syn::Lit::Int(i) if i.base10_digits() == "99")
            } else {
                false
            }
        }),
        "should find literal in else-branch"
    );
}

#[test]
fn any_expr_block_stmts() {
    let expr = parse_expr(quote!({
        let _x = 42;
    }));
    assert!(
        any_expr(&expr, &mut |e| matches!(e, Expr::Lit(_))),
        "should find literal in block local init"
    );
}

#[test]
fn any_expr_index_both_sides() {
    let expr = parse_expr(quote!(arr[i]));
    assert!(any_expr(&expr, &mut |e| {
        matches!(e, Expr::Path(p) if p.path.is_ident("i"))
    }));
}

#[test]
fn any_expr_closure_body() {
    let expr = parse_expr(quote!(|x| 42));
    assert!(any_expr(&expr, &mut |e| matches!(e, Expr::Lit(_))));
}

#[test]
fn any_expr_tuple_elements() {
    let expr = parse_expr(quote!((a, 7, c)));
    assert!(any_expr(&expr, &mut |e| matches!(e, Expr::Lit(_))));
}
