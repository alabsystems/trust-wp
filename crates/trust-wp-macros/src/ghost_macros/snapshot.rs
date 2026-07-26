// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expansion logic for the `snapshot!` macro.

use proc_macro::TokenStream;
use quote::quote;
use syn::Expr;

use crate::{
    expr_walk::any_expr,
    snapshot_rewrite::{
        annotate_closure_params_with_int, annotate_closure_wildcards_only,
        rewrite_snapshot_call_arg_derefs, rewrite_such_that_closure_to_mapping,
        rewrite_unit_block_call_path_args,
    },
    transform::preprocess_view_syntax,
};

/// Check if an expression contains a call to a spec-only function
/// (`such_that`, `dead`, `unreachable`) that cannot be evaluated at runtime.
fn contains_spec_only_call(expr: &Expr) -> bool {
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

fn parse_snapshot_expr(input2: &proc_macro2::TokenStream) -> syn::Result<Expr> {
    match syn::parse2(input2.clone()) {
        Ok(expr) => Ok(expr),
        Err(_first_err) => {
            let wrapped: proc_macro2::TokenStream = quote!({ #input2 });
            syn::parse2::<Expr>(wrapped)
        }
    }
}

fn rewrite_block_closure_locals_to_mappings(block_expr: &syn::ExprBlock) -> syn::ExprBlock {
    let mut rewritten = block_expr.clone();
    for stmt in &mut rewritten.block.stmts {
        let syn::Stmt::Local(local) = stmt else {
            continue;
        };
        let Some(init) = &mut local.init else {
            continue;
        };
        if !matches!(init.expr.as_ref(), Expr::Closure(_)) {
            continue;
        }
        let closure = (*init.expr).clone();
        *init.expr = syn::parse_quote! {
            ::trust_wp_std::logic::Mapping::<_, _>::from_closure(#closure)
        };
    }
    rewritten
}

fn capture_unit_block_snapshot(block_expr: &syn::ExprBlock) -> proc_macro2::TokenStream {
    let block_expr = rewrite_unit_block_call_path_args(block_expr);
    // Preserve unit-returning block statements in verifier MIR so lemma/spec-only
    // effects still occur before we create the placeholder snapshot value.
    //
    // Keep the block behind `cfg(trust_wp)` so normal Rust builds still erase
    // ghost-only statements instead of trying to resolve or run them at runtime.
    // Dropping the block entirely made `snapshot! { lemma(); }` erase the lemma
    // call from verification, losing its postconditions at the call site. (#2299)
    quote! {
        {
            #[cfg(trust_wp)]
            #block_expr
            ::trust_wp_std::ghost::Snapshot::<()>::new_phantom()
        }
    }
}

fn block_returns_unit(block_expr: &syn::ExprBlock) -> bool {
    !matches!(
        block_expr.block.stmts.last(),
        Some(syn::Stmt::Expr(_, None))
    )
}

fn capture_block_seq_mapping_snapshot(
    block_expr: &syn::ExprBlock,
) -> Option<proc_macro2::TokenStream> {
    let has_closure_local = block_expr.block.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            syn::Stmt::Local(local)
                if local
                    .init
                    .as_ref()
                    .is_some_and(|init| matches!(init.expr.as_ref(), Expr::Closure(_)))
        )
    });
    let tail_is_seq_macro = matches!(
        block_expr.block.stmts.last(),
        Some(syn::Stmt::Expr(Expr::Macro(mac), None))
            if mac.mac.path.segments.last().is_some_and(|seg| seg.ident == "seq")
    );
    if !has_closure_local || !tail_is_seq_macro {
        return None;
    }

    let capture_block = rewrite_block_closure_locals_to_mappings(block_expr);
    Some(quote! {
        {
            #[cfg(trust_wp)]
            {
                ::trust_wp_std::ghost::Snapshot::capture(&(#capture_block))
            }
            #[cfg(not(trust_wp))]
            {
                ::trust_wp_std::ghost::Snapshot::new_phantom()
            }
        }
    })
}

fn snapshot_early_capture(expr: &Expr) -> Option<proc_macro2::TokenStream> {
    if let Expr::Block(block_expr) = expr {
        if block_returns_unit(block_expr) {
            return Some(capture_unit_block_snapshot(block_expr));
        }

        if let Some(capture) = capture_block_seq_mapping_snapshot(block_expr) {
            return Some(capture);
        }
    }

    if matches!(expr, Expr::Struct(_)) {
        return Some(quote! {
            ::trust_wp_std::ghost::Snapshot::new_phantom()
        });
    }

    // Tuple expressions like `(atomic, frag.id(), x)` may move non-Copy
    // values into the temporary tuple.  Under cfg(not(trust_wp)) we erase the
    // expression entirely using `Snapshot::from_fn(|| panic!())` — the never
    // type `!` coerces to any `T`, so Rust infers `Snapshot<T>` from the
    // surrounding call-site context (e.g., a function parameter typed as
    // `Snapshot<P::Public>`).  Under cfg(trust_wp) the verifier sees the real
    // capture.  (#2682)
    if matches!(expr, Expr::Tuple(_)) {
        return Some(quote! {
            {
                #[cfg(trust_wp)]
                {
                    ::trust_wp_std::ghost::Snapshot::capture(&(#expr))
                }
                #[cfg(not(trust_wp))]
                {
                    ::trust_wp_std::ghost::Snapshot::from_fn(|| panic!())
                }
            }
        });
    }

    // For spec-only calls (such_that, dead, unreachable): under cfg(trust_wp)
    // the verifier sees the real Snapshot::capture so it can reason about
    // the logical witness. Under cfg(not(trust_wp)) we keep the if-false
    // pattern to preserve type information without runtime panics. (#2245)
    if contains_spec_only_call(expr) {
        return Some(quote! {
            {
                #[cfg(trust_wp)]
                {
                    ::trust_wp_std::ghost::Snapshot::capture(&(#expr))
                }
                #[cfg(not(trust_wp))]
                {
                    #[allow(unreachable_code, unused_variables, dead_code)]
                    if false {
                        ::trust_wp_std::ghost::Snapshot::capture(&(#expr))
                    } else {
                        ::trust_wp_std::ghost::Snapshot::new_phantom()
                    }
                }
            }
        });
    }

    None
}

/// Expand `snapshot!(expr)` macro.
/// A bare unsuffixed integer literal (`1`, `42`), possibly wrapped in a
/// single-expression block (`{ 1 }`) or unary negation (`-1`). Creusot
/// pearlite types these `Int`; trust-wp must lift them for parity. (#route-100 r1)
fn is_bare_unsuffixed_int_literal(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(l) => matches!(&l.lit, syn::Lit::Int(i) if i.suffix().is_empty()),
        Expr::Unary(u) if matches!(u.op, syn::UnOp::Neg(_)) => {
            is_bare_unsuffixed_int_literal(&u.expr)
        }
        Expr::Block(b) if b.block.stmts.len() == 1 => match &b.block.stmts[0] {
            syn::Stmt::Expr(inner, None) => is_bare_unsuffixed_int_literal(inner),
            _ => false,
        },
        Expr::Paren(p) => is_bare_unsuffixed_int_literal(&p.expr),
        _ => false,
    }
}

pub(crate) fn expand_snapshot(input: TokenStream) -> TokenStream {
    let input = preprocess_view_syntax(input);

    let input2: proc_macro2::TokenStream = input.into();
    let expr: Expr = match parse_snapshot_expr(&input2) {
        Ok(expr) => expr,
        Err(e) => {
            return syn::Error::new(
                e.span(),
                format!("snapshot!: failed to parse expression: {e}"),
            )
            .to_compile_error()
            .into();
        }
    };

    let expr = rewrite_snapshot_call_arg_derefs(expr);
    // Annotate untyped closure parameters with Int (Creusot pearlite default).
    // For top-level closures (which become Mapping::from_closure), only annotate
    // wildcard `_` params — named params like `_a` should inherit types from
    // the calling context (e.g., Snapshot<Mapping<u32, bool>>).
    // For closures inside calls (e.g., `such_that(|x| ...)`), annotate all
    // untyped params since they lack external type context.
    let expr = if matches!(expr, Expr::Closure(_)) {
        annotate_closure_wildcards_only(expr)
    } else {
        annotate_closure_params_with_int(expr)
    };
    // Rewrite such_that(|x| ...) closure args to Mapping::from_closure so
    // the driver sees an explicit Mapping matching the std-spec shape. (#2245)
    let expr = rewrite_such_that_closure_to_mapping(expr);
    if let Some(expansion) = snapshot_early_capture(&expr) {
        return expansion.into();
    }

    let captured_expr = if matches!(expr, Expr::Closure(_)) {
        quote! { ::trust_wp_std::logic::Mapping::<_, _>::from_closure(#expr) }
    } else if is_bare_unsuffixed_int_literal(&expr) {
        // Creusot pearlite defaults unsuffixed integer literals to Int.
        // Without lifting, `snapshot! { 1 }` captures `&{integer}` and callers
        // expecting `Snapshot<Int>` die in E0308 before any VC is generated
        // (bug/436_0). `as i128` keeps any unsuffixed literal well-typed for
        // `Int: From<i128>`. (#route-100 r1)
        quote! { ::trust_wp_std::logic::Int::from(#expr as i128) }
    } else {
        quote! { #expr }
    };

    // A `snapshot!` whose argument can have type `&mut T` extends that borrow's
    // loan under `cfg(trust_wp)` — `Snapshot::capture(&expr)` returns
    // `Snapshot<&'b mut T>` carrying the borrow's own lifetime `'b`, so keeping
    // the snapshot alive pins the loan and a later reborrow of the same place is
    // rejected E0499 where Creusot (which ghost-erases the capture) compiles and
    // proves. Only PLACE-like / reference expressions (`b`, `self.g`, `*p`,
    // `a[i]`, `&mut x`) can have `&mut` type; their types are also always fully
    // known at this point, which the type-directed dispatch below requires. A
    // COMPUTED expression (`*n + 1`, `s.len()`, `f(x)`) can never be `&mut` and
    // may have a not-yet-inferred type (e.g. `Int + <literal>` before integer
    // literal fallback), which would poison the dispatch's inference — so those
    // keep the byte-identical direct `Snapshot::capture` path. (bug/869)
    let is_mut_ref_dispatch_candidate = !matches!(expr, Expr::Closure(_))
        && !is_bare_unsuffixed_int_literal(&expr)
        && is_place_or_reference_expr(&expr);

    if is_mut_ref_dispatch_candidate {
        // Under cfg(trust_wp) the verifier build routes through the type-directed
        // snapshot-capture dispatch: `snapshot_capture_select(&(expr))` pins a
        // selector to `expr`'s type from a SINGLE inline reborrow, then the
        // argument-less `.capture()` resolves to the `&mut`-aware inherent
        // capture (fresh, decoupled output lifetime so a `snapshot!` of a `&mut`
        // does NOT extend its loan → no E0499 where Creusot ghost-erases) or,
        // for a plain value, to the identical `Snapshot::capture` fallback.
        //
        // ANONYMOUS-REBORROW LOWERING (bug/869): the captured reference is the
        // ONE inline `&(expr)` argument to `snapshot_capture_select` — never a
        // user-named `let` binding. An earlier shape bound it
        // (`let __trust_wp_snap_ref = &(expr); …capture(__r)`); that `let`
        // surfaced as a user-named MIR local whose reborrow the loop-invariant
        // (pre_loop_resolve) and `proof_assert` pipelines do NOT collapse, so it
        // leaked into their VCs as a free `Var("__trust_wp_snap_ref", …)` and
        // spuriously failed `old_v@ == v@` init (regressing final_borrows,
        // inferred_invariants). As an inline call-argument subexpression,
        // `&(expr)` is instead an ANONYMOUS compiler temp that reborrow-
        // cancellation collapses to the captured value — exactly the MIR shape
        // of a direct `Snapshot::capture(&expr)`, which every pipeline already
        // handles. Threading through the selector (rather than repeating
        // `&(expr)`) keeps it a SINGLE evaluation, so a `snapshot!(&mut place)`
        // forms its `&mut` reborrow once and never hits E0499. The driver reads
        // the captured place from THIS `snapshot_capture_select` argument. (bug/869)
        return quote! {
            {
                #[cfg(trust_wp)]
                {
                    #[allow(unused_imports)]
                    use ::trust_wp_std::ghost::SnapshotCaptureFallback as _;
                    ::trust_wp_std::ghost::snapshot_capture_select(&(#captured_expr)).capture()
                }
                #[cfg(not(trust_wp))]
                {
                    #[allow(unreachable_code, unused_variables, dead_code)]
                    if false {
                        ::trust_wp_std::ghost::Snapshot::capture(&(#captured_expr))
                    } else {
                        ::trust_wp_std::ghost::Snapshot::new_phantom()
                    }
                }
            }
        }
        .into();
    }

    // Use cfg(trust_wp) / cfg(not(trust_wp)) split for the default case so that
    // non-Copy values are not moved at runtime. Under cfg(trust_wp) the verifier
    // sees the real Snapshot::capture; under cfg(not(trust_wp)) an if-false
    // branch preserves type information without evaluating the expression. (#2682)
    quote! {
        {
            #[cfg(trust_wp)]
            {
                ::trust_wp_std::ghost::Snapshot::capture(&(#captured_expr))
            }
            #[cfg(not(trust_wp))]
            {
                #[allow(unreachable_code, unused_variables, dead_code)]
                if false {
                    ::trust_wp_std::ghost::Snapshot::capture(&(#captured_expr))
                } else {
                    ::trust_wp_std::ghost::Snapshot::new_phantom()
                }
            }
        }
    }
    .into()
}

/// Whether `expr` is a place expression or a reference expression — the only
/// syntactic forms that can have `&mut` type and thus need the loan-decoupling
/// snapshot-capture dispatch. Place/reference expressions also always have a
/// fully-known type at macro-expansion time, which the type-directed dispatch
/// requires (a not-yet-inferred type would poison its `&mut` selection). (bug/869)
fn is_place_or_reference_expr(expr: &Expr) -> bool {
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
