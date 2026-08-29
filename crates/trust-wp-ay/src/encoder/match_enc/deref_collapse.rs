// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Rewrites that collapse deref/final wrappers for pattern-bound variables.

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{ExprSort, MatchArm, PureExpr};

/// Collapse `Deref(Var(v))` to `Var(v)` for pattern-bound variables in a
/// match arm body (#2124 AC3).
///
/// When a match arm binds `v` via `Some(v)`, the encoder maps `v` to the
/// destructor application (e.g., `spec_unwrap(result)`). A postcondition like
/// `*v == a[0]` produces `Deref(Var("v"))`, but `encode_deref_or_final` would
/// resolve that to a fresh `v_current` SMT variable disconnected from the
/// binding. This rewriter strips the Deref wrapper so the variable lookup
/// finds the bound destructor term instead.
///
/// `Final(Var(v))` is deliberately NOT stripped here (Final-collapse audit
/// Fix A): this rewriter is sort-blind, and for binders over `&mut`-embedding
/// payloads (e.g. `Some(r)` on `Option<&mut T>`) stripping `^r` to `r`
/// asserts the prophecy inversion `^r == *r` — the adjudicated take_first_mut
/// false accept. Binder-`Final` is left intact so it flows to
/// `encode_deref_or_final`, where the sort-aware fail-closed guard
/// (`final_collapse_guard.rs`) either collapses exactly (pure payloads, via
/// the quantifier-bound Phase-1 fast path) or refuses with an honest error.
///
/// `carrier_bound` (#prophecy-slots Fix B M4) names the subset of `bound`
/// whose BOUND TERM the caller has already observed to be MutRef-carrier
/// sorted. The annotation test below is a syntactic approximation and answers
/// "no" for an UNANNOTATED binder; `carrier_bound` is the authoritative,
/// term-level answer and closes exactly that hole. Callers with no term-level
/// knowledge pass an empty set and get byte-identical legacy behaviour.
#[allow(clippy::too_many_lines)] // Recursive rewriter over PureExpr variants
pub(crate) fn collapse_deref_for_bound_vars(
    expr: &PureExpr,
    bound: &HashSet<&str>,
    carrier_bound: &HashSet<&str>,
) -> PureExpr {
    fn reuse_arc(original: &Arc<PureExpr>, rewritten: PureExpr) -> Arc<PureExpr> {
        if rewritten.ptr_eq_shallow(original.as_ref()) || &rewritten == original.as_ref() {
            Arc::clone(original)
        } else {
            Arc::new(rewritten)
        }
    }

    fn reuse_node(original: &PureExpr, rebuilt: PureExpr) -> PureExpr {
        if rebuilt.ptr_eq_shallow(original) || &rebuilt == original {
            original.clone()
        } else {
            rebuilt
        }
    }

    let rec = |e: &PureExpr| collapse_deref_for_bound_vars(e, bound, carrier_bound);

    match expr {
        // #prophecy-slots (Fix B M1): the strip is declined when the binder's
        // annotation may embed a mutable reference — such a binder is (or may
        // be) a REAL prophecy carrier, and stripping `*r` to `r` would hand
        // the raw carrier to consumers expecting the current value. Declining
        // lets `Deref(Var(r))` flow to `encode_deref_or_final`, whose Phase-1
        // projection arm applies the definitional `mut_ref_current` accessor
        // (mirroring the Fix-A treatment of `Final` below). Blast radius of
        // the decline is confined to ANNOTATED may-embed binders: every such
        // case is handled by wrapper Phase 1 (quantifier-bound) or Phase 1b
        // (annotated `Var`), so the #2124 disconnected-`v_current` class the
        // strip was written for cannot re-open. An UNANNOTATED binder keeps
        // the legacy strip: if its term is carrier-sorted, the stripped `r`
        // is a record-sorted value that can never alias the projected `^r`
        // (a weakening, not an inversion); declining broadly on `None`
        // annotations WOULD re-open #2124.
        //
        // #prophecy-slots (Fix B M4): `carrier_bound` closes the UNANNOTATED
        // hole the paragraph above documents, with the only authority that is
        // not a guess — the binder's ACTUAL bound term sort. The hole is NOT
        // benign for `*r`: the stripped `r` reaches the equality as the whole
        // `(current, final, id)` record, so an Int-level premise clause such
        // as `*first == self@.index_logic(0)` is lifted to a WHOLE-CARRIER
        // equality and its current-value content is lost. (In take_first_mut
        // the lift additionally restored the Int Seq element into the carrier
        // sort, leaving `mut_ref_current(first) ==
        // mut_ref_current(__seq_index_restore_c(view, 0))` against an
        // otherwise-free `__seq_index_restore_c` — vacuous.) Declining hands
        // `Deref(Var(r))` to wrapper Phase 1, which returns the DEFINITIONAL
        // `mut_ref_current(r)`; #2124 cannot re-open, because that arm
        // resolves the BOUND term and never mints a fresh `r_current`.
        PureExpr::Deref(inner)
            if matches!(
                inner.as_ref(),
                PureExpr::Var(n, ann) if bound.contains(n.as_str())
                    && !carrier_bound.contains(n.as_str())
                    && !matches!(
                        ann,
                        Some(a) if crate::encoder::final_collapse_guard::
                            expr_sort_may_embed_mut_ref_syntactic(Some(a))
                    )
            ) =>
        {
            inner.as_ref().clone()
        }
        PureExpr::Deref(inner) => {
            let new_inner = rec(inner);
            reuse_node(expr, PureExpr::Deref(reuse_arc(inner, new_inner)))
        }
        PureExpr::Final(inner) => {
            let new_inner = rec(inner);
            reuse_node(expr, PureExpr::Final(reuse_arc(inner, new_inner)))
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(..) => {
            expr.clone()
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner = rec(inner);
            reuse_node(expr, PureExpr::UnOp(*op, reuse_arc(inner, new_inner)))
        }
        PureExpr::Old(inner) => {
            let new_inner = rec(inner);
            reuse_node(expr, PureExpr::Old(reuse_arc(inner, new_inner)))
        }
        PureExpr::View(inner) => {
            let new_inner = rec(inner);
            reuse_node(expr, PureExpr::View(reuse_arc(inner, new_inner)))
        }
        PureExpr::BinOp(l, op, r) => {
            let new_l = rec(l);
            let new_r = rec(r);
            reuse_node(
                expr,
                PureExpr::BinOp(reuse_arc(l, new_l), *op, reuse_arc(r, new_r)),
            )
        }
        PureExpr::Ite(c, t, e) => {
            let new_c = rec(c);
            let new_t = rec(t);
            let new_e = rec(e);
            reuse_node(
                expr,
                PureExpr::Ite(
                    reuse_arc(c, new_c),
                    reuse_arc(t, new_t),
                    reuse_arc(e, new_e),
                ),
            )
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = rec(receiver);
            let new_args: Vec<PureExpr> = args.iter().map(rec).collect();
            reuse_node(
                expr,
                PureExpr::MethodCall {
                    receiver: reuse_arc(receiver, new_receiver),
                    method: method.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::LogicFnCall { name, args } => {
            let new_args: Vec<PureExpr> = args.iter().map(rec).collect();
            reuse_node(
                expr,
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: new_args,
                },
            )
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let rebuilt = collapse_deref_quantifier(
                var,
                var_sort.as_ref(),
                body,
                triggers,
                bound,
                carrier_bound,
                true,
            );
            reuse_node(expr, rebuilt)
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let rebuilt = collapse_deref_quantifier(
                var,
                var_sort.as_ref(),
                body,
                triggers,
                bound,
                carrier_bound,
                false,
            );
            reuse_node(expr, rebuilt)
        }
        PureExpr::Match { scrutinee, arms } => {
            let rebuilt = collapse_deref_match(scrutinee, arms, bound, carrier_bound);
            reuse_node(expr, rebuilt)
        }
        PureExpr::Let { var, value, body } => {
            let new_value = rec(value);
            let mut inner = bound.clone();
            inner.remove(var.as_str());
            let mut inner_carrier = carrier_bound.clone();
            inner_carrier.remove(var.as_str());
            let new_body = collapse_deref_for_bound_vars(body, &inner, &inner_carrier);
            reuse_node(
                expr,
                PureExpr::Let {
                    var: var.clone(),
                    value: reuse_arc(value, new_value),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetAssume { assumption, body } => {
            let new_assumption = rec(assumption);
            let new_body = rec(body);
            reuse_node(
                expr,
                PureExpr::LetAssume {
                    assumption: reuse_arc(assumption, new_assumption),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::LetObligation { obligation, body } => {
            let new_obligation = rec(obligation);
            let new_body = rec(body);
            reuse_node(
                expr,
                PureExpr::LetObligation {
                    obligation: reuse_arc(obligation, new_obligation),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        PureExpr::Closure { params, body } => {
            let mut inner = bound.clone();
            let mut inner_carrier = carrier_bound.clone();
            for (name, _) in params {
                inner.remove(name.as_str());
                inner_carrier.remove(name.as_str());
            }
            let new_body = collapse_deref_for_bound_vars(body, &inner, &inner_carrier);
            reuse_node(
                expr,
                PureExpr::Closure {
                    params: params.clone(),
                    body: reuse_arc(body, new_body),
                },
            )
        }
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => expr.clone(),
    }
}

/// Rewrite quantifier body/triggers with deref-collapse, shadowing the
/// quantifier-bound variable. Preserves Arc sharing when no structural
/// changes occur in the body.
fn collapse_deref_quantifier(
    var: &str,
    var_sort: Option<&ExprSort>,
    body: &Arc<PureExpr>,
    triggers: &[Vec<PureExpr>],
    bound: &HashSet<&str>,
    carrier_bound: &HashSet<&str>,
    is_forall: bool,
) -> PureExpr {
    fn reuse_arc(original: &Arc<PureExpr>, rewritten: PureExpr) -> Arc<PureExpr> {
        if rewritten.ptr_eq_shallow(original.as_ref()) || &rewritten == original.as_ref() {
            Arc::clone(original)
        } else {
            Arc::new(rewritten)
        }
    }

    let mut inner = bound.clone();
    inner.remove(var);
    let mut inner_carrier = carrier_bound.clone();
    inner_carrier.remove(var);
    let rewritten_body = reuse_arc(
        body,
        collapse_deref_for_bound_vars(body, &inner, &inner_carrier),
    );
    let rewritten_triggers = triggers
        .iter()
        .map(|trig| {
            trig.iter()
                .map(|t| collapse_deref_for_bound_vars(t, &inner, &inner_carrier))
                .collect()
        })
        .collect();
    let cloned_sort = var_sort.cloned();
    if is_forall {
        PureExpr::Forall {
            var: var.to_string(),
            var_sort: cloned_sort,
            body: rewritten_body,
            triggers: rewritten_triggers,
        }
    } else {
        PureExpr::Exists {
            var: var.to_string(),
            var_sort: cloned_sort,
            body: rewritten_body,
            triggers: rewritten_triggers,
        }
    }
}

/// Rewrite nested match expressions with deref-collapse, collecting inner
/// arm bindings for shadowing. Preserves Arc sharing for the scrutinee
/// when no structural changes occur.
fn collapse_deref_match(
    scrutinee: &Arc<PureExpr>,
    arms: &[MatchArm],
    bound: &HashSet<&str>,
    carrier_bound: &HashSet<&str>,
) -> PureExpr {
    fn reuse_arc(original: &Arc<PureExpr>, rewritten: PureExpr) -> Arc<PureExpr> {
        if rewritten.ptr_eq_shallow(original.as_ref()) || &rewritten == original.as_ref() {
            Arc::clone(original)
        } else {
            Arc::new(rewritten)
        }
    }

    PureExpr::Match {
        scrutinee: reuse_arc(
            scrutinee,
            collapse_deref_for_bound_vars(scrutinee, bound, carrier_bound),
        ),
        arms: arms
            .iter()
            .map(|arm| {
                let mut inner = bound.clone();
                // A nested arm binder SHADOWS the outer name, and this layer
                // has no term for it — drop any inherited carrier claim so the
                // decline is never asserted on a binder we did not inspect.
                let mut inner_carrier = carrier_bound.clone();
                for name in arm.pattern.bound_names() {
                    inner.insert(name);
                    inner_carrier.remove(name);
                }
                MatchArm {
                    pattern: arm.pattern.clone(),
                    body: collapse_deref_for_bound_vars(&arm.body, &inner, &inner_carrier),
                }
            })
            .collect(),
    }
}

#[cfg(test)]
mod prophecy_slots_m4_tests {
    //! #prophecy-slots (Fix B M4) — the rewriter-level pins.
    //!
    //! M4's whole mechanism is one predicate: a match binder whose BOUND TERM
    //! is a prophecy carrier must keep its `Deref`, so wrapper Phase 1 can
    //! apply the definitional `mut_ref_current` accessor. Everything else must
    //! be byte-identical to the legacy lane.

    use std::{collections::HashSet, sync::Arc};

    use trust_wp_core::formula::{ExprSort, MatchArm, Pattern, PureExpr};

    use super::collapse_deref_for_bound_vars;

    fn deref_of(name: &str, ann: Option<ExprSort>) -> PureExpr {
        PureExpr::Deref(Arc::new(PureExpr::Var(name.to_string(), ann)))
    }

    fn set(names: &[&'static str]) -> HashSet<&'static str> {
        names.iter().copied().collect()
    }

    /// THE M4 PIN. A binder the caller has observed to be carrier-sorted keeps
    /// its `Deref`. Without this the stripped `r` reaches the equality as the
    /// whole `(current, final, id)` record and an Int-level clause such as
    /// `*first == self@.index_logic(0)` is silently lifted to a whole-carrier
    /// equality, losing its current-value content (the take_first_mut
    /// residual). Contract-parsed pattern binders arrive UNANNOTATED, so the
    /// annotation test alone cannot see this — hence the term-level set.
    #[test]
    fn m4_carrier_binder_declines_the_deref_strip() {
        let expr = deref_of("r", None);
        let bound = set(&["r"]);
        let carrier = set(&["r"]);
        let out = collapse_deref_for_bound_vars(&expr, &bound, &carrier);
        assert_eq!(
            out, expr,
            "a carrier-sorted binder must keep `*r` so wrapper Phase 1 can \
             project `mut_ref_current(r)`"
        );
    }

    /// Over-reach control (#2124): with NO carrier claim the legacy strip is
    /// byte-identical — `*v` still collapses to the bound payload term. This
    /// is the class the strip was written for and M4 must not disturb it.
    #[test]
    fn m4_non_carrier_binder_keeps_the_legacy_deref_strip() {
        let expr = deref_of("v", None);
        let bound = set(&["v"]);
        let out = collapse_deref_for_bound_vars(&expr, &bound, &HashSet::new());
        assert_eq!(
            out,
            PureExpr::Var("v".to_string(), None),
            "an unannotated non-carrier binder must keep the legacy strip"
        );
    }

    /// The M1 annotation lane is untouched: an ANNOTATED may-embed binder
    /// still declines even with an empty carrier set.
    #[test]
    fn m4_annotated_may_embed_binder_still_declines_without_a_carrier_claim() {
        let expr = deref_of("r", Some(ExprSort::MutRef(Box::new(ExprSort::Int))));
        let bound = set(&["r"]);
        let out = collapse_deref_for_bound_vars(&expr, &bound, &HashSet::new());
        assert_eq!(out, expr, "M1's annotation decline must still fire");
    }

    /// A binder that is NOT in `bound` is never touched, carrier or not —
    /// the rewriter only ever rewrites the arm's own binders.
    #[test]
    fn m4_unbound_var_is_never_stripped() {
        let expr = deref_of("x", None);
        let out = collapse_deref_for_bound_vars(&expr, &HashSet::new(), &set(&["x"]));
        assert_eq!(out, expr);
    }

    /// Hygiene: a NESTED arm binder SHADOWS the outer name, and that inner
    /// layer has no term for it. The inherited carrier claim must be dropped
    /// so the decline is never asserted about a binder we did not inspect —
    /// the shadowed name goes back to the legacy strip.
    #[test]
    fn m4_shadowing_arm_binder_drops_the_inherited_carrier_claim() {
        let inner_match = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("o".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                },
                body: deref_of("r", None),
            }],
        };
        let out = collapse_deref_for_bound_vars(&inner_match, &HashSet::new(), &set(&["r"]));
        let PureExpr::Match { arms, .. } = &out else {
            panic!("expected a Match, got {out:?}");
        };
        assert_eq!(
            arms[0].body,
            PureExpr::Var("r".to_string(), None),
            "the shadowing binder must fall back to the legacy strip"
        );
    }

    /// Shadowing hygiene, `Let` form: a `Let` removes the name from `bound`
    /// AND from the carrier claim, so the body is left completely alone —
    /// neither stripped (it is no longer an arm binder) nor claimed.
    #[test]
    fn m4_let_shadowing_drops_the_inherited_carrier_claim() {
        let expr = PureExpr::Let {
            var: "r".to_string(),
            value: Arc::new(PureExpr::Int(1)),
            body: Arc::new(deref_of("r", None)),
        };
        let out = collapse_deref_for_bound_vars(&expr, &set(&["r"]), &set(&["r"]));
        let PureExpr::Let { body, .. } = &out else {
            panic!("expected a Let, got {out:?}");
        };
        assert_eq!(
            body.as_ref(),
            &deref_of("r", None),
            "a `Let`-shadowed name is neither an arm binder nor a carrier claim"
        );
    }
}
