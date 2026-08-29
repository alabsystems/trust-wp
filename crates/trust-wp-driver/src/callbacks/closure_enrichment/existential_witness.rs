// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ground witnessing of existential postcondition goals.
//!
//! An `FnMut`-adapter contract such as `call_fnmut`'s
//!
//! ```text
//! #[ensures(exists<st1, st2, r>
//!     f.postcondition_mut((), st1, r) &&
//!     st1.postcondition_mut((), st2, result) &&
//!     resolve(st2))]
//! ```
//!
//! is an existential GOAL whose witnesses are exactly the intermediate closure
//! states the body already produced (`f`'s post-state after each `f()` call).
//! ay cannot discharge it by E-matching because the negated-goal `forall`'s
//! multi-trigger never joins the two `postcondition_mut` premise facts
//! (`quantifier-ematching-exists-incomplete`).
//!
//! Providing concrete terms for an existential GOAL is unconditionally sound:
//! `P(W) ⊢ ∃X. P(X)`. This pass binds each existential variable to a post-state
//! or result subterm of an ACTUAL `postcondition_mut` premise fact and replaces
//! the quantified goal with that ground instance. If no complete, consistent
//! assignment is found the goal is left untouched (a conservative no-op) — the
//! pass can only turn an otherwise-`unknown` existential goal into a discharged
//! one; it never invents premises and never weakens a `forall`.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{BinOp, PureExpr};

use super::strip_deref_wrappers;

/// A `postcondition_mut(receiver, args, post_state, result)` application, either
/// a ground premise fact or a (partly-quantified) goal conjunct.
struct PcmApp<'a> {
    receiver: &'a PureExpr,
    args: &'a PureExpr,
    post: &'a PureExpr,
    result: &'a PureExpr,
}

fn as_pcm_app(expr: &PureExpr) -> Option<PcmApp<'_>> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "postcondition_mut" && args.len() == 3 => Some(PcmApp {
            receiver,
            args: &args[0],
            post: &args[1],
            result: &args[2],
        }),
        _ => None,
    }
}

/// Replace existential postcondition goals with ground instances witnessed from
/// the `postcondition_mut` facts already available among the premises.
///
/// Returns the number of goals rewritten. Operates only on `goals`
/// (`effective_ensures`); premises are read-only fact sources.
pub(in crate::callbacks) fn witness_existential_postcondition_goals(
    requires: &[PureExpr],
    goals: &mut [PureExpr],
) -> usize {
    let facts: Vec<PcmApp<'_>> = requires.iter().filter_map(as_pcm_app).collect();
    if facts.is_empty() {
        return 0;
    }
    let mut count = 0;
    for goal in goals.iter_mut() {
        if let Some(ground) = try_witness_existential_goal(goal, &facts) {
            *goal = ground;
            count += 1;
        }
    }
    count
}

/// Trivialize `resolve(<concrete closure-env tuple>)` conjuncts inside FnMut-
/// adapter existential ASSUMPTIONS (e.g. `call_fnmut`'s enriched ensures at a
/// call site).
///
/// After the adapter's `exists<.., st2, ..> .. && resolve(st2)` assumption has
/// its post-state `st2` bound to a concrete closure env such as `tuple1(^x)`,
/// the residual `resolve(tuple1(^x))` is spurious: the env already holds the
/// prophecy-final capture `^x`, so re-resolving it should be a no-op. ay's
/// `encode_resolve` instead distributes an extra `Final` over the tuple
/// (`Final(tuple1(^x)) = tuple1(^^x)`), asserting `tuple1(x_final_current) ==
/// tuple1(x_final_final)` and collapsing the two call layers into contradictory
/// premises — flagged (correctly) as a vacuous proof (closures/07 test_fnmut2).
///
/// Resolving a concrete final closure-env value conveys no new information, so
/// replacing it with `true` is sound (it only weakens an assumption). Gated to
/// expressions that carry a `postcondition_mut` chain (the FnMut-adapter shape)
/// so ordinary `resolve(&mut ...)` obligations are untouched. Returns the number
/// of `resolve` atoms trivialized.
pub(in crate::callbacks) fn trivialize_closure_env_resolves_in_assumptions(
    requires: &mut [PureExpr],
) -> usize {
    let mut count = 0;
    for req in requires.iter_mut() {
        if !expr_contains_postcondition_mut(req) {
            continue;
        }
        let rewritten = req.rewrite_bottom_up(|node| match &node {
            PureExpr::LogicFnCall { name, args }
                if name == "resolve" && args.len() == 1 && is_tuple_ctor(&args[0]) =>
            {
                count += 1;
                PureExpr::Bool(true)
            }
            _ => node,
        });
        *req = rewritten;
    }
    count
}

/// True iff `expr` is a tuple constructor logic-fn application (a concrete
/// closure environment).
fn is_tuple_ctor(expr: &PureExpr) -> bool {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity;
    matches!(expr, PureExpr::LogicFnCall { name, args }
        if tuple_logic_fn_arity(name) == Some(args.len()))
}

/// True iff `expr` contains a `postcondition_mut` method call anywhere.
fn expr_contains_postcondition_mut(expr: &PureExpr) -> bool {
    expr.any_recursive(
        |e| matches!(e, PureExpr::MethodCall { method, .. } if method == "postcondition_mut"),
    )
}

/// Try to discharge one existential goal by binding its bound variables to
/// subterms of the premise facts. Returns the ground instance on success.
fn try_witness_existential_goal(goal: &PureExpr, facts: &[PcmApp<'_>]) -> Option<PureExpr> {
    // Peel the existential prefix, collecting bound variable names.
    let mut bound: HashSet<String> = HashSet::new();
    let mut body = goal;
    while let PureExpr::Exists {
        var, body: inner, ..
    } = body
    {
        bound.insert(var.clone());
        body = inner;
    }
    if bound.is_empty() {
        return None;
    }

    // Flatten the top-level conjunction. Every conjunct must be either a
    // `postcondition_mut` application (a chain link to witness) or a
    // `resolve(<bound var>)` (trivially true for a by-value closure post-state —
    // see encoder::quantifier::encode_resolve). Anything else and we decline,
    // so unfamiliar existential goal shapes are left exactly as-is.
    let mut atoms: Vec<&PureExpr> = Vec::new();
    flatten_and(body, &mut atoms);
    let mut chain: Vec<PcmApp<'_>> = Vec::new();
    for atom in &atoms {
        if let Some(app) = as_pcm_app(atom) {
            chain.push(app);
        } else if !is_resolve_of_bound_var(atom, &bound) {
            return None;
        }
    }
    if chain.is_empty() {
        return None;
    }

    // Backtracking-unify each chain link against a premise fact.
    let mut subst: HashMap<String, PureExpr> = HashMap::new();
    if !match_chain(&chain, 0, facts, &bound, &mut subst) {
        return None;
    }
    // Require a complete assignment: every bound variable witnessed.
    if !bound.iter().all(|v| subst.contains_key(v)) {
        return None;
    }

    // Build the ground conjunction: substitute witnesses into the chain links;
    // discharge each `resolve(<bound var>)` to `true`.
    let ground = atoms
        .into_iter()
        .map(|atom| {
            if is_resolve_of_bound_var(atom, &bound) {
                PureExpr::Bool(true)
            } else {
                atom.substitute(&subst)
            }
        })
        .reduce(|acc, p| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(p)))?;
    Some(ground)
}

/// Flatten a right/left-nested `&&` chain into its conjuncts.
fn flatten_and<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    if let PureExpr::BinOp(l, BinOp::And, r) = expr {
        flatten_and(l, out);
        flatten_and(r, out);
    } else {
        out.push(expr);
    }
}

/// True iff `atom` is `resolve(v)` for some existentially-bound `v`.
fn is_resolve_of_bound_var(atom: &PureExpr, bound: &HashSet<String>) -> bool {
    matches!(atom, PureExpr::LogicFnCall { name, args }
        if name == "resolve"
            && args.len() == 1
            && matches!(&args[0], PureExpr::Var(v, _) if bound.contains(v)))
}

/// Backtracking match of chain links (in order) against premise facts, growing a
/// consistent witness substitution over the bound variables.
fn match_chain(
    chain: &[PcmApp<'_>],
    idx: usize,
    facts: &[PcmApp<'_>],
    bound: &HashSet<String>,
    subst: &mut HashMap<String, PureExpr>,
) -> bool {
    if idx == chain.len() {
        return true;
    }
    let link = &chain[idx];
    for fact in facts {
        let mut trial = subst.clone();
        if unify(link.receiver, fact.receiver, bound, &mut trial)
            && unify(link.args, fact.args, bound, &mut trial)
            && unify(link.post, fact.post, bound, &mut trial)
            && unify(link.result, fact.result, bound, &mut trial)
            && match_chain(chain, idx + 1, facts, bound, &mut trial)
        {
            *subst = trial;
            return true;
        }
    }
    false
}

/// Strip `Deref` wrappers without cloning. The ay encoding canonicalizes
/// `Deref(x)` and `x` to the same term for these abstract closure states, so
/// matching must too.
fn strip_deref_ref(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::Deref(inner) => strip_deref_ref(inner),
        _ => expr,
    }
}

/// Match `pattern` (which may mention bound variables) against ground `fact`,
/// binding bound variables in `subst`. Structural, modulo `Deref` wrappers.
fn unify(
    pattern: &PureExpr,
    fact: &PureExpr,
    bound: &HashSet<String>,
    subst: &mut HashMap<String, PureExpr>,
) -> bool {
    let pattern = strip_deref_ref(pattern);
    let fact = strip_deref_ref(fact);

    if let PureExpr::Var(name, _) = pattern {
        if bound.contains(name) {
            // Store the normalized (deref-stripped) fact as the witness so the
            // substituted goal encodes identically to the matched premise fact.
            let witness = strip_deref_wrappers(fact);
            return match subst.get(name) {
                Some(existing) => ground_eq(existing, fact),
                None => {
                    subst.insert(name.clone(), witness);
                    true
                }
            };
        }
    }

    match (pattern, fact) {
        (PureExpr::Var(a, _), PureExpr::Var(b, _)) => a == b,
        (PureExpr::Int(a), PureExpr::Int(b)) => a == b,
        (PureExpr::Bool(a), PureExpr::Bool(b)) => a == b,
        (PureExpr::Final(p), PureExpr::Final(f)) => unify(p, f, bound, subst),
        (PureExpr::View(p), PureExpr::View(f)) => unify(p, f, bound, subst),
        (PureExpr::Old(p), PureExpr::Old(f)) => unify(p, f, bound, subst),
        (
            PureExpr::LogicFnCall { name: pn, args: pa },
            PureExpr::LogicFnCall {
                name: fnm,
                args: fa,
            },
        ) if pn == fnm && pa.len() == fa.len() => {
            pa.iter().zip(fa).all(|(x, y)| unify(x, y, bound, subst))
        }
        (
            PureExpr::MethodCall {
                receiver: pr,
                method: pm,
                args: pa,
            },
            PureExpr::MethodCall {
                receiver: fr,
                method: fm,
                args: fa,
            },
        ) if pm == fm && pa.len() == fa.len() => {
            unify(pr, fr, bound, subst) && pa.iter().zip(fa).all(|(x, y)| unify(x, y, bound, subst))
        }
        _ => false,
    }
}

/// Structural equality of two ground terms, modulo `Deref` wrappers. Used to
/// check that a bound variable's repeated occurrences agree.
fn ground_eq(a: &PureExpr, b: &PureExpr) -> bool {
    let a = strip_deref_ref(a);
    let b = strip_deref_ref(b);
    match (a, b) {
        (PureExpr::Var(x, _), PureExpr::Var(y, _)) => x == y,
        (PureExpr::Int(x), PureExpr::Int(y)) => x == y,
        (PureExpr::Bool(x), PureExpr::Bool(y)) => x == y,
        (PureExpr::Final(x), PureExpr::Final(y)) => ground_eq(x, y),
        (PureExpr::View(x), PureExpr::View(y)) => ground_eq(x, y),
        (PureExpr::Old(x), PureExpr::Old(y)) => ground_eq(x, y),
        (
            PureExpr::LogicFnCall { name: n1, args: a1 },
            PureExpr::LogicFnCall { name: n2, args: a2 },
        ) if n1 == n2 && a1.len() == a2.len() => a1.iter().zip(a2).all(|(x, y)| ground_eq(x, y)),
        (
            PureExpr::MethodCall {
                receiver: r1,
                method: m1,
                args: a1,
            },
            PureExpr::MethodCall {
                receiver: r2,
                method: m2,
                args: a2,
            },
        ) if m1 == m2 && a1.len() == a2.len() => {
            ground_eq(r1, r2) && a1.iter().zip(a2).all(|(x, y)| ground_eq(x, y))
        }
        _ => false,
    }
}
