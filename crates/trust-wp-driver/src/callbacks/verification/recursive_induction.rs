// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sound, well-founded recursive-induction-hypothesis (IH) injection for the
//! verification of a recursive `#[logic]` function's *own* postcondition.
//!
//! # The problem
//!
//! When a recursive logic function `f` with `#[ensures]` is checked against its
//! body, the body contains self-recursive calls `f(A)`. To discharge `f`'s
//! postcondition the prover needs the *induction hypothesis*: that the
//! postcondition already holds at the recursive arguments `A`. The previous
//! mechanism supplied this by emitting `f`'s spec axiom
//! (`∀p. requires(p) ⇒ ensures(p)`) in `Default` mode and relying on E-matching
//! to instantiate it at the recursive call term `f(A)`. That is **UNSOUND**: it
//! hands out the IH for `A` *without checking that `A` is "smaller" than the
//! current arguments*. A logic lemma that "recurses" on its **own** arguments
//! (variant does not decrease) then proves an arbitrary FALSE postcondition by
//! pure circularity — a demonstrated false-accept.
//!
//! # The sound replacement
//!
//! We delete the ungated spec axiom for `f` during its own postcondition check
//! (the caller clears `f`'s `ensures` in the axiom set) and instead inject, for
//! each self-recursive call `f(A)`, the **variant-guarded** hypothesis:
//!
//! ```text
//!   ( 0 ≤ m[A]  ∧  m[A] < m[P]  ∧  requires[A] )  ⇒  ensures[A]
//! ```
//!
//! where `P` are the current parameters, `A` the recursive-call arguments,
//! `m` the declared `#[variant]` measure, `[A]` the simultaneous substitution
//! `P ↦ A`, and (for value-returning `f`) `result` inside `ensures[A]` is
//! replaced by the recursive call value `f(A)` itself (NOT `f(P)` — conflating
//! the two was the prior false-accept).
//!
//! ## Why this can never admit a false-accept
//!
//! For ANY integer-valued measure `m`, the relation `R(y,x) := 0 ≤ m(y) < m(x)`
//! is well-founded (a strictly-decreasing chain of non-negative integers is
//! finite). Well-founded induction over `R` states:
//!
//! ```text
//!   ( ∀x. (∀y. R(y,x) ⇒ P(y)) ⇒ P(x) )  ⊢  ∀x. P(x)
//! ```
//!
//! The hypothesis we inject is exactly `(∀y. R(y,P) ⇒ P(y))` instantiated at the
//! single witness `y := A` — i.e. a *logical consequence* of the inductive-step
//! antecedent that well-founded induction entitles us to assume. Hence: if the
//! prover discharges `ensures(P)` using this hypothesis, it has discharged the
//! inductive step, so `∀x. P(x)` genuinely holds. The argument is independent of
//! *which* expression `m` or `A` is: a wrong/non-decreasing `m` or `A` merely
//! makes the guard unsatisfiable (the IH never fires ⇒ incompleteness), it can
//! never make an invalid lemma provable.
//!
//! Two soundness obligations the construction must (and does) meet:
//!  1. `m` must be **integer**-valued, so `R` is well-founded — over the reals
//!     `0 ≤ y < x` has infinite descending chains. [`is_integer_measure`] only
//!     accepts syntactically-integer measures (int literals, int params,
//!     `+`/`-`/`*` thereof, `.len()`), excluding `Real`/float measures.
//!  2. The lower bound `0 ≤ m[A]` MUST be part of the guard (a bare `m[A] < m[P]`
//!     over integers is not well-founded). It always is.
//!
//! # The no-variant case: structural induction
//!
//! A recursive logic fn with NO `#[variant]` gets the STRUCTURAL
//! (subterm-descent) scheme instead: when the body destructures an ADT
//! parameter with `match` and recurses on a constructor-field binder, the
//! well-founded relation is the strict-subterm order on finite constructor
//! trees and the injected hypothesis is tester-guarded via a `Match` wrapper
//! (ground — no quantifier). See [`structural`] for the scheme, its soundness
//! argument, and the precise fail-closed conditions under which it emits
//! nothing. Lexicographic (multi-)variants remain unsupported (no IH).

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::{
    formula::{resolve_sort_name, BinOp, CaptureAvoidingSubstOptions, ExprSort, PureExpr},
    logic::{AdtDecls, LogicFnDef},
};

mod structural;

/// Build the induction hypotheses for `logic_fn`'s own postcondition
/// verification: variant-guarded (exactly one integer `#[variant]`) or
/// structural subterm-descent (no variant; see [`structural`]). Returns an
/// empty vec (inject nothing) whenever the sound preconditions are not met —
/// incompleteness is always preferred to any soundness risk.
pub(in crate::callbacks) fn build_recursive_induction_hypotheses(
    logic_fn: &LogicFnDef,
    adt_decls: Option<&AdtDecls>,
) -> Vec<PureExpr> {
    if !logic_fn.is_recursive() || logic_fn.ensures().is_empty() {
        return Vec::new();
    }

    // Route on the declared `#[variant]`s:
    //  * exactly one  -> the integer-measure scheme below (unchanged);
    //  * none         -> the STRUCTURAL (subterm-descent) scheme, sound for
    //                    recursion that descends through match-arm constructor
    //                    binders of an ADT parameter (see
    //                    `structural::build_structural_induction_hypotheses`);
    //  * two or more  -> lexicographic variants are conservatively unsupported:
    //                    no IH is injected, so the postcondition becomes
    //                    incomplete (sound) rather than relying on the deleted
    //                    ungated axiom.
    let variants = logic_fn.variants();
    if variants.is_empty() {
        return structural::build_structural_induction_hypotheses(logic_fn, adt_decls);
    }
    if variants.len() != 1 {
        return Vec::new();
    }
    let variant = &variants[0];
    let params = logic_fn.params();
    let param_sorts = logic_fn.param_sorts();

    // Well-foundedness gate: the measure must be integer-sorted (see module
    // docs, obligation 1).
    if !is_integer_measure(variant, params, param_sorts) {
        return Vec::new();
    }

    let mut calls = Vec::new();
    collect_self_calls(logic_fn.body(), logic_fn, &HashMap::new(), &mut calls);
    if calls.is_empty() {
        return Vec::new();
    }

    let param_set: HashSet<&str> = params.iter().map(String::as_str).collect();
    let zero = PureExpr::Int(0);
    let mut hypotheses = Vec::new();
    let mut integrality = Vec::new();
    for call in calls {
        let PureExpr::LogicFnCall { args, .. } = &call else {
            continue;
        };
        // Substitution P ↦ A requires matching arity. A mismatch means we cannot
        // soundly form `m[A]`/`requires[A]`/`ensures[A]`, so skip this call.
        if args.len() != params.len() {
            continue;
        }
        // Every recursive-call argument must be a PARAMETER-ONLY expression.
        // `collect_self_calls` already resolved `let`-bound locals through the
        // binding environment; anything still free that is not a parameter
        // (match-arm binders, quantifier vars, unresolvable locals) would
        // smuggle a body-local name into the IH, where it decouples from the
        // value it named in the body — e.g. vcgen's shadowed
        // `let s = s.remove(..)` used to yield the identity substitution
        // {s ↦ s} and the vacuous guard `len(s) < len(s)`. Emitting NO IH for
        // such a call is the sound fallback (fewer assumptions).
        if args.iter().any(|a| {
            a.free_vars()
                .iter()
                .any(|v| !param_set.contains(v.as_str()))
        }) {
            continue;
        }
        let subst: HashMap<String, PureExpr> =
            params.iter().cloned().zip(args.iter().cloned()).collect();

        let variant_at_args = variant.substitute(&subst);
        let variant_at_params = variant.clone();

        // Guard: 0 ≤ m[A]  ∧  m[A] < m[P]  ∧  requires[A]
        let mut guard = Vec::with_capacity(2 + logic_fn.requires().len());
        guard.push(binop(zero.clone(), BinOp::Le, variant_at_args.clone()));
        guard.push(binop(variant_at_args.clone(), BinOp::Lt, variant_at_params));
        for req in logic_fn.requires() {
            guard.push(req.substitute(&subst));
        }

        // Conclusion: ensures[A], with `result` ↦ the recursive call value f(A).
        // For unit-returning lemmas `ensures` never mentions `result`, so the
        // extra binding is inert; for value-returning lemmas it is the value of
        // the RECURSIVE call (the `call` term), which is the only sound choice.
        let mut concl_subst = subst.clone();
        concl_subst.insert("result".to_string(), call.clone());
        let conclusion: Vec<PureExpr> = logic_fn
            .ensures()
            .iter()
            .map(|e| e.substitute(&concl_subst))
            .collect();

        hypotheses.push(binop(and_all(guard), BinOp::Implies, and_all(conclusion)));

        // Integrality of the measure across a literal decrement. When the
        // recursion steps `m[P] - k` (k a positive literal), `0 ≤ m[A]` is
        // implied by `m[P] > k - 1`; over the RATIONALS a certificate checker
        // replays in, it is not, so the step discharging the IH's own `0 ≤
        // m[A]` guard degrades to an unverified trust rule. The same
        // `is_integer_measure` gate the IH's well-foundedness rests on already
        // established that `m` is integer-sorted, so the stated disjunction is
        // VALID: it excludes no model and can strengthen nothing. It is
        // spelled with `m[P]` rather than `m[A] ≤ -1` because the solver
        // normalises the latter to exactly this, and a certificate step can
        // only resolve against an assertion it can recognise.
        if let Some(step) = literal_decrement(&variant_at_args, variant) {
            integrality.push(binop(
                binop(zero.clone(), BinOp::Le, variant_at_args),
                BinOp::Or,
                binop(variant.clone(), BinOp::Le, PureExpr::Int(step - 1)),
            ));
        }
    }
    hypotheses.extend(integrality);

    hypotheses
}

/// Conservative syntactic check that `expr` denotes an integer measure.
///
/// Accepts only: integer literals; parameters whose sort is `Int` (or
/// unannotated, which defaults to `Int`); `+`/`-`/`*` over such; and `.len()`
/// method calls (always integer-valued). Everything else — in particular
/// `Float`/`Real`-sorted terms and unknown variables — returns `false`. This is
/// the well-foundedness gate (module-doc obligation 1): a measure that slips
/// through must still be integer-valued, never real, so the guarded order
/// `0 ≤ m[A] < m[P]` is well-founded.
fn is_integer_measure(
    expr: &PureExpr,
    params: &[String],
    param_sorts: &[Option<ExprSort>],
) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::Var(name, sort) => {
            if let Some(s) = sort {
                return is_integer_sort(s);
            }
            // Fall back to the parameter sort hint.
            match params.iter().position(|p| p == name) {
                Some(idx) => match param_sorts.get(idx) {
                    // No hint ⇒ the documented default sort is Int.
                    None | Some(None) => true,
                    Some(Some(s)) => is_integer_sort(s),
                },
                None => false,
            }
        }
        PureExpr::BinOp(l, op, r) => {
            matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul)
                && is_integer_measure(l, params, param_sorts)
                && is_integer_measure(r, params, param_sorts)
        }
        // `len()` on a sequence/collection view is integer-valued regardless of
        // receiver sort.
        PureExpr::MethodCall { method, .. } => method == "len" || method.ends_with("::len"),
        _ => false,
    }
}

/// Whether an [`ExprSort`] is encoded by the SMT backend as the integer sort.
///
/// This MUST stay aligned with the encoder's `is_int_model_type`
/// (trust-wp-ay `sort_mapping.rs`), which decides that a named ADT is lowered to
/// SMT `Int`. The well-foundedness of `0 ≤ m[A] < m[P]` requires the measure to
/// land on SMT `Int` (not `Real`); accepting only sorts that lower to `Int`
/// keeps the guard well-founded AND avoids a sort-mismatch encoding error.
/// `creusot`'s mathematical `Int` interns its `Datatype` name as a qualified
/// path (`creusot_std::Int`), so we compare on the bare (last `::`-segment)
/// name. Type parameters, floats, sequences, etc. are rejected (no IH).
pub(in crate::callbacks) fn is_integer_sort(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::Int => true,
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let bare = name.rsplit("::").next().unwrap_or(name.as_str());
            is_int_model_bare_name(bare)
        }
        _ => false,
    }
}

/// Bare ADT names the encoder lowers to SMT `Int` (mirror of trust-wp-ay
/// `is_int_model_type`). All entries are encoded as `Int`, so a measure of such
/// a type yields a well-founded `0 ≤ · < ·` guard.
fn is_int_model_bare_name(name: &str) -> bool {
    matches!(
        name,
        "Int"
            | "Snapshot"
            | "Ghost"
            | "Duration"
            | "Instant"
            | "HashSet"
            | "GhostSet"
            | "FSet"
            | "NonNeg"
            | "RangeInclusive"
            | "NonZeroU8"
            | "NonZeroU16"
            | "NonZeroU32"
            | "NonZeroU64"
            | "NonZeroU128"
            | "NonZeroUsize"
            | "NonZeroI8"
            | "NonZeroI16"
            | "NonZeroI32"
            | "NonZeroI64"
            | "NonZeroI128"
            | "NonZeroIsize"
            | "Rc"
            | "Arc"
            | "Box"
    )
}

/// Whether `call_name` (from a `LogicFnCall` in the body) names `logic_fn`
/// itself. Mirrors the recursion-detection convention (short name, with
/// crate-qualified and `::`-suffix fallbacks plus the `Self::` form).
fn is_self_call_name(call_name: &str, logic_fn: &LogicFnDef) -> bool {
    let short = logic_fn.name();
    call_name == short
        || call_name == logic_fn.full_path()
        || call_name.strip_prefix("Self::") == Some(short)
        || call_name
            .rsplit_once("::")
            .is_some_and(|(_, tail)| tail == short)
}

/// Collect every self-recursive `LogicFnCall` node in `body` (full traversal),
/// resolving `let`-bound locals in the collected call to parameter terms.
///
/// `env` maps each in-scope `let`-bound name to its value expression, already
/// resolved against the enclosing environment at bind time (so env values only
/// mention parameters or *unresolvable* outer locals, never other `let`
/// names). Innermost bindings win: a `let s = s.remove(x)` that SHADOWS the
/// parameter `s` overwrites the (empty) outer entry, and the collected
/// self-call `f(s)` resolves to `f(s.remove(x))` in parameter terms — without
/// this, the shadow made the P ↦ A substitution the identity and the IH guard
/// the vacuous `m(s) < m(s)` (bug/vcgen).
///
/// Names bound by binders we do not resolve through — match-arm patterns,
/// quantifier variables, closure params — SHADOW (remove) env entries for
/// their scope, so an outer `let` value is never wrongly substituted for an
/// inner binder occurrence. Calls whose args still mention such locals are
/// filtered out by the caller's parameter-only check (no IH — sound).
fn collect_self_calls(
    body: &PureExpr,
    logic_fn: &LogicFnDef,
    env: &HashMap<String, PureExpr>,
    out: &mut Vec<PureExpr>,
) {
    match body {
        PureExpr::LogicFnCall { name, args } => {
            if is_self_call_name(name, logic_fn) {
                let resolved = if env.is_empty() {
                    body.clone()
                } else {
                    body.substitute_capture_avoiding(env, &CaptureAvoidingSubstOptions::default())
                };
                out.push(resolved);
            }
            for a in args {
                collect_self_calls(a, logic_fn, env, out);
            }
        }
        PureExpr::BinOp(l, _, r) => {
            collect_self_calls(l, logic_fn, env, out);
            collect_self_calls(r, logic_fn, env, out);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => collect_self_calls(inner, logic_fn, env, out),
        PureExpr::Ite(c, t, e) => {
            collect_self_calls(c, logic_fn, env, out);
            collect_self_calls(t, logic_fn, env, out);
            collect_self_calls(e, logic_fn, env, out);
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            collect_self_calls(receiver, logic_fn, env, out);
            for a in args {
                collect_self_calls(a, logic_fn, env, out);
            }
        }
        PureExpr::Forall {
            var,
            body,
            triggers,
            ..
        }
        | PureExpr::Exists {
            var,
            body,
            triggers,
            ..
        } => {
            let scoped = env_without(env, std::slice::from_ref(var));
            let env = scoped.as_ref().unwrap_or(env);
            collect_self_calls(body, logic_fn, env, out);
            for trig in triggers {
                for t in trig {
                    collect_self_calls(t, logic_fn, env, out);
                }
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_self_calls(scrutinee, logic_fn, env, out);
            for arm in arms {
                // Pattern binders shadow let-bindings for the arm body. We do
                // not attempt to resolve them to destructured scrutinee parts;
                // the caller's parameter-only check drops any IH whose args
                // still mention them.
                let bound = arm.pattern.bound_names();
                let scoped = env_without(env, &bound);
                let arm_env = scoped.as_ref().unwrap_or(env);
                collect_self_calls(&arm.body, logic_fn, arm_env, out);
            }
        }
        PureExpr::Let { var, value, body } => {
            collect_self_calls(value, logic_fn, env, out);
            // Resolve the bound value against the CURRENT env so entries stay
            // fully resolved (a later `let s = s.remove(x)` sees `x` already
            // rewritten to `s.peek()`, yielding a parameter-only value).
            let resolved_value = if env.is_empty() {
                value.as_ref().clone()
            } else {
                value.substitute_capture_avoiding(env, &CaptureAvoidingSubstOptions::default())
            };
            let mut inner = env.clone();
            inner.insert(var.clone(), resolved_value); // innermost binding wins
            collect_self_calls(body, logic_fn, &inner, out);
        }
        PureExpr::LetAssume {
            assumption: value,
            body,
        }
        | PureExpr::LetObligation {
            obligation: value,
            body,
        } => {
            collect_self_calls(value, logic_fn, env, out);
            collect_self_calls(body, logic_fn, env, out);
        }
        PureExpr::Closure { params, body } => {
            let bound: Vec<String> = params.iter().map(|(name, _)| name.clone()).collect();
            let scoped = env_without(env, &bound);
            collect_self_calls(body, logic_fn, scoped.as_ref().unwrap_or(env), out);
        }
        // Leaves (Bool/Int/Float/Var) and any future variants contain no
        // self-call to collect. Missing one would only drop an IH
        // (incompleteness), never affect soundness.
        _ => {}
    }
}

/// `env` minus the given bound names. Returns `None` when nothing is removed
/// (caller keeps using `env` without a clone).
fn env_without<S: AsRef<str>>(
    env: &HashMap<String, PureExpr>,
    bound: &[S],
) -> Option<HashMap<String, PureExpr>> {
    if bound.iter().all(|name| !env.contains_key(name.as_ref())) {
        return None;
    }
    let mut scoped = env.clone();
    for name in bound {
        scoped.remove(name.as_ref());
    }
    Some(scoped)
}

/// `Some(k)` when `at_args` is syntactically `at_params - k` (or `at_params +
/// (-k)`) for a positive integer literal `k` — the decrement shape an integer
/// `#[variant]` almost always takes.
///
/// Syntactic, and deliberately so: the caller states a fact about the two
/// terms it is holding, and a term it cannot see the shape of gets no fact.
fn literal_decrement(at_args: &PureExpr, at_params: &PureExpr) -> Option<i64> {
    let PureExpr::BinOp(lhs, op, rhs) = at_args else {
        return None;
    };
    if lhs.as_ref() != at_params {
        return None;
    }
    let PureExpr::Int(k) = rhs.as_ref() else {
        return None;
    };
    match op {
        BinOp::Sub if *k > 0 => Some(*k),
        BinOp::Add if *k < 0 => k.checked_neg(),
        _ => None,
    }
}

fn binop(l: PureExpr, op: BinOp, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
}

/// Conjoin a list of formulas; empty ⇒ `true`.
fn and_all(mut conjuncts: Vec<PureExpr>) -> PureExpr {
    if conjuncts.is_empty() {
        return PureExpr::Bool(true);
    }
    let first = conjuncts.remove(0);
    conjuncts
        .into_iter()
        .fold(first, |acc, c| binop(acc, BinOp::And, c))
}

#[cfg(test)]
mod tests {
    use trust_wp_core::logic::LogicMode;

    use super::*;

    fn var(n: &str) -> PureExpr {
        PureExpr::Var(n.to_string(), None)
    }

    // num_of_pos-style increasing lemma:
    //   #[requires(j <= k)] #[ensures(P)] #[variant(k - j)]
    //   fn lemma(i,j,k,t) { if j < k { lemma(i, j+1, k, t) } }
    fn increasing_lemma(ensures: PureExpr) -> LogicFnDef {
        let rec_call = PureExpr::LogicFnCall {
            name: "lemma".to_string(),
            args: vec![
                var("i"),
                binop(var("j"), BinOp::Add, PureExpr::Int(1)),
                var("k"),
                var("t"),
            ],
        };
        let body = PureExpr::Ite(
            Arc::new(binop(var("j"), BinOp::Lt, var("k"))),
            Arc::new(rec_call),
            Arc::new(PureExpr::Bool(true)),
        );
        let mut def = LogicFnDef::new_with_requires(
            "lemma".to_string(),
            "crate::lemma".to_string(),
            vec![
                "i".to_string(),
                "j".to_string(),
                "k".to_string(),
                "t".to_string(),
            ],
            vec![binop(var("j"), BinOp::Le, var("k"))],
            body,
        )
        .with_param_sorts(vec![
            Some(ExprSort::Int),
            Some(ExprSort::Int),
            Some(ExprSort::Int),
            Some(ExprSort::Seq),
        ])
        .with_return_sort(Some(ExprSort::Unit))
        .with_variants(vec![binop(var("k"), BinOp::Sub, var("j"))])
        .with_mode(LogicMode::Open)
        .detect_recursion();
        def.set_ensures(vec![ensures]);
        def
    }

    #[test]
    fn injects_guarded_ih_for_decreasing_integer_variant() {
        let ens = binop(
            PureExpr::LogicFnCall {
                name: "num_of_pos".to_string(),
                args: vec![var("i"), var("j"), var("t")],
            },
            BinOp::Le,
            PureExpr::LogicFnCall {
                name: "num_of_pos".to_string(),
                args: vec![var("i"), var("k"), var("t")],
            },
        );
        let def = increasing_lemma(ens);
        let hyps = build_recursive_induction_hypotheses(&def, None);
        assert_eq!(hyps.len(), 1, "exactly one self-recursive call ⇒ one IH");
        let PureExpr::BinOp(guard, BinOp::Implies, concl) = &hyps[0] else {
            panic!("IH must be an implication, got {:?}", hyps[0]);
        };
        // Guard must contain the lower bound 0 <= (k-(j+1)) and the strict
        // decrease (k-(j+1)) < (k-j) — the well-foundedness conjuncts.
        let guard_str = format!("{guard:?}");
        assert!(guard_str.contains("Le"), "guard needs the 0<=m[A] bound");
        assert!(guard_str.contains("Lt"), "guard needs the m[A]<m[P] bound");
        // Conclusion must be the ensures with j ↦ j+1 (num_of_pos(i,j+1,t) ...).
        let concl_str = format!("{concl:?}");
        assert!(concl_str.contains("num_of_pos"));
    }

    #[test]
    fn no_ih_for_non_decreasing_recursion_is_irrelevant_guard_still_unsatisfiable() {
        // Same args (non-decreasing) ⇒ guard is m[A] < m[P] = (k-j) < (k-j),
        // unsatisfiable. We still EMIT the (vacuous) IH; soundness comes from the
        // guard being false, not from refusing to emit. Verify it is emitted and
        // guarded (the SMT layer makes it inert).
        let rec_call = PureExpr::LogicFnCall {
            name: "lemma".to_string(),
            args: vec![var("i"), var("j"), var("k"), var("t")], // SAME args
        };
        let body = PureExpr::Ite(
            Arc::new(binop(var("j"), BinOp::Lt, var("k"))),
            Arc::new(rec_call),
            Arc::new(PureExpr::Bool(true)),
        );
        let mut def = LogicFnDef::new_with_requires(
            "lemma".to_string(),
            "crate::lemma".to_string(),
            vec!["i".into(), "j".into(), "k".into(), "t".into()],
            vec![binop(var("j"), BinOp::Le, var("k"))],
            body,
        )
        .with_param_sorts(vec![
            Some(ExprSort::Int),
            Some(ExprSort::Int),
            Some(ExprSort::Int),
            Some(ExprSort::Seq),
        ])
        .with_variants(vec![binop(var("k"), BinOp::Sub, var("j"))])
        .detect_recursion();
        def.set_ensures(vec![PureExpr::Bool(false)]);
        let hyps = build_recursive_induction_hypotheses(&def, None);
        assert_eq!(hyps.len(), 1);
        // The guard contains (k-j) < (k-j) which is unsatisfiable; the IH cannot
        // fire. (We assert the structure is the guarded implication.)
        assert!(matches!(&hyps[0], PureExpr::BinOp(_, BinOp::Implies, _)));
    }

    #[test]
    fn no_ih_without_variant() {
        let mut def = increasing_lemma(PureExpr::Bool(true)).with_variants(vec![]);
        def.set_ensures(vec![PureExpr::Bool(true)]);
        assert!(build_recursive_induction_hypotheses(&def, None).is_empty());
    }

    #[test]
    fn no_ih_for_non_integer_seq_variant() {
        // Variant `t` is a Seq parameter ⇒ not an integer measure ⇒ no IH.
        let ens = PureExpr::Bool(true);
        let mut def = increasing_lemma(ens).with_variants(vec![var("t")]);
        def.set_ensures(vec![PureExpr::Bool(true)]);
        assert!(
            build_recursive_induction_hypotheses(&def, None).is_empty(),
            "a Seq-sorted variant is not well-founded under integer `<`"
        );
    }

    #[test]
    fn no_ih_for_non_recursive_fn() {
        let mut def = LogicFnDef::new_with_requires(
            "f".to_string(),
            "crate::f".to_string(),
            vec!["x".to_string()],
            vec![],
            var("x"),
        )
        .with_variants(vec![var("x")]);
        def.set_ensures(vec![binop(var("result"), BinOp::Eq, var("x"))]);
        // detect_recursion() not called / body has no self-call ⇒ not recursive.
        assert!(build_recursive_induction_hypotheses(&def, None).is_empty());
    }

    #[test]
    fn shadowed_let_binding_resolves_to_parameter_expression() {
        // bug/vcgen shape:
        //   fn f(x: Int) #[requires(x >= 1)] #[ensures(true)] #[variant(x)]
        //     { let x = x - 1; if x == 0 { true } else { f(x) } }
        // The self-call argument `x` is the let-bound SHADOW of param `x`.
        // Without let-env resolution the P ↦ A substitution is the identity
        // and the IH guard is the vacuous `x < x`. With resolution the arg
        // becomes `x - 1` (parameter-only) and the guard `0 <= x-1 < x`.
        let shadow_body = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(binop(var("x"), BinOp::Sub, PureExpr::Int(1))),
            body: Arc::new(PureExpr::Ite(
                Arc::new(binop(var("x"), BinOp::Eq, PureExpr::Int(0))),
                Arc::new(PureExpr::Bool(true)),
                Arc::new(PureExpr::LogicFnCall {
                    name: "f".to_string(),
                    args: vec![var("x")],
                }),
            )),
        };
        let mut def = LogicFnDef::new_with_requires(
            "f".to_string(),
            "crate::f".to_string(),
            vec!["x".to_string()],
            vec![binop(var("x"), BinOp::Ge, PureExpr::Int(1))],
            shadow_body,
        )
        .with_param_sorts(vec![Some(ExprSort::Int)])
        .with_return_sort(Some(ExprSort::Unit))
        .with_variants(vec![var("x")])
        .with_mode(LogicMode::Open)
        .detect_recursion();
        def.set_ensures(vec![PureExpr::Bool(true)]);

        let hyps = build_recursive_induction_hypotheses(&def, None);
        // One IH, then the measure's integrality across the literal decrement.
        assert_eq!(hyps.len(), 2, "the shadowed self-call must yield an IH");
        assert!(
            matches!(&hyps[1], PureExpr::BinOp(_, BinOp::Or, _)),
            "the trailing fact is the integrality disjunction, got {:?}",
            hyps[1]
        );
        let PureExpr::BinOp(guard, BinOp::Implies, _) = &hyps[0] else {
            panic!("expected guarded implication, got {:?}", hyps[0]);
        };
        let guard_str = format!("{guard:?}");
        assert!(
            guard_str.contains("Sub"),
            "guard must compare the RESOLVED argument x-1 (non-identity), got {guard_str}"
        );
    }

    #[test]
    fn match_binder_argument_emits_no_ih() {
        // Self-call argument mentions a match-arm binder we cannot resolve to
        // a parameter expression — the sound fallback is NO induction
        // hypothesis for that call.
        let body = PureExpr::Match {
            scrutinee: Arc::new(var("x")),
            arms: vec![trust_wp_core::formula::MatchArm {
                pattern: trust_wp_core::formula::Pattern::Binding("n".to_string()),
                body: PureExpr::LogicFnCall {
                    name: "f".to_string(),
                    args: vec![var("n")],
                },
            }],
        };
        let mut def = LogicFnDef::new_with_requires(
            "f".to_string(),
            "crate::f".to_string(),
            vec!["x".to_string()],
            vec![],
            body,
        )
        .with_param_sorts(vec![Some(ExprSort::Int)])
        .with_variants(vec![var("x")])
        .with_mode(LogicMode::Open)
        .detect_recursion();
        def.set_ensures(vec![PureExpr::Bool(true)]);
        assert!(
            build_recursive_induction_hypotheses(&def, None).is_empty(),
            "an argument mentioning an unresolvable match binder must emit no IH"
        );
    }

    #[test]
    fn value_returning_substitutes_result_with_recursive_call() {
        // fn vi(x) -> Int  #[variant(x)] #[requires(x>=0)] #[ensures(result == x)]
        //   { if x == 0 { 0 } else { vi(x-1) + 1 } }
        let rec_call = PureExpr::LogicFnCall {
            name: "vi".to_string(),
            args: vec![binop(var("x"), BinOp::Sub, PureExpr::Int(1))],
        };
        let body = PureExpr::Ite(
            Arc::new(binop(var("x"), BinOp::Eq, PureExpr::Int(0))),
            Arc::new(PureExpr::Int(0)),
            Arc::new(binop(rec_call, BinOp::Add, PureExpr::Int(1))),
        );
        let mut def = LogicFnDef::new_with_requires(
            "vi".to_string(),
            "crate::vi".to_string(),
            vec!["x".to_string()],
            vec![binop(var("x"), BinOp::Ge, PureExpr::Int(0))],
            body,
        )
        .with_param_sorts(vec![Some(ExprSort::Int)])
        .with_return_sort(Some(ExprSort::Int))
        .with_variants(vec![var("x")])
        .detect_recursion();
        def.set_ensures(vec![binop(var("result"), BinOp::Eq, var("x"))]);

        let hyps = build_recursive_induction_hypotheses(&def, None);
        // One IH, then the measure's integrality across the literal decrement.
        assert_eq!(hyps.len(), 2);
        let PureExpr::BinOp(_, BinOp::Implies, concl) = &hyps[0] else {
            panic!("expected guarded implication");
        };
        // Conclusion must be  vi(x-1) == (x-1)  — `result` replaced by the
        // RECURSIVE call value vi(x-1), and `x` by `x-1`.
        let concl_str = format!("{concl:?}");
        assert!(
            concl_str.contains("LogicFnCall") && concl_str.contains("vi"),
            "result must be substituted with the recursive call vi(x-1), got {concl_str}"
        );
    }
}
