// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural-recursion termination check for logic functions.
//!
//! Faithful port of Creusot's `is_structurally_recursive`
//! (`reference/creusot/creusot/src/validate/terminates.rs:669`) over the
//! `PureExpr` logic-function body.
//!
//! A recursive logic function terminates *structurally* when every self-call
//! passes, in some FIXED argument position, a term that is STRICTLY smaller
//! (a strict subterm) than the original argument in that position — and it is
//! always the *same* argument that decreases (otherwise the recursion could
//! "ping-pong" forever). This lets trust-wp accept genuinely-terminating
//! recursive `deep_model` impls (e.g. `syntax/derive_macros/mixed.rs`'s
//! `List`/`Expr`) that recurse on a strict subterm of the matched scrutinee,
//! while still REJECTING:
//!   * `bug/459` — `A::deep_model` recurses *mutually* through `Box<A>`'s
//!     `DeepModel` impl. In the parsed body the recursive `.deep_model()` is
//!     applied to the *bare* `Box<A>` binding (`receiver: Var("a")`, the
//!     `Deref` is OUTSIDE the call, `*a.deep_model()` ≡ `*(a.deep_model())`),
//!     so it is NOT a same-type self-call — there is no `Deref`-unwrapped Self
//!     receiver — and the candidate set is never confirmed → `false`.
//!   * `bug/1966` — `me`/`sneak`/`nonstrictly`/`nested`/`falso`: same-arg,
//!     non-strict, or mutual recursion → `false`.
//!
//! ## Soundness (PARAMOUNT)
//! This predicate is CONSERVATIVE. It returns `true` only when it can prove a
//! single fixed argument strictly decreases (via a strict subterm of the
//! original arg in that position) on EVERY genuine self-call. Any uncertainty
//! — an unrecognised pattern/shape, a non-strict decrease, a different arg per
//! call, or a wrapper/mutual cycle — yields `false`, leaving the node rejected.
//! It never accepts mutual recursion.

use std::collections::HashMap;

use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use super::LogicRecursionNode;

/// Prefix the contract parser emits for named-field projection
/// (`x.elem` → `__trust_wp_field_elem(x)`).
const NAMED_FIELD_FN_PREFIX: &str = "__trust_wp_field_";
/// Prefix for tuple-index projection (`x.0` → `__trust_wp_tuple_get_0(x)`).
const TUPLE_FIELD_FN_PREFIX: &str = "__trust_wp_tuple_get_";

/// Returns `true` when `node` is a recursive logic function whose recursion is
/// provably terminating by structural (strict-subterm) decrease on a single
/// fixed argument — Creusot's `is_structurally_recursive`.
///
/// Only invoked for nodes that the recursion checker has already flagged as
/// recursive (deep_model dispatch / self-edge). For a genuinely non-recursive
/// body this is never consulted, so "no self-call observed" deliberately maps
/// to `false` (see [`StructuralRecursion::valid`]).
pub(super) fn is_structurally_recursive(node: &LogicRecursionNode) -> bool {
    if node.params.is_empty() {
        // No argument can decrease (e.g. `falso()`): never structural.
        return false;
    }

    let mut state = StructuralRecursion::new(node);
    state.visit(&node.body);
    state.valid()
}

/// A variable's relationship to a recursion argument: it is (possibly strictly)
/// a substructure of argument `root`.
#[derive(Clone, Copy)]
struct SmallerThan {
    root: usize,
    strictly: bool,
}

struct StructuralRecursion<'a> {
    /// Map from in-scope variable name to the argument it is a substructure of.
    /// Each formal parameter starts mapped to itself, non-strictly.
    smaller_than: HashMap<String, SmallerThan>,
    /// The implementing function's formal parameter names, by position.
    params: &'a [String],
    /// Candidate strictly-decreasing argument positions. Starts full; a
    /// self-call that fails to strictly decrease position `i` removes `i`.
    /// Mirrors Creusot's `decreasing_args` `DenseBitSet`.
    decreasing_args: Vec<bool>,
    /// Whether this is a `deep_model` impl (changes how `.deep_model()`
    /// method-calls are interpreted as self-calls).
    is_deep_model: bool,
    /// The bare function name (used to recognise direct logic-call self-calls).
    self_name: &'a str,
    /// True once at least one genuine same-function self-call has been seen.
    /// Required for `valid()`: a recursion expressed only through a wrapper's
    /// impl (bug/459) has zero genuine self-calls and must NOT be accepted.
    saw_self_call: bool,
}

impl<'a> StructuralRecursion<'a> {
    fn new(node: &'a LogicRecursionNode) -> Self {
        let mut smaller_than = HashMap::new();
        for (i, p) in node.params.iter().enumerate() {
            smaller_than.insert(
                p.clone(),
                SmallerThan {
                    root: i,
                    strictly: false,
                },
            );
        }
        Self {
            smaller_than,
            params: &node.params,
            decreasing_args: vec![true; node.params.len()],
            is_deep_model: node.name == "deep_model",
            self_name: &node.name,
            saw_self_call: false,
        }
    }

    /// Creusot `valid()`: some single argument strictly decreases on every
    /// self-call. We additionally require at least one genuine self-call to be
    /// seen — without that a wrapper/mutual cycle (bug/459) or a stray
    /// non-recursive body would vacuously pass.
    fn valid(&self) -> bool {
        self.saw_self_call && self.decreasing_args.iter().any(|&b| b)
    }

    /// Find the argument `t`'s value is a substructure of, and whether strictly.
    /// Mirrors Creusot `root` ∘ `local_root`.
    fn root(&self, t: &PureExpr) -> Option<SmallerThan> {
        let (var, strictly) = local_root(t)?;
        let &base = self.smaller_than.get(&var)?;
        Some(SmallerThan {
            root: base.root,
            strictly: strictly || base.strictly,
        })
    }

    /// `t` is a STRICT substructure of formal parameter position `arg`.
    fn is_strictly_smaller_than(&self, t: &PureExpr, arg: usize) -> bool {
        matches!(self.root(t), Some(SmallerThan { root, strictly: true }) if root == arg)
    }

    /// Record that the variables bound by `pat` are (possibly strictly) smaller
    /// than `root`, mirroring Creusot `bind_smaller` / `Pattern::binds_smaller`.
    fn bind_smaller(&mut self, root: usize, strictly: bool, pat: &Pattern) {
        let mut binds = Vec::new();
        pattern_binds_smaller(pat, false, &mut binds);
        for (name, strictly2) in binds {
            self.smaller_than.insert(
                name,
                SmallerThan {
                    root,
                    strictly: strictly || strictly2,
                },
            );
        }
    }

    /// Process a self-call passing `args` in order, removing any argument
    /// position that does not strictly decrease (Creusot's `Call` arm).
    fn note_self_call(&mut self, args: &[&PureExpr]) {
        self.saw_self_call = true;
        for (i, arg) in args.iter().enumerate() {
            if i >= self.params.len() {
                break;
            }
            if !self.is_strictly_smaller_than(arg, i) {
                self.decreasing_args[i] = false;
            }
        }
        // A self-call with FEWER positional args than there are parameters
        // cannot establish decrease for the missing positions: conservatively
        // drop them so they are never the sole "decreasing" witness.
        for i in args.len()..self.params.len() {
            self.decreasing_args[i] = false;
        }
    }

    /// Visit an expression, binding pattern variables (let/match) ahead of time
    /// (binders are unique post-parse) and noting self-calls. Mirrors Creusot's
    /// `TermVisitor for StructuralRecursion`.
    fn visit(&mut self, expr: &PureExpr) {
        match expr {
            // A direct logic-function self-call: `f(a0, a1, ...)`.
            PureExpr::LogicFnCall { name, args } if self.call_is_self(name) => {
                let refs: Vec<&PureExpr> = args.iter().collect();
                self.note_self_call(&refs);
            }
            // A `.deep_model()` self-call on a `Deref`-unwrapped Self receiver:
            // `(*tail).deep_model()` — the receiver is arg 0 (`self`). The
            // `Deref` proves the boxed field was unwrapped to the Self type, so
            // the dispatch lands on THIS impl. A bare-`Box` receiver (bug/459's
            // `a.deep_model()`, `receiver: Var("a")`) is NOT counted here — it
            // dispatches into the wrapper's impl (mutual recursion).
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if self.is_deep_model && method == "deep_model" && args.is_empty() => {
                if is_unwrapped_self_receiver(receiver) {
                    self.note_self_call(&[receiver]);
                }
            }
            PureExpr::Let { var, value, body } => {
                if let Some(SmallerThan { root, strictly }) = self.root(value) {
                    self.bind_smaller(root, strictly, &Pattern::Binding(var.clone()));
                }
                self.visit(value);
                self.visit(body);
                return;
            }
            PureExpr::Match { scrutinee, arms } => {
                if let Some(SmallerThan { root, strictly }) = self.root(scrutinee) {
                    for MatchArm { pattern, .. } in arms {
                        self.bind_smaller(root, strictly, pattern);
                    }
                }
                self.visit(scrutinee);
                for MatchArm { body, .. } in arms {
                    self.visit(body);
                }
                return;
            }
            _ => {}
        }

        // Default: recurse into every child (also covers the args/receiver of a
        // matched self-call, so nested self-calls — bug/1966 `nested` — are
        // checked too: `nested(*m, nested(n, ()))` removes arg 0 on the inner
        // call because the inner passes `n` unchanged).
        for_each_child(expr, &mut |child| self.visit(child));
    }

    /// Is the logic-call `name` a call to this same function?
    fn call_is_self(&self, name: &str) -> bool {
        // Field/tuple/constructor projections are not calls; the parser emits
        // them as `__trust_wp_field_*` / `__trust_wp_tuple*`. They never name
        // the function, so an exact / suffix match on the bare name is enough.
        if name.starts_with("__trust_wp_") {
            return false;
        }
        // The bare function name; in trust-wp's parsed bodies a direct
        // recursive call appears as the bare ident (e.g. `nonstrictly(i)`),
        // optionally path-qualified.
        name == self.self_name || name.ends_with(&format!("::{}", self.self_name))
    }
}

/// Mirrors Creusot `local_root`: return the variable `v` such that the value of
/// `t` is a substructure of `v`, with `true` if it is a STRICT substructure.
/// Peels transparent wrappers (`Old`/`View`) non-strictly, `Deref` and field/
/// tuple projections strictly, down to a `Var`.
fn local_root(t: &PureExpr) -> Option<(String, bool)> {
    let mut cur = t;
    let mut strictly = false;
    loop {
        match cur {
            PureExpr::Var(name, _) => return Some((name.clone(), strictly)),
            // Transparent coercions / views: not a structural descent.
            PureExpr::Old(inner) | PureExpr::View(inner) => {
                cur = inner;
            }
            // `*x` descends into the pointee: a strict subterm.
            PureExpr::Deref(inner) => {
                cur = inner;
                strictly = true;
            }
            // Field / tuple projection: `__trust_wp_field_<f>(x)` /
            // `__trust_wp_tuple_get_<i>(x)` — a strict subterm of the single arg.
            PureExpr::LogicFnCall { name, args }
                if (name.starts_with(NAMED_FIELD_FN_PREFIX)
                    || name.starts_with(TUPLE_FIELD_FN_PREFIX))
                    && args.len() == 1 =>
            {
                cur = &args[0];
                strictly = true;
            }
            _ => return None,
        }
    }
}

/// Is `receiver` a Self-typed value obtained by `Deref`-unwrapping a (strict)
/// subterm of `self`? This is the signature of a same-type `deep_model`
/// self-call (`(*tail).deep_model()`), as opposed to a `.deep_model()` on a
/// bare wrapper binding (bug/459). Requires the outermost shape to include a
/// `Deref` so the receiver's type is the unwrapped Self, not `Box<Self>`.
fn is_unwrapped_self_receiver(receiver: &PureExpr) -> bool {
    // The receiver must contain a Deref (an unwrap) and resolve, via
    // `local_root`, to a STRICT subterm — i.e. its root is strictly smaller
    // than the parameter it came from.
    let has_deref = receiver_contains_deref(receiver);
    has_deref && matches!(local_root(receiver), Some((_, true)))
}

/// True if the receiver chain (peeling Old/View) reaches a `Deref` before a
/// non-projection node. A bare `Var` (bug/459 `a`) returns false.
fn receiver_contains_deref(receiver: &PureExpr) -> bool {
    let mut cur = receiver;
    loop {
        match cur {
            PureExpr::Deref(_) => return true,
            PureExpr::Old(inner) | PureExpr::View(inner) => cur = inner,
            PureExpr::LogicFnCall { name, args }
                if (name.starts_with(NAMED_FIELD_FN_PREFIX)
                    || name.starts_with(TUPLE_FIELD_FN_PREFIX))
                    && args.len() == 1 =>
            {
                cur = &args[0];
            }
            _ => return false,
        }
    }
}

/// Mirrors Creusot `Pattern::binds_smaller`: collect every variable bound by
/// `pat` together with whether it is STRICTLY smaller than the destructured
/// scrutinee. A bare top-level binding (`x` in `match s { x => ... }`) is an
/// alias — NON-strict (this keeps bug/1966 `nonstrictly` rejected). Any
/// variable bound *inside* a constructor / tuple destructure is strict.
fn pattern_binds_smaller(pat: &Pattern, strictly: bool, out: &mut Vec<(String, bool)>) {
    match pat {
        Pattern::Wildcard => {}
        Pattern::Binding(name) => out.push((name.clone(), strictly)),
        Pattern::Literal(_) => {}
        Pattern::Constructor { inner, .. } => {
            if let Some(inner) = inner {
                // Anything matched under a constructor is a strict subterm.
                pattern_binds_smaller(inner, true, out);
            }
        }
        Pattern::Alias { alias, pattern } => {
            // `name @ pat`: the alias names the whole matched value at this
            // level (same strictness), and the inner pattern continues.
            out.push((alias.clone(), strictly));
            pattern_binds_smaller(pattern, strictly, out);
        }
        Pattern::Tuple(elems) => {
            for e in elems {
                // Tuple elements are strict subterms of the tuple.
                pattern_binds_smaller(e, true, out);
            }
        }
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

/// Apply `f` to every direct child sub-expression of `expr`. Used for the
/// default visitor descent (everything not specially handled in `visit`).
fn for_each_child(expr: &PureExpr, f: &mut dyn FnMut(&PureExpr)) {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        PureExpr::BinOp(a, _, b) => {
            f(a);
            f(b);
        }
        PureExpr::UnOp(_, a)
        | PureExpr::Old(a)
        | PureExpr::Deref(a)
        | PureExpr::Final(a)
        | PureExpr::View(a) => f(a),
        PureExpr::Ite(c, t, e) => {
            f(c);
            f(t);
            f(e);
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            f(receiver);
            for a in args {
                f(a);
            }
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            f(body);
            for trig in triggers {
                for t in trig {
                    f(t);
                }
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            f(scrutinee);
            for arm in arms {
                f(&arm.body);
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for a in args {
                f(a);
            }
        }
        PureExpr::Let { value, body, .. } => {
            f(value);
            f(body);
        }
        PureExpr::LetAssume { assumption, body } => {
            f(assumption);
            f(body);
        }
        PureExpr::LetObligation { obligation, body } => {
            f(obligation);
            f(body);
        }
        PureExpr::Closure { body, .. } => f(body),
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

#[cfg(test)]
#[path = "structural_tests.rs"]
mod tests;
