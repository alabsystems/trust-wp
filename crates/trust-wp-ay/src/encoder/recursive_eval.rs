// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive logic function evaluation helpers (#1292).
//!
//! Ground-expression evaluation and constant folding for logic function calls.
//! Used by the quantifier instantiation pipeline (`logic_fn.rs`) to evaluate
//! recursive definitions to concrete values when all arguments are literals.
//!
//! # Key Functions
//! - [`try_evaluate_recursive`]: Fully evaluates ground recursive logic function calls
//! - [`collect_concrete_logic_fn_calls`]: Finds ground-instantiable calls in expression trees
//! - [`simplify_ground`]: Constant-folds arithmetic/boolean expressions
//! - [`is_ground_expr`]: Checks whether an expression contains no free variables
//! - [`is_obviously_false`]: Quick syntactic falsehood check
use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{
    int_bounds::pow2_expr, MatchArm, Pattern, PureExpr, PureExprDepthLimitedTraversalExt as _,
};

use super::MAX_ENCODING_DEPTH;

/// Memoization cache for recursive logic function evaluation (#2021).
///
/// Keys are `(fn_name, evaluated_args)` — the same function called with the
/// same concrete arguments always produces the same result, regardless of
/// call-site depth. This eliminates O(2^n) blowup for branching recursion
/// patterns (e.g., Fibonacci: `fib(n) = fib(n-1) + fib(n-2)`).
pub(crate) type EvalCache = HashMap<(String, Vec<PureExpr>), Option<PureExpr>>;

/// Try to fully evaluate a ground expression containing recursive logic
/// function calls to a concrete literal value (Int or Bool).
///
/// This performs repeated substitution and constant folding:
/// 1. When encountering `f(concrete_args)`, substitute args into body
/// 2. Simplify the result (constant fold arithmetic, resolve ITEs)
/// 3. If the result still contains function calls, recurse (up to depth limit)
/// 4. Return `Some(literal)` if fully reduced, `None` if stuck
///
/// Uses memoization to avoid re-evaluating the same `(fn, args)` pairs,
/// reducing branching recursion from O(2^n) to O(n) (#2021).
/// Convenience wrapper that creates a fresh cache per call.
///
/// Production code should prefer [`try_evaluate_recursive_cached`] with a
/// shared cache when evaluating multiple calls in a loop.
pub(crate) fn try_evaluate_recursive(
    expr: &PureExpr,
    fns: &HashMap<&str, &trust_wp_core::logic::LogicFnDef>,
    max_depth: usize,
) -> Option<PureExpr> {
    let mut cache = EvalCache::new();
    try_evaluate_recursive_cached(expr, fns, max_depth, &mut cache)
}

/// Like [`try_evaluate_recursive`] but accepts an external memoization cache.
///
/// Callers that evaluate many ground calls in a loop (e.g.,
/// [`assert_recursive_logic_fn_ground_instances`]) should create one
/// `EvalCache` and reuse it across invocations so that shared
/// sub-problems are not re-evaluated.
pub(crate) fn try_evaluate_recursive_cached(
    expr: &PureExpr,
    fns: &HashMap<&str, &trust_wp_core::logic::LogicFnDef>,
    max_depth: usize,
    cache: &mut EvalCache,
) -> Option<PureExpr> {
    try_evaluate_recursive_inner(expr, fns, max_depth, 0, cache)
}

fn try_evaluate_recursive_inner(
    expr: &PureExpr,
    fns: &HashMap<&str, &trust_wp_core::logic::LogicFnDef>,
    max_depth: usize,
    depth: usize,
    cache: &mut EvalCache,
) -> Option<PureExpr> {
    if depth > max_depth {
        return None;
    }

    match expr {
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => Some(expr.clone()),
        PureExpr::LogicFnCall { name, args } => {
            // First, evaluate all arguments
            let mut eval_args = Vec::with_capacity(args.len());
            for arg in args {
                eval_args.push(try_evaluate_recursive_inner(
                    arg, fns, max_depth, depth, cache,
                )?);
            }

            // Check the memoization cache before expanding the function body.
            let cache_key = (name.clone(), eval_args.clone());
            if let Some(cached) = cache.get(&cache_key) {
                return cached.clone();
            }

            // Look up the function
            let Some(&lf) = fns.get(name.as_str()) else {
                cache.insert(cache_key, None);
                return None;
            };

            // Check preconditions
            let mut subs = HashMap::new();
            for (i, param) in lf.params().iter().enumerate() {
                if i < eval_args.len() {
                    subs.insert(param.clone(), eval_args[i].clone());
                }
            }
            for req in lf.requires() {
                let substituted = simplify_ground(&req.substitute(&subs));
                if is_obviously_false(&substituted) {
                    cache.insert(cache_key, None);
                    return None; // Precondition violated
                }
            }

            // Substitute and simplify the body
            let ground_body = simplify_ground(&lf.body().substitute(&subs));

            // Recursively evaluate remaining function calls in the body
            let result =
                try_evaluate_recursive_inner(&ground_body, fns, max_depth, depth + 1, cache);
            cache.insert(cache_key, result.clone());
            result
        }
        PureExpr::BinOp(l, op, r) => {
            let el = try_evaluate_recursive_inner(l, fns, max_depth, depth, cache)?;
            let er = try_evaluate_recursive_inner(r, fns, max_depth, depth, cache)?;
            Some(simplify_ground(&PureExpr::BinOp(
                reuse_arc(l, el),
                *op,
                reuse_arc(r, er),
            )))
        }
        PureExpr::UnOp(op, e) => {
            let ee = try_evaluate_recursive_inner(e, fns, max_depth, depth, cache)?;
            Some(simplify_ground(&PureExpr::UnOp(*op, reuse_arc(e, ee))))
        }
        PureExpr::Ite(c, t, e) => {
            let ec = try_evaluate_recursive_inner(c, fns, max_depth, depth, cache)?;
            match &ec {
                PureExpr::Bool(true) => {
                    try_evaluate_recursive_inner(t, fns, max_depth, depth, cache)
                }
                PureExpr::Bool(false) => {
                    try_evaluate_recursive_inner(e, fns, max_depth, depth, cache)
                }
                _ => None, // Can't resolve ITE condition
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "pow2" && args.is_empty() => {
            let receiver = try_evaluate_recursive_inner(receiver, fns, max_depth, depth, cache)?;
            let PureExpr::Int(exp) = receiver else {
                return None;
            };
            let exp = u32::try_from(exp).ok()?;
            Some(simplify_ground(&pow2_expr(exp)))
        }
        _ => None, // Variables and other non-ground constructs
    }
}

/// Collect concrete logic function calls from an expression tree.
///
/// Uses `for_each_recursive_with_depth_limit` for exhaustive variant
/// coverage. The visitor checks each `LogicFnCall` node for membership in
/// `recursive_fns` and ground arguments. (#2654)
pub(crate) fn collect_concrete_logic_fn_calls(
    expr: &PureExpr,
    recursive_fns: &HashMap<&str, &trust_wp_core::logic::LogicFnDef>,
    out: &mut Vec<(String, Vec<PureExpr>)>,
) {
    expr.for_each_recursive_with_depth_limit(MAX_ENCODING_DEPTH, |node| {
        if let PureExpr::LogicFnCall { name, args } = node {
            if recursive_fns.contains_key(name.as_str()) && args.iter().all(is_ground_expr) {
                out.push((name.clone(), args.clone()));
            }
        }
    });
}

/// Check if an expression is ground (contains no free variables).
///
/// Uses `any_recursive_with_depth_limit` for exhaustive variant coverage.
/// An expression is ground iff it contains only `Int`, `Bool`, `BinOp`,
/// `UnOp`, `Ite`, and `LogicFnCall` nodes — any other variant (including
/// `Var`) makes it non-ground. `on_limit = true` means the predicate
/// fires at depth limit, returning "not ground" (fail-closed). (#2654)
fn is_ground_expr(expr: &PureExpr) -> bool {
    !expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        !matches!(
            e,
            PureExpr::Int(_)
                | PureExpr::Bool(_)
                | PureExpr::Float(_)
                | PureExpr::BinOp(..)
                | PureExpr::UnOp(..)
                | PureExpr::Ite(..)
                | PureExpr::LogicFnCall { .. }
        )
    })
}

/// Try to constant-fold a binary operation on two simplified operands.
///
/// Returns `Some(result)` if the operation can be folded, `None` otherwise.
/// Uses checked arithmetic to avoid panics on overflow.
fn try_fold_binop(
    sl: &PureExpr,
    op: trust_wp_core::formula::BinOp,
    sr: &PureExpr,
) -> Option<PureExpr> {
    use trust_wp_core::formula::BinOp;
    if let (PureExpr::Int(lv), PureExpr::Int(rv)) = (sl, sr) {
        match op {
            BinOp::Add => return lv.checked_add(*rv).map(PureExpr::Int),
            BinOp::Sub => return lv.checked_sub(*rv).map(PureExpr::Int),
            BinOp::Mul => return lv.checked_mul(*rv).map(PureExpr::Int),
            // SMT-LIB div/mod use Euclidean semantics (#2191):
            //   div: floor toward -∞ (not truncation toward 0)
            //   mod: result always non-negative
            // Use checked_rem first to detect overflow (e.g., i64::MIN / -1),
            // then apply Euclidean semantics.
            BinOp::Div if *rv != 0 => {
                return lv
                    .checked_div(*rv)
                    .map(|_| PureExpr::Int(lv.div_euclid(*rv)))
            }
            BinOp::Mod if *rv != 0 => {
                return lv
                    .checked_rem(*rv)
                    .map(|_| PureExpr::Int(lv.rem_euclid(*rv)))
            }
            // Truncated machine ops (Rust signed `/`/`%`): `checked_div`/
            // `checked_rem` ARE Rust's toward-zero ops and return None on
            // overflow (i64::MIN / -1), declining the fold.
            BinOp::DivTrunc if *rv != 0 => return lv.checked_div(*rv).map(PureExpr::Int),
            BinOp::RemTrunc if *rv != 0 => return lv.checked_rem(*rv).map(PureExpr::Int),
            BinOp::Eq => return Some(PureExpr::Bool(lv == rv)),
            BinOp::Ne => return Some(PureExpr::Bool(lv != rv)),
            BinOp::Gt => return Some(PureExpr::Bool(lv > rv)),
            BinOp::Ge => return Some(PureExpr::Bool(lv >= rv)),
            BinOp::Lt => return Some(PureExpr::Bool(lv < rv)),
            BinOp::Le => return Some(PureExpr::Bool(lv <= rv)),
            _ => {}
        }
    }
    if let (PureExpr::Bool(lb), PureExpr::Bool(rb)) = (sl, sr) {
        match op {
            BinOp::And => return Some(PureExpr::Bool(*lb && *rb)),
            BinOp::Or => return Some(PureExpr::Bool(*lb || *rb)),
            BinOp::Implies => return Some(PureExpr::Bool(!lb || *rb)),
            BinOp::Eq => return Some(PureExpr::Bool(lb == rb)),
            BinOp::Ne => return Some(PureExpr::Bool(lb != rb)),
            _ => {}
        }
    }
    None
}

/// Simplify a ground expression by constant-folding arithmetic and comparisons.
///
/// Uses `rewrite_bottom_up_with_depth_limit` for exhaustive variant coverage.
/// The rewrite function receives each node with already-simplified children
/// and applies constant folding for `BinOp`, `UnOp`, `Ite`, and `Match`
/// (when the scrutinee is a known constructor). (#2654, #3318)
pub(crate) fn simplify_ground(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up_with_depth_limit(MAX_ENCODING_DEPTH, |node| match node {
        PureExpr::BinOp(ref l, op, ref r) => {
            if let Some(folded) = try_fold_binop(l, op, r) {
                folded
            } else {
                node
            }
        }
        PureExpr::UnOp(op, ref e) => match (op, e.as_ref()) {
            (trust_wp_core::formula::UnOp::Neg, PureExpr::Int(v)) => {
                if let Some(r) = v.checked_neg() {
                    PureExpr::Int(r)
                } else {
                    node
                }
            }
            (trust_wp_core::formula::UnOp::Not, PureExpr::Bool(b)) => PureExpr::Bool(!b),
            (trust_wp_core::formula::UnOp::BitNot, PureExpr::Int(v)) => PureExpr::Int(!v),
            _ => node,
        },
        PureExpr::Ite(ref c, ref t, ref e) => match c.as_ref() {
            PureExpr::Bool(true) => t.as_ref().clone(),
            PureExpr::Bool(false) => e.as_ref().clone(),
            _ => node,
        },
        PureExpr::Match {
            ref scrutinee,
            ref arms,
        } => {
            if let Some(reduced) = try_reduce_match_constructor(scrutinee, arms) {
                reduced
            } else {
                node
            }
        }
        PureExpr::MethodCall {
            ref receiver,
            ref method,
            ref args,
        } if method == "pow2" && args.is_empty() => match receiver.as_ref() {
            PureExpr::Int(exp) => u32::try_from(*exp)
                .map(|exp| simplify_ground(&pow2_expr(exp)))
                .unwrap_or(node),
            _ => node,
        },
        other => other,
    })
}

/// Reduce a match expression when the scrutinee is a known constructor.
///
/// When the scrutinee is a `LogicFnCall` (constructor like `None()`, `Some(1)`,
/// `Ok(x)`, `Err(y)`) or `Deref` of one (from `*self` substitution), and one
/// of the match arms has a matching `Constructor` pattern, we can statically
/// reduce the match to that arm's body with appropriate bindings substituted.
///
/// This is critical for proof_assert verification where match-style
/// postconditions like `match *None() { Some(v) => ..., None => ... }` appear
/// as preconditions. Without this reduction, the solver sees the full ITE chain
/// and may fail to simplify when the deref'd constructor sort doesn't align
/// with the datatype tester expectations. (#3318)
pub(crate) fn try_reduce_match_constructor(
    scrutinee: &PureExpr,
    arms: &[MatchArm],
) -> Option<PureExpr> {
    // Strip Deref wrappers to find the underlying constructor.
    // Match postconditions from `match *self { ... }` produce
    // Deref(LogicFnCall("None", [])) after self-substitution.
    let inner = strip_deref_layers(scrutinee);

    let (ctor_name, ctor_args) = match inner {
        PureExpr::LogicFnCall { name, args } => (name.as_str(), args.as_slice()),
        _ => return None,
    };

    for arm in arms {
        if let Some(bindings) = match_constructor_pattern(&arm.pattern, ctor_name, ctor_args) {
            if bindings.is_empty() {
                return Some(arm.body.clone());
            }
            return Some(arm.body.substitute(&bindings));
        }
    }

    // No constructor pattern matched — check for wildcard/binding fallback.
    // The last arm in well-formed match expressions is often a catch-all.
    for arm in arms.iter().rev() {
        match &arm.pattern {
            Pattern::Wildcard => return Some(arm.body.clone()),
            Pattern::Binding(name) => {
                let mut bindings = HashMap::new();
                bindings.insert(name.clone(), inner.clone());
                return Some(arm.body.substitute(&bindings));
            }
            Pattern::Alias { alias, pattern }
                if matches!(pattern.as_ref(), Pattern::Wildcard | Pattern::Binding(_)) =>
            {
                let mut bindings = match_inner_pattern(pattern, inner)?;
                merge_binding(&mut bindings, alias.clone(), inner.clone())?;
                return Some(arm.body.substitute(&bindings));
            }
            _ => {}
        }
    }

    None
}

/// Strip `Deref` wrappers from an expression to find the underlying value.
fn strip_deref_layers(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::Deref(inner) => strip_deref_layers(inner),
        other => other,
    }
}

/// Try to match a `Pattern` against a known constructor name and its arguments.
///
/// Returns `Some(bindings)` if the pattern matches, where bindings map
/// pattern-bound variable names to the constructor's field values.
/// Returns `None` if the pattern does not match this constructor.
fn match_constructor_pattern(
    pattern: &Pattern,
    ctor_name: &str,
    ctor_args: &[PureExpr],
) -> Option<HashMap<String, PureExpr>> {
    match pattern {
        Pattern::Alias { alias, pattern } => {
            let ctor_expr = PureExpr::LogicFnCall {
                name: ctor_name.to_string(),
                args: ctor_args.to_vec(),
            };
            let mut bindings = match_inner_pattern(pattern, &ctor_expr)?;
            merge_binding(&mut bindings, alias.clone(), ctor_expr)?;
            Some(bindings)
        }
        Pattern::Constructor { name, inner } => {
            if name != ctor_name {
                return None;
            }
            match inner {
                None => {
                    // Nullary constructor pattern (e.g., `None`).
                    // Matches if the constructor has no arguments.
                    if ctor_args.is_empty() {
                        Some(HashMap::new())
                    } else {
                        None
                    }
                }
                Some(inner_pattern) => {
                    if ctor_args.len() == 1 {
                        // Single-field constructor (e.g., `Some(v)`).
                        return match_inner_pattern(inner_pattern, &ctor_args[0]);
                    }
                    // Multi-field constructor: inner must be a Tuple pattern.
                    if let Pattern::Tuple(patterns) = inner_pattern.as_ref() {
                        if patterns.len() != ctor_args.len() {
                            return None;
                        }
                        let mut all_bindings = HashMap::new();
                        for (pat, val) in patterns.iter().zip(ctor_args.iter()) {
                            let bindings = match_inner_pattern(pat, val)?;
                            for (k, v) in bindings {
                                merge_binding(&mut all_bindings, k, v)?;
                            }
                        }
                        Some(all_bindings)
                    } else {
                        None
                    }
                }
            }
        }
        // Wildcard and Binding patterns match any constructor; handled by caller.
        _ => None,
    }
}

/// Match an inner pattern against a concrete value, producing bindings.
fn match_inner_pattern(pattern: &Pattern, value: &PureExpr) -> Option<HashMap<String, PureExpr>> {
    match pattern {
        Pattern::Alias { alias, pattern } => {
            let mut bindings = match_inner_pattern(pattern, value)?;
            merge_binding(&mut bindings, alias.clone(), value.clone())?;
            Some(bindings)
        }
        Pattern::Wildcard => Some(HashMap::new()),
        Pattern::Binding(name) => {
            let mut bindings = HashMap::new();
            bindings.insert(name.clone(), value.clone());
            Some(bindings)
        }
        Pattern::Literal(lit) => {
            if lit == value {
                Some(HashMap::new())
            } else {
                None
            }
        }
        Pattern::Constructor { name, inner } => {
            // Nested constructor pattern (e.g., `Some(Ok(x))`).
            if let PureExpr::LogicFnCall {
                name: ctor_name,
                args,
            } = value
            {
                if ctor_name == name {
                    match inner {
                        None if args.is_empty() => Some(HashMap::new()),
                        Some(inner_pat) if args.len() == 1 => {
                            match_inner_pattern(inner_pat, &args[0])
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
        Pattern::Tuple(patterns) => {
            // Tuple pattern against tuple constructor.
            if let PureExpr::LogicFnCall { args, .. } = value {
                if patterns.len() != args.len() {
                    return None;
                }
                let mut all_bindings = HashMap::new();
                for (pat, val) in patterns.iter().zip(args.iter()) {
                    let bindings = match_inner_pattern(pat, val)?;
                    for (k, v) in bindings {
                        merge_binding(&mut all_bindings, k, v)?;
                    }
                }
                Some(all_bindings)
            } else {
                None
            }
        }
        // Pattern is #[non_exhaustive]; handle future variants conservatively.
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

fn merge_binding(
    bindings: &mut HashMap<String, PureExpr>,
    name: String,
    value: PureExpr,
) -> Option<()> {
    if let Some(existing) = bindings.get(&name) {
        if existing != &value {
            return None;
        }
        return Some(());
    }
    bindings.insert(name, value);
    Some(())
}

fn reuse_arc(original: &Arc<PureExpr>, rewritten: PureExpr) -> Arc<PureExpr> {
    if rewritten.ptr_eq_shallow(original.as_ref()) || &rewritten == original.as_ref() {
        Arc::clone(original)
    } else {
        Arc::new(rewritten)
    }
}

/// Quick syntactic check for obviously false expressions.
pub(crate) fn is_obviously_false(expr: &PureExpr) -> bool {
    matches!(simplify_ground(expr), PureExpr::Bool(false))
}

#[cfg(test)]
mod tests;
