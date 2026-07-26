// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Substitution policy, free-variable summaries, and scoped overlay state.

use std::collections::{HashMap, HashSet};

use super::{super::pure_expr::PureExpr, depth_limit_exceeded};

/// Options for capture-avoiding substitution.
///
/// `depth_limit` is caller policy. ay-backed callers can pass the encoder's
/// recursion limit, while non-ay callers can leave it as `None`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CaptureAvoidingSubstOptions {
    /// Maximum recursion depth before the transformation conservatively stops.
    pub depth_limit: Option<usize>,
}

#[derive(Clone, Copy)]
pub(super) struct SubstituteOptions<'a> {
    pub(super) filter: Option<&'a HashSet<&'a str>>,
    pub(super) beta_reduce_tuples: bool,
}

impl SubstituteOptions<'_> {
    pub(super) fn allows_name(self, name: &str) -> bool {
        match self.filter {
            Some(filter) => filter.contains(name),
            None => true,
        }
    }
}

/// Pre-collected free variable names for one substitution value.
///
/// If the collection hit the depth limit, `truncated` is true and membership
/// checks must fall back to the recursive `expr_has_free_occurrence` scan for
/// this value rather than trusting the summary alone.
struct FreeVarSummary {
    names: HashSet<String>,
    truncated: bool,
}

/// Collect free variable names from `expr`, respecting the depth limit.
fn collect_free_vars_with_limit(expr: &PureExpr, depth_limit: Option<usize>) -> FreeVarSummary {
    let mut names = HashSet::new();
    let truncated = collect_free_vars_inner(expr, &mut names, 0, depth_limit, &HashSet::new());
    FreeVarSummary { names, truncated }
}

/// Returns `true` if depth was exceeded (truncated).
fn collect_free_vars_inner(
    expr: &PureExpr,
    out: &mut HashSet<String>,
    depth: usize,
    depth_limit: Option<usize>,
    bound: &HashSet<String>,
) -> bool {
    if depth_limit_exceeded(depth, depth_limit) {
        return true;
    }
    let next = depth + 1;
    match expr {
        PureExpr::Var(name, _) => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
            false
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => false,
        PureExpr::BinOp(left, _, right) => {
            collect_free_vars_inner(left, out, next, depth_limit, bound)
                | collect_free_vars_inner(right, out, next, depth_limit, bound)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner) => collect_free_vars_inner(inner, out, next, depth_limit, bound),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_free_vars_inner(cond, out, next, depth_limit, bound)
                | collect_free_vars_inner(then_expr, out, next, depth_limit, bound)
                | collect_free_vars_inner(else_expr, out, next, depth_limit, bound)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            let mut trunc = collect_free_vars_inner(receiver, out, next, depth_limit, bound);
            for arg in args {
                trunc |= collect_free_vars_inner(arg, out, next, depth_limit, bound);
            }
            trunc
        }
        PureExpr::LogicFnCall { args, .. } => {
            let mut trunc = false;
            for arg in args {
                trunc |= collect_free_vars_inner(arg, out, next, depth_limit, bound);
            }
            trunc
        }
        PureExpr::Forall { var, body, .. } | PureExpr::Exists { var, body, .. } => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            collect_free_vars_inner(body, out, next, depth_limit, &inner_bound)
        }
        PureExpr::Let { var, value, body } => {
            let trunc = collect_free_vars_inner(value, out, next, depth_limit, bound);
            let mut inner_bound = bound.clone();
            inner_bound.insert(var.clone());
            trunc | collect_free_vars_inner(body, out, next, depth_limit, &inner_bound)
        }
        PureExpr::Match { scrutinee, arms } => {
            let mut trunc = collect_free_vars_inner(scrutinee, out, next, depth_limit, bound);
            for arm in arms {
                let mut inner_bound = bound.clone();
                for name in arm.pattern.bound_names() {
                    inner_bound.insert(name.to_string());
                }
                trunc |= collect_free_vars_inner(&arm.body, out, next, depth_limit, &inner_bound);
            }
            trunc
        }
        PureExpr::LetAssume { assumption, body }
        | PureExpr::LetObligation {
            obligation: assumption,
            body,
        } => {
            collect_free_vars_inner(assumption, out, next, depth_limit, bound)
                | collect_free_vars_inner(body, out, next, depth_limit, bound)
        }
        PureExpr::Closure { params, body } => {
            let mut inner_bound = bound.clone();
            for (param, _) in params {
                inner_bound.insert(param.clone());
            }
            collect_free_vars_inner(body, out, next, depth_limit, &inner_bound)
        }
    }
}

/// Scoped view of a substitution map that shadows binder names in-place.
///
/// Capture-avoiding substitution only needs to hide existing substitution keys
/// at binder boundaries; it never introduces new replacement entries. Tracking
/// shadowed names avoids cloning the full substitution map for each binder.
///
/// Maintains a pre-collected free-variable summary per base entry and an
/// aggregate count of visible free-var mentions so that capture checks
/// answer from the aggregate instead of rescanning visible value ASTs.
pub(super) struct ScopedSubstitutions<'a> {
    base: &'a HashMap<String, PureExpr>,
    shadowed: HashMap<String, usize>,
    /// Per-base-entry free variable summaries, keyed by substitution key.
    summaries: HashMap<String, FreeVarSummary>,
    /// Aggregate count of each free variable name across currently visible
    /// (non-shadowed) substitution values. A name with count > 0 appears
    /// free in at least one visible value.
    visible_free_var_counts: HashMap<String, usize>,
}

impl<'a> ScopedSubstitutions<'a> {
    /// Create a scoped view with precomputed free-variable summaries.
    ///
    /// Used by the capture-avoiding substitution path where `visible_value_mentions`
    /// needs the free-var cache.
    pub(super) fn new(base: &'a HashMap<String, PureExpr>, depth_limit: Option<usize>) -> Self {
        let mut summaries = HashMap::with_capacity(base.len());
        let mut visible_free_var_counts: HashMap<String, usize> = HashMap::new();
        for (key, value) in base {
            let summary = collect_free_vars_with_limit(value, depth_limit);
            for name in &summary.names {
                *visible_free_var_counts.entry(name.clone()).or_default() += 1;
            }
            summaries.insert(key.clone(), summary);
        }
        Self {
            base,
            shadowed: HashMap::new(),
            summaries,
            visible_free_var_counts,
        }
    }

    /// Create a lightweight scoped view without free-variable summaries.
    ///
    /// Used by the plain substitution path (`substitute()` / `substitute_filtered()`)
    /// where only shadow/unshadow tracking is needed, not capture avoidance.
    pub(super) fn new_plain(base: &'a HashMap<String, PureExpr>) -> Self {
        Self {
            base,
            shadowed: HashMap::new(),
            summaries: HashMap::new(),
            visible_free_var_counts: HashMap::new(),
        }
    }

    pub(super) fn get(&self, name: &str) -> Option<&PureExpr> {
        if self.is_shadowed(name) {
            None
        } else {
            self.base.get(name)
        }
    }

    pub(super) fn contains_key(&self, name: &str) -> bool {
        !self.is_shadowed(name) && self.base.contains_key(name)
    }

    pub(super) fn shadow_name(&mut self, name: &str) {
        let was_visible = !self.is_shadowed(name) && self.base.contains_key(name);
        *self.shadowed.entry(name.to_string()).or_default() += 1;
        // If this name was a visible base key and is now shadowed for the
        // first time, subtract its free-var summary from the aggregate.
        if was_visible {
            if let Some(summary) = self.summaries.get(name) {
                for var in &summary.names {
                    if let Some(count) = self.visible_free_var_counts.get_mut(var) {
                        *count = count.saturating_sub(1);
                    }
                }
            }
        }
    }

    pub(super) fn shadow_names<'b>(
        &mut self,
        names: impl IntoIterator<Item = &'b str>,
    ) -> Vec<String> {
        let names: Vec<String> = names.into_iter().map(str::to_owned).collect();
        for name in &names {
            self.shadow_name(name);
        }
        names
    }

    pub(super) fn unshadow_name(&mut self, name: &str) {
        let mut remove_entry = false;
        if let Some(count) = self.shadowed.get_mut(name) {
            *count -= 1;
            remove_entry = *count == 0;
        }
        if remove_entry {
            self.shadowed.remove(name);
        }
        // If this name is a base key and just became visible again, add its
        // free-var summary back to the aggregate.
        let now_visible = !self.is_shadowed(name) && self.base.contains_key(name);
        if now_visible && remove_entry {
            if let Some(summary) = self.summaries.get(name) {
                for var in &summary.names {
                    *self.visible_free_var_counts.entry(var.clone()).or_default() += 1;
                }
            }
        }
    }

    fn is_shadowed(&self, name: &str) -> bool {
        self.shadowed.contains_key(name)
    }

    /// Check whether `name` appears free in any currently visible substitution
    /// value. Uses the precomputed aggregate counts and falls back to AST
    /// scanning only for entries whose summaries were truncated by depth limits.
    pub(super) fn visible_value_mentions(&self, name: &str, depth_limit: Option<usize>) -> bool {
        // Fast path: if the aggregate says this name is mentioned, it is.
        if self.visible_free_var_counts.get(name).copied().unwrap_or(0) > 0 {
            return true;
        }
        // Slow path: check truncated summaries via full AST scan.
        let options = CaptureAvoidingSubstOptions { depth_limit };
        self.base
            .iter()
            .filter(|(key, _)| !self.is_shadowed(key))
            .any(|(key, value)| {
                self.summaries.get(key).is_some_and(|s| s.truncated)
                    && super::rename::expr_has_free_occurrence(value, name, &options)
            })
    }
}
