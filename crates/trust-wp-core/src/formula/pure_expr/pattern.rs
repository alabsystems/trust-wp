// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pattern binding helpers for match-arm pattern analysis.

use super::{Pattern, PureExpr};

impl Pattern {
    /// Check whether this pattern binds the given variable name.
    ///
    /// Used by `expr_references_var_name` and `expr_references_any_var` to
    /// exclude bound variables from free-variable searches, preventing false
    /// positives when a bound variable shadows a name in the search set. (#1468)
    #[must_use]
    pub fn binds_name(&self, name: &str) -> bool {
        match self {
            Pattern::Wildcard | Pattern::Literal(_) => false,
            Pattern::Binding(n) => n == name,
            Pattern::Constructor { inner, .. } => {
                inner.as_ref().is_some_and(|p| p.binds_name(name))
            }
            Pattern::Alias { alias, pattern } => alias == name || pattern.binds_name(name),
            Pattern::Tuple(elements) => elements.iter().any(|p| p.binds_name(name)),
        }
    }

    /// Collect all variable names bound by this pattern.
    ///
    /// Used by traversal functions that track bound variables (e.g.,
    /// `collect_ground_resolve_recursive`) to shadow pattern-bound names
    /// when recursing into match arm bodies.
    #[must_use]
    pub fn bound_names(&self) -> Vec<&str> {
        let mut names = Vec::new();
        self.collect_bound_name_refs(&mut names);
        names
    }

    fn collect_bound_name_refs<'a>(&'a self, out: &mut Vec<&'a str>) {
        match self {
            Pattern::Wildcard | Pattern::Literal(_) => {}
            Pattern::Binding(name) => out.push(name),
            Pattern::Constructor { inner, .. } => {
                if let Some(p) = inner {
                    p.collect_bound_name_refs(out);
                }
            }
            Pattern::Alias { alias, pattern } => {
                out.push(alias);
                pattern.collect_bound_name_refs(out);
            }
            Pattern::Tuple(elements) => {
                for p in elements {
                    p.collect_bound_name_refs(out);
                }
            }
        }
    }

    /// Return a new pattern with `old_name` renamed to `new_name` in bindings.
    ///
    /// Used by capture-avoiding substitution to alpha-rename match arm pattern
    /// bindings when a substitution value's free variable would collide.
    #[must_use]
    pub fn rename_binding(&self, old_name: &str, new_name: &str) -> Pattern {
        match self {
            Pattern::Wildcard | Pattern::Literal(_) => self.clone(),
            Pattern::Binding(name) if name == old_name => Pattern::Binding(new_name.to_string()),
            Pattern::Binding(_) => self.clone(),
            Pattern::Constructor { name, inner } => Pattern::Constructor {
                name: name.clone(),
                inner: inner
                    .as_ref()
                    .map(|p| Box::new(p.rename_binding(old_name, new_name))),
            },
            Pattern::Alias { alias, pattern } => Pattern::Alias {
                alias: if alias == old_name {
                    new_name.to_string()
                } else {
                    alias.clone()
                },
                pattern: Box::new(pattern.rename_binding(old_name, new_name)),
            },
            Pattern::Tuple(elements) => Pattern::Tuple(
                elements
                    .iter()
                    .map(|p| p.rename_binding(old_name, new_name))
                    .collect(),
            ),
        }
    }

    /// Remove bindings introduced by this pattern from the substitution map.
    ///
    /// Used by `substitute_vars_in_expr` to shadow pattern-bound variables in
    /// match arm bodies, preventing incorrect substitution of shadowed names.
    pub fn collect_bindings(&self, subs: &mut std::collections::HashMap<String, PureExpr>) {
        match self {
            Pattern::Wildcard | Pattern::Literal(_) => {}
            Pattern::Binding(name) => {
                subs.remove(name);
            }
            Pattern::Constructor { inner, .. } => {
                if let Some(inner_pat) = inner {
                    inner_pat.collect_bindings(subs);
                }
            }
            Pattern::Alias { alias, pattern } => {
                subs.remove(alias);
                pattern.collect_bindings(subs);
            }
            Pattern::Tuple(elements) => {
                for elem in elements {
                    elem.collect_bindings(subs);
                }
            }
        }
    }
}
