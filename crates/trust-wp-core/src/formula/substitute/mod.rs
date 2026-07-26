// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Variable substitution for pure expressions.
//!
//! Provides the formula-aware substitution family
//! (`substitute()`, `substitute_no_tuple_beta()`, and `substitute_filtered()`)
//! plus the capture-avoiding `substitute_capture_avoiding()` helper.

mod capture_avoiding;
mod overlay;
mod plain;
pub(crate) mod rename;

use std::collections::{HashMap, HashSet};

use capture_avoiding::substitute_capture_avoiding_inner;
pub use overlay::CaptureAvoidingSubstOptions;
use overlay::{ScopedSubstitutions, SubstituteOptions};
use plain::substitute_with_options_inner;
pub use rename::{expr_has_free_occurrence, rename_free_var};

use super::pure_expr::{reuse_arc, reuse_node as reuse_expr, PureExpr};

fn depth_limit_exceeded(depth: usize, depth_limit: Option<usize>) -> bool {
    matches!(depth_limit, Some(limit) if depth > limit)
}

impl PureExpr {
    /// Substitute variables in this expression.
    ///
    /// Each variable matching a key in `substitutions` is replaced with
    /// the corresponding expression. Other variables are left unchanged.
    ///
    /// At binder boundaries (`Forall`, `Exists`, `Match`, `Let`, `Closure`),
    /// the bound variable is shadowed in an overlay rather than cloning the
    /// full substitution map. This makes binder traversal O(1) per binder
    /// instead of O(s) per binder.
    ///
    /// Includes tuple beta-reduction: `tuple_get_N(tupleK(a0,...)) → aN`.
    ///
    /// # Arguments
    /// * `substitutions` - Map from variable names to replacement expressions
    ///
    /// # Returns
    /// A new expression with substitutions applied
    #[must_use]
    pub fn substitute(&self, substitutions: &HashMap<String, PureExpr>) -> PureExpr {
        self.substitute_with_options(
            substitutions,
            SubstituteOptions {
                filter: None,
                beta_reduce_tuples: true,
            },
        )
    }

    /// Substitute variables without tuple beta-reduction.
    ///
    /// Like `substitute()`, but skips the `tuple_get_N(tupleK(...)) → aN`
    /// reduction. Use this in `proof_assert` paths where projected write facts
    /// (e.g., `tuple_get_0(p) == 4`) come through as separate preconditions
    /// that the solver must reason about. Beta-reduction would collapse
    /// `tuple_get_0(tuple2(2, 3))` → `2` before the solver sees the write
    /// fact, making post-mutation assertions unprovable. (#1572)
    #[must_use]
    pub fn substitute_no_tuple_beta(&self, substitutions: &HashMap<String, PureExpr>) -> PureExpr {
        self.substitute_with_options(
            substitutions,
            SubstituteOptions {
                filter: None,
                beta_reduce_tuples: false,
            },
        )
    }

    /// Substitute variables using a scoped overlay instead of cloning the
    /// substitution `HashMap` at binder boundaries.
    fn substitute_with_options(
        &self,
        substitutions: &HashMap<String, PureExpr>,
        options: SubstituteOptions<'_>,
    ) -> PureExpr {
        let mut binding = ScopedSubstitutions::new_plain(substitutions);
        substitute_with_options_inner(self, &mut binding, options)
    }

    /// Substitute variables while alpha-renaming binders that would capture
    /// free variables from substitution values.
    #[must_use]
    pub fn substitute_capture_avoiding(
        &self,
        substitutions: &HashMap<String, PureExpr>,
        options: &CaptureAvoidingSubstOptions,
    ) -> PureExpr {
        let mut scoped_substitutions = ScopedSubstitutions::new(substitutions, options.depth_limit);
        substitute_capture_avoiding_inner(self, &mut scoped_substitutions, 0, options.depth_limit)
    }

    /// Substitute variables in this expression, only for variables in the filter set.
    ///
    /// This is used for loop body effect substitution where only modified variables
    /// should be replaced. A variable is substituted if it appears in BOTH `filter`
    /// AND `substitutions`.
    ///
    /// # Arguments
    /// * `filter` - Set of variable names eligible for substitution
    /// * `substitutions` - Map from variable names to replacement expressions
    ///
    /// # Returns
    /// A new expression with filtered substitutions applied
    ///
    /// # Example
    /// ```
    /// use std::collections::{HashMap, HashSet};
    ///
    /// use trust_wp_core::formula::PureExpr;
    ///
    /// let expr = PureExpr::Var("x".to_string(), None);
    /// let filter: HashSet<&str> = ["x"].into_iter().collect();
    /// let mut subs = HashMap::new();
    /// subs.insert("x".to_string(), PureExpr::Int(42));
    ///
    /// let result = expr.substitute_filtered(&filter, &subs);
    /// assert!(matches!(result, PureExpr::Int(42)));
    /// ```
    #[must_use]
    pub fn substitute_filtered(
        &self,
        filter: &HashSet<&str>,
        substitutions: &HashMap<String, PureExpr>,
    ) -> PureExpr {
        self.substitute_with_options(
            substitutions,
            SubstituteOptions {
                filter: Some(filter),
                beta_reduce_tuples: true,
            },
        )
    }
}
