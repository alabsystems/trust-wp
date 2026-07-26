// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Postcondition transformation for mutable references and closure captures.
//!
//! Implements the `RustHorn`-style encoding transforms that rewrite
//! `*x` → `^x` for mutable reference postconditions and handle closure
//! capture pre/postcondition rewrites.
//!
//! Internal structure:
//! - `traversal` — shared `inside_old`-aware tree walk
//! - `closure_capture` — `self.N` pre/postcondition rewrite rules
//! - `mut_refs` — `*x` / `^x` normalization for `&mut` params

mod closure_capture;
mod mut_refs;
mod traversal;

use super::pure_expr::PureExpr;

impl PureExpr {
    /// Transform a postcondition for mutable borrow verification.
    ///
    /// In user-facing syntax, postconditions like `*x == old(*x) + 1` mean:
    /// - `*x` refers to the final value (when the borrow ends)
    /// - `old(*x)` refers to the initial value (at function entry)
    ///
    /// But internally, the `RustHorn` encoding uses:
    /// - `Final(Var(x))` (^x) for the final value
    /// - `Deref(Var(x))` (*x) for the initial/current value
    ///
    /// This function transforms postconditions from user syntax to `RustHorn` encoding:
    /// - `Deref(Var(x))` where x is a mut ref param → `Final(Var(x))`
    /// - `Old(Deref(Var(x)))` stays unchanged (already refers to initial)
    ///
    /// # Arguments
    /// * `mut_ref_params` - Set of parameter names that are `&mut T`
    ///
    /// # Returns
    /// Transformed expression suitable for `verify_mut_borrow_function`
    ///
    /// # Example
    /// ```
    /// use std::{collections::HashSet, sync::Arc};
    ///
    /// use trust_wp_core::formula::PureExpr;
    ///
    /// // *x == old(*x) + 1
    /// let postcond = PureExpr::BinOp(
    ///     Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
    ///         "x".to_string(),
    ///         None,
    ///     )))),
    ///     trust_wp_core::formula::BinOp::Eq,
    ///     Arc::new(PureExpr::BinOp(
    ///         Arc::new(PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
    ///             PureExpr::Var("x".to_string(), None),
    ///         ))))),
    ///         trust_wp_core::formula::BinOp::Add,
    ///         Arc::new(PureExpr::Int(1)),
    ///     )),
    /// );
    ///
    /// let mut_refs: HashSet<String> = ["x".to_string()].into_iter().collect();
    /// let transformed = postcond.transform_postcondition_for_mut_refs(&mut_refs);
    ///
    /// // Now: ^x == old(*x) + 1
    /// // - *x became ^x (Final) because it's outside Old
    /// // - old(*x) stayed the same
    /// ```
    #[must_use]
    pub fn transform_postcondition_for_mut_refs(
        &self,
        mut_ref_params: &std::collections::HashSet<String>,
    ) -> PureExpr {
        mut_refs::transform_postcondition_for_mut_refs(self, mut_ref_params)
    }

    /// Transform a postcondition for `FnMut` closure captures.
    ///
    /// For closure captures that are mutated (tracked as `self.N` in `final_values`),
    /// bare `Var("self.N")` in the postcondition must be mapped to:
    /// - `Final(Deref(Var("self.N")))` outside `old()` (the final captured value)
    /// - `Deref(Var("self.N"))` inside `old()` (the initial value)
    ///
    /// This differs from `transform_postcondition_for_mut_refs` which transforms
    /// `Deref(Var("x"))` → `Final(Var("x"))`. Closure captures don't use explicit
    /// deref syntax in user contracts because the capture substitution already
    /// resolved the variable name to `self.N`.
    #[must_use]
    pub fn transform_closure_capture_postcondition(
        &self,
        capture_fields: &std::collections::HashSet<String>,
    ) -> PureExpr {
        closure_capture::transform_closure_capture_postcondition(self, capture_fields)
    }

    /// Transform a precondition for `FnMut` closure captures.
    ///
    /// In preconditions, `Var("self.N")` should become `Deref(Var("self.N"))`
    /// to reference the current (initial) value of the capture at function entry.
    #[must_use]
    pub fn transform_closure_capture_precondition(
        &self,
        capture_fields: &std::collections::HashSet<String>,
    ) -> PureExpr {
        closure_capture::transform_closure_capture_precondition(self, capture_fields)
    }
}
