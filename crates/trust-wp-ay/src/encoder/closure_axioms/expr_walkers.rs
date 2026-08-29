// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PureExpr tree walkers for detecting `postcondition_mut` method calls.
//!
//! These are pure static methods on `AYEncoder` that traverse `PureExpr` trees
//! without requiring encoder state. Used by the Skolemization and eager
//! instantiation logic in [`super::fn_mut_once`] and by verification setup
//! code in `verify/setup.rs` and `verify/loops/mod.rs`.

use trust_wp_core::formula::{PureExpr, PureExprDepthLimitedTraversalExt as _};

use super::super::{AYEncoder, MAX_ENCODING_DEPTH};

/// Result of a single-pass postcondition context scan (#2694).
///
/// Consolidates three separate expression-tree traversals into one pass.
/// The three boolean flags (`has_any`, `has_mut`, `has_once`) are computed
/// simultaneously during a single depth-limited walk of each expression.
/// This avoids 2 redundant traversals of potentially large expression trees
/// in `assert_standard_axioms`, where `body_has_any_closure_postcondition`,
/// `body_has_any_postcondition_mut`, and `body_has_any_postcondition_once`
/// were called sequentially on the same requires + body_assumptions slices.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct PostconditionContextFlags {
    /// True if any of `postcondition`, `postcondition_mut`, or `postcondition_once`
    /// method calls appear in the scanned expressions.
    pub(crate) has_any: bool,
    /// True if a `postcondition_mut` method call appears.
    pub(crate) has_mut: bool,
    /// True if a `postcondition_once` method call appears.
    pub(crate) has_once: bool,
}

impl PostconditionContextFlags {
    /// Merge flags from another scan (logical OR on each field).
    fn merge(&mut self, other: Self) {
        self.has_any |= other.has_any;
        self.has_mut |= other.has_mut;
        self.has_once |= other.has_once;
    }

    /// True when all three flags are set — no further scanning needed.
    fn is_saturated(&self) -> bool {
        self.has_any && self.has_mut && self.has_once
    }
}

impl AYEncoder {
    /// Single-pass scan of requires + body_assumptions for closure spec method
    /// calls (#2694).
    ///
    /// Replaces 3 sequential traversals (any, mut, once) with one pass that sets
    /// all three flags simultaneously. `has_any` is intentionally raised for both
    /// closure postconditions and closure preconditions so solver-tail demand
    /// guards do not skip closure axioms when a VC only exposes `precondition(...)`
    /// ground terms, as in `generic_deref.rs`. Early-exits as soon as all three
    /// flags are saturated.
    pub(crate) fn scan_postcondition_context(
        requires: &[PureExpr],
        body_assumptions: &[&PureExpr],
    ) -> PostconditionContextFlags {
        let mut flags = PostconditionContextFlags::default();

        for expr in requires {
            flags.merge(Self::scan_single_expr(expr));
            if flags.is_saturated() {
                return flags;
            }
        }
        for expr in body_assumptions {
            flags.merge(Self::scan_single_expr(expr));
            if flags.is_saturated() {
                return flags;
            }
        }
        flags
    }

    /// Scan a single expression for postcondition method calls.
    fn scan_single_expr(body: &PureExpr) -> PostconditionContextFlags {
        let mut flags = PostconditionContextFlags::default();
        // fail-closed: `on_limit = true` assumes postcondition exists at depth limit
        body.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
            if let PureExpr::MethodCall { method, .. } = e {
                match method.as_str() {
                    "precondition" => {
                        flags.has_any = true;
                    }
                    "postcondition" => {
                        flags.has_any = true;
                    }
                    "postcondition_mut" => {
                        flags.has_any = true;
                        flags.has_mut = true;
                    }
                    "postcondition_once" => {
                        flags.has_any = true;
                        flags.has_once = true;
                    }
                    _ => {}
                }
            }
            // Return true only when saturated to trigger early-exit from traversal
            flags.is_saturated()
        });
        flags
    }

    /// Check whether a `PureExpr` body contains a `postcondition_mut` method call
    /// that references the given bound variable name.
    ///
    /// Uses the binding-aware walker to skip subtrees where `var` is shadowed
    /// by a binder (Forall/Exists/Let/Closure/Match pattern bindings).
    pub(crate) fn body_has_postcondition_mut_with_var(body: &PureExpr, var: &str) -> bool {
        // fail-closed: `on_limit = true` assumes postcondition_mut exists at depth limit
        body.any_recursive_binding_aware_with_depth_limit(var, MAX_ENCODING_DEPTH, true, |e| {
            if let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = e
            {
                // Check both receiver and args — the bound variable may appear as
                // the receiver (e.g., `st1.postcondition_mut((), st2, result)`) or
                // as a state/result argument. Previously only args were checked,
                // causing Skolemization to skip existential variables that appear
                // as chained postcondition_mut receivers. (#2668)
                method == "postcondition_mut"
                    && (crate::expr::expr_mentions_var(receiver, var)
                        || args.iter().any(|a| crate::expr::expr_mentions_var(a, var)))
            } else {
                false
            }
        })
    }

    /// Check whether a `PureExpr` transitively contains any `postcondition_mut`
    /// method call, ignoring which variables are referenced. Used to decide
    /// whether to Skolemize through intermediate existential layers that don't
    /// directly bind a variable used in postcondition_mut args.
    pub(crate) fn body_has_any_postcondition_mut(body: &PureExpr) -> bool {
        // fail-closed: `on_limit = true` assumes postcondition_mut exists at depth limit
        body.any_recursive_with_depth_limit(
            MAX_ENCODING_DEPTH,
            true,
            |e| matches!(e, PureExpr::MethodCall { method, .. } if method == "postcondition_mut"),
        )
    }

    /// Check whether a `PureExpr` transitively contains any `postcondition_once`
    /// method call. Retained for test-only agreement verification with the
    /// consolidated `scan_postcondition_context` implementation (#2694).
    /// Production code uses `scan_postcondition_context` instead. (#2668, #2674)
    #[cfg(test)]
    pub(crate) fn body_has_any_postcondition_once(body: &PureExpr) -> bool {
        // fail-closed: `on_limit = true` assumes postcondition_once exists at depth limit
        body.any_recursive_with_depth_limit(
            MAX_ENCODING_DEPTH,
            true,
            |e| matches!(e, PureExpr::MethodCall { method, .. } if method == "postcondition_once"),
        )
    }

    /// Check whether a `PureExpr` transitively contains any closure postcondition
    /// method call (`postcondition`, `postcondition_mut`, or `postcondition_once`).
    ///
    /// Retained for test-only agreement verification with the consolidated
    /// `scan_postcondition_context` implementation (#2694).
    /// Production code uses `scan_postcondition_context` instead. (#2674)
    #[cfg(test)]
    pub(crate) fn body_has_any_closure_postcondition(body: &PureExpr) -> bool {
        // fail-closed: `on_limit = true` assumes a postcondition exists at depth limit
        body.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
            matches!(e, PureExpr::MethodCall { method, .. }
                if method == "postcondition"
                    || method == "postcondition_mut"
                    || method == "postcondition_once")
        })
    }
}
