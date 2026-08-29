// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic function name collection from `PureExpr` trees.

use std::collections::HashSet;

use trust_wp_core::formula::{Pattern, PureExpr, PureExprDepthLimitedTraversalExt as _};

use crate::encoder::MAX_ENCODING_DEPTH;

/// Recursively collects all logic function names referenced in an expression.
///
/// Traverses the `PureExpr` tree and inserts the name of every `LogicFnCall`
/// into the provided set. Used by `filter_logic_fns_for_goal` to determine
/// which logic function axioms need to be included in a verification query.
pub(crate) fn collect_logic_fn_names(expr: &PureExpr, names: &mut HashSet<String>) {
    expr.for_each_recursive_with_depth_limit(MAX_ENCODING_DEPTH, |node| {
        match node {
            PureExpr::MethodCall {
                receiver, method, ..
            } => {
                // Method-style logic functions (e.g., `self.sub_pre(rhs)`) are
                // encoded as MethodCall AST nodes but still require the matching
                // logic function definition to be registered. Collect the method
                // name so goal filtering keeps the dependency.
                names.insert(method.clone());

                // Closure-spec methods are different: the method name is the
                // built-in dispatcher (`precondition`, `postcondition`, etc.)
                // while the receiver is the actual logic-function carrier that
                // must stay registered for the encoder to assert its axioms.
                if matches!(
                    method.as_str(),
                    "precondition" | "postcondition" | "postcondition_once" | "postcondition_mut"
                ) {
                    if let Some(receiver_name) = receiver_logic_fn_name(receiver) {
                        names.insert(receiver_name.clone());
                        if let Some((_, leaf)) = receiver_name.rsplit_once("::") {
                            names.insert(leaf.to_string());
                        }
                    }
                }
            }
            PureExpr::LogicFnCall { name, .. } => {
                names.insert(name.clone());
            }
            PureExpr::Match { arms, .. } => {
                // The walker handles arm bodies; patterns need separate traversal
                // because Pattern::Literal can contain nested PureExpr trees.
                for arm in arms {
                    collect_logic_fn_names_in_pattern(&arm.pattern, names);
                }
            }
            _ => {}
        }
    });
}

fn receiver_logic_fn_name(receiver: &PureExpr) -> Option<String> {
    match receiver {
        PureExpr::Var(name, _) => Some(name.clone()),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => receiver_logic_fn_name(inner),
        _ => None,
    }
}

/// Collects logic function names from pattern literals.
///
/// Helper for `collect_logic_fn_names` to handle match arm patterns.
/// Pattern literals can contain expressions that reference logic functions.
fn collect_logic_fn_names_in_pattern(pattern: &Pattern, names: &mut HashSet<String>) {
    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) => {}
        Pattern::Literal(expr) => collect_logic_fn_names(expr, names),
        Pattern::Constructor {
            inner: Some(inner), ..
        } => collect_logic_fn_names_in_pattern(inner, names),
        Pattern::Constructor { inner: None, .. } => {}
        Pattern::Tuple(elements) => {
            for elem in elements {
                collect_logic_fn_names_in_pattern(elem, names);
            }
        }
        // Pattern is non-exhaustive across crates, so keep a wildcard arm.
        #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
        _ => {}
    }
}
