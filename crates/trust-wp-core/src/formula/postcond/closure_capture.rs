// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure-capture postcondition and precondition transforms.
//!
//! For `FnMut` closures, captured mutable state is tracked as `self.N` fields.
//! This module rewrites `Var("self.N")` references depending on position:
//!
//! - **Postcondition** (outside `old`): `Var("self.N")` → `Final(Deref(Var("self.N")))`
//! - **Postcondition** (inside `old`): `Var("self.N")` → `Deref(Var("self.N"))`
//! - **Precondition**: `Var("self.N")` → `Deref(Var("self.N"))`

use std::{collections::HashSet, sync::Arc};

use super::{super::pure_expr::PureExpr, traversal::rewrite_with_old_context};

/// Rewrite a postcondition for `FnMut` closure captures.
pub(crate) fn transform_closure_capture_postcondition(
    expr: &PureExpr,
    capture_fields: &HashSet<String>,
) -> PureExpr {
    rewrite_captures(expr, capture_fields, false)
}

/// Rewrite a precondition for `FnMut` closure captures.
pub(crate) fn transform_closure_capture_precondition(
    expr: &PureExpr,
    capture_fields: &HashSet<String>,
) -> PureExpr {
    rewrite_captures(expr, capture_fields, true)
}

fn rewrite_captures(
    expr: &PureExpr,
    capture_fields: &HashSet<String>,
    is_precondition: bool,
) -> PureExpr {
    rewrite_with_old_context(expr, false, &mut |node, inside_old| {
        match node {
            PureExpr::Var(name, sort) if capture_fields.contains(name) => {
                let capture = PureExpr::Var(name.clone(), sort.clone());
                Some(if inside_old || is_precondition {
                    PureExpr::Deref(Arc::new(capture))
                } else {
                    PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(capture))))
                })
            }
            // Deref(Var("self.N")) for a capture field — same transform as bare Var.
            PureExpr::Deref(inner) => {
                if let PureExpr::Var(name, sort) = inner.as_ref() {
                    if capture_fields.contains(name) {
                        let capture = PureExpr::Var(name.clone(), sort.clone());
                        return Some(if inside_old || is_precondition {
                            PureExpr::Deref(Arc::new(capture))
                        } else {
                            PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(capture))))
                        });
                    }
                }
                None // fall through to generic recursion
            }
            _ => None, // fall through to generic recursion
        }
    })
}
