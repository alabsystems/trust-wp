// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specification text whose named-field metadata was never PLACED.
//!
//! The contract parser cannot see a declaration, so it hands the driver a
//! constructor name with the field names it read glued on —
//! [`named_struct_ctor_name`](super::named_struct_ctor_name) builds
//! `"S{b,a}"` for `S { b: _, a: aa }`. Those names are an INSTRUCTION to the
//! driver: place each sub-pattern at the index its declaration gives it. They
//! are not a representation the encoder can read. The encoder binds
//! sub-patterns positionally, so a name that still carries field metadata when
//! it arrives there binds them in the order they were WRITTEN — which is the
//! right answer only when the author happened to write the fields in
//! declaration order, and types one field as another otherwise.
//!
//! This module is the detector for that condition, and it lives beside
//! [`named_struct_ctor_name`] and
//! [`parse_named_struct_ctor`](super::parse_named_struct_ctor) on purpose: the
//! encoding of the metadata and the test for "still encoded" cannot drift
//! apart if they are the same forty lines.
//!
//! Both walks below match every variant of [`PureExpr`] and [`Pattern`]
//! explicitly — no `_ =>` arm. Both types are `#[non_exhaustive]`, which binds
//! only other crates; inside this one the compiler still demands every variant,
//! so a variant added later that can hold a constructor name or a sub-pattern
//! is a COMPILE ERROR here rather than a silent hole in the detector.

use super::{parse_named_struct_ctor, Pattern, PureExpr};

/// The first constructor name in `expr` that still carries the parser's
/// named-field metadata, or `None` when every named-field pattern and literal
/// in it has been placed at its declared indices.
///
/// Searches the whole expression tree, including the PATTERNS of every match
/// arm — where a reordered named-field pattern hides from the plain
/// [`PureExpr::any_recursive`] walker, which visits arm bodies but not arm
/// patterns (`tests/adversarial/cases/s82_structpat_reorder_*`).
#[must_use]
pub fn first_unplaced_named_ctor(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => None,
        PureExpr::BinOp(left, _, right) => {
            first_unplaced_named_ctor(left).or_else(|| first_unplaced_named_ctor(right))
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => first_unplaced_named_ctor(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => first_unplaced_named_ctor(cond)
            .or_else(|| first_unplaced_named_ctor(then_expr))
            .or_else(|| first_unplaced_named_ctor(else_expr)),
        PureExpr::MethodCall { receiver, args, .. } => first_unplaced_named_ctor(receiver)
            .or_else(|| args.iter().find_map(first_unplaced_named_ctor)),
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            first_unplaced_named_ctor(body).or_else(|| {
                triggers
                    .iter()
                    .flat_map(|trigger| trigger.iter())
                    .find_map(first_unplaced_named_ctor)
            })
        }
        PureExpr::Match { scrutinee, arms } => first_unplaced_named_ctor(scrutinee).or_else(|| {
            arms.iter().find_map(|arm| {
                first_unplaced_named_ctor_in_pattern(&arm.pattern)
                    .or_else(|| first_unplaced_named_ctor(&arm.body))
            })
        }),
        PureExpr::LogicFnCall { name, args } => {
            if parse_named_struct_ctor(name).is_some() {
                return Some(name);
            }
            args.iter().find_map(first_unplaced_named_ctor)
        }
        PureExpr::Let { value, body, .. } => {
            first_unplaced_named_ctor(value).or_else(|| first_unplaced_named_ctor(body))
        }
        PureExpr::LetAssume { assumption, body } => {
            first_unplaced_named_ctor(assumption).or_else(|| first_unplaced_named_ctor(body))
        }
        PureExpr::LetObligation { obligation, body } => {
            first_unplaced_named_ctor(obligation).or_else(|| first_unplaced_named_ctor(body))
        }
        PureExpr::Closure { body, .. } => first_unplaced_named_ctor(body),
    }
}

/// The first constructor name in `pattern` that still carries named-field
/// metadata.
#[must_use]
pub fn first_unplaced_named_ctor_in_pattern(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) => None,
        Pattern::Literal(expr) => first_unplaced_named_ctor(expr),
        Pattern::Constructor { name, inner } => {
            if parse_named_struct_ctor(name).is_some() {
                return Some(name);
            }
            inner
                .as_deref()
                .and_then(first_unplaced_named_ctor_in_pattern)
        }
        Pattern::Alias { pattern, .. } => first_unplaced_named_ctor_in_pattern(pattern),
        Pattern::Tuple(elements) => elements
            .iter()
            .find_map(first_unplaced_named_ctor_in_pattern),
    }
}

#[cfg(test)]
mod tests {
    use super::{first_unplaced_named_ctor, first_unplaced_named_ctor_in_pattern};
    use crate::formula::{MatchArm, Pattern, PureExpr};

    fn named_pattern() -> Pattern {
        Pattern::Constructor {
            name: "S{b,a}".to_string(),
            inner: Some(Box::new(Pattern::Tuple(vec![
                Pattern::Wildcard,
                Pattern::Binding("aa".to_string()),
            ]))),
        }
    }

    #[test]
    fn a_placed_pattern_is_not_reported() {
        let arm = MatchArm {
            pattern: Pattern::Constructor {
                name: "S".to_string(),
                inner: Some(Box::new(Pattern::Binding("aa".to_string()))),
            },
            body: PureExpr::Var("aa".to_string(), None),
        };
        let expr = PureExpr::Match {
            scrutinee: std::sync::Arc::new(PureExpr::Var("s".to_string(), None)),
            arms: vec![arm],
        };
        assert_eq!(first_unplaced_named_ctor(&expr), None);
    }

    #[test]
    fn a_match_arm_pattern_is_searched() {
        let expr = PureExpr::Match {
            scrutinee: std::sync::Arc::new(PureExpr::Var("s".to_string(), None)),
            arms: vec![MatchArm {
                pattern: named_pattern(),
                body: PureExpr::Var("aa".to_string(), None),
            }],
        };
        assert_eq!(first_unplaced_named_ctor(&expr), Some("S{b,a}"));
    }

    #[test]
    fn a_nested_sub_pattern_is_searched() {
        let pattern = Pattern::Tuple(vec![
            Pattern::Wildcard,
            Pattern::Alias {
                alias: "w".to_string(),
                pattern: Box::new(named_pattern()),
            },
        ]);
        assert_eq!(
            first_unplaced_named_ctor_in_pattern(&pattern),
            Some("S{b,a}")
        );
    }

    #[test]
    fn a_struct_literal_is_searched() {
        let expr = PureExpr::LogicFnCall {
            name: "S{b,a}".to_string(),
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        };
        assert_eq!(first_unplaced_named_ctor(&expr), Some("S{b,a}"));
    }
}
