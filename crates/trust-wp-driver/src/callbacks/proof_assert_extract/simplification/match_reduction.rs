// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Static match elimination for concrete constructor scrutinees.
//!
//! When a `PureExpr::Match` has a scrutinee that is a concrete constructor
//! (e.g., `*None()`, `*Some(1)`, `*Ok(v)`, `*Err(e)`), the match can be
//! resolved at the expression level without SMT encoding.

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

/// Extract the constructor name and arguments from a concrete constructor expression.
///
/// Recognizes patterns like:
/// - `LogicFnCall { name: "Some", args: [v] }` → `("Some", [v])`
/// - `LogicFnCall { name: "None", args: [] }` → `("None", [])`
/// - `LogicFnCall { name: "Ok", args: [v] }` → `("Ok", [v])`
/// - `LogicFnCall { name: "Err", args: [v] }` → `("Err", [v])`
/// - `Deref(LogicFnCall { ... })` → unwraps Deref and recurses
///
/// Returns `None` if the expression is not a concrete constructor.
pub(super) fn extract_constructor(expr: &PureExpr) -> Option<(&str, &[PureExpr])> {
    match expr {
        PureExpr::Deref(inner) | PureExpr::Old(inner) => extract_constructor(inner),
        PureExpr::LogicFnCall { name, args } => {
            // Constructor names may be unqualified ("Some") or path-qualified
            // ("core::option::Option::Some").
            let short_name = name.rsplit("::").next().unwrap_or(name);
            match short_name {
                "Some" | "None" | "Ok" | "Err" => Some((short_name, args.as_slice())),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Try to match a pattern against a concrete constructor, producing variable bindings.
///
/// Returns `Some(bindings)` if the pattern matches the constructor, where `bindings`
/// maps bound variable names to the constructor argument values.
/// Returns `None` if the pattern does not match.
fn match_pattern_against_constructor(
    pattern: &Pattern,
    ctor_name: &str,
    ctor_args: &[PureExpr],
) -> Option<HashMap<String, PureExpr>> {
    match pattern {
        Pattern::Alias { alias, pattern } => {
            let mut bindings = match_pattern_against_constructor(pattern, ctor_name, ctor_args)?;
            let ctor_expr = PureExpr::LogicFnCall {
                name: ctor_name.to_string(),
                args: ctor_args.to_vec(),
            };
            merge_pattern_binding(&mut bindings, alias.clone(), ctor_expr)?;
            Some(bindings)
        }
        Pattern::Constructor { name, inner } => {
            if name != ctor_name {
                return None;
            }
            let mut bindings = HashMap::new();
            match (inner, ctor_args) {
                // Constructor with inner pattern and one argument: Some(v) vs Some(1)
                (Some(inner_pat), [arg]) => match inner_pat.as_ref() {
                    Pattern::Binding(var_name) => {
                        bindings.insert(var_name.clone(), arg.clone());
                    }
                    Pattern::Wildcard => {}
                    _ => return None,
                },
                // Nullary constructor: None vs None()
                (None, []) => {}
                // Arity mismatch
                _ => return None,
            }
            Some(bindings)
        }
        Pattern::Wildcard => Some(HashMap::new()),
        Pattern::Binding(var_name) => {
            let ctor_expr = PureExpr::LogicFnCall {
                name: ctor_name.to_string(),
                args: ctor_args.to_vec(),
            };
            let mut bindings = HashMap::new();
            bindings.insert(var_name.clone(), ctor_expr);
            Some(bindings)
        }
        _ => None,
    }
}

fn merge_pattern_binding(
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

/// Statically reduce match expressions with concrete constructor scrutinees.
///
/// When a `PureExpr::Match` has a scrutinee that is a concrete constructor
/// (e.g., `*None()`, `*Some(1)`, `*Ok(v)`, `*Err(e)`), the match can be
/// resolved at the expression level without SMT encoding:
///
/// ```text
/// match *None() { Some(v) => body1, None => body2 } → body2
/// match *Some(1) { Some(v) => body1[v:=1], None => body2 } → body1[v:=1]
/// ```
///
/// This is critical for proof_assert verification: postconditions from
/// match-style specs (e.g., `Option::ok_or`) produce match expressions as
/// assumed facts. When the scrutinee is known at the call site (e.g.,
/// `let none: Option<i32> = None; none.ok_or(true)`), the assumed fact
/// contains a match on a concrete constructor that the ay encoder cannot
/// statically evaluate. This pass resolves those matches before encoding.
///
/// Applied recursively to sub-expressions. (#2675)
pub(in crate::callbacks) fn reduce_concrete_matches(expr: PureExpr) -> PureExpr {
    match expr {
        PureExpr::Match { scrutinee, arms } => {
            let reduced_scrutinee = reduce_concrete_matches(Arc::unwrap_or_clone(scrutinee));

            if let Some((ctor_name, ctor_args)) = extract_constructor(&reduced_scrutinee) {
                for arm in &arms {
                    if let Some(bindings) =
                        match_pattern_against_constructor(&arm.pattern, ctor_name, ctor_args)
                    {
                        let reduced_body = reduce_concrete_matches(arm.body.clone());
                        if bindings.is_empty() {
                            return reduced_body;
                        }
                        return reduce_concrete_matches(reduced_body.substitute(&bindings));
                    }
                }
            }

            // Could not reduce — return match with recursively reduced parts
            PureExpr::Match {
                scrutinee: Arc::new(reduced_scrutinee),
                arms: arms
                    .into_iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern,
                        body: reduce_concrete_matches(arm.body),
                    })
                    .collect(),
            }
        }
        PureExpr::BinOp(left, op, right) => {
            let l = reduce_concrete_matches(Arc::unwrap_or_clone(left));
            let r = reduce_concrete_matches(Arc::unwrap_or_clone(right));
            PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
        }
        PureExpr::UnOp(op, inner) => {
            let i = reduce_concrete_matches(Arc::unwrap_or_clone(inner));
            PureExpr::UnOp(op, Arc::new(i))
        }
        PureExpr::Ite(cond, then_br, else_br) => {
            let c = reduce_concrete_matches(Arc::unwrap_or_clone(cond));
            let t = reduce_concrete_matches(Arc::unwrap_or_clone(then_br));
            let e = reduce_concrete_matches(Arc::unwrap_or_clone(else_br));
            PureExpr::Ite(Arc::new(c), Arc::new(t), Arc::new(e))
        }
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name,
            args: args.into_iter().map(reduce_concrete_matches).collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var,
            value: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(value))),
            body: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(body))),
        },
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(reduce_concrete_matches(
            Arc::unwrap_or_clone(inner),
        ))),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(reduce_concrete_matches(
            Arc::unwrap_or_clone(inner),
        ))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(reduce_concrete_matches(
            Arc::unwrap_or_clone(inner),
        ))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(reduce_concrete_matches(
            Arc::unwrap_or_clone(inner),
        ))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(receiver))),
            method,
            args: args.into_iter().map(reduce_concrete_matches).collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var,
            var_sort,
            body: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(body))),
            triggers,
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var,
            var_sort,
            body: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(body))),
            triggers,
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(assumption))),
            body: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(body))),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(obligation))),
            body: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(body))),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params,
            body: Arc::new(reduce_concrete_matches(Arc::unwrap_or_clone(body))),
        },
        // Leaves: Bool, Int, Float, Var — pass through unchanged
        other => other,
    }
}
