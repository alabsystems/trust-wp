// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unfold a call-site type-invariant OBLIGATION whose receiver is an aggregate
//! the caller built.
//!
//! `inv` is DEFINED as its body and nothing else is asserted about the symbol,
//! so replacing the goal `inv(t)` with `body[t/self]` neither strengthens nor
//! weakens it (D-63). What it does change is decidability: the defining
//! instance is produced only for a receiver the caller already holds `inv` of,
//! so an obligation over a constructor application was undischargeable for
//! every argument — a caller that built the value in the call itself could
//! never pass it, however plainly its fields satisfy the invariant.
//!
//! Restricted to a receiver that IS a tuple-constructor application, which is
//! how a caller-built aggregate reaches here — directly, behind the `*` a
//! `&mut` parameter's clause applies to the value handed in, or as the payload
//! of an enum constructor a decomposition matches on. The last two are read
//! exactly as the encoder reads them: `*` distributed into the constructor's
//! arguments, and the match reduced to the arm the constructor selects. A
//! receiver the caller holds a premise about must keep the symbol: there the
//! goal is discharged by matching that premise syntactically, and unfolding
//! one side alone would break the match and turn a coverage gain into a loss.
//!
//! Every other shape REFUSES and keeps the symbol, because each is a way for
//! `body` to be something other than the whole invariant, or for `self` to
//! stand for something other than the whole receiver:
//!
//! * a container invariant, whose real content is the element bridge the
//!   encoder builds beside the body rather than the body itself;
//! * a newtype, whose body is written against the collapsed `self.0 == self`
//!   identity, so substituting the CONSTRUCTOR for `self` states the clause
//!   about the wrapper where it meant the payload;
//! * a body naming anything but its own self parameter, which would leave a
//!   symbol the substitution never bound;
//! * a method name more than one definition answers to, where there is no
//!   single body to unfold.

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::{
    formula::{internal::tuple_lowering::tuple_logic_fn_arity, MatchArm, Pattern, PureExpr},
    logic::{is_invariant_method_name, type_invariant_method_name, TypeInvariantDef},
};

use super::super::parsing::ParsedContract;

/// The one definition `method` names, when exactly one may be unfolded.
fn unfoldable_def<'a>(
    method: &str,
    type_invariant_defs: &'a [TypeInvariantDef],
) -> Option<&'a TypeInvariantDef> {
    let mut found: Option<&TypeInvariantDef> = None;
    for def in type_invariant_defs {
        if type_invariant_method_name(def.type_name()) != method {
            continue;
        }
        if found.is_some() {
            return None;
        }
        found = Some(def);
    }
    let def = found?;
    if def.element_invariant_method().is_some() || def.is_newtype() {
        return None;
    }
    let self_param = def.self_param();
    if def.body().free_vars().iter().any(|name| name != self_param) {
        return None;
    }
    Some(def)
}

/// Whether `expr` is a tuple-constructor application — the shape a caller's
/// own aggregate construction lowers to.
fn is_constructed_aggregate(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if tuple_logic_fn_arity(name) == Some(args.len())
    )
}

/// `*c` for a constructor application `c`, as the encoder reads it: the
/// dereference distributed into the arguments (`encode_wrapper_rewrite`). A
/// constructor application is a value, never a reference carrier, so this is
/// the same term the solver would build — only now the unfold can see it.
fn deref_through_constructor(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::Deref(inner) = expr else {
        return None;
    };
    let PureExpr::LogicFnCall { name, args } = inner.as_ref() else {
        return None;
    };
    Some(PureExpr::LogicFnCall {
        name: name.clone(),
        args: args
            .iter()
            .map(|arg| PureExpr::Deref(Arc::new(arg.clone())))
            .collect(),
    })
}

/// The receiver an invariant obligation is unfolded at, when it is a
/// constructed aggregate by value or behind `*`.
fn constructed_receiver(receiver: &PureExpr) -> Option<PureExpr> {
    if is_constructed_aggregate(receiver) {
        return Some(receiver.clone());
    }
    deref_through_constructor(receiver).filter(is_constructed_aggregate)
}

/// Whether `body` is what an enum decomposition puts in an arm: `true`, or an
/// invariant applied to the payload binding (behind `*` for a reference).
fn is_decomposition_arm_body(body: &PureExpr) -> bool {
    match body {
        PureExpr::Bool(true) => true,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            args.is_empty()
                && is_invariant_method_name(method)
                && matches!(receiver.as_ref(), PureExpr::Var(..) | PureExpr::Deref(_))
        }
        _ => false,
    }
}

/// An enum decomposition `match C(..) { .. }` reduced to the arm constructor
/// `C` selects, with its payload bound — what the encoder's
/// `try_reduce_match_constructor` computes, restricted to the shape the
/// parameter-clause builder emits.
///
/// Every arm must be a constructor pattern and name a distinct variant: the
/// arms then list the scrutinee enum's variants, so a scrutinee applying one
/// of those names IS that variant, and no catch-all arm can be chosen for a
/// scrutinee that is not a constructor at all.
fn reduce_decomposition_match(scrutinee: &PureExpr, arms: &[MatchArm]) -> Option<PureExpr> {
    if !arms.iter().all(|arm| is_decomposition_arm_body(&arm.body)) {
        return None;
    }
    let constructed = match scrutinee {
        PureExpr::LogicFnCall { .. } => scrutinee.clone(),
        other => deref_through_constructor(other)?,
    };
    let PureExpr::LogicFnCall { name, args } = &constructed else {
        return None;
    };
    let mut names = Vec::with_capacity(arms.len());
    for arm in arms {
        let Pattern::Constructor { name, .. } = &arm.pattern else {
            return None;
        };
        if names.contains(&name) {
            return None;
        }
        names.push(name);
    }
    let arm = arms
        .iter()
        .find(|arm| matches!(&arm.pattern, Pattern::Constructor { name: n, .. } if n == name))?;
    let Pattern::Constructor { inner, .. } = &arm.pattern else {
        return None;
    };
    let fields: Vec<&Pattern> = match (inner.as_deref(), args.len()) {
        (None, 0) => Vec::new(),
        (Some(Pattern::Tuple(fields)), n) if n > 1 && fields.len() == n => fields.iter().collect(),
        (Some(single), 1) => vec![single],
        _ => return None,
    };
    let mut binding: HashMap<String, PureExpr> = HashMap::new();
    for (field, value) in fields.into_iter().zip(args) {
        match field {
            Pattern::Wildcard => {}
            Pattern::Binding(bound) => {
                binding.insert(bound.clone(), value.clone());
            }
            _ => return None,
        }
    }
    Some(arm.body.substitute(&binding))
}

fn unfold_expr(expr: &PureExpr, type_invariant_defs: &[TypeInvariantDef]) -> PureExpr {
    expr.rewrite_bottom_up(|node| match &node {
        PureExpr::Match { scrutinee, arms } => match reduce_decomposition_match(scrutinee, arms) {
            // The selected arm is a fresh obligation over the payload the
            // caller wrote; unfold it in turn.
            Some(selected) => unfold_expr(&selected, type_invariant_defs),
            None => node,
        },
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if !args.is_empty() {
                return node;
            }
            let Some(receiver) = constructed_receiver(receiver) else {
                return node;
            };
            let Some(def) = unfoldable_def(method, type_invariant_defs) else {
                return node;
            };
            // `substitute` beta-reduces `tuple_get_N(tupleK(..))`, so the body's
            // field projections land on the components the caller wrote.
            let mut binding: HashMap<String, PureExpr> = HashMap::new();
            binding.insert(def.self_param().to_string(), receiver);
            def.body().substitute(&binding)
        }
        _ => node,
    })
}

/// Unfold in the call-site OBLIGATION vectors only.
///
/// An assumption carrying `inv(ctor)` is left alone: it is already as strong
/// as its unfolding, nothing is waiting to be matched against it, and the
/// narrower the set of expressions this pass can reach the smaller the surface
/// on which a refusal above could be wrong.
pub(super) fn unfold_constructed_invariant_obligations(
    parsed: &mut ParsedContract,
    type_invariant_defs: &[TypeInvariantDef],
) {
    if type_invariant_defs.is_empty() {
        return;
    }
    parsed.rewrite_each_call_obligation(|expr| unfold_expr(expr, type_invariant_defs));
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    fn sum10_body() -> PureExpr {
        // `self.a + self.b == 10` in the positional form the crate-level
        // named-field rewrite leaves invariant bodies in.
        use trust_wp_core::formula::{internal::tuple_lowering::tuple_field_logic_fn_name, BinOp};
        let get = |i: usize| PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(i),
            args: vec![PureExpr::Var("self".to_string(), None)],
        };
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(get(0)),
                BinOp::Add,
                Arc::new(get(1)),
            )),
            BinOp::Eq,
            Arc::new(PureExpr::Int(10)),
        )
    }

    fn def() -> TypeInvariantDef {
        TypeInvariantDef::new("Sum10".to_string(), "self".to_string(), sum10_body())
    }

    fn ctor() -> PureExpr {
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple2".to_string(),
            args: vec![PureExpr::Int(4), PureExpr::Int(6)],
        }
    }

    fn obligation(receiver: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: type_invariant_method_name("Sum10"),
            args: vec![],
        }
    }

    #[test]
    fn a_constructed_receiver_is_unfolded_at_its_components() {
        let out = unfold_expr(&obligation(ctor()), &[def()]);
        // The body's projections beta-reduce onto what the caller wrote, so
        // nothing of the opaque symbol survives.
        assert!(!format!("{out:?}").contains("invariant"), "{out:?}");
        assert!(out.free_vars().is_empty(), "{out:?}");
    }

    #[test]
    fn a_receiver_the_caller_holds_a_premise_about_keeps_the_symbol() {
        // Unfolding one side of a premise/goal pair breaks the match that is
        // the only way such an obligation is discharged today.
        let var = PureExpr::Var("s".to_string(), None);
        let input = obligation(var);
        assert_eq!(unfold_expr(&input, &[def()]), input);
    }

    #[test]
    fn a_newtype_def_is_refused() {
        let input = obligation(ctor());
        assert_eq!(unfold_expr(&input, &[def().with_newtype(true)]), input);
    }

    #[test]
    fn a_container_def_is_refused() {
        let input = obligation(ctor());
        let container = def().with_element_invariant_method(Some("inv_elem".to_string()));
        assert_eq!(unfold_expr(&input, &[container]), input);
    }

    #[test]
    fn a_body_naming_anything_but_self_is_refused() {
        use trust_wp_core::formula::BinOp;
        let leaky = TypeInvariantDef::new(
            "Sum10".to_string(),
            "self".to_string(),
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("elsewhere".to_string(), None)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(10)),
            ),
        );
        let input = obligation(ctor());
        assert_eq!(unfold_expr(&input, &[leaky]), input);
    }

    #[test]
    fn a_dereferenced_constructed_receiver_is_unfolded_as_the_encoder_reads_it() {
        // A `&mut` parameter's clause is `inv(*x)`; with `x` the aggregate
        // the caller wrote, the solver reads `*tupleK(..)` as the constructor
        // over dereferenced components.
        let out = unfold_expr(&obligation(PureExpr::Deref(Arc::new(ctor()))), &[def()]);
        assert!(!format!("{out:?}").contains("invariant"), "{out:?}");
        assert!(out.free_vars().is_empty(), "{out:?}");
    }

    fn decomposition(scrutinee: PureExpr, some_body: PureExpr) -> PureExpr {
        PureExpr::Match {
            scrutinee: Arc::new(scrutinee),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Bool(true),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("$p".to_string()))),
                    },
                    body: some_body,
                },
            ],
        }
    }

    fn some(payload: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: "Some".to_string(),
            args: vec![payload],
        }
    }

    #[test]
    fn a_decomposition_over_a_constructed_variant_selects_its_arm_and_unfolds_it() {
        let input = decomposition(
            some(ctor()),
            obligation(PureExpr::Var("$p".to_string(), None)),
        );
        let out = unfold_expr(&input, &[def()]);
        assert!(!format!("{out:?}").contains("invariant"), "{out:?}");
        assert!(out.free_vars().is_empty(), "{out:?}");
        let none = PureExpr::LogicFnCall {
            name: "None".to_string(),
            args: vec![],
        };
        let input = decomposition(none, obligation(PureExpr::Var("$p".to_string(), None)));
        assert_eq!(unfold_expr(&input, &[def()]), PureExpr::Bool(true));
    }

    #[test]
    fn a_match_whose_scrutinee_is_not_a_listed_variant_is_kept() {
        // A logic call that names no arm's variant, and a variable, say nothing
        // about which arm runs.
        let payload = obligation(PureExpr::Var("$p".to_string(), None));
        for scrutinee in [
            PureExpr::LogicFnCall {
                name: "make".to_string(),
                args: vec![ctor()],
            },
            PureExpr::Var("o".to_string(), None),
        ] {
            let input = decomposition(scrutinee, payload.clone());
            assert_eq!(unfold_expr(&input, &[def()]), input);
        }
    }

    #[test]
    fn a_match_that_is_not_a_decomposition_is_kept() {
        // A catch-all arm or an arm body of any other shape is a clause the
        // user wrote, not the builder's decomposition.
        let with_catch_all = PureExpr::Match {
            scrutinee: Arc::new(some(ctor())),
            arms: vec![MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Bool(true),
            }],
        };
        assert_eq!(unfold_expr(&with_catch_all, &[def()]), with_catch_all);
        let user_body = decomposition(some(ctor()), PureExpr::Bool(false));
        assert_eq!(unfold_expr(&user_body, &[def()]), user_body);
    }

    #[test]
    fn a_method_name_two_defs_answer_to_is_refused() {
        let input = obligation(ctor());
        assert_eq!(unfold_expr(&input, &[def(), def()]), input);
    }
}
