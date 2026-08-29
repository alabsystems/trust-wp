// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constructor method call reduction and boolean constant propagation.
//!
//! Statically evaluates method calls on concrete constructors (e.g.,
//! `None().is_some()` → `false`) and performs boolean constant folding
//! (e.g., `false ==> X` → `true`).

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, MatchArm, PureExpr, UnOp};

use super::match_reduction::extract_constructor;

/// Statically evaluate method calls on concrete constructor expressions.
///
/// When an implication-style postcondition references `is_some()`, `is_none()`,
/// or `unwrap()` on a concrete constructor (e.g., `None().is_some()`,
/// `Some(1).unwrap()`), these can be resolved at the expression level:
///
/// - `None().is_some()` → `false`
/// - `None().is_none()` → `true`
/// - `Some(v).is_some()` → `true`
/// - `Some(v).is_none()` → `false`
/// - `Some(v).unwrap()` → `v`
/// - `Ok(v).is_ok()` → `true`
/// - `Ok(v).is_err()` → `false`
/// - `Err(e).is_ok()` → `false`
/// - `Err(e).is_err()` → `true`
///
/// Additional method reductions with one argument:
/// - `Some(v).unwrap_or(d)` → `v`
/// - `None().unwrap_or(d)` → `d`
/// - `Ok(v).unwrap_or(d)` → `v`
/// - `Err(e).unwrap_or(d)` → `d`
/// - `Ok(v).ok()` → `Some(v)`
/// - `Err(e).ok()` → `None()`
/// - `Ok(v).err()` → `None()`
/// - `Err(e).err()` → `Some(e)`
///
/// Also simplifies boolean constant propagation:
/// - `false ==> X` → `true` (vacuously true)
/// - `true ==> X` → `X`
/// - `true && X` → `X`, `false && X` → `false`
/// - `true || X` → `true`, `false || X` → `X`
/// - `X && true` → `X`, `X && false` → `false`
/// - `X || true` → `true`, `X || false` → `X`
/// - `not(true)` → `false`, `not(false)` → `true`
/// - `if true { X } else { Y }` → `X`, `if false { X } else { Y }` → `Y`
///
/// Applied recursively. (#2675)
pub(in crate::callbacks) fn reduce_concrete_constructor_method_calls(expr: PureExpr) -> PureExpr {
    match expr {
        PureExpr::MethodCall {
            receiver,
            ref method,
            ref args,
        } if args.is_empty() => {
            let reduced_receiver =
                reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(receiver));
            if let Some((ctor_name, ctor_args)) = extract_constructor(&reduced_receiver) {
                match (ctor_name, method.as_str()) {
                    ("Some", "is_some") | ("Ok", "is_ok") | ("Err", "is_err") => {
                        return PureExpr::Bool(true);
                    }
                    ("None", "is_some") | ("Ok", "is_err") | ("Err", "is_ok") => {
                        return PureExpr::Bool(false);
                    }
                    ("Some", "is_none") | ("None", "is_ok") | ("None", "is_err") => {
                        return PureExpr::Bool(false);
                    }
                    ("None", "is_none") => {
                        return PureExpr::Bool(true);
                    }
                    ("Some", "unwrap") | ("Ok", "unwrap") => {
                        if let [inner] = ctor_args {
                            return reduce_concrete_constructor_method_calls(inner.clone());
                        }
                    }
                    ("Err", "unwrap_err") => {
                        if let [inner] = ctor_args {
                            return reduce_concrete_constructor_method_calls(inner.clone());
                        }
                    }
                    // ok()/err() conversions: Result → Option
                    ("Ok", "ok") => {
                        if let [inner] = ctor_args {
                            return PureExpr::LogicFnCall {
                                name: "Some".to_string(),
                                args: vec![reduce_concrete_constructor_method_calls(inner.clone())],
                            };
                        }
                    }
                    ("Err", "ok") | ("None", "ok") => {
                        return PureExpr::LogicFnCall {
                            name: "None".to_string(),
                            args: vec![],
                        };
                    }
                    ("Err", "err") => {
                        if let [inner] = ctor_args {
                            return PureExpr::LogicFnCall {
                                name: "Some".to_string(),
                                args: vec![reduce_concrete_constructor_method_calls(inner.clone())],
                            };
                        }
                    }
                    ("Ok", "err") | ("None", "err") => {
                        return PureExpr::LogicFnCall {
                            name: "None".to_string(),
                            args: vec![],
                        };
                    }
                    // flatten: None().flatten() → None()
                    ("None", "flatten") => {
                        return PureExpr::LogicFnCall {
                            name: "None".to_string(),
                            args: vec![],
                        };
                    }
                    _ => {}
                }
            }
            // Not reducible — rebuild with reduced receiver
            PureExpr::MethodCall {
                receiver: Arc::new(reduced_receiver),
                method: method.clone(),
                args: args.clone(),
            }
        }
        // One-arg method calls on concrete constructors (e.g., unwrap_or)
        PureExpr::MethodCall {
            receiver,
            ref method,
            ref args,
        } if args.len() == 1 => {
            let reduced_receiver =
                reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(receiver));
            let reduced_arg = reduce_concrete_constructor_method_calls(args[0].clone());
            if let Some((ctor_name, ctor_args)) = extract_constructor(&reduced_receiver) {
                match (ctor_name, method.as_str()) {
                    // unwrap_or: Some(v)/Ok(v) → v, None/Err → default
                    ("Some", "unwrap_or") | ("Ok", "unwrap_or") => {
                        if let [inner] = ctor_args {
                            return reduce_concrete_constructor_method_calls(inner.clone());
                        }
                    }
                    ("None", "unwrap_or") | ("Err", "unwrap_or") => {
                        return reduced_arg;
                    }
                    // ok_or: Option → Result conversion
                    // Some(v).ok_or(e) → Ok(v)
                    ("Some", "ok_or") => {
                        if let [inner] = ctor_args {
                            return PureExpr::LogicFnCall {
                                name: "Ok".to_string(),
                                args: vec![reduce_concrete_constructor_method_calls(inner.clone())],
                            };
                        }
                    }
                    // None().ok_or(e) → Err(e)
                    ("None", "ok_or") => {
                        return PureExpr::LogicFnCall {
                            name: "Err".to_string(),
                            args: vec![reduced_arg],
                        };
                    }
                    // expect: same as unwrap but with message arg
                    // Some(v).expect(msg) → v, Ok(v).expect(msg) → v
                    ("Some", "expect") | ("Ok", "expect") => {
                        if let [inner] = ctor_args {
                            return reduce_concrete_constructor_method_calls(inner.clone());
                        }
                    }
                    // expect_err: Err(e).expect_err(msg) → e
                    ("Err", "expect_err") => {
                        if let [inner] = ctor_args {
                            return reduce_concrete_constructor_method_calls(inner.clone());
                        }
                    }
                    // Short-circuit: None/Err stay None/Err for map/and_then/filter
                    // None().map(f) → None(), Err(e).map(f) → Err(e)
                    ("None", "map") | ("None", "and_then") | ("None", "filter") => {
                        return PureExpr::LogicFnCall {
                            name: "None".to_string(),
                            args: vec![],
                        };
                    }
                    ("Err", "map") | ("Err", "and_then") => {
                        if let [inner] = ctor_args {
                            return PureExpr::LogicFnCall {
                                name: "Err".to_string(),
                                args: vec![reduce_concrete_constructor_method_calls(inner.clone())],
                            };
                        }
                    }
                    // Short-circuit: Some/Ok stay Some/Ok for or/or_else
                    // Some(v).or(y) → Some(v), Ok(v).or(y) → Ok(v)
                    ("Some", "or") | ("Some", "or_else") => {
                        if let [inner] = ctor_args {
                            return PureExpr::LogicFnCall {
                                name: "Some".to_string(),
                                args: vec![reduce_concrete_constructor_method_calls(inner.clone())],
                            };
                        }
                    }
                    ("Ok", "or") | ("Ok", "or_else") => {
                        if let [inner] = ctor_args {
                            return PureExpr::LogicFnCall {
                                name: "Ok".to_string(),
                                args: vec![reduce_concrete_constructor_method_calls(inner.clone())],
                            };
                        }
                    }
                    // map_err short-circuit: Ok(v).map_err(f) → Ok(v)
                    ("Ok", "map_err") => {
                        if let [inner] = ctor_args {
                            return PureExpr::LogicFnCall {
                                name: "Ok".to_string(),
                                args: vec![reduce_concrete_constructor_method_calls(inner.clone())],
                            };
                        }
                    }
                    _ => {}
                }
            }
            PureExpr::MethodCall {
                receiver: Arc::new(reduced_receiver),
                method: method.clone(),
                args: vec![reduced_arg],
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(receiver),
            )),
            method,
            args: args
                .into_iter()
                .map(reduce_concrete_constructor_method_calls)
                .collect(),
        },
        PureExpr::BinOp(left, op, right) => {
            let l = reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(left));
            let r = reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(right));
            // Boolean constant folding for Implies, And, Or
            match op {
                BinOp::Implies => match &l {
                    PureExpr::Bool(false) => return PureExpr::Bool(true),
                    PureExpr::Bool(true) => return r,
                    _ => {}
                },
                BinOp::And => match (&l, &r) {
                    (PureExpr::Bool(true), _) => return r,
                    (PureExpr::Bool(false), _) => return PureExpr::Bool(false),
                    (_, PureExpr::Bool(true)) => return l,
                    (_, PureExpr::Bool(false)) => return PureExpr::Bool(false),
                    _ => {}
                },
                BinOp::Or => match (&l, &r) {
                    (PureExpr::Bool(true), _) => return PureExpr::Bool(true),
                    (PureExpr::Bool(false), _) => return r,
                    (_, PureExpr::Bool(true)) => return PureExpr::Bool(true),
                    (_, PureExpr::Bool(false)) => return l,
                    _ => {}
                },
                _ => {}
            }
            PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
        }
        PureExpr::UnOp(op, inner) => {
            let i = reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(inner));
            // Boolean negation constant folding
            if matches!(op, UnOp::Not) {
                match &i {
                    PureExpr::Bool(true) => return PureExpr::Bool(false),
                    PureExpr::Bool(false) => return PureExpr::Bool(true),
                    _ => {}
                }
            }
            PureExpr::UnOp(op, Arc::new(i))
        }
        PureExpr::Ite(cond, then_br, else_br) => {
            let c = reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(cond));
            let t = reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(then_br));
            let e = reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(else_br));
            // Constant condition folding
            match &c {
                PureExpr::Bool(true) => return t,
                PureExpr::Bool(false) => return e,
                _ => {}
            }
            PureExpr::Ite(Arc::new(c), Arc::new(t), Arc::new(e))
        }
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name,
            args: args
                .into_iter()
                .map(reduce_concrete_constructor_method_calls)
                .collect(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(scrutinee),
            )),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: reduce_concrete_constructor_method_calls(arm.body),
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var,
            value: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(value),
            )),
            body: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(body),
            )),
        },
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(
            reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(inner)),
        )),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(reduce_concrete_constructor_method_calls(
            Arc::unwrap_or_clone(inner),
        ))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(
            reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(inner)),
        )),
        PureExpr::View(inner) => PureExpr::View(Arc::new(
            reduce_concrete_constructor_method_calls(Arc::unwrap_or_clone(inner)),
        )),
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var,
            var_sort,
            body: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(body),
            )),
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
            body: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(body),
            )),
            triggers,
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(assumption),
            )),
            body: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(body),
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(obligation),
            )),
            body: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(body),
            )),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params,
            body: Arc::new(reduce_concrete_constructor_method_calls(
                Arc::unwrap_or_clone(body),
            )),
        },
        // Leaves: Bool, Int, Float, Var — pass through unchanged
        other => other,
    }
}
