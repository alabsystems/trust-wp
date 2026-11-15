// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A substitution never captures: a binder a substituted value's free name
//! would fall under is renamed apart. The plain substitution shadowed a
//! binder's own name and substituted beneath it anyway, so `forall<y> y ==
//! result` with `result := y` read `forall<y> y == y`, and a logic function
//! `forall<i> 0 <= i ==> m <= i` unfolded at `m := i@` read `i@ <= i`: the
//! driver verified both, false, at exit 0.

use std::{collections::HashMap, sync::Arc};

use super::CaptureAvoidingSubstOptions;
use crate::formula::{BinOp, ExprSort, MatchArm, Pattern, PureExpr};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn eq(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), BinOp::Eq, Arc::new(right))
}

fn forall(name: &str, body: PureExpr) -> PureExpr {
    PureExpr::Forall {
        var: name.to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![],
    }
}

/// `expr` with every binder renamed to `#k`, `k` its order of appearance:
/// two expressions are alpha-equivalent exactly when these are equal.
#[allow(clippy::too_many_lines)]
fn canonical(expr: &PureExpr) -> PureExpr {
    fn bind(env: &mut Vec<(String, String)>, next: &mut usize, name: &str) -> String {
        let canonical = format!("#{next}");
        *next += 1;
        env.push((name.to_string(), canonical.clone()));
        canonical
    }
    fn go(expr: &PureExpr, env: &mut Vec<(String, String)>, next: &mut usize) -> PureExpr {
        match expr {
            PureExpr::Var(name, sort) => PureExpr::Var(
                env.iter()
                    .rev()
                    .find(|(bound, _)| bound == name)
                    .map_or_else(|| name.clone(), |(_, canonical)| canonical.clone()),
                sort.clone(),
            ),
            PureExpr::Int(_) | PureExpr::Bool(_) => expr.clone(),
            PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
                Arc::new(go(left, env, next)),
                *op,
                Arc::new(go(right, env, next)),
            ),
            PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
                Arc::new(go(cond, env, next)),
                Arc::new(go(then_expr, env, next)),
                Arc::new(go(else_expr, env, next)),
            ),
            PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
                name: name.clone(),
                args: args.iter().map(|arg| go(arg, env, next)).collect(),
            },
            PureExpr::Forall {
                var,
                var_sort,
                body,
                ..
            }
            | PureExpr::Exists {
                var,
                var_sort,
                body,
                ..
            } => {
                let canonical = bind(env, next, var);
                let body = Arc::new(go(body, env, next));
                env.pop();
                if matches!(expr, PureExpr::Forall { .. }) {
                    PureExpr::Forall {
                        var: canonical,
                        var_sort: var_sort.clone(),
                        body,
                        triggers: vec![],
                    }
                } else {
                    PureExpr::Exists {
                        var: canonical,
                        var_sort: var_sort.clone(),
                        body,
                        triggers: vec![],
                    }
                }
            }
            PureExpr::Let { var, value, body } => {
                let value = Arc::new(go(value, env, next));
                let canonical = bind(env, next, var);
                let body = Arc::new(go(body, env, next));
                env.pop();
                PureExpr::Let {
                    var: canonical,
                    value,
                    body,
                }
            }
            PureExpr::Closure { params, body } => {
                let params = params
                    .iter()
                    .map(|(name, sort)| (bind(env, next, name), sort.clone()))
                    .collect::<Vec<_>>();
                let body = Arc::new(go(body, env, next));
                env.truncate(env.len() - params.len());
                PureExpr::Closure { params, body }
            }
            PureExpr::Match { scrutinee, arms } => PureExpr::Match {
                scrutinee: Arc::new(go(scrutinee, env, next)),
                arms: arms
                    .iter()
                    .map(|arm| {
                        let names: Vec<String> = arm
                            .pattern
                            .bound_names()
                            .into_iter()
                            .map(str::to_string)
                            .collect();
                        let mut pattern = arm.pattern.clone();
                        for name in &names {
                            let canonical = bind(env, next, name);
                            pattern = pattern.rename_binding(name, &canonical);
                        }
                        let body = go(&arm.body, env, next);
                        env.truncate(env.len() - names.len());
                        MatchArm { pattern, body }
                    })
                    .collect(),
            },
            other => panic!("the generator writes no {other:?}"),
        }
    }
    go(expr, &mut Vec::new(), &mut 0)
}

/// xorshift64*: the corpus is identical on every run.
struct Rng(u64);

impl Rng {
    fn below(&mut self, bound: usize) -> usize {
        let mut state = self.0;
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        self.0 = state;
        usize::try_from(state.wrapping_mul(0x2545_F491_4F6C_DD1D) % bound as u64).expect("fits")
    }
}

const NAMES: [&str; 4] = ["a", "b", "c", "result"];

/// A term over `NAMES` with every binder the plain substitution handles.
fn term(rng: &mut Rng, depth: usize) -> PureExpr {
    let name = |rng: &mut Rng| NAMES[rng.below(NAMES.len())].to_string();
    if depth == 0 {
        return if rng.below(4) == 0 {
            PureExpr::Int(i64::try_from(rng.below(3)).expect("small"))
        } else {
            PureExpr::Var(name(rng), None)
        };
    }
    let next = depth - 1;
    match rng.below(9) {
        0 => PureExpr::BinOp(
            Arc::new(term(rng, next)),
            BinOp::Add,
            Arc::new(term(rng, next)),
        ),
        1 => eq(term(rng, next), term(rng, next)),
        2 => PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![term(rng, next), term(rng, next)],
        },
        3 => forall(&name(rng), term(rng, next)),
        4 => PureExpr::Exists {
            var: name(rng),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(term(rng, next)),
            triggers: vec![],
        },
        5 => PureExpr::Let {
            var: name(rng),
            value: Arc::new(term(rng, next)),
            body: Arc::new(term(rng, next)),
        },
        6 => PureExpr::Closure {
            params: vec![(name(rng), None)],
            body: Arc::new(term(rng, next)),
        },
        7 => PureExpr::Match {
            scrutinee: Arc::new(term(rng, next)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding(name(rng)))),
                    },
                    body: term(rng, next),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: term(rng, next),
                },
            ],
        },
        _ => PureExpr::Ite(
            Arc::new(term(rng, next)),
            Arc::new(term(rng, next)),
            Arc::new(term(rng, next)),
        ),
    }
}

/// The unit cases the driver measured.
#[test]
fn a_substitution_renames_a_binder_apart_from_the_values_beneath_it() {
    let mut result_is_y = HashMap::new();
    result_is_y.insert("result".to_string(), var("y"));
    let substituted = forall("y", eq(var("y"), var("result"))).substitute(&result_is_y);
    assert_eq!(
        canonical(&substituted),
        canonical(&forall("z", eq(var("z"), var("y")))),
        "{substituted}"
    );
    // A binder no value mentions keeps its name, and one that rebinds the
    // key itself shadows it.
    let untouched = forall("x", eq(var("x"), var("result")));
    assert_eq!(
        untouched.substitute(&result_is_y),
        forall("x", eq(var("x"), var("y")))
    );
    let shadowing = forall("result", eq(var("result"), var("y")));
    assert_eq!(shadowing.substitute(&result_is_y), shadowing);
    // The filtered substitution renames as well.
    let filter = ["result"].into_iter().collect();
    assert_eq!(
        canonical(
            &forall("y", eq(var("y"), var("result"))).substitute_filtered(&filter, &result_is_y)
        ),
        canonical(&forall("z", eq(var("z"), var("y"))))
    );
}

/// Generated: terms with every binder, each substituted with values that
/// read the names those binders bind. The capture-avoiding substitution is
/// the oracle; the plain one must agree with it up to the names of binders.
#[test]
fn the_plain_substitution_agrees_with_the_capture_avoiding_one() {
    let mut rng = Rng(0x6879_6769_656e_6521);
    let mut mismatches = Vec::new();
    let mut captures = 0;
    for _ in 0..3000 {
        let expr = term(&mut rng, 4);
        let mut substitutions = HashMap::new();
        for name in NAMES {
            if rng.below(2) == 0 {
                substitutions.insert(name.to_string(), term(&mut rng, 1));
            }
        }
        let plain = expr.substitute_no_tuple_beta(&substitutions);
        let oracle = expr
            .substitute_capture_avoiding(&substitutions, &CaptureAvoidingSubstOptions::default());
        if oracle.to_string().contains('$') {
            captures += 1;
        }
        if canonical(&plain) != canonical(&oracle) {
            mismatches.push(format!(
                "{expr} [{substitutions:?}]\n  plain: {plain}\n  oracle: {oracle}"
            ));
        }
    }
    eprintln!("substitution hygiene: 3000 terms, {captures} of them capturing");
    assert!(
        captures > 300,
        "only {captures} cases capture: the corpus is vacuous"
    );
    assert!(
        mismatches.is_empty(),
        "{} of 3000 disagree:\n{}",
        mismatches.len(),
        mismatches
            .iter()
            .take(5)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// Every binder of a name the predicate accepts is renamed, with what it
/// binds; everything else is left.
#[test]
fn binders_are_renamed_apart_from_the_names_given() {
    let expr = PureExpr::Let {
        var: "p".to_string(),
        value: Arc::new(var("p")),
        body: Arc::new(eq(var("p"), forall("q", eq(var("q"), var("p"))))),
    };
    let renamed = expr.rename_binders_apart(|name| name == "p");
    let PureExpr::Let {
        var: bound,
        value,
        body,
    } = &renamed
    else {
        panic!("{renamed}");
    };
    assert_ne!(bound, "p");
    assert_eq!(value.as_ref(), &var("p"), "the value is outside the binder");
    assert_eq!(
        body.as_ref(),
        &eq(var(bound), forall("q", eq(var("q"), var(bound))))
    );
    assert_eq!(canonical(&renamed), canonical(&expr));
}
