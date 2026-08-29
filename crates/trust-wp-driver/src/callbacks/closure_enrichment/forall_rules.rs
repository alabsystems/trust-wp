// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Forall precondition rule collection and instantiation.
//!
//! Extracts universally-quantified `postcondition_mut => precondition` patterns
//! from requires clauses and instantiates them with ground call information.

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

#[derive(Clone)]
struct ForallPreconditionRule {
    receiver: PureExpr,
    arg: PureExpr,
}

fn normalize_closure_receiver(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Deref(inner) => inner.as_ref().clone(),
        _ => expr.clone(),
    }
}

/// Recognize a single `forall<st, r> postcondition_mut(RECV, args, st, r) ==>
/// precondition(st, args)` requires premise, returning its (normalized receiver,
/// args) rule if it matches.
fn forall_precondition_rule(req: &PureExpr) -> Option<ForallPreconditionRule> {
    let mut binders: Vec<String> = Vec::new();
    let mut inner = req;
    while let PureExpr::Forall { var, body, .. } = inner {
        binders.push(var.clone());
        inner = body;
    }
    if binders.len() < 2 {
        return None;
    }
    let st_var = binders.first()?;
    let r_var = binders.get(1)?;

    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = inner else {
        return None;
    };
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = antecedent.as_ref()
    else {
        return None;
    };
    if method != "postcondition_mut" || args.len() != 3 {
        return None;
    }
    let PureExpr::Var(st_arg, _) = &args[1] else {
        return None;
    };
    let PureExpr::Var(r_arg, _) = &args[2] else {
        return None;
    };
    if st_arg != st_var || r_arg != r_var {
        return None;
    }

    let PureExpr::MethodCall {
        receiver: consequent_receiver,
        method: consequent_method,
        args: consequent_args,
    } = consequent.as_ref()
    else {
        return None;
    };
    if consequent_method != "precondition" || consequent_args.len() != 1 {
        return None;
    }
    let PureExpr::Var(consequent_st, _) = consequent_receiver.as_ref() else {
        return None;
    };
    if consequent_st != st_var {
        return None;
    }
    if consequent_args[0] != args[0] {
        return None;
    }

    Some(ForallPreconditionRule {
        receiver: normalize_closure_receiver(receiver),
        arg: args[0].clone(),
    })
}

fn collect_forall_precondition_rules(requires: &[PureExpr]) -> Vec<ForallPreconditionRule> {
    requires
        .iter()
        .filter_map(forall_precondition_rule)
        .collect()
}

/// Instantiate forall postcondition_mut=>precondition rules using ground calls.
///
/// Adds entailed assumptions of the form `POST.precondition(args)` for each
/// matching ground `postcondition_mut(RECV, args, POST, result)` call.
pub(in crate::callbacks) fn instantiate_forall_precondition_rules(
    requires: &mut Vec<PureExpr>,
) -> usize {
    let rules = collect_forall_precondition_rules(requires);
    if rules.is_empty() {
        return 0;
    }

    let ground_calls: Vec<(PureExpr, PureExpr, PureExpr)> = requires
        .iter()
        .filter_map(|req| {
            let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = req
            else {
                return None;
            };
            if method != "postcondition_mut" || args.len() != 3 {
                return None;
            }
            Some((
                normalize_closure_receiver(receiver),
                args[0].clone(),
                args[1].clone(),
            ))
        })
        .collect();

    let mut added = 0usize;
    let mut new_assumptions = Vec::new();
    for rule in &rules {
        for (recv, arg, post_state) in &ground_calls {
            if *recv != rule.receiver || *arg != rule.arg {
                continue;
            }
            let grounded = PureExpr::MethodCall {
                receiver: Arc::new(post_state.clone()),
                method: "precondition".to_string(),
                args: vec![arg.clone()],
            };
            if !requires.contains(&grounded) && !new_assumptions.contains(&grounded) {
                new_assumptions.push(grounded);
                added += 1;
            }
        }
    }
    requires.extend(new_assumptions);
    added
}

/// Prune raw `forall<st, r> postcondition_mut(RECV, args, st, r) ==>
/// precondition(st, args)` requires premises once every ground instance has
/// already been materialized by [`instantiate_forall_precondition_rules`].
///
/// The forall's single `postcondition_mut` trigger can only ever instantiate at
/// the ground `postcondition_mut(RECV, args, POST, _)` facts already present, and
/// each such instance's `precondition(POST, args)` consequence is materialized as
/// an ordinary premise. The raw forall is then redundant over the available
/// facts, yet leaving it in the premise set drives the base-consistency
/// (non-vacuity) re-solve into undecidable quantifier territory — demoting an
/// otherwise-discharged proof to `quantifier-ematching-exists-incomplete`
/// (closures/07 `call_fnmut`, whose existential goal is separately ground-
/// witnessed).
///
/// A forall is pruned ONLY when every matching ground `postcondition_mut` fact
/// already has its `precondition(POST, args)` premise present, so the premise set
/// stays logically equivalent over the available facts. (Dropping a premise is
/// sound regardless — it only weakens the assumptions; the materialization check
/// additionally rules out any completeness regression.) Returns the count pruned.
pub(in crate::callbacks) fn prune_materialized_forall_precondition_rules(
    requires: &mut Vec<PureExpr>,
) -> usize {
    // Ground `postcondition_mut(RECV, arg, POST, _)` facts (normalized receiver).
    let ground_calls: Vec<(PureExpr, PureExpr, PureExpr)> = requires
        .iter()
        .filter_map(|req| {
            let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = req
            else {
                return None;
            };
            if method != "postcondition_mut" || args.len() != 3 {
                return None;
            }
            Some((
                normalize_closure_receiver(receiver),
                args[0].clone(),
                args[1].clone(),
            ))
        })
        .collect();

    // Ground `precondition(RECV, arg)` facts (receiver, arg).
    let precondition_facts: Vec<(PureExpr, PureExpr)> = requires
        .iter()
        .filter_map(|req| {
            let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = req
            else {
                return None;
            };
            if method != "precondition" || args.len() != 1 {
                return None;
            }
            Some((receiver.as_ref().clone(), args[0].clone()))
        })
        .collect();

    let mut removed = 0;
    requires.retain(|req| {
        let Some(rule) = forall_precondition_rule(req) else {
            return true;
        };
        // Every matching ground fact's `precondition(POST, arg)` must already be
        // materialized for the raw forall to be redundant.
        let all_materialized = ground_calls
            .iter()
            .filter(|(recv, arg, _)| *recv == rule.receiver && *arg == rule.arg)
            .all(|(_, arg, post)| {
                precondition_facts
                    .iter()
                    .any(|(pre_recv, pre_arg)| pre_recv == post && pre_arg == arg)
            });
        if all_materialized {
            removed += 1;
            false
        } else {
            true
        }
    });
    removed
}
