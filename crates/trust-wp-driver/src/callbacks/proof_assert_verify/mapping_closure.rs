// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};

use crate::{
    callbacks::proof_assert_extract::collapse_idempotent_views,
    mir_analysis::effects::MappingClosureInfo,
};

/// For each call assumption of the form `mapping.get(arg)` where `mapping`
/// matches a `MappingClosureInfo`'s result variable, substitute `arg` into
/// the closure body. Returns the resulting ground instances.
///
/// This provides the solver with concrete facts without requiring e-matching
/// on the forall axiom, and avoids sort interop issues between `mapping_get`
/// (returns `Sort::Int`) and Bool-valued closure bodies. (#2245)
pub(in crate::callbacks) fn instantiate_mapping_closure_ground(
    call_assumptions: &[PureExpr],
    mapping_closures: &[MappingClosureInfo],
) -> Vec<PureExpr> {
    if mapping_closures.is_empty() {
        return Vec::new();
    }

    let mapping_bodies = collect_mapping_bodies(mapping_closures);
    let mut instances = Vec::new();
    for assumption in call_assumptions {
        collect_ground_instances_from_method_call(assumption, &mapping_bodies, &mut instances);
    }
    let first_pass = instances.clone();
    for instance in &first_pass {
        collect_ground_terms_recursive(instance, &mapping_bodies, &mut instances);
    }
    instances
}

/// Walk an expression tree and instantiate mapping closure bodies for any
/// `mapping.get(arg)` or `mapping.index_logic(arg)` sub-expressions where
/// `mapping` matches a `MappingClosureInfo`. (#2245)
///
/// This complements `instantiate_mapping_closure_ground` (which scans
/// `call_assumptions`) by also extracting ground terms from the assertion
/// expression itself, after program-point substitutions have been applied.
pub(in crate::callbacks) fn instantiate_mapping_closure_ground_from_expr(
    expr: &PureExpr,
    mapping_closures: &[MappingClosureInfo],
) -> Vec<PureExpr> {
    if mapping_closures.is_empty() {
        return Vec::new();
    }

    let mapping_bodies = collect_mapping_bodies(mapping_closures);
    let mut instances = Vec::new();
    collect_ground_terms_recursive(expr, &mapping_bodies, &mut instances);
    // Chained instantiation: scan generated instances for further mapping
    // applications (e.g., closure 3 body references closure 2's mapping).
    // One extra level is sufficient for the `such_that.rs` pattern.
    let first_pass = instances.clone();
    for instance in &first_pass {
        collect_ground_terms_recursive(instance, &mapping_bodies, &mut instances);
    }
    instances
}

pub(in crate::callbacks) fn inline_bool_mapping_closure_calls(
    expr: &PureExpr,
    mapping_closures: &[MappingClosureInfo],
) -> PureExpr {
    if mapping_closures.is_empty() {
        return expr.clone();
    }

    let mapping_bodies = collect_mapping_bodies(mapping_closures);
    inline_bool_mapping_closure_calls_with_map(expr, &mapping_bodies)
}

pub(in crate::callbacks) fn retain_relevant_mapping_closure_foralls(
    assumed_facts: &mut Vec<PureExpr>,
    mapping_closures: &[MappingClosureInfo],
    assertion: &PureExpr,
    preconditions: &[PureExpr],
    call_obligations: &[PureExpr],
) -> usize {
    if assumed_facts.is_empty() || mapping_closures.is_empty() {
        return 0;
    }

    let generated_foralls = generated_mapping_closure_foralls(mapping_closures);
    if generated_foralls.is_empty() {
        return 0;
    }

    let mapping_names: HashSet<String> = generated_foralls
        .iter()
        .map(|(_, name)| name.clone())
        .collect();
    let mut relevant_names = HashSet::new();

    collect_relevant_mapping_uses(assertion, &mapping_names, &mut relevant_names, false);
    for expr in preconditions.iter().chain(call_obligations.iter()) {
        collect_relevant_mapping_uses(expr, &mapping_names, &mut relevant_names, false);
    }
    for fact in assumed_facts.iter() {
        if generated_foralls
            .iter()
            .any(|(generated, _)| generated == fact)
        {
            continue;
        }
        collect_relevant_mapping_uses(fact, &mapping_names, &mut relevant_names, false);
    }

    let before = assumed_facts.len();
    assumed_facts.retain(|fact| {
        generated_foralls
            .iter()
            .find(|(generated, _)| generated == fact)
            .is_none_or(|(_, mapping_name)| relevant_names.contains(mapping_name))
    });
    before - assumed_facts.len()
}

fn collect_mapping_bodies(
    mapping_closures: &[MappingClosureInfo],
) -> HashMap<String, &MappingClosureInfo> {
    let mut mapping_bodies = HashMap::new();
    for mapping_closure in mapping_closures {
        if let PureExpr::Var(ref name, _) = mapping_closure.result_var {
            mapping_bodies.insert(name.clone(), mapping_closure);
        }
    }
    mapping_bodies
}

fn generated_mapping_closure_foralls(
    mapping_closures: &[MappingClosureInfo],
) -> Vec<(PureExpr, String)> {
    mapping_closures
        .iter()
        .filter_map(|mapping_closure| {
            let PureExpr::Var(name, _) = &mapping_closure.result_var else {
                return None;
            };
            mapping_closure
                .to_forall_axiom()
                .map(|axiom| (axiom, name.clone()))
        })
        .collect()
}

fn mapping_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => mapping_var_name(inner),
        _ => None,
    }
}

fn collect_arg_mapping_names(
    args: &[PureExpr],
    mapping_names: &HashSet<String>,
    relevant_names: &mut HashSet<String>,
) {
    for arg in args {
        for name in arg.free_vars() {
            if mapping_names.contains(&name) {
                relevant_names.insert(name);
            }
        }
    }
}

fn collect_relevant_mapping_uses(
    expr: &PureExpr,
    mapping_names: &HashSet<String>,
    relevant_names: &mut HashSet<String>,
    inside_quantifier: bool,
) {
    match expr {
        PureExpr::Var(name, _) if inside_quantifier && mapping_names.contains(name) => {
            relevant_names.insert(name.clone());
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            // `get`/`index_logic`/`lookup` read the closure map directly. `set`
            // reads it through the McCarthy frame — `get(m.set(k, v), k')` for
            // `k' != k` reduces to `get(m, k')`, so a `from_closure` map used only
            // as a `.set` receiver is still relevant to any downstream `.get`. A
            // total-`Mapping` `snapshot!(m.set(..))` chain (mapping_indexing)
            // surfaces the closure map exclusively as a `set` receiver, so
            // omitting `set` here dropped its defining forall and left the base
            // value unconstrained. (#newfrontier)
            if matches!(method.as_str(), "get" | "index_logic" | "lookup" | "set") {
                if let Some(name) = mapping_var_name(receiver) {
                    if mapping_names.contains(name) {
                        relevant_names.insert(name.to_string());
                    }
                }
            }
            collect_relevant_mapping_uses(
                receiver,
                mapping_names,
                relevant_names,
                inside_quantifier,
            );
            for arg in args {
                collect_relevant_mapping_uses(
                    arg,
                    mapping_names,
                    relevant_names,
                    inside_quantifier,
                );
            }
        }
        PureExpr::LogicFnCall { name, args } => {
            if name != "seq" {
                collect_arg_mapping_names(args, mapping_names, relevant_names);
            }
            for arg in args {
                collect_relevant_mapping_uses(
                    arg,
                    mapping_names,
                    relevant_names,
                    inside_quantifier,
                );
            }
        }
        PureExpr::BinOp(left, _, right) => {
            collect_relevant_mapping_uses(left, mapping_names, relevant_names, inside_quantifier);
            collect_relevant_mapping_uses(right, mapping_names, relevant_names, inside_quantifier);
        }
        PureExpr::UnOp(_, operand)
        | PureExpr::Old(operand)
        | PureExpr::Deref(operand)
        | PureExpr::Final(operand)
        | PureExpr::View(operand) => {
            collect_relevant_mapping_uses(
                operand,
                mapping_names,
                relevant_names,
                inside_quantifier,
            );
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_relevant_mapping_uses(cond, mapping_names, relevant_names, inside_quantifier);
            collect_relevant_mapping_uses(
                then_expr,
                mapping_names,
                relevant_names,
                inside_quantifier,
            );
            collect_relevant_mapping_uses(
                else_expr,
                mapping_names,
                relevant_names,
                inside_quantifier,
            );
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            collect_relevant_mapping_uses(body, mapping_names, relevant_names, true);
            for trigger in triggers {
                for trigger_expr in trigger {
                    collect_relevant_mapping_uses(
                        trigger_expr,
                        mapping_names,
                        relevant_names,
                        true,
                    );
                }
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_relevant_mapping_uses(
                scrutinee,
                mapping_names,
                relevant_names,
                inside_quantifier,
            );
            for arm in arms {
                collect_relevant_mapping_uses(
                    &arm.body,
                    mapping_names,
                    relevant_names,
                    inside_quantifier,
                );
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_relevant_mapping_uses(value, mapping_names, relevant_names, inside_quantifier);
            collect_relevant_mapping_uses(body, mapping_names, relevant_names, inside_quantifier);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_relevant_mapping_uses(
                assumption,
                mapping_names,
                relevant_names,
                inside_quantifier,
            );
            collect_relevant_mapping_uses(body, mapping_names, relevant_names, inside_quantifier);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_relevant_mapping_uses(
                obligation,
                mapping_names,
                relevant_names,
                inside_quantifier,
            );
            collect_relevant_mapping_uses(body, mapping_names, relevant_names, inside_quantifier);
        }
        PureExpr::Closure { body, .. } => {
            collect_relevant_mapping_uses(body, mapping_names, relevant_names, inside_quantifier);
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        _ => {}
    }
}

fn inline_bool_mapping_closure_calls_with_map(
    expr: &PureExpr,
    mapping_bodies: &HashMap<String, &MappingClosureInfo>,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if (method == "get" || method == "index_logic") && args.len() == 1 => {
            if let PureExpr::Var(ref recv_name, _) = *receiver {
                if let Some(mapping_closure) = mapping_bodies.get(recv_name) {
                    if let Some(param) = mapping_closure.param_names.first() {
                        let mut subs = HashMap::new();
                        subs.insert(param.clone(), args[0].clone());
                        let rewritten = inline_bool_mapping_closure_calls_with_map(
                            &mapping_closure.body_expr.substitute(&subs),
                            mapping_bodies,
                        );
                        if is_bool_expr(&rewritten) {
                            return collapse_idempotent_views(rewritten);
                        }
                    }
                }
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            }
        }
        other => other,
    })
}

fn push_unique_instance(instances: &mut Vec<PureExpr>, instance: PureExpr) {
    if !instances.contains(&instance) {
        instances.push(instance);
    }
}

fn collect_ground_instances_from_method_call(
    expr: &PureExpr,
    mapping_bodies: &HashMap<String, &MappingClosureInfo>,
    instances: &mut Vec<PureExpr>,
) {
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        if (method == "get" || method == "index_logic") && args.len() == 1 {
            if let PureExpr::Var(ref recv_name, _) = **receiver {
                if let Some(mapping_closure) = mapping_bodies.get(recv_name) {
                    if let Some(param) = mapping_closure.param_names.first() {
                        let mut subs = HashMap::new();
                        subs.insert(param.clone(), normalize_mapping_arg_to_int(&args[0]));
                        let instance =
                            collapse_idempotent_views(mapping_closure.body_expr.substitute(&subs));
                        push_unique_instance(instances, instance);
                    }
                }
            }
        }
    }
}

/// Recursively walk a PureExpr, collecting ground instantiations for mapping
/// closures wherever `mapping.get(arg)` or `mapping.index_logic(arg)` appears.
fn collect_ground_terms_recursive(
    expr: &PureExpr,
    mapping_bodies: &HashMap<String, &MappingClosureInfo>,
    instances: &mut Vec<PureExpr>,
) {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if (method == "get" || method == "index_logic") && args.len() == 1 => {
            if let PureExpr::Var(ref recv_name, _) = **receiver {
                if let Some(mapping_closure) = mapping_bodies.get(recv_name) {
                    if let Some(param) = mapping_closure.param_names.first() {
                        let mut subs = HashMap::new();
                        subs.insert(param.clone(), normalize_mapping_arg_to_int(&args[0]));
                        let body_instantiated =
                            collapse_idempotent_views(mapping_closure.body_expr.substitute(&subs));
                        // For Bool-valued closures (predicates), push just the body
                        // as a fact. For Int-valued closures, push the equation
                        // `mapping.get(arg) == body[x:=arg]` so the solver can
                        // reduce mapping applications to concrete values.
                        if is_bool_expr(&body_instantiated) {
                            push_unique_instance(instances, body_instantiated);
                        } else {
                            let get_call = PureExpr::MethodCall {
                                receiver: receiver.clone(),
                                method: "get".to_string(),
                                args: args.clone(),
                            };
                            push_unique_instance(
                                instances,
                                PureExpr::BinOp(
                                    Arc::new(get_call),
                                    BinOp::Eq,
                                    Arc::new(body_instantiated),
                                ),
                            );
                        }
                    }
                }
            }
            // Also recurse into receiver and args.
            collect_ground_terms_recursive(receiver, mapping_bodies, instances);
            for arg in args {
                collect_ground_terms_recursive(arg, mapping_bodies, instances);
            }
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            collect_ground_terms_recursive(receiver, mapping_bodies, instances);
            for arg in args {
                collect_ground_terms_recursive(arg, mapping_bodies, instances);
            }
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            collect_ground_terms_recursive(lhs, mapping_bodies, instances);
            collect_ground_terms_recursive(rhs, mapping_bodies, instances);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            collect_ground_terms_recursive(inner, mapping_bodies, instances);
        }
        PureExpr::Ite(cond, then_br, else_br) => {
            collect_ground_terms_recursive(cond, mapping_bodies, instances);
            collect_ground_terms_recursive(then_br, mapping_bodies, instances);
            collect_ground_terms_recursive(else_br, mapping_bodies, instances);
        }
        _ => {}
    }
}

/// Quick check whether a PureExpr is a boolean expression (usable directly
/// as a precondition fact). Comparison and boolean ops are Bool; arithmetic
/// and variables are not.
fn is_bool_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Bool(_) => true,
        PureExpr::BinOp(_, op, _) => matches!(
            op,
            BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or
                | BinOp::Implies
        ),
        PureExpr::UnOp(UnOp::Not, _) => true,
        // View-wrapped comparison: View(a op b) for comparison ops.
        PureExpr::View(inner) => is_bool_expr(inner),
        _ => false,
    }
}

fn normalize_mapping_arg_to_int(expr: &PureExpr) -> PureExpr {
    expr.clone().rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, _) => PureExpr::Var(name, Some(ExprSort::Int)),
        other => other,
    })
}
