// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type invariant method rewriting in expression trees.
//!
//! Rewrites `invariant()` and `inv(x)` calls to type-qualified invariant
//! methods (e.g., `__trust_wp_invariant_MyStruct`) throughout a parsed contract.

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::{formula::PureExpr, logic::is_invariant_method_name};

use super::super::{contract_rewrite::receiver_root_var_name, parsing::ParsedContract};

fn structural_invariant_expr_for_root(
    root: &str,
    param_structural_exprs: &HashMap<String, PureExpr>,
    result_structural_expr: Option<&PureExpr>,
) -> Option<PureExpr> {
    if root == "result" {
        result_structural_expr.cloned()
    } else {
        param_structural_exprs.get(root).cloned()
    }
}

pub(in crate::callbacks) fn rewrite_type_invariant_methods_expr_with_structural(
    expr: &PureExpr,
    param_methods: &HashMap<String, String>,
    result_method: Option<&str>,
    param_structural_exprs: &HashMap<String, PureExpr>,
    result_structural_expr: Option<&PureExpr>,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if args.is_empty() && is_invariant_method_name(&method) {
                if let Some(name) = receiver_root_var_name(receiver.as_ref()) {
                    if let Some(rewritten_method) = if name == "result" {
                        result_method.map(ToOwned::to_owned)
                    } else {
                        param_methods.get(name).cloned()
                    } {
                        return PureExpr::MethodCall {
                            receiver,
                            method: rewritten_method,
                            args,
                        };
                    }
                    if let Some(structural_expr) = structural_invariant_expr_for_root(
                        name,
                        param_structural_exprs,
                        result_structural_expr,
                    ) {
                        return structural_expr;
                    }
                }
            }

            PureExpr::MethodCall {
                receiver,
                method,
                args,
            }
        }
        PureExpr::LogicFnCall { name, args } if name == "inv" && args.len() == 1 => {
            let arg = args.into_iter().next().expect("checked unary inv");
            if let Some(var_name) = receiver_root_var_name(&arg) {
                if let Some(method) = if var_name == "result" {
                    result_method.map(ToOwned::to_owned)
                } else {
                    param_methods.get(var_name).cloned()
                } {
                    return PureExpr::MethodCall {
                        receiver: Arc::new(arg),
                        method,
                        args: vec![],
                    };
                }
                if let Some(structural_expr) = structural_invariant_expr_for_root(
                    var_name,
                    param_structural_exprs,
                    result_structural_expr,
                ) {
                    return structural_expr;
                }
            }

            PureExpr::LogicFnCall {
                name,
                args: vec![arg],
            }
        }
        other => other,
    })
}

/// Discharge bare `inv(arg)` / `arg.invariant()` calls whose root is a known
/// parameter (or `result`) that has **no** registered type invariant to the
/// constant `true`.
///
/// Motivation (#8373): for every `&mut` parameter, `contract_transform` injects
/// the Creusot reborrow side-conditions `inv(x)` and `inv(*x)` into the
/// *requires*. When the pointee type carries a user/synthetic invariant, the
/// structural rewrite (`rewrite_type_invariant_methods_expr_with_structural`)
/// retargets `inv(x)` to the type-qualified `__trust_wp_invariant_<Type>`
/// symbol. But when the pointee type has no invariant (e.g. a primitive
/// `&mut i32`, or `&mut &mut i32`), `param_methods`/structural maps have no
/// entry, so the bare `inv(...)` call survives and the encoder lowers it to an
/// *unconstrained* placeholder UF (`logic_inv__placeholder_..._ret_b`). Asserting
/// that opaque predicate as a precondition trips ay's model-validation guard
/// (#8373): the solver may pick a model where the UF is `false`, contradicting
/// the asserted-true atom, and degrades the whole obligation to `Unknown`.
///
/// The faithful Creusot semantics is that a type with no `Invariant` impl has
/// `inv == true`. Rewriting these bare calls to `true` realises that, and is
/// sound by construction: every site this touches is an *assumption* (requires
/// position) for a root with no registered invariant, so replacing `inv(arg)`
/// with `true` only **removes** an (uninterpretable) hypothesis — it can never
/// admit a model the original rejected, hence cannot create a false-accept.
///
/// The rewrite is deliberately gated on the root being a member of
/// `known_trivial_roots` (the function's parameter names, plus `result`) that is
/// absent from both `param_methods` and the structural map. Roots that are not
/// recognised parameters, or that DO carry an invariant, are left untouched so
/// the existing type-qualified rewrite remains authoritative.
pub(in crate::callbacks) fn discharge_trivial_inv_calls_expr(
    expr: &PureExpr,
    known_trivial_roots: &std::collections::HashSet<String>,
) -> PureExpr {
    fn root_is_trivial(
        arg: &PureExpr,
        known_trivial_roots: &std::collections::HashSet<String>,
    ) -> bool {
        receiver_root_var_name(arg).is_some_and(|root| known_trivial_roots.contains(root))
    }

    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args }
            if name == "inv"
                && args.len() == 1
                && root_is_trivial(&args[0], known_trivial_roots) =>
        {
            PureExpr::Bool(true)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if args.is_empty()
            && is_invariant_method_name(&method)
            && root_is_trivial(receiver.as_ref(), known_trivial_roots) =>
        {
            PureExpr::Bool(true)
        }
        other => other,
    })
}

/// Non-structural convenience wrapper (test-only after #1296 structural expansion).
#[cfg(test)]
pub(in crate::callbacks) fn rewrite_type_invariant_methods_expr(
    expr: &PureExpr,
    param_methods: &HashMap<String, String>,
    result_method: Option<&str>,
) -> PureExpr {
    rewrite_type_invariant_methods_expr_with_structural(
        expr,
        param_methods,
        result_method,
        &HashMap::new(),
        None,
    )
}

pub(in crate::callbacks) fn rewrite_parsed_contract_type_invariant_methods_with_structural(
    parsed: &mut ParsedContract,
    param_methods: &HashMap<String, String>,
    result_method: Option<&str>,
    param_structural_exprs: &HashMap<String, PureExpr>,
    result_structural_expr: Option<&PureExpr>,
) {
    if param_methods.is_empty()
        && result_method.is_none()
        && param_structural_exprs.is_empty()
        && result_structural_expr.is_none()
    {
        return;
    }
    parsed.rewrite_all_exprs(|expr| {
        rewrite_type_invariant_methods_expr_with_structural(
            expr,
            param_methods,
            result_method,
            param_structural_exprs,
            result_structural_expr,
        )
    });
}

/// Non-structural convenience wrapper for parsed contracts (test-only after #1296).
#[cfg(test)]
pub(in crate::callbacks) fn rewrite_parsed_contract_type_invariant_methods(
    parsed: &mut ParsedContract,
    param_methods: &HashMap<String, String>,
    result_method: Option<&str>,
) {
    rewrite_parsed_contract_type_invariant_methods_with_structural(
        parsed,
        param_methods,
        result_method,
        &HashMap::new(),
        None,
    );
}
