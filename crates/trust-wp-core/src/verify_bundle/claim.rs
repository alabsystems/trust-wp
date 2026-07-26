// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use super::{
    trust_formula::{decode_trust_formula_v1_claim, validate_native_replay_definedness},
    BundleClaimFormat, BundleDiagnostic, BundleObligation,
};
use crate::{
    contract_parser::parse_contract,
    formula::{BinOp, CaptureAvoidingSubstOptions, ExprSort, PureExpr, UnOp},
};

/// Parsed native proof input for a bundle obligation.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeBundlePredicate {
    pub obligation_id: String,
    pub claim_format: NativeClaimFormat,
    pub predicate: PureExpr,
}

/// Native claim formats with a real decoder into [`PureExpr`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeClaimFormat {
    TrustWpPureExprV1,
    TrustFormulaV1,
}

impl NativeClaimFormat {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TrustWpPureExprV1 => "TrustWpPureExprV1",
            Self::TrustFormulaV1 => "TrustFormulaV1",
        }
    }
}

/// Convert a bundle obligation claim into trust-wp's native predicate IR.
///
/// This is intentionally fail-closed: only claim formats with a real typed
/// decoder into [`PureExpr`] are accepted as native proof input. Opaque formats
/// remain valid interchange artifacts, not replay claims.
pub fn native_predicate_for_obligation(
    obligation: &BundleObligation,
) -> Result<NativeBundlePredicate, BundleDiagnostic> {
    let (claim_format, predicate) = match &obligation.claim.format {
        BundleClaimFormat::TrustWpPureExprV1 => {
            let predicate = parse_contract(obligation.claim.payload.trim()).map_err(|err| {
                BundleDiagnostic::invalid(
                    "obligation.claim.payload",
                    format!(
                        "obligation `{}` has invalid TrustWpPureExprV1 claim payload: {err}",
                        obligation.id
                    ),
                )
            })?;
            validate_native_replay_definedness(&predicate).map_err(|err| {
                BundleDiagnostic::invalid(
                    "obligation.claim.payload",
                    format!(
                        "obligation `{}` has undefined TrustWpPureExprV1 arithmetic: {err}",
                        obligation.id
                    ),
                )
            })?;
            (NativeClaimFormat::TrustWpPureExprV1, predicate)
        }
        BundleClaimFormat::TrustFormulaV1 => (
            NativeClaimFormat::TrustFormulaV1,
            decode_trust_formula_v1_claim(obligation.claim.payload.trim()).map_err(|err| {
                BundleDiagnostic::invalid(
                    "obligation.claim.payload",
                    format!(
                        "obligation `{}` has invalid TrustFormulaV1 claim payload: {err}",
                        obligation.id
                    ),
                )
            })?,
        ),
        BundleClaimFormat::SmtLib2 => return Err(opaque_format_diagnostic(obligation, "SMT-LIB2")),
        BundleClaimFormat::Other(format) => {
            return Err(opaque_format_diagnostic(obligation, format.as_str()));
        }
    };

    // A verification condition is the NEGATION to be refuted (`And(defs.., Not(goal))`,
    // UNSAT iff valid), but native replay proves predicates TRUE. Convert a
    // refutation-form claim into the equivalent positive validity goal
    // (`Implies(And(defs), goal)`) so the deductive prover (assumption-projection,
    // implication rules) can discharge it. Already-positive claims pass through.
    let predicate = vc_to_positive_goal(predicate);

    if !is_boolean_predicate(&predicate) {
        return Err(BundleDiagnostic::invalid(
            "obligation.claim.payload",
            format!(
                "obligation `{}` claim payload is not a typed boolean predicate",
                obligation.id
            ),
        ));
    }

    Ok(NativeBundlePredicate {
        obligation_id: obligation.id.clone(),
        claim_format,
        predicate,
    })
}

/// Rewrite a refutation-form verification condition into the equivalent positive
/// validity goal that native replay can prove TRUE.
///
/// A VC is the claim's negation: `And(a1.., Not(g1), .., Not(gm))`, which is UNSAT
/// (discharged) iff `And(a_i) ⟹ And(g_j)` is valid. Native replay proves
/// predicates TRUE, so we hand it that positive implication instead of the raw
/// refutation (which it would try, wrongly, to evaluate to TRUE). Transformation
/// is applied ONLY when a negated conjunct (the goal) is present — an
/// already-positive claim is returned unchanged.
fn vc_to_positive_goal(expr: PureExpr) -> PureExpr {
    fn flatten_and(e: PureExpr, out: &mut Vec<PureExpr>) {
        if let PureExpr::BinOp(left, BinOp::And, right) = e {
            flatten_and((*left).clone(), out);
            flatten_and((*right).clone(), out);
        } else {
            out.push(e);
        }
    }
    fn and_all(mut conjuncts: Vec<PureExpr>) -> PureExpr {
        if conjuncts.is_empty() {
            return PureExpr::Bool(true);
        }
        let first = conjuncts.remove(0);
        conjuncts.into_iter().fold(first, |acc, next| {
            PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(next))
        })
    }

    // A bare negated goal (`Not(P)`): valid iff `P` is.
    if let PureExpr::UnOp(UnOp::Not, inner) = &expr {
        return (**inner).clone();
    }
    // A conjunction that may carry negated goals (the VC refutation form).
    if matches!(expr, PureExpr::BinOp(_, BinOp::And, _)) {
        let mut conjuncts = Vec::new();
        flatten_and(expr, &mut conjuncts);
        let mut assumptions = Vec::new();
        let mut goals = Vec::new();
        for conjunct in conjuncts {
            if let PureExpr::UnOp(UnOp::Not, inner) = &conjunct {
                goals.push((**inner).clone());
            } else {
                assumptions.push(conjunct);
            }
        }
        if goals.is_empty() {
            // Not a refutation form — rebuild the original conjunction unchanged.
            return and_all(assumptions);
        }
        let goal = and_all(goals);
        return if assumptions.is_empty() {
            goal
        } else {
            PureExpr::BinOp(
                Arc::new(and_all(assumptions)),
                BinOp::Implies,
                Arc::new(goal),
            )
        };
    }
    expr
}

fn opaque_format_diagnostic(obligation: &BundleObligation, format: &str) -> BundleDiagnostic {
    BundleDiagnostic::invalid(
        "obligation.claim.format",
        format!(
            "obligation `{}` uses opaque claim format `{format}`; native proof input requires a typed decoder into PureExpr",
            obligation.id
        ),
    )
}

fn is_boolean_predicate(expr: &PureExpr) -> bool {
    matches!(infer_native_sort(expr), Some(NativeExprSort::Bool))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeExprSort {
    Bool,
    Int,
    Pointer(NativePointerKind),
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativePointerKind {
    Thin,
    Fat,
}

fn infer_native_sort(expr: &PureExpr) -> Option<NativeExprSort> {
    let mut env = HashMap::new();
    infer_native_sort_with_env(expr, &mut env)
}

fn infer_native_sort_with_env(
    expr: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
) -> Option<NativeExprSort> {
    match expr {
        PureExpr::Bool(_) => Some(NativeExprSort::Bool),
        PureExpr::Int(_) => Some(NativeExprSort::Int),
        PureExpr::Var(_, Some(ExprSort::Bool)) => Some(NativeExprSort::Bool),
        PureExpr::Var(_, Some(ExprSort::Int)) => Some(NativeExprSort::Int),
        PureExpr::Var(_, Some(sort)) => native_sort_from_expr_sort(sort),
        PureExpr::Var(name, None) => env
            .get(name)
            .and_then(native_sort_from_expr_sort)
            .or(Some(NativeExprSort::Unknown)),
        PureExpr::BinOp(left, op, right) => match op {
            BinOp::Eq | BinOp::Ne => {
                compatible_comparison(left, right, env).then_some(NativeExprSort::Bool)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                int_like(left, env).then_some(())?;
                int_like(right, env).then_some(NativeExprSort::Bool)
            }
            BinOp::And | BinOp::Or | BinOp::Implies => bool_like(left, right, env),
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::DivTrunc
            | BinOp::RemTrunc
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::BitOr => {
                int_like(left, env).then_some(())?;
                int_like(right, env).then_some(NativeExprSort::Int)
            }
        },
        PureExpr::UnOp(UnOp::Not, inner) => (infer_native_sort_with_env(inner, env)?
            == NativeExprSort::Bool)
            .then_some(NativeExprSort::Bool),
        PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, inner) => {
            int_like(inner, env).then_some(NativeExprSort::Int)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            (infer_native_sort_with_env(cond, env)? == NativeExprSort::Bool).then_some(())?;
            merge_branch_sorts(
                infer_native_sort_with_env(then_expr, env)?,
                infer_native_sort_with_env(else_expr, env)?,
            )
        }
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
        } => with_bound_sort(env, var, var_sort.as_ref(), |env| {
            (infer_native_sort_with_env(body, env)? == NativeExprSort::Bool)
                .then_some(NativeExprSort::Bool)
        }),
        PureExpr::Let { var, value, body } => {
            infer_native_sort_with_env(&inline_let_binding(var, value, body), env)
        }
        PureExpr::Closure { body, .. } => infer_native_sort_with_env(body, env),
        PureExpr::LetAssume { assumption, body } => bool_like(assumption, body, env),
        PureExpr::LetObligation { obligation, body } => bool_like(obligation, body, env),
        PureExpr::Old(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => {
            infer_native_sort_with_env(inner, env)
        }
        PureExpr::Deref(_) => Some(NativeExprSort::Unknown),
        PureExpr::Float(_)
        | PureExpr::MethodCall { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. } => None,
    }
}

fn inline_let_binding(var: &str, value: &PureExpr, body: &PureExpr) -> PureExpr {
    let mut substitutions = HashMap::new();
    substitutions.insert(var.to_string(), value.clone());
    body.substitute_capture_avoiding(&substitutions, &CaptureAvoidingSubstOptions::default())
}

fn bool_like(
    left: &PureExpr,
    right: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
) -> Option<NativeExprSort> {
    (infer_native_sort_with_env(left, env)? == NativeExprSort::Bool).then_some(())?;
    (infer_native_sort_with_env(right, env)? == NativeExprSort::Bool)
        .then_some(NativeExprSort::Bool)
}

fn int_like(expr: &PureExpr, env: &mut HashMap<String, ExprSort>) -> bool {
    matches!(
        infer_native_sort_with_env(expr, env),
        Some(NativeExprSort::Int | NativeExprSort::Unknown)
    )
}

fn compatible_comparison(
    left: &PureExpr,
    right: &PureExpr,
    env: &mut HashMap<String, ExprSort>,
) -> bool {
    left == right
        || sorts_compatible(
            infer_native_sort_with_env(left, env),
            infer_native_sort_with_env(right, env),
        )
}

fn sorts_compatible(left: Option<NativeExprSort>, right: Option<NativeExprSort>) -> bool {
    matches!(
        (left, right),
        (Some(NativeExprSort::Unknown), Some(_))
            | (Some(_), Some(NativeExprSort::Unknown))
            | (Some(NativeExprSort::Bool), Some(NativeExprSort::Bool))
            | (Some(NativeExprSort::Int), Some(NativeExprSort::Int))
            | (
                Some(NativeExprSort::Pointer(_)),
                Some(NativeExprSort::Pointer(_))
            )
    )
}

fn merge_branch_sorts(left: NativeExprSort, right: NativeExprSort) -> Option<NativeExprSort> {
    match (left, right) {
        (NativeExprSort::Unknown, sort) | (sort, NativeExprSort::Unknown) => Some(sort),
        (NativeExprSort::Bool, NativeExprSort::Bool) => Some(NativeExprSort::Bool),
        (NativeExprSort::Int, NativeExprSort::Int) => Some(NativeExprSort::Int),
        (NativeExprSort::Pointer(left), NativeExprSort::Pointer(right)) if left == right => {
            Some(NativeExprSort::Pointer(left))
        }
        _ => None,
    }
}

fn native_sort_from_expr_sort(sort: &ExprSort) -> Option<NativeExprSort> {
    match sort {
        ExprSort::Bool => Some(NativeExprSort::Bool),
        ExprSort::Int => Some(NativeExprSort::Int),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => Some(NativeExprSort::Pointer(
            pointer_kind_from_referent_sort(inner),
        )),
        ExprSort::TypeParam(_) => Some(NativeExprSort::Unknown),
        ExprSort::Seq
        | ExprSort::Unit
        | ExprSort::Datatype(_)
        | ExprSort::FMap
        | ExprSort::Tuple(_)
        | ExprSort::Float => None,
    }
}

fn pointer_kind_from_referent_sort(sort: &ExprSort) -> NativePointerKind {
    match sort {
        ExprSort::Seq | ExprSort::FMap => NativePointerKind::Fat,
        _ => NativePointerKind::Thin,
    }
}

fn with_bound_sort<T>(
    env: &mut HashMap<String, ExprSort>,
    var: &str,
    var_sort: Option<&ExprSort>,
    f: impl FnOnce(&mut HashMap<String, ExprSort>) -> T,
) -> T {
    let previous = match var_sort {
        Some(sort) => env.insert(var.to_string(), sort.clone()),
        None => env.remove(var),
    };
    let result = f(env);
    match previous {
        Some(sort) => {
            env.insert(var.to_string(), sort);
        }
        None => {
            env.remove(var);
        }
    }
    result
}
