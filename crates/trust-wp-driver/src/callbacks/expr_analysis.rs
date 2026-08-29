// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expression tree walkers for extracting variable patterns.
//!
//! Contains `extract_old_deref_vars`, `extract_final_vars`,
//! `analyze_call_assumptions`, `expr_contains_old`, and
//! `synthesize_identity_final_values` for inspecting `PureExpr` trees.

use std::collections::{HashMap, HashSet};

use tracing::trace;
use trust_wp_core::formula::PureExpr;

/// Extract variable names from `old(*var)` patterns in an expression.
///
/// This is used to detect mutable reference parameters when MIR analysis
/// isn't available. The presence of `old(*x)` in a postcondition indicates
/// that `x` is a mutable reference parameter.
pub(super) fn extract_old_deref_vars(expr: &PureExpr, vars: &mut HashSet<String>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::Old(inner) = node {
            if let PureExpr::Deref(deref_inner) = inner.as_ref() {
                if let PureExpr::Var(name, _) = deref_inner.as_ref() {
                    vars.insert(name.clone());
                }
            }
        }
    });
}

/// Extract variable names from `^var` (Final(Var(name))) patterns in an expression.
///
/// This is used to detect &mut parameters referenced with prophecy values in
/// postconditions. The presence of `^f` in an ensures clause indicates that
/// `f` is a mutable reference parameter whose final value must be constrained.
pub(super) fn extract_final_vars(expr: &PureExpr, vars: &mut HashSet<String>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::Final(inner) = node {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                vars.insert(name.clone());
            }
        }
    });
}

/// Extract `self.N` variable names from expressions containing `self.N`
/// references through `Final`, `Old`, `View`, or `Deref` wrappers. (#2668, #2318)
///
/// Used as a fallback to detect closure capture fields in postconditions when
/// `extract_mut_borrow_body` fails for complex closure bodies. The presence
/// of `^self.1`, `old(self.1)`, `^old(self.1)`, or `(^old(self.1))@` in ensures
/// indicates that `self.1` is a mutable closure capture field needing
/// postcondition transformation.
///
/// Handles nested patterns such as:
/// - `Final(Var("self.N"))` -> `^self.N`
/// - `Old(Var("self.N"))` -> `old(self.N)`
/// - `Final(Old(Var("self.N")))` -> `^old(self.N)` (#2318: Box-wrapped captures)
/// - `View(Final(Old(Var("self.N"))))` -> `(^old(self.N))@`
pub(super) fn extract_final_self_field_vars(expr: &PureExpr, vars: &mut HashSet<String>) {
    expr.for_each_recursive(|node| match node {
        PureExpr::Final(inner) | PureExpr::Old(inner) | PureExpr::View(inner) => {
            if let Some(name) = peel_to_self_field_var(inner) {
                vars.insert(name.to_string());
            }
        }
        _ => {}
    });
}

/// Peel through `Final`, `Old`, `View`, and `Deref` wrappers to find a
/// `Var("self.N")` at the root. Returns `Some(name)` if found.
///
/// This supports arbitrarily nested wrapper chains such as
/// `Final(Old(Var("self.1")))` or `View(Final(Old(Var("self.2"))))`.
fn peel_to_self_field_var(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) if name.starts_with("self.") => Some(name.as_str()),
        PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner)
        | PureExpr::Deref(inner) => peel_to_self_field_var(inner),
        _ => None,
    }
}

/// Analyze call assumptions to determine if identity final value synthesis is safe
/// and which variables are closure-spec receivers.
///
/// Returns `(has_mutating, receivers)`:
/// - `has_mutating`: true if any assumption uses postcondition_mut/postcondition_once
///   or is a non-MethodCall expression (conservatively unsafe).
/// - `receivers`: set of variable names that appear as receivers in closure-spec
///   method calls (e.g., `f` from `(*f).postcondition(arg, result)`).
pub(super) fn analyze_call_assumptions(assumptions: &[PureExpr]) -> (bool, HashSet<String>) {
    let mut has_mutating = false;
    let mut receivers = HashSet::new();
    for a in assumptions {
        if let PureExpr::MethodCall {
            method, receiver, ..
        } = a
        {
            if method == "postcondition_mut" || method == "postcondition_once" {
                has_mutating = true;
                break;
            }
            // Extract receiver variable name: Var("f") or Deref(Var("f"))
            match receiver.as_ref() {
                PureExpr::Var(name, _) => {
                    receivers.insert(name.clone());
                }
                PureExpr::Deref(inner) => {
                    if let PureExpr::Var(name, _) = inner.as_ref() {
                        receivers.insert(name.clone());
                    }
                }
                _ => {}
            }
        } else {
            // Non-MethodCall assumption: conservatively block identity synthesis
            has_mutating = true;
            break;
        }
    }
    (has_mutating, receivers)
}

#[derive(Default)]
struct StructuredCallEffectAnalysis {
    has_opaque_assumption: bool,
    receivers: HashSet<String>,
}

fn receiver_name(receiver: &PureExpr) -> Option<String> {
    match receiver {
        PureExpr::Var(name, _) => Some(name.clone()),
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn is_mutating_method_name(method: &str) -> bool {
    method == "postcondition_mut" || method == "postcondition_once"
}

fn analyze_structured_call_effects(
    expr: &PureExpr,
    in_mutating_scope: bool,
    analysis: &mut StructuredCallEffectAnalysis,
) {
    match expr {
        PureExpr::LetAssume { assumption, body } => {
            let mut next_scope = in_mutating_scope;
            match assumption.as_ref() {
                PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                } => {
                    if let Some(name) = receiver_name(receiver) {
                        analysis.receivers.insert(name);
                    }
                    if is_mutating_method_name(method) {
                        next_scope = true;
                    }
                    analyze_structured_call_effects(receiver, in_mutating_scope, analysis);
                    for arg in args {
                        analyze_structured_call_effects(arg, in_mutating_scope, analysis);
                    }
                }
                _ => {
                    if !in_mutating_scope {
                        analysis.has_opaque_assumption = true;
                    }
                    analyze_structured_call_effects(assumption, in_mutating_scope, analysis);
                }
            }
            analyze_structured_call_effects(body, next_scope, analysis);
        }
        PureExpr::LetObligation { obligation, body } => {
            analyze_structured_call_effects(obligation, in_mutating_scope, analysis);
            analyze_structured_call_effects(body, in_mutating_scope, analysis);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            analyze_structured_call_effects(cond, in_mutating_scope, analysis);
            analyze_structured_call_effects(then_expr, in_mutating_scope, analysis);
            analyze_structured_call_effects(else_expr, in_mutating_scope, analysis);
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            analyze_structured_call_effects(lhs, in_mutating_scope, analysis);
            analyze_structured_call_effects(rhs, in_mutating_scope, analysis);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            analyze_structured_call_effects(inner, in_mutating_scope, analysis);
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            for trigger in triggers {
                for trigger_expr in trigger {
                    analyze_structured_call_effects(trigger_expr, in_mutating_scope, analysis);
                }
            }
            analyze_structured_call_effects(body, in_mutating_scope, analysis);
        }
        PureExpr::Match { scrutinee, arms } => {
            analyze_structured_call_effects(scrutinee, in_mutating_scope, analysis);
            for arm in arms {
                analyze_structured_call_effects(&arm.body, in_mutating_scope, analysis);
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                analyze_structured_call_effects(arg, in_mutating_scope, analysis);
            }
        }
        PureExpr::Let { value, body, .. } => {
            analyze_structured_call_effects(value, in_mutating_scope, analysis);
            analyze_structured_call_effects(body, in_mutating_scope, analysis);
        }
        PureExpr::MethodCall {
            receiver,
            method: _,
            args,
        } => {
            if let Some(name) = receiver_name(receiver) {
                analysis.receivers.insert(name);
            }
            analyze_structured_call_effects(receiver, in_mutating_scope, analysis);
            for arg in args {
                analyze_structured_call_effects(arg, in_mutating_scope, analysis);
            }
        }
        PureExpr::Closure { body, .. } => {
            analyze_structured_call_effects(body, in_mutating_scope, analysis);
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

fn analyze_call_assumptions_from_expr(expr: &PureExpr) -> (bool, HashSet<String>) {
    let mut analysis = StructuredCallEffectAnalysis::default();
    analyze_structured_call_effects(expr, false, &mut analysis);
    (analysis.has_opaque_assumption, analysis.receivers)
}

/// Why identity final value synthesis was skipped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum IdentityFinalValueSynthesisSkipReason {
    /// The function already has a concrete mut-borrow body.
    HasMutBorrowBody,
    /// No `^var` terms were present in the relevant ensures clauses.
    NoFinalVars,
    /// No `^var` terms matched a closure receiver.
    NoRelevantFinalVars,
    /// At least one call assumption was non-`MethodCall` or mutating.
    MutatingOrOpaqueCallAssumption,
}

/// Diagnose why identity final value synthesis would not run.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn diagnose_identity_final_value_synthesis_skip(
    has_mut_borrow_body: bool,
    effective_ensures: &[PureExpr],
    call_assumptions: &[PureExpr],
) -> Option<IdentityFinalValueSynthesisSkipReason> {
    diagnose_identity_final_value_synthesis_skip_with_expr(
        has_mut_borrow_body,
        effective_ensures,
        call_assumptions,
        None,
    )
}

pub(super) fn diagnose_identity_final_value_synthesis_skip_with_expr(
    has_mut_borrow_body: bool,
    effective_ensures: &[PureExpr],
    call_assumptions: &[PureExpr],
    call_effect_expr: Option<&PureExpr>,
) -> Option<IdentityFinalValueSynthesisSkipReason> {
    if has_mut_borrow_body {
        return Some(IdentityFinalValueSynthesisSkipReason::HasMutBorrowBody);
    }

    let mut final_vars = HashSet::new();
    for e in effective_ensures {
        extract_final_vars(e, &mut final_vars);
    }
    if final_vars.is_empty() {
        return Some(IdentityFinalValueSynthesisSkipReason::NoFinalVars);
    }

    let (has_mutating_assumption, closure_receivers) = match call_effect_expr {
        Some(expr) => analyze_call_assumptions_from_expr(expr),
        None => analyze_call_assumptions(call_assumptions),
    };
    if has_mutating_assumption {
        return Some(IdentityFinalValueSynthesisSkipReason::MutatingOrOpaqueCallAssumption);
    }
    let filtered_vars: HashSet<_> = final_vars
        .intersection(&closure_receivers)
        .cloned()
        .collect();
    if filtered_vars.is_empty() {
        return Some(IdentityFinalValueSynthesisSkipReason::NoRelevantFinalVars);
    }

    None
}

/// Check if a PureExpr tree contains any `Old(..)` node. (#1962)
///
/// Replaces the fragile `format!("{e}").contains("old(")` string-matching
/// with a structural tree walk that is immune to Display format changes.
/// Extracted from verification.rs as part of #1526 Phase 5.
pub(super) fn expr_contains_old(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Old(_)))
}

/// Check whether an expression contains a mutating closure spec call.
///
/// This is provenance-only: it answers whether the original effect came from a
/// `postcondition_mut`/`postcondition_once` call, regardless of later wrapper
/// stripping or assumption flattening.
pub(super) fn contains_mutating_call_effect(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| {
        matches!(
            node,
            PureExpr::MethodCall { method, .. }
                if method == "postcondition_mut" || method == "postcondition_once"
        )
    })
}

/// Synthesize identity final values for &mut params when the MIR extractor
/// couldn't analyze the body (e.g., function calls) but the call goes through
/// Fn::call (immutable). (#520, #530)
///
/// Fn::call takes `&self`, so it cannot modify the closure environment,
/// meaning `f_final == f_current` for the &mut parameter. This enables
/// Fn → FnMut weakening: the `fn_mut` law axiom requires `self == res_state`,
/// which is only provable when `f_final` is constrained.
///
/// Extracted from verification.rs as part of #1526 Phase 5.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn synthesize_identity_final_values(
    has_mut_borrow_body: bool,
    effective_ensures: &[PureExpr],
    call_assumptions: &[PureExpr],
) -> Option<HashMap<String, PureExpr>> {
    synthesize_identity_final_values_with_expr(
        has_mut_borrow_body,
        effective_ensures,
        call_assumptions,
        None,
    )
}

pub(super) fn synthesize_identity_final_values_with_expr(
    has_mut_borrow_body: bool,
    effective_ensures: &[PureExpr],
    call_assumptions: &[PureExpr],
    call_effect_expr: Option<&PureExpr>,
) -> Option<HashMap<String, PureExpr>> {
    if diagnose_identity_final_value_synthesis_skip_with_expr(
        has_mut_borrow_body,
        effective_ensures,
        call_assumptions,
        call_effect_expr,
    )
    .is_some()
    {
        return None;
    }

    let mut final_vars = HashSet::new();
    for e in effective_ensures {
        extract_final_vars(e, &mut final_vars);
    }
    let (_, closure_receivers) = match call_effect_expr {
        Some(expr) => analyze_call_assumptions_from_expr(expr),
        None => analyze_call_assumptions(call_assumptions),
    };
    let filtered_vars: HashSet<_> = final_vars
        .intersection(&closure_receivers)
        .cloned()
        .collect();
    if filtered_vars.is_empty() {
        return None;
    }

    let mut fv = HashMap::new();
    for var in &filtered_vars {
        // Use bare Var (not Deref) because closure spec methods normalize
        // receivers: (*f).postcondition(...) strips the deref, encoding the
        // receiver as plain `f` in SMT. The final value `f_final = f` (bare)
        // connects to the fn_mut law's `self == res_state` constraint.
        // Using Deref would produce `f_final = f_current`, leaving `f` and
        // `f_current` unrelated in the SMT context.
        fv.insert(var.clone(), PureExpr::Var(var.clone(), None));
    }
    trace!(
        params = fv.len(),
        "synthesized identity final values (Fn::call preserves state)",
    );
    Some(fv)
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, sync::Arc};

    use trust_wp_core::formula::PureExpr;

    use super::*;

    #[test]
    fn test_extract_final_self_field_direct_final() {
        // Final(Var("self.0")) should be detected
        let expr = PureExpr::Final(Arc::new(PureExpr::Var("self.0".to_string(), None)));
        let mut vars = HashSet::new();
        extract_final_self_field_vars(&expr, &mut vars);
        assert!(
            vars.contains("self.0"),
            "should detect Final(Var(\"self.0\"))"
        );
    }

    #[test]
    fn test_extract_final_self_field_direct_old() {
        // Old(Var("self.1")) should be detected
        let expr = PureExpr::Old(Arc::new(PureExpr::Var("self.1".to_string(), None)));
        let mut vars = HashSet::new();
        extract_final_self_field_vars(&expr, &mut vars);
        assert!(
            vars.contains("self.1"),
            "should detect Old(Var(\"self.1\"))"
        );
    }

    #[test]
    fn test_extract_final_self_field_nested_final_old() {
        // Final(Old(Var("self.1"))) should be detected (#2318)
        // This pattern arises from ^old(self.1) after box deref erasure
        let expr = PureExpr::Final(Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
            "self.1".to_string(),
            None,
        )))));
        let mut vars = HashSet::new();
        extract_final_self_field_vars(&expr, &mut vars);
        assert!(
            vars.contains("self.1"),
            "should detect Final(Old(Var(\"self.1\"))) — nested pattern from #2318"
        );
    }

    #[test]
    fn test_extract_final_self_field_view_final_old() {
        // View(Final(Old(Var("self.2")))) should be detected (#2318)
        // This pattern arises from (^old(self.2))@ after box deref erasure
        let expr = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Old(
            Arc::new(PureExpr::Var("self.2".to_string(), None)),
        )))));
        let mut vars = HashSet::new();
        extract_final_self_field_vars(&expr, &mut vars);
        assert!(
            vars.contains("self.2"),
            "should detect View(Final(Old(Var(\"self.2\")))) — full #2318 ensures pattern"
        );
    }

    #[test]
    fn test_extract_final_self_field_nested_in_binop() {
        // BinOp(View(Final(Old(Var("self.1")))), Add, View(Final(Old(Var("self.2")))))
        // Both self.1 and self.2 should be detected
        let lhs = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Old(
            Arc::new(PureExpr::Var("self.1".to_string(), None)),
        )))));
        let rhs = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Old(
            Arc::new(PureExpr::Var("self.2".to_string(), None)),
        )))));
        let expr = PureExpr::BinOp(
            Arc::new(lhs),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(rhs),
        );
        let mut vars = HashSet::new();
        extract_final_self_field_vars(&expr, &mut vars);
        assert!(vars.contains("self.1"), "should detect self.1 in LHS");
        assert!(vars.contains("self.2"), "should detect self.2 in RHS");
    }

    #[test]
    fn test_extract_final_self_field_non_self_ignored() {
        // Final(Var("x")) should NOT be added (not a self.N field)
        let expr = PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)));
        let mut vars = HashSet::new();
        extract_final_self_field_vars(&expr, &mut vars);
        assert!(vars.is_empty(), "non-self variables should be ignored");
    }

    #[test]
    fn test_extract_final_self_field_bare_var_ignored() {
        // Bare Var("self.0") (not inside Final/Old/View) should NOT be detected
        let expr = PureExpr::Var("self.0".to_string(), None);
        let mut vars = HashSet::new();
        extract_final_self_field_vars(&expr, &mut vars);
        assert!(
            vars.is_empty(),
            "bare Var without Final/Old wrapper should not be detected"
        );
    }

    #[test]
    fn test_structured_call_effect_preserves_mutating_scope_for_identity_synthesis() {
        let ensures = vec![PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "f".to_string(),
                None,
            )))),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        )];
        let mutating_call = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "f".to_string(),
                None,
            )))),
            method: "postcondition_mut".to_string(),
            args: vec![PureExpr::Var("arg".to_string(), None)],
        };
        let nested_opaque_fact = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::Int(10)),
        );
        let call_effect_expr = PureExpr::LetAssume {
            assumption: Arc::new(mutating_call),
            body: Arc::new(PureExpr::LetAssume {
                assumption: Arc::new(nested_opaque_fact),
                body: Arc::new(PureExpr::Bool(true)),
            }),
        };

        assert_eq!(
            diagnose_identity_final_value_synthesis_skip_with_expr(
                false,
                &ensures,
                &[],
                Some(&call_effect_expr),
            ),
            None,
            "structured mutating call scope should keep identity synthesis alive"
        );
        let synthesized = synthesize_identity_final_values_with_expr(
            false,
            &ensures,
            &[],
            Some(&call_effect_expr),
        )
        .expect("structured mutating call scope should synthesize identity final values");
        assert_eq!(
            synthesized.get("f"),
            Some(&PureExpr::Var("f".to_string(), None)),
            "structured call effect should preserve the closure receiver"
        );
    }
}
