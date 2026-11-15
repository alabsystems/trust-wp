// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{formula::PureExpr, logic::TypeInvariantDef};
use trust_wp_driver::StdSpec;

use super::get_arg_names_from_def_id;
use crate::contracts::{FunctionContract, TraitMethodContract};

/// Build the callee-keyed spec table.
///
/// The synthesized type-invariant preconditions are computed HERE, once per
/// callee, and stored beside the source clauses. Both consumers read this one
/// vector: the callee's own body takes it as a premise
/// (`clause_enrichment`), and every call site owes it as an obligation
/// (`apply_invariant_preconditions_with_effects`). Computing it a second time
/// somewhere else is how the grant and the obligation drift apart, which is
/// the free grant this table closes.
pub(in crate::callbacks) fn build_user_spec_table(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    type_invariant_defs: &[TypeInvariantDef],
) -> HashMap<DefId, StdSpec> {
    let mut specs = HashMap::new();
    for contract in contracts {
        let inv_requires = param_invariant_grant(tcx, contract.def_id, type_invariant_defs);
        // A CLOSURE's captures are the same relation one step over: its body is
        // verified holding `inv(capture)`, and the site that builds the closure
        // is the hand-over that owes it. Decided once here, like the parameter
        // vector beside it, so the premise and the construction-site obligation
        // cannot name different captures.
        let capture_inv_requires = crate::callbacks::type_invariants::build_capture_invariants(
            &crate::callbacks::closure_enrichment::closure_capture_fields(tcx, contract.def_id),
            type_invariant_defs,
        );
        let ensures = ensures_granted_at_call(tcx, contract.def_id, &contract.ensures);
        // A contractless callee still OWES its parameters' type invariants.
        // Skipping it here would leave it holding the premise in its own body
        // while no caller ever pays for it. A type parameter's invariant alone
        // does not earn an entry: an entry turns every call from the
        // fail-closed opaque lane into a spec call, and a clause that grants
        // nothing concrete is no reason to change how a call is modelled.
        // Skipped, the body holds no premise either — both sides read here.
        if contract.requires.is_empty()
            && ensures.is_empty()
            && only_type_param_invariants(&inv_requires)
            && capture_inv_requires.is_empty()
        {
            continue;
        }
        specs.insert(
            contract.def_id,
            StdSpec {
                inv_requires,
                capture_inv_requires,
                requires: contract.requires.clone(),
                ensures,
                param_names: None,
            },
        );
    }
    specs
}

/// The parameter type invariants `def_id` is granted: the vector both spec
/// tables store, which its body holds as premises and every call into it owes.
///
/// ONE function for the tables and for the discovery that decides which
/// callers are examined at all (`discovery::call_may_enter_invariant_grant`):
/// a caller the discovery reads as owing nothing is a caller no lane charges.
pub(in crate::callbacks) fn param_invariant_grant(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    type_invariant_defs: &[TypeInvariantDef],
) -> Vec<PureExpr> {
    let arg_names = get_arg_names_from_def_id(tcx, def_id).unwrap_or_default();
    let (inv_requires, _) = crate::callbacks::type_invariants::build_type_invariant_clauses(
        tcx,
        def_id,
        &arg_names,
        type_invariant_defs,
    );
    obligation_bearing_invariant_clauses(inv_requires, type_invariant_defs)
}

/// Whether every clause states a type parameter's invariant (vacuously, none).
pub(in crate::callbacks) fn only_type_param_invariants(clauses: &[PureExpr]) -> bool {
    clauses
        .iter()
        .all(crate::callbacks::mentions_type_param_invariant)
}

/// The postconditions a call to `callee` is handed.
///
/// A call to an item that only builds a coroutine (an `async fn`, an async
/// trait method, an async closure) runs none of the body its contract is
/// written about: it returns the future, and the body runs when the future is
/// polled, if ever. Its `ensures` describes that body's completion, so the
/// call is granted none of it, whether the item is refused (D-117) or
/// `#[trusted]`: a `&mut` argument's final value is whatever the future does
/// to it, and a future dropped unpolled does nothing
/// (async_fn_mut_param_ensures_granted_at_unpolled_call.rs). The `requires` is
/// still owed at the call; that only costs completeness.
fn ensures_granted_at_call(tcx: TyCtxt<'_>, callee: DefId, ensures: &[String]) -> Vec<String> {
    if crate::callbacks::verification::skip_decision::is_coroutine_body(tcx, callee) {
        Vec::new()
    } else {
        ensures.to_vec()
    }
}

/// Drop clauses whose invariant body is literally `true`.
///
/// `build_container_invariant_defs` synthesizes `TypeInvariantDef`s with a
/// `true` body for Vec/VecDeque; the real content of such a def is its
/// ELEMENT invariant bridge, so a def that carries one is kept. Filtering on
/// the body rather than on syntheticity is what keeps the element bridge.
///
/// The same filter runs on the premise side, because a premise and an
/// obligation that disagree about which clauses exist is the defect this
/// module exists to prevent.
fn obligation_bearing_invariant_clauses(
    clauses: Vec<PureExpr>,
    type_invariant_defs: &[TypeInvariantDef],
) -> Vec<PureExpr> {
    let vacuous: std::collections::HashSet<String> = type_invariant_defs
        .iter()
        .filter(|d| {
            matches!(d.body(), PureExpr::Bool(true)) && d.element_invariant_method().is_none()
        })
        .map(|d| trust_wp_core::logic::type_invariant_method_name(d.type_name()))
        .collect();
    if vacuous.is_empty() {
        return clauses;
    }
    clauses
        .into_iter()
        .filter(|c| !matches!(c, PureExpr::MethodCall { method, .. } if vacuous.contains(method)))
        .collect()
}

/// Build the trait-method-keyed spec table, the one a generic call site reads.
///
/// The synthesized type-invariant preconditions are computed here from the
/// trait DECLARATION's signature, by the same builder and under the same
/// vacuous-clause filter as the user table, because the declaration is all a
/// generic caller can see. Blanking them let `t.m(broken)` behind a `T: Trait`
/// bound pay nothing while the impl body still enjoyed `inv(param)`.
///
/// The names the clauses are built over are stored as `param_names` rather
/// than left to the call site's own resolver: the obligation substitutes a
/// clause by parameter name, so the builder and the substituter must read one
/// list, not two lists that happen to agree.
pub(in crate::callbacks) fn build_trait_spec_table(
    tcx: TyCtxt<'_>,
    trait_contracts: &[TraitMethodContract],
    type_invariant_defs: &[TypeInvariantDef],
) -> HashMap<DefId, StdSpec> {
    let mut specs = HashMap::new();
    for contract in trait_contracts {
        let arg_names = get_arg_names_from_def_id(tcx, contract.method_def_id).unwrap_or_default();
        let inv_requires = param_invariant_grant(tcx, contract.method_def_id, type_invariant_defs);
        let ensures = ensures_granted_at_call(tcx, contract.method_def_id, &contract.ensures);
        // A trait method that writes no clause of its own still OWES its
        // parameters' type invariants, exactly as a contractless free function
        // does in the user table.
        if contract.requires.is_empty()
            && ensures.is_empty()
            && only_type_param_invariants(&inv_requires)
        {
            continue;
        }
        specs.insert(
            contract.method_def_id,
            StdSpec {
                inv_requires,
                // A trait method declaration is never a closure.
                capture_inv_requires: Vec::new(),
                requires: contract.requires.clone(),
                ensures,
                param_names: (!arg_names.is_empty()).then_some(arg_names),
            },
        );
    }
    specs
}

/// Prefix of the positional names both sides of a refinement check are
/// renamed to. It lies in the reserved `__trust_wp_` namespace, which the
/// refinement check refuses in user clauses and parameter names.
pub(in crate::callbacks) const REFINEMENT_PARAM_PREFIX: &str = "__trust_wp_p";

/// Positional renaming for a trait refinement check.
#[derive(Debug, Clone, PartialEq)]
pub(in crate::callbacks) struct PositionalParamRenaming {
    /// The name parameter `i` has on both sides after renaming.
    pub(in crate::callbacks) names: Vec<String>,
    /// Trait parameter name -> positional name (only names that change).
    pub(in crate::callbacks) trait_subs: HashMap<String, PureExpr>,
    /// Impl parameter name -> positional name (only names that change).
    pub(in crate::callbacks) impl_subs: HashMap<String, PureExpr>,
}

/// Rename the parameters of both sides of a trait refinement check to the
/// same positional names, so parameter `i` of the trait and parameter `i` of
/// the impl become one variable and no other parameter does.
///
/// Both sides are renamed (renaming only the impl side onto the trait's names
/// is not injective when a trait name also occurs at another impl position,
/// or when two trait positions share a name). The positional names are
/// `__trust_wp_p{i}`, except that a receiver named `self` on both sides stays
/// `self` (a keyword, never the name of another parameter). Refused (`Err`,
/// no renaming) when the arities differ, when either side's names are not
/// pairwise distinct, when a parameter is named `result` (which a
/// postcondition uses for the return value) or lies in the reserved
/// `__trust_wp_p` namespace.
pub(in crate::callbacks) fn build_positional_param_renaming(
    trait_names: &[String],
    impl_names: &[String],
) -> Result<PositionalParamRenaming, String> {
    if trait_names.len() != impl_names.len() {
        return Err(format!(
            "the trait method has {} parameters and the impl method {}",
            trait_names.len(),
            impl_names.len()
        ));
    }
    for (side, names) in [("trait", trait_names), ("impl", impl_names)] {
        let mut seen = std::collections::HashSet::new();
        for name in names {
            if name == "result" {
                return Err(format!(
                    "{side} parameter `result` conflicts with the reserved `result` identifier"
                ));
            }
            if name.starts_with(REFINEMENT_PARAM_PREFIX) {
                return Err(format!(
                    "{side} parameter `{name}` uses the reserved `{REFINEMENT_PARAM_PREFIX}` prefix"
                ));
            }
            if !seen.insert(name.as_str()) {
                return Err(format!(
                    "{side} parameter name `{name}` does not name exactly one parameter"
                ));
            }
        }
    }
    let names: Vec<String> = trait_names
        .iter()
        .zip(impl_names)
        .enumerate()
        .map(|(idx, (trait_name, impl_name))| {
            if trait_name == "self" && impl_name == "self" {
                "self".to_string()
            } else {
                format!("{REFINEMENT_PARAM_PREFIX}{idx}")
            }
        })
        .collect();
    let subs = |side: &[String]| -> HashMap<String, PureExpr> {
        side.iter()
            .zip(&names)
            .filter(|(from, to)| from != to)
            .map(|(from, to)| (from.clone(), PureExpr::Var(to.clone(), None)))
            .collect()
    };
    let trait_subs = subs(trait_names);
    let impl_subs = subs(impl_names);
    Ok(PositionalParamRenaming {
        names,
        trait_subs,
        impl_subs,
    })
}
