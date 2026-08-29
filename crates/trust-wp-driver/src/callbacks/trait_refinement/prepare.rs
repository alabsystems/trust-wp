// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{TyCtxt, TyKind};
use tracing::debug;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::TraitRefinementRequest;
use crate::{
    callbacks::{
        contract_rewrite::rewrite_ref_deep_model_calls_expr,
        integer_range::build_unsigned_range_preconditions,
        logic_fn_scope::{
            build_scoped_self_logic_fn_path_map, inline_scoped_self_logic_fn_calls,
            normalize_logic_fn_names,
        },
        parsing::{
            build_param_normalization, get_arg_names_from_def_id, parse_contract_clauses,
            ClauseParseError,
        },
        type_invariants::{
            build_type_invariant_clauses, build_type_invariant_method_map,
            build_type_invariant_structural_expr_map,
            rewrite_type_invariant_methods_expr_with_structural,
        },
    },
    mir_analysis::translate::ty_to_expr_sort_enriched,
};

/// Error from preparing refinement clauses for trait refinement checking.
#[derive(Debug, Clone, thiserror::Error)]
pub(super) enum RefinementPrepareError {
    #[error(transparent)]
    ClauseParse(#[from] ClauseParseError),
}

pub(super) struct PreparedRefinementClauses {
    pub(super) trait_method_path: String,
    pub(super) trait_requires: Vec<PureExpr>,
    pub(super) trait_ensures: Vec<PureExpr>,
    pub(super) impl_requires: Vec<PureExpr>,
    pub(super) impl_ensures: Vec<PureExpr>,
    pub(super) result_expr: Option<PureExpr>,
}

fn build_signature_sort_map(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
) -> HashMap<String, ExprSort> {
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return HashMap::new();
    }

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();
    let mut sort_map = HashMap::new();

    for (i, ty) in inputs.iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        if let Some(sort) = ty_to_expr_sort_enriched(tcx, *ty) {
            sort_map.insert(arg_names[i].clone(), sort);
        }
    }

    if let Some(sort) = ty_to_expr_sort_enriched(tcx, sig.output()) {
        sort_map.insert("result".to_string(), sort);
    }

    sort_map
}

fn annotate_refinement_var_sorts(
    expr: &PureExpr,
    sort_map: &HashMap<String, ExprSort>,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, None) => match sort_map.get(name.as_str()) {
            Some(sort) => PureExpr::Var(name, Some(sort.clone())),
            None => PureExpr::Var(name, None),
        },
        PureExpr::Var(name, Some(ExprSort::TypeParam(id))) => match sort_map.get(name.as_str()) {
            Some(sort) => PureExpr::Var(name, Some(sort.clone())),
            None => PureExpr::Var(name, Some(ExprSort::TypeParam(id))),
        },
        other => other,
    })
}

fn annotate_refinement_clause_sorts(
    exprs: Vec<PureExpr>,
    sort_map: &HashMap<String, ExprSort>,
) -> Vec<PureExpr> {
    if sort_map.is_empty() {
        exprs
    } else {
        exprs
            .into_iter()
            .map(|expr| annotate_refinement_var_sorts(&expr, sort_map))
            .collect()
    }
}

fn sort_contains_type_param(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::TypeParam(_) => true,
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => sort_contains_type_param(inner),
        _ => false,
    }
}

fn normalized_impl_sort_map(
    impl_sort_map: &HashMap<String, ExprSort>,
    param_subs: &HashMap<String, PureExpr>,
) -> HashMap<String, ExprSort> {
    impl_sort_map
        .iter()
        .map(|(name, sort)| {
            let normalized_name = match param_subs.get(name) {
                Some(PureExpr::Var(trait_name, _)) => trait_name.clone(),
                _ => name.clone(),
            };
            (normalized_name, sort.clone())
        })
        .collect()
}

fn concrete_trait_sort_map(
    trait_sort_map: &HashMap<String, ExprSort>,
    normalized_impl_sort_map: &HashMap<String, ExprSort>,
) -> HashMap<String, ExprSort> {
    trait_sort_map
        .iter()
        .map(|(name, trait_sort)| {
            let sort = if sort_contains_type_param(trait_sort) {
                normalized_impl_sort_map
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| trait_sort.clone())
            } else {
                trait_sort.clone()
            };
            (name.clone(), sort)
        })
        .collect()
}

/// Identify trait method parameter names whose declared type is a generic
/// type parameter (e.g., `Self`, `Self::Item`, `&mut Self`, or any associated
/// type) — i.e., the type is not a concrete ADT in the trait signature.
///
/// This guards the #B2 invariant-mirror so that we only mirror impl-side
/// invariant clauses for parameters where the trait side can't generate
/// them itself (because the trait type is generic, not a concrete ADT).
fn trait_self_typed_params(
    tcx: TyCtxt<'_>,
    trait_method_def_id: DefId,
    trait_names: &[String],
) -> HashSet<String> {
    let mut result = HashSet::new();
    if tcx.def_kind(trait_method_def_id) == rustc_hir::def::DefKind::Closure {
        return result;
    }
    let sig = tcx.fn_sig(trait_method_def_id).instantiate_identity();
    let sig = sig.skip_binder();
    for (i, ty) in sig.inputs().iter().enumerate() {
        if i >= trait_names.len() {
            break;
        }
        let peeled = match ty.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            _ => *ty,
        };
        // Generic type params (Self, T) and projections (Self::Item) cannot
        // get a direct invariant method mapping on the trait side because
        // `build_type_invariant_method_map` requires `TyKind::Adt`.
        if matches!(peeled.kind(), TyKind::Param(_) | TyKind::Alias(..)) {
            result.insert(trait_names[i].clone());
        }
    }
    result
}

/// Keep only those impl-side invariant clauses whose top-level receiver
/// refers to a trait parameter that the trait sees as a generic type
/// (i.e., a name in `self_param_names`).
///
/// The impl-side `build_type_invariant_clauses` produces `MethodCall`
/// clauses of the form `<arg>.invariant()` or `(^<arg>).invariant()`.
/// We mirror only those rooted at a `self`-typed trait parameter, since
/// other parameters already have matching clauses on the trait side.
fn mirror_invariant_clauses_for_self_params(
    clauses: &[PureExpr],
    self_param_names: &HashSet<String>,
) -> Vec<PureExpr> {
    clauses
        .iter()
        .filter(|expr| {
            if let Some(name) = invariant_clause_root_param_name(expr) {
                self_param_names.contains(name)
            } else {
                false
            }
        })
        .cloned()
        .collect()
}

/// Extract the underlying parameter name from an invariant-call expression
/// shape produced by `build_type_invariant_clauses`. Returns `None` for
/// expressions that don't match the expected shape (e.g., tuple-field
/// invariants, enum-variant invariants).
fn invariant_clause_root_param_name(expr: &PureExpr) -> Option<&String> {
    // Expected shapes:
    //   <self>.invariant()
    //   (*<self>).invariant()       (for &T / &mut T receivers)
    //   (^<self>).invariant()       (for &mut T postconditions)
    let PureExpr::MethodCall { receiver, .. } = expr else {
        return None;
    };
    let mut cur = receiver.as_ref();
    loop {
        match cur {
            PureExpr::Var(name, _) => return Some(name),
            PureExpr::Deref(inner) | PureExpr::Final(inner) => {
                cur = inner.as_ref();
            }
            _ => return None,
        }
    }
}

fn normalize_refinement_clause(
    expr: PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    impl_def_path: &str,
) -> PureExpr {
    let expr = rewrite_ref_deep_model_calls_expr(&expr);
    let Some(logic_fns) = logic_fns else {
        return expr;
    };
    let self_logic_fn_path_map = build_scoped_self_logic_fn_path_map(logic_fns, impl_def_path);
    let expr = inline_scoped_self_logic_fn_calls(expr, logic_fns, impl_def_path);
    normalize_logic_fn_names(expr, &self_logic_fn_path_map)
}

fn normalize_refinement_clauses(
    exprs: Vec<PureExpr>,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    impl_def_path: &str,
) -> Vec<PureExpr> {
    exprs
        .into_iter()
        .map(|expr| normalize_refinement_clause(expr, logic_fns, impl_def_path))
        .collect()
}

pub(super) fn prepare_refinement_clauses(
    tcx: TyCtxt<'_>,
    req: &TraitRefinementRequest<'_>,
) -> Result<PreparedRefinementClauses, RefinementPrepareError> {
    let trait_method_path = format!(
        "{}::{}",
        req.trait_contract.trait_path, req.trait_contract.method_name
    );
    let mut trait_requires = parse_contract_clauses(
        &req.trait_contract.requires,
        "trait requires",
        &trait_method_path,
    )?;
    let mut trait_ensures = parse_contract_clauses(
        &req.trait_contract.ensures,
        "trait ensures",
        &trait_method_path,
    )?;

    // Resolve trait parameter names for normalization and range constraint parity (#479, #2363).
    let trait_names_opt = get_arg_names_from_def_id(tcx, req.trait_contract.method_def_id);
    let trait_sort_map = trait_names_opt
        .as_ref()
        .map_or_else(HashMap::new, |trait_names| {
            build_signature_sort_map(tcx, req.trait_contract.method_def_id, trait_names)
        });
    let impl_sort_map = build_signature_sort_map(tcx, req.impl_def_id, req.impl_arg_names);

    // Normalize impl parameter names to match trait parameter names (#479).
    let param_subs = if let Some(ref trait_names) = trait_names_opt {
        let trait_arg_count = trait_names.len();
        if let Some(subs) = build_param_normalization(trait_names, req.impl_arg_names) {
            subs
        } else {
            if req.verbose {
                debug!(
                    "trust-wp:   (skipping refinement param normalization due to arity mismatch: trait={}, impl={})",
                    trait_arg_count,
                    req.impl_arg_names.len()
                );
            }
            HashMap::new()
        }
    } else {
        if req.verbose {
            debug!(
                "trust-wp:   (trait parameter names unavailable; skipping refinement param normalization)"
            );
        }
        HashMap::new()
    };

    if !req.type_invariant_defs.is_empty() {
        if let Some(ref trait_names) = trait_names_opt {
            let (trait_param_methods, trait_result_method) = build_type_invariant_method_map(
                tcx,
                req.trait_contract.method_def_id,
                trait_names,
                req.type_invariant_defs,
            );
            let (trait_param_structural_exprs, trait_result_structural_expr) =
                build_type_invariant_structural_expr_map(
                    tcx,
                    req.trait_contract.method_def_id,
                    trait_names,
                    req.type_invariant_defs,
                );
            trait_requires = trait_requires
                .iter()
                .map(|expr| {
                    rewrite_type_invariant_methods_expr_with_structural(
                        expr,
                        &trait_param_methods,
                        trait_result_method.as_deref(),
                        &trait_param_structural_exprs,
                        trait_result_structural_expr.as_ref(),
                    )
                })
                .collect();
            trait_ensures = trait_ensures
                .iter()
                .map(|expr| {
                    rewrite_type_invariant_methods_expr_with_structural(
                        expr,
                        &trait_param_methods,
                        trait_result_method.as_deref(),
                        &trait_param_structural_exprs,
                        trait_result_structural_expr.as_ref(),
                    )
                })
                .collect();
        }
    }

    let impl_base_requires: Vec<PureExpr> = if req.type_invariant_defs.is_empty() {
        req.base_requires.to_vec()
    } else {
        let (impl_param_methods, impl_result_method) = build_type_invariant_method_map(
            tcx,
            req.impl_def_id,
            req.impl_arg_names,
            req.type_invariant_defs,
        );
        let (impl_param_structural_exprs, impl_result_structural_expr) =
            build_type_invariant_structural_expr_map(
                tcx,
                req.impl_def_id,
                req.impl_arg_names,
                req.type_invariant_defs,
            );
        req.base_requires
            .iter()
            .map(|expr| {
                rewrite_type_invariant_methods_expr_with_structural(
                    expr,
                    &impl_param_methods,
                    impl_result_method.as_deref(),
                    &impl_param_structural_exprs,
                    impl_result_structural_expr.as_ref(),
                )
            })
            .collect()
    };
    let impl_base_ensures: Vec<PureExpr> = if req.type_invariant_defs.is_empty() {
        req.base_ensures.to_vec()
    } else {
        let (impl_param_methods, impl_result_method) = build_type_invariant_method_map(
            tcx,
            req.impl_def_id,
            req.impl_arg_names,
            req.type_invariant_defs,
        );
        let (impl_param_structural_exprs, impl_result_structural_expr) =
            build_type_invariant_structural_expr_map(
                tcx,
                req.impl_def_id,
                req.impl_arg_names,
                req.type_invariant_defs,
            );
        req.base_ensures
            .iter()
            .map(|expr| {
                rewrite_type_invariant_methods_expr_with_structural(
                    expr,
                    &impl_param_methods,
                    impl_result_method.as_deref(),
                    &impl_param_structural_exprs,
                    impl_result_structural_expr.as_ref(),
                )
            })
            .collect()
    };

    // Add integer-range preconditions to the trait side for clause-view parity (#2363).
    //
    // The impl's `base_requires` includes View-wrapped integer-range constraints
    // (e.g., `View(n) >= -2^31`, `View(n) <= 2^31-1`) injected by the driver
    // before contract transformation. Without matching constraints on the trait
    // side, precondition refinement falsely fails because the solver cannot prove
    // `trait_requires => int_range_constraints` from user-written clauses alone.
    if let Some(ref trait_names) = trait_names_opt {
        let trait_int_ranges =
            build_unsigned_range_preconditions(tcx, req.trait_contract.method_def_id, trait_names);
        if !trait_int_ranges.is_empty() {
            if req.verbose {
                debug!(
                    "trust-wp:   (adding {} trait-side integer range precondition(s) for refinement parity)",
                    trait_int_ranges.len()
                );
            }
            trait_requires.extend(trait_int_ranges);
        }
    }
    let impl_int_ranges =
        build_unsigned_range_preconditions(tcx, req.impl_def_id, req.impl_arg_names);
    if !impl_int_ranges.is_empty() {
        if req.verbose {
            debug!(
                "trust-wp:   (adding {} impl-signature integer range precondition(s) to trait side for refinement parity)",
                impl_int_ranges.len()
            );
        }
        if param_subs.is_empty() {
            trait_requires.extend(impl_int_ranges);
        } else {
            trait_requires.extend(
                impl_int_ranges
                    .iter()
                    .map(|expr| expr.substitute(&param_subs)),
            );
        }
    }

    // Build impl-side base clauses with parameter normalization (#479).
    let mut impl_requires = if param_subs.is_empty() {
        impl_base_requires
    } else {
        if req.verbose {
            debug!(
                "trust-wp:   (normalizing {} impl param(s) for refinement check)",
                param_subs.len()
            );
        }
        impl_base_requires
            .iter()
            .map(|expr| expr.substitute(&param_subs))
            .collect()
    };

    let mut impl_ensures = if param_subs.is_empty() {
        impl_base_ensures
    } else {
        impl_base_ensures
            .iter()
            .map(|expr| expr.substitute(&param_subs))
            .collect()
    };

    // Add type-invariant clauses for refinement parity (#1579).
    //
    // Normal body verification enriches contracts with type-invariant clauses
    // before solving. Without matching enrichment on the refinement path,
    // refinement rejects impl contracts that are valid under trust-wp's own
    // verification model whenever the proof relies on argument or result type
    // invariants.
    if !req.type_invariant_defs.is_empty() {
        // Trait side: use the trait method's signature and trait parameter names.
        if let Some(ref trait_names) = trait_names_opt {
            let (trait_inv_req, trait_inv_ens) = build_type_invariant_clauses(
                tcx,
                req.trait_contract.method_def_id,
                trait_names,
                req.type_invariant_defs,
            );
            if !trait_inv_req.is_empty() || !trait_inv_ens.is_empty() {
                if req.verbose {
                    debug!(
                        "trust-wp:   (adding {} trait-side type invariant clause(s) for refinement parity)",
                        trait_inv_req.len() + trait_inv_ens.len()
                    );
                }
                trait_requires.extend(trait_inv_req);
                trait_ensures.extend(trait_inv_ens);
            }
        }

        // Impl side: use the impl method's signature and impl argument names.
        // Invariant clauses are synthesized from the impl's own def_id, then
        // normalized with param_subs to align parameter names with the trait
        // side (preserving existing RenamedParamImpl behavior from #479).
        let (impl_inv_req, impl_inv_ens) = build_type_invariant_clauses(
            tcx,
            req.impl_def_id,
            req.impl_arg_names,
            req.type_invariant_defs,
        );
        if !impl_inv_req.is_empty() || !impl_inv_ens.is_empty() {
            if req.verbose {
                debug!(
                    "trust-wp:   (adding {} impl-side type invariant clause(s) for refinement parity)",
                    impl_inv_req.len() + impl_inv_ens.len()
                );
            }
            let normalized_impl_inv_req: Vec<PureExpr> = if param_subs.is_empty() {
                impl_inv_req.clone()
            } else {
                impl_inv_req
                    .iter()
                    .map(|expr| expr.substitute(&param_subs))
                    .collect()
            };
            let normalized_impl_inv_ens: Vec<PureExpr> = if param_subs.is_empty() {
                impl_inv_ens.clone()
            } else {
                impl_inv_ens
                    .iter()
                    .map(|expr| expr.substitute(&param_subs))
                    .collect()
            };
            impl_requires.extend(normalized_impl_inv_req.iter().cloned());
            impl_ensures.extend(normalized_impl_inv_ens.iter().cloned());

            // #B2: Mirror impl-side invariant clauses onto the trait side when
            // the corresponding trait parameter is a generic type parameter
            // (e.g., `Self`, `Self::Item`).
            //
            // The trait-side `build_type_invariant_clauses` call above cannot
            // emit invariant clauses for `Self`-typed parameters because
            // `Self` is a generic param, not a concrete ADT. The impl's
            // invariant is part of the type's contract, so it must be
            // assumed everywhere the type appears — including on the trait
            // side of the refinement check. Without this mirror, the
            // refinement `trait_requires => impl_requires` reduces to
            // `true => Inv(self)`, which trivially fails (sat).
            //
            // We skip mirroring if the trait method's corresponding parameter
            // is itself a concrete ADT with an invariant (those clauses are
            // already generated by the trait-side call above).
            if let Some(ref trait_names) = trait_names_opt {
                let trait_self_param_set =
                    trait_self_typed_params(tcx, req.trait_contract.method_def_id, trait_names);
                if !trait_self_param_set.is_empty() {
                    let mirrored_req = mirror_invariant_clauses_for_self_params(
                        &normalized_impl_inv_req,
                        &trait_self_param_set,
                    );
                    let mirrored_ens = mirror_invariant_clauses_for_self_params(
                        &normalized_impl_inv_ens,
                        &trait_self_param_set,
                    );
                    if !mirrored_req.is_empty() || !mirrored_ens.is_empty() {
                        if req.verbose {
                            debug!(
                                "trust-wp:   (mirroring {} impl-side type invariant clause(s) onto trait side for Self-typed params)",
                                mirrored_req.len() + mirrored_ens.len()
                            );
                        }
                        trait_requires.extend(mirrored_req);
                        trait_ensures.extend(mirrored_ens);
                    }
                }
            }
        }
    }

    let impl_clause_sort_map = if trait_sort_map.is_empty() {
        &impl_sort_map
    } else {
        &trait_sort_map
    };
    let normalized_impl_sort_map = normalized_impl_sort_map(&impl_sort_map, &param_subs);
    let trait_clause_sort_map = concrete_trait_sort_map(&trait_sort_map, &normalized_impl_sort_map);
    let result_expr = impl_clause_sort_map
        .get("result")
        .cloned()
        .map(|sort| PureExpr::Var("result".to_string(), Some(sort)));
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    let impl_def_path = format!("{local_crate_name}::{}", tcx.def_path_str(req.impl_def_id));

    let trait_requires = normalize_refinement_clauses(
        annotate_refinement_clause_sorts(trait_requires, &trait_clause_sort_map),
        req.logic_fns_opt,
        &impl_def_path,
    );
    let trait_ensures = normalize_refinement_clauses(
        annotate_refinement_clause_sorts(trait_ensures, &trait_clause_sort_map),
        req.logic_fns_opt,
        &impl_def_path,
    );
    let impl_requires = normalize_refinement_clauses(
        annotate_refinement_clause_sorts(impl_requires, impl_clause_sort_map),
        req.logic_fns_opt,
        &impl_def_path,
    );
    let impl_ensures = normalize_refinement_clauses(
        annotate_refinement_clause_sorts(impl_ensures, impl_clause_sort_map),
        req.logic_fns_opt,
        &impl_def_path,
    );

    Ok(PreparedRefinementClauses {
        trait_method_path,
        trait_requires,
        trait_ensures,
        impl_requires,
        impl_ensures,
        result_expr,
    })
}
