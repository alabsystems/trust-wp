// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared verification preparation state and helpers extracted from `verification.rs`.

mod logic_body_callees;
mod logic_fn_catalog;
mod logic_impl_discharge;
mod program_callees;

use std::collections::{HashMap, HashSet};

use logic_fn_catalog::{
    build_trait_logic_fn_groups, rewrite_logic_fn_method_calls,
    substitute_const_items_into_logic_fns,
};
pub(in crate::callbacks) use logic_fn_catalog::{
    downgrade_unverified_logic_specs, filter_downstream_logic_fns, neutralized,
    neutralized_axiom_reached,
};
use program_callees::program_fns_with_requires;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    formula::PureExpr,
    logic::{LogicFnDef, TypeInvariantDef},
};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        super::contracts::{FunctionContract, TraitMethodContract},
        adt_analysis::{build_adt_decls, build_adt_field_ranges},
        contract_rewrite::{
            build_user_shadowed_builtins, simplify_newtype_field_access_expr, UserShadowedBuiltins,
        },
        ghost_context::collect_trusted_proof_assert_assumptions,
        logic_fn_scope::insert_logic_fn_path_aliases,
        parsing::build_user_spec_table,
        reporting::VerificationCounters,
        verification_context::VerificationRunConfig,
    },
    logic_fn_verify::{verify_logic_fn_postconditions, VerifyConfig},
};

/// Shared state computed once during verification preparation (#1526 Phase 5).
pub(in crate::callbacks) struct PreparedVerification<'a> {
    pub(super) user_specs: HashMap<DefId, StdSpec>,
    pub(super) trusted_proof_assert_assumptions:
        HashMap<rustc_hir::def_id::LocalDefId, Vec<PureExpr>>,
    pub(super) trait_contract_map: HashMap<DefId, HashMap<String, &'a TraitMethodContract>>,
    pub(super) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    pub(super) simplified_logic_fns: Vec<LogicFnDef>,
    pub(super) has_simplified: bool,
    /// Downstream-safe logic function slice with unverified axioms neutralized (#1878).
    ///
    /// After logic-function postcondition verification, any function whose
    /// postcondition returned `Unknown` is neutralized in place (forced opaque
    /// with its `ensures` cleared) so downstream solver queries never receive
    /// unverified axioms while the function's declaration — and thus its return
    /// sort — stays available. The full slice (via `logic_fns()`) is preserved
    /// for path/skip metadata. See `filter_downstream_logic_fns`.
    pub(super) downstream_logic_fns: Vec<LogicFnDef>,
    pub(super) has_downstream_filter: bool,
    pub(super) logic_fn_paths: HashSet<String>,
    pub(super) logic_fn_has_ensures: HashSet<String>,
    pub(super) logic_method_names: HashSet<String>,
    /// Builtin names shadowed by local USER #[logic] trait impls, by ADT sort.
    pub(super) user_shadowed_builtins: UserShadowedBuiltins,
    pub(super) const_item_substitutions: HashMap<String, PureExpr>,
    /// Local logic impls checked against the postcondition of the trait
    /// logic method they implement that did not establish it
    /// (`logic_impl_discharge`). The contract loop settles such an impl's
    /// trait contract from this, never by silence.
    pub(super) undischarged_logic_impls: HashSet<DefId>,
}

impl<'a> PreparedVerification<'a> {
    pub(in crate::callbacks) fn logic_fns(
        &self,
        config: &'a VerificationRunConfig<'a>,
    ) -> &[LogicFnDef] {
        if self.has_simplified {
            &self.simplified_logic_fns
        } else {
            config.logic_fns
        }
    }

    /// Returns the downstream-safe logic function slice (#1878).
    ///
    /// Excludes logic functions whose postconditions could not be verified
    /// (`Unknown` result). Use this for all solver-facing paths. Use
    /// `logic_fns()` for path/skip metadata that needs the full catalog.
    pub(in crate::callbacks) fn downstream_logic_fns(
        &self,
        config: &'a VerificationRunConfig<'a>,
    ) -> &[LogicFnDef] {
        if self.has_downstream_filter {
            &self.downstream_logic_fns
        } else {
            self.logic_fns(config)
        }
    }

    /// Build a minimal `PreparedVerification` for SMT emission (#2123).
    ///
    /// Only populates fields used by `enrich_effective_clauses`:
    /// `user_specs`, `trusted_proof_assert_assumptions`, `const_item_substitutions`.
    /// Other fields are set to empty/default values.
    pub(in crate::callbacks) fn for_smt_emission(
        user_specs: HashMap<DefId, StdSpec>,
        trusted_proof_assert_assumptions: HashMap<rustc_hir::def_id::LocalDefId, Vec<PureExpr>>,
        const_item_substitutions: HashMap<String, PureExpr>,
    ) -> PreparedVerification<'a> {
        PreparedVerification {
            user_specs,
            trusted_proof_assert_assumptions,
            trait_contract_map: HashMap::new(),
            type_invariants_opt: None,
            simplified_logic_fns: Vec::new(),
            has_simplified: false,
            downstream_logic_fns: Vec::new(),
            has_downstream_filter: false,
            logic_fn_paths: HashSet::new(),
            logic_fn_has_ensures: HashSet::new(),
            logic_method_names: HashSet::new(),
            user_shadowed_builtins: UserShadowedBuiltins::default(),
            const_item_substitutions,
            undischarged_logic_impls: HashSet::new(),
        }
    }
}

/// Prepare shared verification state (#1526 Phase 5).
pub(in crate::callbacks) fn prepare_verification<'a>(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    config: &'a VerificationRunConfig<'a>,
    counters: &mut VerificationCounters,
    unverified_axioms: &mut HashSet<String>,
) -> PreparedVerification<'a> {
    let logic_fns = config.logic_fns;
    let type_invariant_defs = config.type_invariant_defs;
    let mut user_specs = build_user_spec_table(tcx, config.all_contracts, type_invariant_defs);
    crate::logic::identity::resolve_spec_table_texts(tcx, &mut user_specs);
    // trusted_proof_assert_assumptions is built AFTER logic-function verification
    // so the downgraded user_specs is used (#1878 leak path 3).
    let mut trait_contract_map: HashMap<DefId, HashMap<String, &TraitMethodContract>> =
        HashMap::new();
    for tc in config.trait_contracts {
        trait_contract_map
            .entry(tc.trait_def_id)
            .or_default()
            .insert(tc.method_name.clone(), tc);
    }
    let type_invariants_opt = if type_invariant_defs.is_empty() {
        None
    } else {
        Some(type_invariant_defs)
    };
    let newtype_type_names: HashSet<String> = type_invariant_defs
        .iter()
        .filter(|d| d.is_newtype())
        .map(|d| d.type_name().to_string())
        .collect();
    let (mut simplified_logic_fns, mut has_simplified) = if newtype_type_names.is_empty() {
        (Vec::new(), false)
    } else {
        let simplified: Vec<_> = logic_fns
            .iter()
            .map(|lf| {
                let is_newtype_method = lf
                    .full_path()
                    .rsplit_once("::")
                    .is_some_and(|(prefix, _)| newtype_type_names.contains(prefix));
                if !is_newtype_method {
                    return lf.clone();
                }
                let newtype_params: HashSet<String> = lf
                    .params()
                    .iter()
                    .filter(|p| *p == "self")
                    .cloned()
                    .collect();
                let mut s = lf.clone();
                let new_body = simplify_newtype_field_access_expr(s.body(), &newtype_params);
                s.set_body(new_body);
                for require in s.requires_mut() {
                    *require = simplify_newtype_field_access_expr(require, &newtype_params);
                }
                for ensure in s.ensures_mut() {
                    *ensure = simplify_newtype_field_access_expr(ensure, &newtype_params);
                }
                s
            })
            .collect();
        (simplified, true)
    };
    let effective_logic_fns: &[LogicFnDef] = if has_simplified {
        &simplified_logic_fns
    } else {
        logic_fns
    };
    let trait_logic_fn_groups = build_trait_logic_fn_groups(tcx, effective_logic_fns);
    let mut logic_fn_paths = HashSet::new();
    let mut logic_fn_has_ensures = HashSet::new();
    for logic_fn in effective_logic_fns {
        insert_logic_fn_path_aliases(&mut logic_fn_paths, logic_fn.full_path());
        if !logic_fn.ensures().is_empty() {
            insert_logic_fn_path_aliases(&mut logic_fn_has_ensures, logic_fn.full_path());
        }
    }
    let logic_method_names: HashSet<String> = effective_logic_fns
        .iter()
        .filter(|lf| lf.params().first().is_some_and(|param| param == "self"))
        .map(|lf| lf.short_name().to_string())
        .collect();
    let user_shadowed_builtins = build_user_shadowed_builtins(tcx);
    if !logic_method_names.is_empty() || !user_shadowed_builtins.is_empty() {
        if !has_simplified {
            simplified_logic_fns = logic_fns.to_vec();
            has_simplified = true;
        }
        rewrite_logic_fn_method_calls(
            &mut simplified_logic_fns,
            &logic_method_names,
            &user_shadowed_builtins,
        );
    }
    // The logic pass and its consumers read one table (D-111). Its values
    // reach logic functions only after the pass (below); its refusals must
    // reach them before it, or a bare constant name the crate gives two
    // meanings is one free symbol standing for both while postconditions are
    // checked (const_short_name_logic_pass_free_symbol_granted.rs).
    let const_item_substitutions = super::super::const_items::const_item_substitutions(tcx);
    let constant_refusals = super::super::const_items::refusals_only(&const_item_substitutions);
    if !constant_refusals.is_empty() {
        if !has_simplified {
            simplified_logic_fns = logic_fns.to_vec();
            has_simplified = true;
        }
        substitute_const_items_into_logic_fns(&mut simplified_logic_fns, &constant_refusals);
    }
    let effective_logic_fns: &[LogicFnDef] = if has_simplified {
        &simplified_logic_fns
    } else {
        logic_fns
    };
    // Build crate-wide ADT field ranges so logic function verification can
    // inject range axioms for unsigned fields (e.g., `u32` field of `List::Cons`
    // constrained to `[0, 2^32)`). Without this, logic functions that operate
    // on ADTs with unsigned fields produce spurious counterexamples because
    // the solver assigns negative values. (#2178, #2097 RC1)
    let crate_adt_field_ranges = {
        let mut combined = trust_wp_core::logic::AdtFieldRanges::new();
        for contract in contracts {
            if tcx.def_kind(contract.def_id) == rustc_hir::def::DefKind::Closure {
                continue;
            }
            let per_fn = build_adt_field_ranges(tcx, contract.def_id);
            for (adt_name, ctor_ranges) in per_fn {
                combined.entry(adt_name).or_insert(ctor_ranges);
            }
        }
        if combined.is_empty() {
            None
        } else {
            Some(combined)
        }
    };
    let crate_adt_decls = {
        let mut combined = trust_wp_core::logic::AdtDecls::new();
        for contract in contracts {
            if tcx.def_kind(contract.def_id) == rustc_hir::def::DefKind::Closure {
                continue;
            }
            let per_fn = build_adt_decls(tcx, contract.def_id);
            for (adt_name, decl) in per_fn {
                combined.entry(adt_name).or_insert(decl);
            }
        }
        if combined.is_empty() {
            None
        } else {
            Some(combined)
        }
    };
    let impl_owed_postconditions =
        logic_impl_discharge::impl_owed_trait_logic_decls(tcx, effective_logic_fns);
    let (program_fns_with_requires, program_fn_def_ids) = program_fns_with_requires(
        tcx,
        config.all_contracts,
        config.trait_contracts,
        &logic_fn_paths,
    );
    let logic_body_callees =
        logic_body_callees::logic_body_callees(tcx, effective_logic_fns, &program_fn_def_ids);
    let verify_cfg = VerifyConfig {
        logic_fns: effective_logic_fns,
        type_invariants_opt,
        track_level: config.track_level,
        timeout: config.timeout,
        strict_axioms: config.strict_axioms,
        trait_logic_fn_groups: Some(&trait_logic_fn_groups),
        impl_owed_postconditions: Some(&impl_owed_postconditions),
        adt_field_ranges: crate_adt_field_ranges,
        adt_decls: crate_adt_decls,
        program_fns_with_requires: Some(&program_fns_with_requires),
        logic_body_callees: &logic_body_callees,
    };
    let mut logic_credits =
        verify_logic_fn_postconditions(&verify_cfg, counters, unverified_axioms);
    // Before any consumer reads a trait logic method's axiom: every local
    // impl owes it, or it is withdrawn, and so is every logic credit that
    // leaned on an axiom withdrawn after its proof.
    let undischarged_logic_impls =
        logic_impl_discharge::verify_logic_impls_discharge_trait_postconditions(
            tcx,
            &verify_cfg,
            counters,
            unverified_axioms,
            &mut logic_credits,
        );

    let (mut downstream_logic_fns, has_downstream_filter) = if unverified_axioms.is_empty() {
        (Vec::new(), false)
    } else {
        let filtered = filter_downstream_logic_fns(effective_logic_fns, unverified_axioms);
        // Downgrade user_specs: clear `ensures` for unverified logic function DefIds.
        // Build an expanded alias set so tcx.def_path_str() matches regardless of
        // whether it returns the full path or the crate-relative alias.
        let mut unverified_aliases: HashSet<String> = HashSet::new();
        for path in unverified_axioms.iter() {
            insert_logic_fn_path_aliases(&mut unverified_aliases, path);
        }
        let unverified_logic_spec_ids: HashSet<DefId> = contracts
            .iter()
            .filter_map(|contract| {
                let def_path = tcx.def_path_str(contract.def_id);
                unverified_aliases
                    .contains(&def_path)
                    .then_some(contract.def_id)
            })
            .collect();
        downgrade_unverified_logic_specs(&mut user_specs, |def_id| {
            unverified_logic_spec_ids.contains(def_id)
        });
        (filtered, true)
    };

    // Build trusted proof_assert assumptions AFTER the user_specs downgrade so
    // unverified logic function postconditions are not injected into
    // effective_requires via clause_enrichment (#1878 leak path 3).
    let trusted_proof_assert_logic_fns = if has_downstream_filter {
        downstream_logic_fns.as_slice()
    } else {
        effective_logic_fns
    };
    let (trusted_proof_assert_assumptions, trusted_pa_warnings) =
        collect_trusted_proof_assert_assumptions(
            tcx,
            contracts,
            &user_specs,
            trusted_proof_assert_logic_fns,
        );
    counters.warnings = counters.warnings.saturating_add(trusted_pa_warnings);
    let trusted_pa_assumption_count = trusted_proof_assert_assumptions
        .values()
        .map(Vec::len)
        .sum::<usize>();
    if trusted_pa_assumption_count > 0 {
        counters.assumed = counters.assumed.saturating_add(trusted_pa_assumption_count);
        eprintln!(
            "trust-wp: {trusted_pa_assumption_count} proof_assert assumption(s) injected without proof"
        );
    }

    // Const-item values must be visible THROUGH logic-fn defining axioms too
    // (ledger int-shift-full, bits.rs `empty`): specs get the substitution
    // per contract in `apply_const_item_substitutions`, but a logic-fn body
    // like `USIZE_BITS as u32 - val.leading_zeros_logic()` previously kept
    // the bare name, leaving `USIZE_BITS` an UNCONSTRAINED solver variable
    // inside `ffs_logic`'s axiom. Value-dependent side obligations — the
    // machine-int shift-amount range needs `ffs_logic(val) <= 64`, which is
    // only derivable with `USIZE_BITS == 64` pinned — were then refutable at
    // arbitrary const values. Substitute the evaluated constants into the
    // logic-fn bodies/contracts exactly like the specs that call them.
    if !const_item_substitutions.is_empty() {
        let any_reference = |fns: &[LogicFnDef]| {
            fns.iter().any(|lf| {
                let references = |expr: &PureExpr| {
                    expr.any_free_var(|name, _sort| {
                        const_item_substitutions.contains_key(name)
                            && !lf.params().iter().any(|param| param == name)
                    })
                };
                references(lf.body())
                    || lf.requires().iter().any(|e| references(e))
                    || lf.ensures().iter().any(|e| references(e))
            })
        };
        if !has_simplified && any_reference(logic_fns) {
            simplified_logic_fns = logic_fns.to_vec();
            has_simplified = true;
        }
        if has_simplified {
            substitute_const_items_into_logic_fns(
                &mut simplified_logic_fns,
                &const_item_substitutions,
            );
        }
        if has_downstream_filter {
            substitute_const_items_into_logic_fns(
                &mut downstream_logic_fns,
                &const_item_substitutions,
            );
        }
    }
    PreparedVerification {
        user_specs,
        trusted_proof_assert_assumptions,
        trait_contract_map,
        type_invariants_opt,
        simplified_logic_fns,
        has_simplified,
        downstream_logic_fns,
        has_downstream_filter,
        logic_fn_paths,
        logic_fn_has_ensures,
        logic_method_names,
        user_shadowed_builtins,
        const_item_substitutions,
        undischarged_logic_impls,
    }
}
