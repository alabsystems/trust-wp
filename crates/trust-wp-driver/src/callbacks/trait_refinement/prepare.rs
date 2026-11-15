// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::{
    def::{DefKind, Namespace, Res},
    def_id::DefId,
    ItemKind, UseKind,
};
use rustc_middle::ty::{TyCtxt, TyKind};
use tracing::debug;
use trust_wp_core::{
    contract_parser::parse_contract_written_types,
    formula::{CaptureAvoidingSubstOptions, ExprSort, PureExpr},
};

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
            build_positional_param_renaming, get_arg_names_from_def_id, parse_contract_clauses,
            ClauseParseError,
        },
        type_invariants::{
            build_type_invariant_clauses, build_type_invariant_method_map,
            build_type_invariant_structural_expr_map, mentions_type_param_invariant,
            rewrite_type_invariant_methods_expr_with_structural,
        },
    },
    logic::spec_calls::ClauseRef,
    mir_analysis::translate::ty_to_expr_sort_enriched,
};

/// Error from preparing refinement clauses for trait refinement checking.
#[derive(Debug, Clone, thiserror::Error)]
pub(super) enum RefinementPrepareError {
    #[error(transparent)]
    ClauseParse(#[from] ClauseParseError),
    /// A clause names something whose meaning depends on the scope the
    /// clause was written in (see [`super::scope`]).
    #[error(
        "{side} clause names {name}, which cannot be resolved in the clause's own scope; \
         refinement is not checked on scope-dependent names"
    )]
    ScopeDependent { side: &'static str, name: String },
    /// A registered logic function shares the parser's synthetic accessor
    /// namespace, so tuple and field accessors are ambiguous.
    #[error("logic function `{0}` uses a reserved synthetic name; refinement is not checked")]
    ReservedLogicFnName(String),
    /// The parameters of the two sides cannot be matched one-to-one by
    /// position (see [`build_positional_param_renaming`]).
    #[error("parameters cannot be matched by position: {0}; refinement is not checked")]
    ParamNaming(String),
}

/// Refuse clause sets that name anything outside the scope-independent
/// vocabulary of [`super::scope`].
fn check_clause_scope(
    side: &'static str,
    clauses: &[PureExpr],
    params: &HashSet<&str>,
    clause_kind: super::scope::ClauseKind,
) -> Result<(), RefinementPrepareError> {
    match clauses
        .iter()
        .find_map(|clause| super::scope::first_scope_dependent_name(clause, params, clause_kind))
    {
        Some(name) => Err(RefinementPrepareError::ScopeDependent { side, name }),
        None => Ok(()),
    }
}

/// Refuse clause texts that write a type the parsed AST does not record
/// faithfully (see [`super::scope::first_unrecorded_written_type`]). The
/// accepted written types (`Int`, `bool`) are collected into `used` for the
/// shadowing check.
fn check_clause_written_types(
    side: &'static str,
    texts: &[String],
    used: &mut HashSet<&'static str>,
) -> Result<(), RefinementPrepareError> {
    for text in texts {
        let written = parse_contract_written_types(text).map_err(|_| {
            RefinementPrepareError::ScopeDependent {
                side,
                name: "clause text whose written types could not be re-read".to_string(),
            }
        })?;
        if let Some(name) = super::scope::first_unrecorded_written_type(&written) {
            return Err(RefinementPrepareError::ScopeDependent { side, name });
        }
        for written in &written {
            if let Some(name) = super::scope::FAITHFUL_WRITTEN_TYPES
                .iter()
                .find(|name| written.text.as_deref() == Some(**name))
            {
                used.insert(name);
            }
        }
    }
    Ok(())
}

/// `Int` means `trust_wp_std`'s logic integer (re-exported by the Creusot
/// prelude shims); `bool` means the primitive.
fn is_canonical_written_type(tcx: TyCtxt<'_>, did: DefId, name: &str) -> bool {
    name == "Int"
        && tcx.def_kind(did) == DefKind::Struct
        && tcx.crate_name(did.krate).as_str() == "trust_wp_std"
        && tcx.item_name(did).as_str() == "Int"
}

/// The module named by the compiler-injected standard-library prelude import
/// (`#[prelude_import] use std::prelude::rust_20xx::*`), whose HIR path keeps
/// no resolution. The import is recognised by its `StdImports` expansion; its
/// crate is the one the equally injected `extern crate` item loaded, and the
/// module is found by walking that crate's module tree along the path. `None`
/// (refuse) whenever any step does not resolve to exactly one module.
pub(crate) fn std_prelude_glob_module(
    tcx: TyCtxt<'_>,
    item: &rustc_hir::Item<'_>,
) -> Option<DefId> {
    let is_std_import = |span: rustc_span::Span| {
        matches!(
            span.ctxt().outer_expn_data().kind,
            rustc_span::ExpnKind::AstPass(rustc_span::hygiene::AstPass::StdImports)
        )
    };
    if !is_std_import(item.span) {
        return None;
    }
    let ItemKind::Use(rustc_hir::UseTree {
        prefix: path,
        kind: UseKind::Glob,
    }) = item.kind
    else {
        return None;
    };
    let (first, rest) = path.segments.split_first()?;
    let crate_items = tcx.hir_crate_items(());
    let mut cnums = crate_items.free_items().filter_map(|item_id| {
        let extern_item = tcx.hir_item(item_id);
        let ItemKind::ExternCrate(_, ident) = extern_item.kind else {
            return None;
        };
        (ident.name == first.ident.name && is_std_import(extern_item.span))
            .then(|| tcx.extern_mod_stmt_cnum(extern_item.owner_id.def_id))
            .flatten()
    });
    let cnum = cnums.next()?;
    if cnums.next().is_some() {
        return None;
    }
    let mut module = cnum.as_def_id();
    for segment in rest {
        let mut found = tcx
            .module_children(module)
            .iter()
            .filter_map(|child| match child.res {
                Res::Def(DefKind::Mod, did) if child.ident.name == segment.ident.name => Some(did),
                _ => None,
            });
        module = found.next()?;
        if found.next().is_some() {
            return None;
        }
    }
    Some(module)
}

/// A local item, import or glob-imported extern item that could give one of
/// the written type names in `names` a meaning other than the canonical one
/// in some scope. Clause text is resolved without scopes, so any such item
/// anywhere in the crate refuses the check. Local glob targets need no
/// inspection: every local item is examined by name directly.
fn shadowed_written_type_name(tcx: TyCtxt<'_>, names: &HashSet<&'static str>) -> Option<String> {
    let crate_items = tcx.hir_crate_items(());
    for local_def_id in crate_items.definitions() {
        let did = local_def_id.to_def_id();
        let kind = tcx.def_kind(did);
        let in_type_namespace = kind.ns() == Some(Namespace::TypeNS)
            || matches!(kind, DefKind::TyParam | DefKind::ExternCrate);
        if !in_type_namespace {
            continue;
        }
        if let Some(item_name) = tcx.opt_item_name(did) {
            if names.contains(item_name.as_str()) {
                return Some(format!(
                    "type `{item_name}` (shadowed by local {} `{item_name}`)",
                    kind.descr(did)
                ));
            }
        }
    }
    for item_id in crate_items.free_items() {
        let item = tcx.hir_item(item_id);
        // Each leaf of the item's use tree.
        for (path, use_kind) in crate::hir_use::item_use_leaves(item) {
            match use_kind {
                UseKind::Single(ident) => {
                    let name = ident.name.as_str();
                    if !names.contains(name) {
                        continue;
                    }
                    let canonical = match path.res.type_ns {
                        // Imports nothing in the type namespace.
                        None => continue,
                        Some(Res::PrimTy(prim)) => prim.name_str() == name,
                        Some(Res::Def(_, did)) => is_canonical_written_type(tcx, did, name),
                        Some(_) => false,
                    };
                    if !canonical {
                        return Some(format!("type `{name}` (shadowed by an import)"));
                    }
                }
                UseKind::Glob => {
                    // rustc lowers a module glob into the type namespace and an
                    // enum glob into the value namespace (its variants).
                    // The injected standard-library prelude import keeps no
                    // resolution in HIR; its module is re-resolved from the crate
                    // the injected `extern crate` loaded.
                    let prelude_module = std_prelude_glob_module(tcx, item);
                    let glob_res = match (path.res.type_ns, path.res.value_ns, prelude_module) {
                        (Some(res @ Res::Def(DefKind::Mod, _)), _, _)
                        | (None, Some(res @ Res::Def(DefKind::Enum, _)), _) => res,
                        (Some(Res::Err), Some(Res::Err), Some(module)) => {
                            Res::Def(DefKind::Mod, module)
                        }
                        (type_ns, value_ns, _) => {
                            return Some(format!(
                                "an accepted type name next to an unresolved glob import \
                             (type {type_ns:?}, value {value_ns:?}) at {:?}",
                                item.span
                            ));
                        }
                    };
                    let Res::Def(kind, did) = glob_res else {
                        unreachable!("glob_res is a Res::Def by construction");
                    };
                    if did.is_local() {
                        continue;
                    }
                    if !matches!(kind, DefKind::Mod | DefKind::Enum) {
                        return Some(
                            "an accepted type name next to a glob import of an item \
                         that is not a module"
                                .to_string(),
                        );
                    }
                    for child in tcx.module_children(did) {
                        let name = child.ident.name.as_str();
                        if !names.contains(name) {
                            continue;
                        }
                        let canonical = match child.res {
                            Res::PrimTy(prim) => prim.name_str() == name,
                            Res::Def(kind, did) => {
                                (kind.ns() != Some(Namespace::TypeNS)
                                    && !matches!(kind, DefKind::TyParam | DefKind::ExternCrate))
                                    || is_canonical_written_type(tcx, did, name)
                            }
                            _ => false,
                        };
                        if !canonical {
                            return Some(format!(
                                "type `{name}` (shadowed by a glob import of `{}`)",
                                tcx.def_path_str(did)
                            ));
                        }
                    }
                }
                UseKind::Nested { .. } => {}
            }
        }
    }
    None
}

pub(super) struct PreparedRefinementClauses {
    pub(super) trait_method_path: String,
    pub(super) trait_requires: Vec<PureExpr>,
    pub(super) trait_ensures: Vec<PureExpr>,
    pub(super) impl_requires: Vec<PureExpr>,
    pub(super) impl_ensures: Vec<PureExpr>,
    pub(super) result_expr: Option<PureExpr>,
    /// How many leading `impl_requires` and `trait_ensures` clauses are
    /// premises and never goals. Nonzero only for an inherited contract
    /// (`clauses_are_the_trait_s`), whose user clauses are the trait's one
    /// text on both sides: stated as goals they ask whether a clause implies
    /// itself, which the solver cannot see once the encoder gives each
    /// occurrence of a name it does not resolve its own symbol (a sibling
    /// logic method at `Self`). What types add stays a goal.
    pub(super) premise_only_impl_requires: usize,
    pub(super) premise_only_trait_ensures: usize,
}

/// Rename impl parameters to the trait's parameter names (#479).
///
/// Capture-avoiding: an impl clause binder that shares a trait parameter's
/// name is alpha-renamed first. Plain substitution would let the binder
/// capture the renamed parameter (`exists<x> x == y@ && x > 0` with
/// `y := x` becomes the tautology `exists<x> x == x && x > 0`).
pub(super) fn rename_impl_params(
    expr: &PureExpr,
    param_subs: &HashMap<String, PureExpr>,
) -> PureExpr {
    expr.substitute_capture_avoiding(param_subs, &CaptureAvoidingSubstOptions::default())
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

/// The scope closure and written-type checks of both sides' user clauses.
///
/// Fail-closed: clauses are unscoped strings, so the check runs only on the
/// user-written clauses of both sides whose every name is a parameter,
/// `result`, a binder, or fixed pearlite vocabulary. Clauses added later
/// (integer ranges, type invariants) are derived from rustc types, not from
/// clause text.
///
/// Returns whether the impl's own ensures were left out: they enter the
/// postcondition direction only as premises, so when they name something
/// scope-dependent and the trait method states no ensures of its own, that
/// direction owes only clauses derived from the signature, and dropping a
/// premise can only make an obligation harder.
fn check_refinement_clause_scope(
    tcx: TyCtxt<'_>,
    req: &TraitRefinementRequest<'_>,
    trait_names_opt: Option<&[String]>,
    trait_requires: &[PureExpr],
    trait_ensures: &[PureExpr],
    impl_base_requires: &[PureExpr],
    impl_base_ensures: &[PureExpr],
) -> Result<bool, RefinementPrepareError> {
    let trait_params: HashSet<&str> = trait_names_opt
        .into_iter()
        .flatten()
        .map(String::as_str)
        .collect();
    let impl_params: HashSet<&str> = req.impl_arg_names.iter().map(String::as_str).collect();
    use super::scope::ClauseKind;
    check_clause_scope(
        "trait requires",
        trait_requires,
        &trait_params,
        ClauseKind::Requires,
    )?;
    check_clause_scope(
        "impl requires",
        impl_base_requires,
        &impl_params,
        ClauseKind::Requires,
    )?;
    // A precondition-only check builds no obligation from either side's
    // ensures, so their names cannot reach a verdict.
    let mut impl_ensures_dropped = false;
    if !req.precondition_only {
        check_clause_scope(
            "trait ensures",
            trait_ensures,
            &trait_params,
            ClauseKind::Ensures,
        )?;
        if let Err(error) = check_clause_scope(
            "impl ensures",
            impl_base_ensures,
            &impl_params,
            ClauseKind::Ensures,
        ) {
            if !trait_ensures.is_empty() {
                return Err(error);
            }
            impl_ensures_dropped = true;
        }
    }
    // Written types (fail-closed): the parser erases casts, ascriptions and
    // `let` annotations and drops binder types it cannot map to a sort, so
    // they are checked on the clause text both sides were parsed from.
    let mut written_type_names = HashSet::new();
    check_clause_written_types(
        "trait requires",
        &req.trait_contract.requires,
        &mut written_type_names,
    )?;
    check_clause_written_types(
        "impl requires",
        req.impl_requires_text,
        &mut written_type_names,
    )?;
    if !req.precondition_only {
        check_clause_written_types(
            "trait ensures",
            &req.trait_contract.ensures,
            &mut written_type_names,
        )?;
        if !impl_ensures_dropped {
            check_clause_written_types(
                "impl ensures",
                req.impl_ensures_text,
                &mut written_type_names,
            )?;
        }
    }
    if !written_type_names.is_empty() {
        if let Some(name) = shadowed_written_type_name(tcx, &written_type_names) {
            return Err(RefinementPrepareError::ScopeDependent {
                side: "a refinement",
                name,
            });
        }
    }

    Ok(impl_ensures_dropped)
}

pub(super) fn prepare_refinement_clauses(
    tcx: TyCtxt<'_>,
    req: &TraitRefinementRequest<'_>,
) -> Result<PreparedRefinementClauses, RefinementPrepareError> {
    let trait_method_path = format!(
        "{}::{}",
        req.trait_contract.trait_path, req.trait_contract.method_name
    );
    let trait_requires = parse_contract_clauses(
        &req.trait_contract.requires,
        "trait requires",
        &trait_method_path,
    )?;
    let trait_ensures = parse_contract_clauses(
        &req.trait_contract.ensures,
        "trait ensures",
        &trait_method_path,
    )?;

    // An inherited contract (`clauses_are_the_trait_s`) keeps the one
    // resolution its body obligation was restated in, so neither side is
    // re-read. Otherwise each side is read where it was written: the impl's
    // clause in the impl method's scope (the reading its own verification
    // uses), the trait's in the trait method's scope (the reading its grant
    // uses) with each declaration call instantiated at THIS impl by rustc's
    // instance resolution. A call both sides bind to one id names one
    // definition, and the scope closure admits exactly those; a call that does
    // not bind, or stays a declaration, is refused as before.
    let (trait_requires, trait_ensures, impl_base_requires, impl_base_ensures) =
        if req.clauses_are_the_trait_s {
            (
                trait_requires,
                trait_ensures,
                req.base_requires.to_vec(),
                req.base_ensures.to_vec(),
            )
        } else {
            // Each expression is read against the type-check body of the
            // clause it was parsed from (`spec_calls`). Where the expressions
            // do not line up one for one with the texts, no clause is paired
            // with its body: every type-dependent call is refused, and no
            // clause is ever dropped (a dropped premise or trait `ensures`
            // would weaken what the refinement owes).
            let clause_refs = |texts: &[String], len: usize, kind: &str| -> Vec<ClauseRef> {
                if texts.len() == len {
                    texts
                        .iter()
                        .map(|text| ClauseRef::written(kind, text))
                        .collect()
                } else {
                    vec![ClauseRef::Unknown; len]
                }
            };
            let trait_at_impl = |exprs: Vec<PureExpr>, texts: &[String], kind: &str| {
                let refs = clause_refs(texts, exprs.len(), kind);
                exprs
                    .iter()
                    .zip(&refs)
                    .map(|(expr, clause)| {
                        crate::logic::identity::resolve_trait_clause_at_impl(
                            tcx,
                            req.trait_contract.method_def_id,
                            req.impl_def_id,
                            expr,
                            clause,
                        )
                    })
                    .collect::<Vec<PureExpr>>()
            };
            let in_impl_scope = |exprs: &[PureExpr], texts: &[String], kind: &str| {
                let refs = clause_refs(texts, exprs.len(), kind);
                exprs
                    .iter()
                    .zip(&refs)
                    .map(|(expr, clause)| {
                        crate::logic::identity::resolve_logic_fn_paths_in_scope(
                            tcx,
                            req.impl_def_id,
                            expr,
                            crate::logic::identity::ClausePosition::Signature,
                            clause,
                        )
                    })
                    .collect::<Vec<PureExpr>>()
            };
            (
                trait_at_impl(trait_requires, &req.trait_contract.requires, "requires"),
                trait_at_impl(trait_ensures, &req.trait_contract.ensures, "ensures"),
                in_impl_scope(req.base_requires, req.impl_requires_text, "requires"),
                in_impl_scope(req.base_ensures, req.impl_ensures_text, "ensures"),
            )
        };

    // Resolve trait parameter names for normalization and range constraint parity (#479, #2363).
    let trait_names_opt = get_arg_names_from_def_id(tcx, req.trait_contract.method_def_id);

    // The parser's synthetic accessors must be unambiguous on both sides.
    if let Some(reserved) = req.logic_fns_opt.and_then(|logic_fns| {
        logic_fns.iter().find(|lf| {
            lf.name()
                .starts_with(super::scope::SYNTHETIC_LOGIC_FN_PREFIX)
        })
    }) {
        return Err(RefinementPrepareError::ReservedLogicFnName(
            reserved.full_path().to_string(),
        ));
    }
    // An inherited contract compares the trait's clause text with itself,
    // renamed to the impl's parameters position by position: whatever a name
    // in it means, it means the same on both sides and in the impl's body
    // obligation, which was restated in the trait's resolution. Only then is
    // the scope closure moot.
    let impl_ensures_dropped = if req.clauses_are_the_trait_s {
        false
    } else {
        check_refinement_clause_scope(
            tcx,
            req,
            trait_names_opt.as_deref(),
            &trait_requires,
            &trait_ensures,
            &impl_base_requires,
            &impl_base_ensures,
        )?
    };

    // Positional parameter renaming (#479), fail-closed. Both sides are
    // renamed to the same positional names, so trait parameter `i` and impl
    // parameter `i` become one variable and no other pair does; the renaming
    // is refused unless it is injective on both sides. Without trait
    // parameter names (an external trait method with no MIR) the trait side
    // may state no clause over its parameters, so it must state none at all.
    let renaming = match trait_names_opt.as_deref() {
        Some(trait_names) => build_positional_param_renaming(trait_names, req.impl_arg_names),
        None => {
            let trait_states_clauses =
                !trait_requires.is_empty() || (!req.precondition_only && !trait_ensures.is_empty());
            if trait_states_clauses {
                Err("the trait method's parameter names are unavailable".to_string())
            } else {
                build_positional_param_renaming(req.impl_arg_names, req.impl_arg_names)
            }
        }
    }
    .map_err(RefinementPrepareError::ParamNaming)?;
    let canonical_names: &[String] = &renaming.names;
    // The trait side's own enrichments only run when its names are known.
    let trait_names_opt: Option<&[String]> = trait_names_opt.as_ref().map(|_| canonical_names);
    let trait_requires_user: Vec<PureExpr> = trait_requires
        .iter()
        .map(|expr| rename_impl_params(expr, &renaming.trait_subs))
        .collect();
    let trait_ensures_user: Vec<PureExpr> = trait_ensures
        .iter()
        .map(|expr| rename_impl_params(expr, &renaming.trait_subs))
        .collect();
    let user_trait_ensures = trait_ensures_user.len();
    let mut trait_requires = trait_requires_user;
    let mut trait_ensures = trait_ensures_user;
    let base_requires: Vec<PureExpr> = impl_base_requires
        .iter()
        .map(|expr| rename_impl_params(expr, &renaming.impl_subs))
        .collect();
    let base_ensures: Vec<PureExpr> = if impl_ensures_dropped {
        Vec::new()
    } else {
        impl_base_ensures
            .iter()
            .map(|expr| rename_impl_params(expr, &renaming.impl_subs))
            .collect()
    };
    let trait_sort_map = trait_names_opt.map_or_else(HashMap::new, |trait_names| {
        build_signature_sort_map(tcx, req.trait_contract.method_def_id, trait_names)
    });
    let impl_sort_map = build_signature_sort_map(tcx, req.impl_def_id, canonical_names);

    if !req.type_invariant_defs.is_empty() {
        if let Some(trait_names) = trait_names_opt {
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
        base_requires.clone()
    } else {
        let (impl_param_methods, impl_result_method) = build_type_invariant_method_map(
            tcx,
            req.impl_def_id,
            canonical_names,
            req.type_invariant_defs,
        );
        let (impl_param_structural_exprs, impl_result_structural_expr) =
            build_type_invariant_structural_expr_map(
                tcx,
                req.impl_def_id,
                canonical_names,
                req.type_invariant_defs,
            );
        base_requires
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
        base_ensures.clone()
    } else {
        let (impl_param_methods, impl_result_method) = build_type_invariant_method_map(
            tcx,
            req.impl_def_id,
            canonical_names,
            req.type_invariant_defs,
        );
        let (impl_param_structural_exprs, impl_result_structural_expr) =
            build_type_invariant_structural_expr_map(
                tcx,
                req.impl_def_id,
                canonical_names,
                req.type_invariant_defs,
            );
        base_ensures
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
    if let Some(trait_names) = trait_names_opt {
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
    let impl_int_ranges = build_unsigned_range_preconditions(tcx, req.impl_def_id, canonical_names);
    if !impl_int_ranges.is_empty() {
        if req.verbose {
            debug!(
                "trust-wp:   (adding {} impl-signature integer range precondition(s) to trait side for refinement parity)",
                impl_int_ranges.len()
            );
        }
        trait_requires.extend(impl_int_ranges);
    }

    // Impl-side base clauses, already in positional parameter names (#479).
    let user_impl_requires = impl_base_requires.len();
    let mut impl_requires = impl_base_requires;
    let mut impl_ensures = impl_base_ensures;

    // Add type-invariant clauses for refinement parity (#1579).
    //
    // Normal body verification enriches contracts with type-invariant clauses
    // before solving. Without matching enrichment on the refinement path,
    // refinement rejects impl contracts that are valid under trust-wp's own
    // verification model whenever the proof relies on argument or result type
    // invariants.
    if !req.type_invariant_defs.is_empty() {
        // Trait side: use the trait method's signature and trait parameter names.
        if let Some(trait_names) = trait_names_opt {
            let (mut trait_inv_req, trait_inv_ens) = build_type_invariant_clauses(
                tcx,
                req.trait_contract.method_def_id,
                trait_names,
                req.type_invariant_defs,
            );
            // A type parameter's invariant is charged where a call fixes the
            // parameter, not here. Kept, the trait's `Self` and an impl's own
            // parameter would be two symbols for one instantiation, and a
            // blanket impl's premise could never be implied.
            trait_inv_req.retain(|clause| !mentions_type_param_invariant(clause));
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
        // built over the positional parameter names shared with the trait
        // side (RenamedParamImpl, #479).
        let (mut impl_inv_req, impl_inv_ens) = build_type_invariant_clauses(
            tcx,
            req.impl_def_id,
            canonical_names,
            req.type_invariant_defs,
        );
        impl_inv_req.retain(|clause| !mentions_type_param_invariant(clause));
        if !impl_inv_req.is_empty() || !impl_inv_ens.is_empty() {
            if req.verbose {
                debug!(
                    "trust-wp:   (adding {} impl-side type invariant clause(s) for refinement parity)",
                    impl_inv_req.len() + impl_inv_ens.len()
                );
            }
            let normalized_impl_inv_req = impl_inv_req;
            let normalized_impl_inv_ens = impl_inv_ens;
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
            if let Some(trait_names) = trait_names_opt {
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
    let trait_clause_sort_map = concrete_trait_sort_map(&trait_sort_map, &impl_sort_map);
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

    let (premise_only_impl_requires, premise_only_trait_ensures) = if req.clauses_are_the_trait_s {
        (user_impl_requires, user_trait_ensures)
    } else {
        (0, 0)
    };
    Ok(PreparedRefinementClauses {
        trait_method_path,
        trait_requires,
        trait_ensures,
        impl_requires,
        impl_ensures,
        result_expr,
        premise_only_impl_requires,
        premise_only_trait_ensures,
    })
}
