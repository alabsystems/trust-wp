// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use trust_wp_core::{
    contract_parser::TURBOFISH_ARG_WRAPPER_NAME,
    formula::{ExprSort, PureExpr},
};

use super::ParsedContract;

/// Propagate MIR-derived ExprSort annotations onto `PureExpr::Var` nodes in
/// parsed contract expressions. (#994, Phase 2 - ExprSort enrichment)
///
/// The contract parser produces all `Var` nodes with `None` sort because it
/// operates on text without type information. This function builds a
/// name -> ExprSort map from the function's MIR signature **and** from MIR
/// `var_debug_info` entries for function-local variables that appear in any
/// contract clause (100doors Fix A, Part of #5). It then walks every
/// expression in the contract to annotate matching `Var(name, None)` nodes.
///
/// `None` annotations are replaced, and parser-introduced turbofish type
/// placeholders are allowed to upgrade to concrete const-generic sorts.
pub(super) fn propagate_param_sort_annotations(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    parsed: &mut ParsedContract,
) {
    // Closures don't support fn_sig(); use capture metadata instead. (#2668)
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        propagate_closure_capture_sort_annotations(tcx, def_id, parsed);
        return;
    }

    let contract_names = collect_contract_var_names_in_parsed(parsed);
    let sort_map = param_sort_map(tcx, def_id, &parsed.arg_names, &contract_names, false);
    if sort_map.is_empty() {
        return;
    }

    // Walk all expressions and annotate Var(name, None) where name is in sort_map.
    parsed.rewrite_all_exprs(|expr| annotate_var_sorts(expr, &sort_map));
}

/// Annotate a standalone expression with the parameter sorts of `def_id`.
///
/// Parsed expressions produced outside `ParsedContract` (for example leading
/// proof_assert lemma assumptions) otherwise keep `Var(_, None)` and can
/// diverge from the same variable in contract clauses after the normal
/// structural rewrite pass annotates those clauses.
pub(in crate::callbacks) fn annotate_expr_with_param_sorts(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    arg_names: &[String],
    expr: &PureExpr,
) -> PureExpr {
    let mut contract_names = HashSet::new();
    collect_free_var_names_into(expr, &mut contract_names);
    let sort_map = if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        closure_capture_sort_map(tcx, def_id, arg_names)
    } else {
        param_sort_map(tcx, def_id, arg_names, &contract_names, true)
    };
    if sort_map.is_empty() {
        expr.clone()
    } else {
        annotate_var_sorts(expr, &sort_map)
    }
}

/// Annotate standalone expressions with the parameter sorts of `def_id`.
pub(in crate::callbacks) fn annotate_exprs_with_param_sorts(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    arg_names: &[String],
    exprs: &[PureExpr],
) -> Vec<PureExpr> {
    let mut contract_names = HashSet::new();
    for expr in exprs {
        collect_free_var_names_into(expr, &mut contract_names);
    }
    let sort_map = if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        closure_capture_sort_map(tcx, def_id, arg_names)
    } else {
        param_sort_map(tcx, def_id, arg_names, &contract_names, true)
    };
    if sort_map.is_empty() {
        exprs.to_vec()
    } else {
        exprs
            .iter()
            .map(|expr| annotate_var_sorts(expr, &sort_map))
            .collect()
    }
}

/// Build a sort map for a closure's formal args, return type, and captured
/// variables. Mirrors [`propagate_closure_capture_sort_annotations`] but
/// returns the map instead of walking a parsed contract, so callers like
/// [`annotate_expr_with_param_sorts`] can apply it to standalone expressions
/// (proof_assert assertions / preconditions inside closure bodies).
///
/// Without this, a `proof_assert!(y.0@ == 0)` inside a nested closure that
/// captures `y: Zero<T>` leaves `Var("y", None)` in the parsed expression.
/// The encoder then synthesizes a `Tuple1` carrier for the `tuple_get_0(y)`
/// rewrite and later collides with the `Zero` sort produced by the
/// postcondition-side rewrite, surfacing as
/// `sort conflict: variable 'y': declared as Uninterpreted("Tuple1"),
/// requested as Uninterpreted("Zero")`. (closures/10_tyinv)
fn closure_capture_sort_map(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    arg_names: &[String],
) -> HashMap<String, ExprSort> {
    use rustc_middle::ty::TyKind;

    use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

    let mut sort_map: HashMap<String, ExprSort> = HashMap::new();

    let Some(local_def_id) = def_id.as_local() else {
        return sort_map;
    };

    let Some(body_with_facts) = super::super::try_get_body_with_context(tcx, local_def_id) else {
        return sort_map;
    };
    let mir_body = super::super::super::mir_analysis::get_mir_body(&body_with_facts);

    // Closure formal arguments: contract-side arg_names are zipped with MIR
    // arg locals.
    for (idx, local) in mir_body.args_iter().enumerate() {
        let Some(name) = arg_names.get(idx) else {
            continue;
        };
        if let Some(sort) = ty_to_expr_sort_enriched(tcx, mir_body.local_decls[local].ty) {
            sort_map.insert(name.clone(), normalize_standalone_param_sort(sort));
        }
    }
    if let Some(sort) = ty_to_expr_sort_enriched(tcx, mir_body.return_ty()) {
        sort_map.insert("result".to_string(), normalize_standalone_param_sort(sort));
    }

    let captures = tcx.closure_captures(local_def_id);
    let closure_substs = {
        let env_ty = mir_body.local_decls[rustc_middle::mir::Local::from_u32(1)].ty;
        match env_ty.kind() {
            TyKind::Closure(_, substs) => Some(*substs),
            TyKind::Ref(_, inner, _) => match inner.kind() {
                TyKind::Closure(_, substs) => Some(*substs),
                _ => None,
            },
            _ => None,
        }
    };

    if let Some(substs) = closure_substs {
        for (idx, (capture, upvar_ty)) in captures
            .iter()
            .zip(substs.as_closure().upvar_tys())
            .enumerate()
        {
            if let Some(sort) = ty_to_expr_sort_enriched(tcx, upvar_ty) {
                let normalized = normalize_standalone_param_sort(sort);
                let name = capture.var_ident.as_str().to_string();
                sort_map.insert(name, normalized.clone());
                sort_map.insert(format!("self.{idx}"), normalized);
            }
        }
    }

    sort_map
}

/// Collect the set of variable names referenced anywhere in `parsed`'s
/// contract clauses (requires / ensures / invariants / variants / call
/// assumptions / obligations).
///
/// Used by [`param_sort_map`] to decide which function-local variables (i.e.
/// names that appear in MIR `var_debug_info` but are not function parameters)
/// should be annotated with an `ExprSort` derived from their MIR type.
/// (100doors Fix A, Part of #5)
fn collect_contract_var_names_in_parsed(parsed: &ParsedContract) -> HashSet<String> {
    let mut names = HashSet::new();
    for expr in &parsed.requires {
        collect_free_var_names_into(expr, &mut names);
    }
    for expr in &parsed.ensures {
        collect_free_var_names_into(expr, &mut names);
    }
    if let Some(result_expr) = &parsed.result_expr {
        collect_free_var_names_into(result_expr, &mut names);
    }
    for expr in &parsed.call_assumptions {
        collect_free_var_names_into(expr, &mut names);
    }
    for expr in &parsed.pre_loop_call_assumptions {
        collect_free_var_names_into(expr, &mut names);
    }
    for expr in &parsed.call_obligations {
        collect_free_var_names_into(expr, &mut names);
    }
    for expr in &parsed.pre_loop_call_obligations {
        collect_free_var_names_into(expr, &mut names);
    }
    for expr in &parsed.post_loop_call_obligations {
        collect_free_var_names_into(expr, &mut names);
    }
    for expr in &parsed.loop_fields.invariants {
        collect_free_var_names_into(expr, &mut names);
    }
    for (_, _, invariants) in &parsed.loop_fields.per_loop_invariants {
        for expr in invariants {
            collect_free_var_names_into(expr, &mut names);
        }
    }
    for expr in &parsed.loop_fields.variants {
        collect_free_var_names_into(expr, &mut names);
    }
    for (_, _, variants) in &parsed.loop_fields.per_loop_variants {
        for expr in variants {
            collect_free_var_names_into(expr, &mut names);
        }
    }
    for group in &parsed.loop_fields.loop_obligation_groups {
        for expr in &group.obligations {
            collect_free_var_names_into(expr, &mut names);
        }
        if let Some(cond) = &group.condition {
            collect_free_var_names_into(cond, &mut names);
        }
    }
    names
}

/// Insert every free-variable name of `expr` into `names`.
///
/// Uses `PureExpr::for_each_free_var` so variables bound by enclosing
/// quantifiers, `let`s, match-arm patterns, or closure parameters are
/// correctly excluded.
fn collect_free_var_names_into(expr: &PureExpr, names: &mut HashSet<String>) {
    expr.for_each_free_var(|name, _sort| {
        names.insert(name.to_string());
    });
}

fn param_sort_map(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    arg_names: &[String],
    contract_names: &HashSet<String>,
    normalize_immutable_refs: bool,
) -> HashMap<String, ExprSort> {
    use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return HashMap::new();
    }

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let mut sort_map = HashMap::new();

    for (i, ty) in sig.inputs().iter().enumerate() {
        let Some(name) = arg_names.get(i) else {
            break;
        };
        if let Some(sort) = ty_to_expr_sort_enriched(tcx, *ty) {
            let sort = if normalize_immutable_refs {
                normalize_standalone_param_sort(sort)
            } else {
                sort
            };
            sort_map.insert(name.clone(), sort);
        }
    }

    if let Some(sort) = ty_to_expr_sort_enriched(tcx, sig.output()) {
        sort_map.insert("result".to_string(), sort);
    }

    for param_def in &tcx.generics_of(def_id).own_params {
        if matches!(
            param_def.kind,
            rustc_middle::ty::GenericParamDefKind::Const { .. }
        ) {
            sort_map.insert(param_def.name.as_str().to_string(), ExprSort::Int);
        }
    }

    // Annotate function-local variables whose names appear in contract
    // clauses. This closes the leakage gap where a `let mut v: Vec<bool>` in
    // a function body would otherwise be left with `Var("v", None)` in any
    // inherited loop invariant, causing the encoder to declare it as `Int`
    // and route `v@.len()` through the `fset_len` UF fallback.
    // (100doors Fix A, Part of #5)
    if !contract_names.is_empty() {
        annotate_local_vars_from_mir(
            tcx,
            def_id,
            arg_names,
            contract_names,
            normalize_immutable_refs,
            &mut sort_map,
        );
    }

    sort_map
}

/// Walk the function's MIR body and insert sort annotations for any
/// function-local whose source name appears in `contract_names` but is not
/// already in `sort_map`.
///
/// Locals are identified via `body.var_debug_info` (entries whose value is a
/// bare `Place` with empty projection). Function parameters are deliberately
/// skipped — they are handled by the signature-driven loop above, which is
/// the authoritative source for parameter sorts (it sees `&T` / `&mut T` in
/// the function signature, while `var_debug_info` types may peel a layer).
fn annotate_local_vars_from_mir(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    arg_names: &[String],
    contract_names: &HashSet<String>,
    normalize_immutable_refs: bool,
    sort_map: &mut HashMap<String, ExprSort>,
) {
    use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

    let Some(local_def_id) = def_id.as_local() else {
        return;
    };

    let Some(body_with_facts) = super::super::try_get_body_with_context(tcx, local_def_id) else {
        return;
    };
    let mir_body = super::super::super::mir_analysis::get_mir_body(&body_with_facts);

    let arg_count = mir_body.arg_count;

    for debug in &mir_body.var_debug_info {
        let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        if !place.projection.is_empty() {
            continue;
        }
        // Skip argument locals — handled by the signature loop above. MIR's
        // argument locals are `_1..=_arg_count`.
        if place.local.as_usize() >= 1 && place.local.as_usize() <= arg_count {
            continue;
        }
        let name = debug.name.to_string();
        if sort_map.contains_key(&name) {
            continue;
        }
        if !contract_names.contains(&name) {
            continue;
        }
        // Defensive: also skip names that match a function parameter (the
        // arg_names slice). This handles any edge cases where parameter
        // bookkeeping disagrees with MIR arg_count.
        if arg_names.iter().any(|p| p == &name) {
            continue;
        }
        let ty = mir_body.local_decls[place.local].ty;
        if let Some(sort) = ty_to_expr_sort_enriched(tcx, ty) {
            let sort = if normalize_immutable_refs {
                normalize_standalone_param_sort(sort)
            } else {
                sort
            };
            sort_map.insert(name, sort);
        }
    }
}

fn normalize_standalone_param_sort(sort: ExprSort) -> ExprSort {
    match sort {
        ExprSort::Ref(inner) => *inner,
        other => other,
    }
}

/// Propagate sort annotations for closure capture variables. (#2668)
///
/// Closures don't have `fn_sig()`, so this function uses MIR local types for
/// formal arguments and closure capture metadata for captured variable names.
/// This enables sort annotations on contracts like `|b: &bool| *b` and capture
/// contracts like `#[ensures((^*old(bx))@ + (^**old(by))@ == 3)]`.
fn propagate_closure_capture_sort_annotations(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    parsed: &mut ParsedContract,
) {
    use rustc_middle::ty::TyKind;

    use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

    let Some(local_def_id) = def_id.as_local() else {
        return;
    };

    let Some(body_with_facts) = super::super::try_get_body_with_context(tcx, local_def_id) else {
        return;
    };
    let mir_body = super::super::super::mir_analysis::get_mir_body(&body_with_facts);

    let mut sort_map: HashMap<String, ExprSort> = HashMap::new();

    for (idx, local) in mir_body.args_iter().enumerate() {
        let Some(name) = parsed.arg_names.get(idx) else {
            continue;
        };
        if let Some(sort) = ty_to_expr_sort_enriched(tcx, mir_body.local_decls[local].ty) {
            sort_map.insert(name.clone(), sort);
        }
    }
    if let Some(sort) = ty_to_expr_sort_enriched(tcx, mir_body.return_ty()) {
        sort_map.insert("result".to_string(), sort);
    }

    let captures = tcx.closure_captures(local_def_id);

    // Get upvar types from closure substs.
    let closure_substs = {
        let env_ty = mir_body.local_decls[rustc_middle::mir::Local::from_u32(1)].ty;
        match env_ty.kind() {
            TyKind::Closure(_, substs) => Some(*substs),
            TyKind::Ref(_, inner, _) => match inner.kind() {
                TyKind::Closure(_, substs) => Some(*substs),
                _ => None,
            },
            _ => None,
        }
    };

    if let Some(substs) = closure_substs {
        for (idx, (capture, upvar_ty)) in captures
            .iter()
            .zip(substs.as_closure().upvar_tys())
            .enumerate()
        {
            if let Some(sort) = ty_to_expr_sort_enriched(tcx, upvar_ty) {
                // Include both original capture name and substituted self.N
                // name, since closure_capture_substitutions rewrites the
                // original names before this pass runs.
                let name = capture.var_ident.as_str().to_string();
                sort_map.insert(name, sort.clone());
                sort_map.insert(format!("self.{idx}"), sort);
            }
        }
    }

    if sort_map.is_empty() {
        return;
    }

    parsed.rewrite_all_exprs(|expr| annotate_var_sorts(expr, &sort_map));
}

/// Recursively annotate `PureExpr::Var(name, None)` nodes with sorts from the map.
pub(super) fn annotate_var_sorts(
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

pub(super) fn normalize_turbofish_logic_fn_args(parsed: &mut ParsedContract) {
    parsed.rewrite_all_exprs(normalize_turbofish_logic_fn_expr);
}

/// Layout intrinsic function names that should preserve their type parameter
/// in the SMT function name. When the turbofish contains a known primitive
/// type (e.g., `size_of_logic::<u32>()`), the type name is encoded into the
/// function name as `size_of_logic__u32` so the encoder can assert concrete
/// layout values. (#2324)
const LAYOUT_INTRINSICS: &[&str] = &["size_of_logic", "align_of_logic"];

/// A call's generic arguments, from the parser's wrappers: a const argument
/// becomes the leading value argument it is, and a type argument leaves the
/// argument list. A type argument is part of which function is called
/// (`k::<u8>()` and `k::<u16>()` are two values), so the call is renamed to
/// the instance its type arguments name, `k::<u8>`: dropped from a name that
/// stayed `k`, two calls differing only in a type argument were read as one.
/// A layout intrinsic's instance is spelled `size_of_logic__u8`, the name its
/// axioms are declared under (#2324).
pub(super) fn normalize_turbofish_logic_fn_expr(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args } if name == TURBOFISH_ARG_WRAPPER_NAME => {
            PureExpr::LogicFnCall { name, args }
        }
        PureExpr::LogicFnCall { name, args } => {
            let mut normalized = Vec::with_capacity(args.len());
            let mut type_args: Vec<String> = Vec::new();
            let mut idx = 0usize;
            while idx < args.len() {
                let Some(inner) = turbofish_wrapper_inner(&args[idx]) else {
                    break;
                };
                match inner {
                    PureExpr::Var(type_name, Some(ExprSort::TypeParam(_))) => {
                        type_args.push(type_name.clone());
                    }
                    PureExpr::Var(type_name, _) if LAYOUT_INTRINSICS.contains(&name.as_str()) => {
                        type_args.push(type_name.clone());
                    }
                    _ => normalized.push(inner.clone()),
                }
                idx += 1;
            }
            normalized.extend(args[idx..].iter().cloned());
            let name = if type_args.is_empty() {
                name
            } else if LAYOUT_INTRINSICS.contains(&name.as_str()) {
                format!("{name}__{}", type_args.join("__"))
            } else {
                format!("{name}::<{}>", type_args.join(", "))
            };
            PureExpr::LogicFnCall {
                name,
                args: normalized,
            }
        }
        other => other,
    })
}

/// Erase one layer of `Deref` for parameters whose original type is `Box<T>`.
///
/// When a parameter `x` has type `Box<&mut i32>`, `ty_to_expr_sort_enriched`
/// transparently peels the Box and assigns `MutRef(Int)` as the ExprSort. The
/// contract parser, however, has no type information — when the user writes `*x`
/// (meaning "deref the Box"), it produces `Deref(Var("x"))`. The encoder then
/// interprets this as "deref the MutRef" (yielding `x_current: Int`), which is
/// one level too deep.
///
/// This rewrite erases the spurious Box Deref layer: `Deref(Var("x"))` → `Var("x")`
/// for Box parameters. Applied after sort annotations so we can identify Box
/// params by inspecting the original Rust type.
///
/// For closures, inspects capture metadata instead of `fn_sig()` to identify
/// Box-wrapped captures that need deref erasure. (#2668)
pub(super) fn erase_box_deref_in_contract(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    parsed: &mut ParsedContract,
) {
    use rustc_middle::ty::TyKind;

    // For closures, use capture metadata to find Box-wrapped captures.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        erase_box_deref_in_closure_contract(tcx, def_id, parsed);
        return;
    }

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();

    let mut box_params: HashSet<String> = HashSet::new();

    for (i, ty) in inputs.iter().enumerate() {
        if i >= parsed.arg_names.len() {
            break;
        }
        // Detect Box<T> parameters (adt_def.is_box() check).
        if let TyKind::Adt(adt_def, _) = ty.kind() {
            if adt_def.is_box() {
                box_params.insert(parsed.arg_names[i].clone());
            }
        }
    }

    if box_params.is_empty() {
        return;
    }

    // Use rewrite_all_exprs_except_final_values to avoid stripping semantic
    // Deref wrappers from mut_borrow final values. (#2668)
    parsed.rewrite_all_exprs_except_final_values(|expr| erase_box_deref_expr(expr, &box_params));
}

/// Erase Box deref layers in closure contracts using capture metadata. (#2668)
///
/// Closures don't have `fn_sig()`, so the standard `erase_box_deref_in_contract`
/// cannot inspect parameter types. Instead, this function examines the closure's
/// captured variables: if a capture's upvar type is `Box<T>`, the capture variable
/// name is added to the Box params set for deref erasure.
///
/// This is critical for closures like `09_fnonce_resolve` that capture
/// `Box<&mut i32>` or `Box<Box<&mut i32>>`: the contract parser emits
/// `Deref(Var("bx"))` for `*bx`, but `ty_to_expr_sort_enriched` already peels
/// the Box, so the Deref is spurious.
fn erase_box_deref_in_closure_contract(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    parsed: &mut ParsedContract,
) {
    use rustc_middle::ty::TyKind;

    let Some(local_def_id) = def_id.as_local() else {
        return;
    };

    let captures = tcx.closure_captures(local_def_id);
    if captures.is_empty() {
        return;
    }

    let closure_substs = {
        let Some(body_with_facts) = super::super::try_get_body_with_context(tcx, local_def_id)
        else {
            return;
        };
        let mir_body = super::super::super::mir_analysis::get_mir_body(&body_with_facts);
        let env_ty = mir_body.local_decls[rustc_middle::mir::Local::from_u32(1)].ty;
        match env_ty.kind() {
            TyKind::Closure(_, substs) => Some(*substs),
            TyKind::Ref(_, inner, _) => match inner.kind() {
                TyKind::Closure(_, substs) => Some(*substs),
                _ => None,
            },
            _ => None,
        }
    };

    let mut box_params: HashSet<String> = HashSet::new();
    let mut max_box_depth: usize = 0;

    if let Some(substs) = closure_substs {
        for (idx, (capture, upvar_ty)) in captures
            .iter()
            .zip(substs.as_closure().upvar_tys())
            .enumerate()
        {
            if is_box_type(upvar_ty) {
                // Include both the original capture name (e.g., "bx") and
                // the substituted self.N name (e.g., "self.1"). By the time
                // erase_box_deref runs, closure_capture_substitutions has
                // already rewritten Var("bx") -> Var("self.1") in contract
                // expressions, so the self.N form is what we'll actually
                // encounter. Include the original name for completeness.
                let name = capture.var_ident.as_str().to_string();
                box_params.insert(name);
                box_params.insert(format!("self.{idx}"));
                // Track the maximum Box nesting depth so we can run
                // enough erasure passes. Box<Box<&mut T>> needs 2 passes.
                let depth = box_nesting_depth(tcx, upvar_ty);
                if depth > max_box_depth {
                    max_box_depth = depth;
                }
            }
        }
    }

    if box_params.is_empty() {
        return;
    }

    // Run erasure passes up to the maximum Box nesting depth. Each pass
    // erases one Deref(Var("x")) layer for Box params. For Box<Box<&mut T>>
    // the contract has Deref(Deref(Var("self.2"))) which needs two passes:
    // pass 1 erases the inner Deref to Deref(Var("self.2")),
    // pass 2 erases the remaining Deref to Var("self.2"). (#2318)
    //
    // CRITICAL: use rewrite_all_exprs_except_final_values to avoid stripping
    // semantic Deref wrappers from mut_borrow final values. In final_values,
    // Deref(Var("self.1")) represents actual &mut dereference extracted from
    // MIR, NOT spurious Box dereference from the contract parser. (#2668)
    for _ in 0..max_box_depth {
        parsed
            .rewrite_all_exprs_except_final_values(|expr| erase_box_deref_expr(expr, &box_params));
    }
}

/// Check if a type is `Box<T>` (any `T`).
fn is_box_type(ty: rustc_middle::ty::Ty<'_>) -> bool {
    use rustc_middle::ty::TyKind;
    matches!(ty.kind(), TyKind::Adt(adt_def, _) if adt_def.is_box())
}

/// Count the Box nesting depth of a type.
///
/// - `Box<&mut T>` -> 1
/// - `Box<Box<&mut T>>` -> 2
/// - `Box<Box<Box<T>>>` -> 3
/// - `&mut T` -> 0
/// - `i32` -> 0
///
/// Used to determine how many deref erasure passes are needed for
/// Box-wrapped closure captures. (#2318)
fn box_nesting_depth<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> usize {
    use rustc_middle::ty::TyKind;
    match ty.kind() {
        TyKind::Adt(adt_def, substs) if adt_def.is_box() => {
            // Box<T>'s first type parameter is T.
            if let Some(inner_ty) = substs.types().next() {
                1 + box_nesting_depth(tcx, inner_ty)
            } else {
                1
            }
        }
        _ => 0,
    }
}

/// Check if an expression is a wrapped Box-param variable (not bare Var).
///
/// Returns true for `Old(Var("x"))`, `View(Old(Var("x")))`, etc. where "x"
/// is a Box param. Returns FALSE for bare `Var("x")` — the wrapper layer
/// is required. This distinction matters because `Deref(Var("x"))` is the
/// direct Box-deref pattern (handled by the primary check), while
/// `Deref(Old(Var("x")))` needs wrapper-aware erasure. (#2668)
fn is_wrapped_box_param_var(expr: &PureExpr, box_params: &HashSet<String>) -> bool {
    match expr {
        PureExpr::Old(inner) | PureExpr::View(inner) => inner_has_box_param_root(inner, box_params),
        _ => false,
    }
}

/// Check if the root variable of an expression (peeling Old/View) is a Box param.
fn inner_has_box_param_root(expr: &PureExpr, box_params: &HashSet<String>) -> bool {
    match expr {
        PureExpr::Var(name, _) => box_params.contains(name.as_str()),
        PureExpr::Old(inner) | PureExpr::View(inner) => inner_has_box_param_root(inner, box_params),
        _ => false,
    }
}

/// Erase one layer of Deref around Var nodes for Box parameters.
///
/// `Deref(Var("x"))` → `Var("x")` when `x` is a Box param. Also handles
/// wrappers between Deref and Var: `Deref(Old(Var("x")))` → `Old(Var("x"))`
/// when `x` is a Box param. This is necessary because contract expressions
/// like `*old(bx)` parse as `Deref(Old(Var("bx")))`, where the `Old`
/// wrapper preserves the Box type and the Deref is spurious. (#2668)
///
/// Deeper patterns like `Deref(Deref(Var("x")))` (double deref) become
/// `Deref(Var("x"))` — the outer Box deref is erased, keeping the inner
/// MutRef deref intact.
///
/// The rewrite is top-down for the Deref-of-Var pattern: when we see
/// `Deref(Var("x"))` where x is a Box param, we erase it and do NOT
/// recurse further into the erased Deref. For other node types, we
/// recurse normally.
pub(super) fn erase_box_deref_expr(expr: &PureExpr, box_params: &HashSet<String>) -> PureExpr {
    use std::sync::Arc;

    match expr {
        // Deref(Var("x")) where x is a Box param → Var("x")
        // Also: Deref(Old(Var("x"))) → Old(Var("x")) for Box params. (#2668)
        // This erases the Box deref layer. The Var("x") retains its MutRef sort.
        PureExpr::Deref(inner) => {
            // Direct Deref(Var("x")) check (original pattern).
            if let PureExpr::Var(name, _) = inner.as_ref() {
                if box_params.contains(name.as_str()) {
                    return inner.as_ref().clone();
                }
            }
            // Deref(Old(Var("x"))) or Deref(View(Var("x"))) check (#2668).
            if is_wrapped_box_param_var(inner, box_params) {
                // Erase this Deref layer. Recurse into inner to handle nested
                // patterns (e.g., Deref(Old(Deref(Old(Var("x")))))).
                return erase_box_deref_expr(inner, box_params);
            }
            // Recurse into inner
            let new_inner = erase_box_deref_expr(inner, box_params);
            // After recursion, the inner may now be a wrapped-box-param pattern
            // (e.g., Deref(Deref(Old(Var("x")))) → inner Deref recurses to
            // Old(Var("x")), and now Deref(Old(Var("x"))) should be erased).
            // Only erase if there's a wrapper — bare Var means the inner Box
            // deref was already handled and this Deref is a different kind
            // (e.g., MutRef deref).
            if is_wrapped_box_param_var(&new_inner, box_params) {
                return new_inner;
            }
            if &new_inner == inner.as_ref() {
                expr.clone()
            } else {
                PureExpr::Deref(Arc::new(new_inner))
            }
        }
        PureExpr::Final(inner) => {
            // Final(Var("x")) on a Box param: also erase, since ^(box_val)
            // is the Box's final state = the inner value itself. But only
            // erase when the inner value IS a Var (direct Box Final).
            if let PureExpr::Var(name, _) = inner.as_ref() {
                if box_params.contains(name.as_str()) {
                    return inner.as_ref().clone();
                }
            }
            let new_inner = erase_box_deref_expr(inner, box_params);
            if &new_inner == inner.as_ref() {
                expr.clone()
            } else {
                PureExpr::Final(Arc::new(new_inner))
            }
        }
        PureExpr::BinOp(l, op, r) => {
            let new_l = erase_box_deref_expr(l, box_params);
            let new_r = erase_box_deref_expr(r, box_params);
            if &new_l == l.as_ref() && &new_r == r.as_ref() {
                expr.clone()
            } else {
                PureExpr::BinOp(Arc::new(new_l), *op, Arc::new(new_r))
            }
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner = erase_box_deref_expr(inner, box_params);
            if &new_inner == inner.as_ref() {
                expr.clone()
            } else {
                PureExpr::UnOp(*op, Arc::new(new_inner))
            }
        }
        PureExpr::Ite(c, t, e) => {
            let new_c = erase_box_deref_expr(c, box_params);
            let new_t = erase_box_deref_expr(t, box_params);
            let new_e = erase_box_deref_expr(e, box_params);
            if &new_c == c.as_ref() && &new_t == t.as_ref() && &new_e == e.as_ref() {
                expr.clone()
            } else {
                PureExpr::Ite(Arc::new(new_c), Arc::new(new_t), Arc::new(new_e))
            }
        }
        PureExpr::Old(inner) => {
            let new_inner = erase_box_deref_expr(inner, box_params);
            if &new_inner == inner.as_ref() {
                expr.clone()
            } else {
                PureExpr::Old(Arc::new(new_inner))
            }
        }
        PureExpr::View(inner) => {
            let new_inner = erase_box_deref_expr(inner, box_params);
            if &new_inner == inner.as_ref() {
                expr.clone()
            } else {
                PureExpr::View(Arc::new(new_inner))
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = erase_box_deref_expr(receiver, box_params);
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|a| erase_box_deref_expr(a, box_params))
                .collect();
            let args_changed = new_args.iter().zip(args.iter()).any(|(n, o)| n != o);
            if &new_receiver == receiver.as_ref() && !args_changed {
                expr.clone()
            } else {
                PureExpr::MethodCall {
                    receiver: Arc::new(new_receiver),
                    method: method.clone(),
                    args: new_args,
                }
            }
        }
        PureExpr::LogicFnCall { name, args } => {
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|a| erase_box_deref_expr(a, box_params))
                .collect();
            let args_changed = new_args.iter().zip(args.iter()).any(|(n, o)| n != o);
            if !args_changed {
                expr.clone()
            } else {
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: new_args,
                }
            }
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let new_body = erase_box_deref_expr(body, box_params);
            let new_triggers: Vec<Vec<PureExpr>> = triggers
                .iter()
                .map(|trig| {
                    trig.iter()
                        .map(|t| erase_box_deref_expr(t, box_params))
                        .collect()
                })
                .collect();
            if &new_body == body.as_ref() {
                expr.clone()
            } else {
                PureExpr::Forall {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: Arc::new(new_body),
                    triggers: new_triggers,
                }
            }
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let new_body = erase_box_deref_expr(body, box_params);
            let new_triggers: Vec<Vec<PureExpr>> = triggers
                .iter()
                .map(|trig| {
                    trig.iter()
                        .map(|t| erase_box_deref_expr(t, box_params))
                        .collect()
                })
                .collect();
            if &new_body == body.as_ref() {
                expr.clone()
            } else {
                PureExpr::Exists {
                    var: var.clone(),
                    var_sort: var_sort.clone(),
                    body: Arc::new(new_body),
                    triggers: new_triggers,
                }
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            let new_scrutinee = erase_box_deref_expr(scrutinee, box_params);
            let new_arms: Vec<_> = arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: erase_box_deref_expr(&arm.body, box_params),
                })
                .collect();
            PureExpr::Match {
                scrutinee: Arc::new(new_scrutinee),
                arms: new_arms,
            }
        }
        // Leaf nodes — no change
        _ => expr.clone(),
    }
}

fn turbofish_wrapper_inner(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if name == TURBOFISH_ARG_WRAPPER_NAME && args.len() == 1 =>
        {
            args.first()
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    //! Unit tests for the function-local variable sort annotation extension
    //! (100doors Fix A, Part of #5).
    //!
    //! The MIR-walking part of [`param_sort_map`] requires a real `TyCtxt` and
    //! is exercised by the harness. These tests cover:
    //!  - the contract-name collection helpers
    //!    ([`collect_contract_var_names_in_parsed`],
    //!     [`collect_free_var_names_into`]),
    //!  - the integration assertion that, given the sort-map that
    //!    [`annotate_local_vars_from_mir`] would produce for a `Vec<bool>`
    //!    local, [`annotate_var_sorts`] rewrites every `Var(name, None)` for
    //!    that local — including inside inherited loop-invariant clones — to
    //!    `Var(name, Some(Datatype("Vec")))`.

    use std::{
        collections::{HashMap, HashSet},
        sync::Arc,
    };

    use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

    use super::{
        annotate_var_sorts, collect_contract_var_names_in_parsed, collect_free_var_names_into,
    };
    use crate::callbacks::parsing::{LoopFields, MutBorrowFields, ParsedContract};

    fn empty_parsed_contract() -> ParsedContract {
        ParsedContract {
            requires: vec![],
            ensures: vec![],
            result_expr: None,
            result_expr_spanned: None,
            arg_names: vec![],
            call_assumptions: vec![],
            pre_loop_call_assumptions: vec![],
            call_obligations: vec![],
            pre_loop_call_obligations: vec![],
            post_loop_call_obligations: vec![],
            loop_fields: LoopFields {
                invariants: vec![],
                per_loop_invariants: vec![],
                per_loop_variants: vec![],
                all_loop_spans: vec![],
                variants: vec![],
                loop_analysis: None,
                loop_obligation_groups: vec![],
            },
            mut_borrow: MutBorrowFields {
                mut_borrow_body: None,
                mut_ref_param_names: HashSet::new(),
                state_params: HashSet::new(),
                projected_final_pins: Vec::new(),
                stale_call_final_params: HashSet::new(),
            },
            reborrow_prophecy: None,
            returning_path_facts: vec![],
            extraction_fail_closed_reason: None,
            panic_unreachability_obligations: 0,
            user_written_false_obligations: 0,
            proved_dead_edges: Default::default(),
        }
    }

    /// `door_open@.len() == 100`
    fn door_open_len_invariant() -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "door_open".to_string(),
                    None,
                )))),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(100)),
        )
    }

    #[test]
    fn collect_free_var_names_excludes_bound_vars() {
        // forall<i: Int> i >= 0 && door_open@.len() == 100
        let expr = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("i".to_string(), None)),
                    BinOp::Ge,
                    Arc::new(PureExpr::Int(0)),
                )),
                BinOp::And,
                Arc::new(door_open_len_invariant()),
            )),
            triggers: vec![],
        };

        let mut names = HashSet::new();
        collect_free_var_names_into(&expr, &mut names);

        assert!(
            names.contains("door_open"),
            "free variable `door_open` should be collected"
        );
        assert!(
            !names.contains("i"),
            "bound variable `i` must NOT be collected as a free name"
        );
    }

    #[test]
    fn collect_contract_var_names_walks_loop_invariants() {
        // Place the 100doors invariant only in `loop_fields.invariants`; the
        // helper must still pick up `door_open` from there.
        let mut parsed = empty_parsed_contract();
        parsed
            .loop_fields
            .invariants
            .push(door_open_len_invariant());

        let names = collect_contract_var_names_in_parsed(&parsed);

        assert!(
            names.contains("door_open"),
            "loop invariant clause should contribute names to the contract set"
        );
    }

    #[test]
    fn collect_contract_var_names_walks_per_loop_invariants_and_variants() {
        // Per-loop invariants and per-loop variants (used by multi-loop
        // bodies like 100doors) must also contribute names.
        let mut parsed = empty_parsed_contract();
        parsed
            .loop_fields
            .per_loop_invariants
            .push((0, 10, vec![door_open_len_invariant()]));
        parsed.loop_fields.per_loop_variants.push((
            0,
            10,
            vec![PureExpr::Var("counter".to_string(), None)],
        ));

        let names = collect_contract_var_names_in_parsed(&parsed);

        assert!(
            names.contains("door_open"),
            "per-loop invariant names should be collected"
        );
        assert!(
            names.contains("counter"),
            "per-loop variant names should be collected"
        );
    }

    /// End-to-end at the rewrite layer: given the sort_map that Fix A
    /// produces for a `let mut door_open: Vec<bool>` local (i.e. a
    /// `Datatype("Vec")` entry under the local's source name), the
    /// contract rewrite pipeline must annotate every `Var("door_open", None)`
    /// — including inside an inherited loop invariant — with that sort.
    ///
    /// This is the property that drives the 100doors fix: once `door_open`
    /// carries `Datatype("Vec")` in the inherited inner-loop invariant,
    /// the bootstrap hint plan registers it as `Seq`, the encoder declares
    /// `door_open: Seq` (not `Int`), and `door_open@.len()` routes through
    /// `seq_len` instead of the `fset_len(Int)` UF fallback.
    #[test]
    fn vec_typed_local_in_invariant_picks_up_datatype_vec_annotation() {
        let vec_sort = ExprSort::Datatype(intern_sort_name("Vec"));
        let mut sort_map = HashMap::new();
        sort_map.insert("door_open".to_string(), vec_sort.clone());

        // Two clones of the same invariant — mirrors `inherit_outer_invariant`
        // copying the outer invariant into the inner loop's clause list.
        let outer = door_open_len_invariant();
        let inner_clone = outer.clone();

        let annotated_outer = annotate_var_sorts(&outer, &sort_map);
        let annotated_inner = annotate_var_sorts(&inner_clone, &sort_map);

        // Both clones now carry Datatype("Vec") on the `door_open` Var.
        let expected_var = PureExpr::Var("door_open".to_string(), Some(vec_sort.clone()));
        let expected = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(expected_var))),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(100)),
        );
        assert_eq!(annotated_outer, expected);
        assert_eq!(annotated_inner, expected);
    }

    /// Defensive: Names that are NOT in the sort map (e.g. locals not
    /// referenced by any contract clause) remain unannotated. This mirrors
    /// the `annotate_local_vars_from_mir` filter — only locals that appear
    /// in `contract_names` get a MIR-derived sort.
    #[test]
    fn local_not_in_sort_map_is_left_unannotated() {
        let mut sort_map = HashMap::new();
        sort_map.insert(
            "door_open".to_string(),
            ExprSort::Datatype(intern_sort_name("Vec")),
        );

        // `pass` is not in the sort_map (in 100doors it's the for-loop index,
        // an Int local). The rewrite must NOT invent a sort for it.
        let expr = PureExpr::Var("pass".to_string(), None);
        let annotated = annotate_var_sorts(&expr, &sort_map);
        assert_eq!(annotated, PureExpr::Var("pass".to_string(), None));
    }
}
