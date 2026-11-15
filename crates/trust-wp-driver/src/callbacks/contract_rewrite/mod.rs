// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract expression rewriting passes.
//!
//! Contains logic method call rewriting (user-defined logic methods -> LogicFnCall)
//! and newtype field-0 simplification (tuple_get_0(x) -> x for newtype params).

use std::collections::HashSet;

use super::parsing::ParsedContract;

mod constructed_invariant;
mod fmap_partition;
mod logic_methods;
mod named_fields;
mod newtype;
mod placement;
mod sort_annotations;

use constructed_invariant::unfold_constructed_invariant_obligations;
use fmap_partition::rewrite_parsed_contract_fmap_partition_get_some_invariants;
pub(in crate::callbacks) use logic_methods::rewrite_ref_deep_model_calls_expr;
pub(super) use logic_methods::{
    build_user_shadowed_builtins, receiver_root_var_name,
    rewrite_logic_fn_defs_shadowed_builtin_calls, rewrite_logic_method_calls_expr,
    UserShadowedBuiltins,
};
use logic_methods::{
    rewrite_parsed_contract_logic_method_calls, rewrite_parsed_contract_shadowed_builtin_calls,
    rewrite_ref_deep_model_calls_in_contract,
};
use named_fields::rewrite_named_field_access_in_contract;
#[cfg(test)]
use named_fields::{reorder_named_fields_to_positional, rewrite_named_struct_pattern};
pub(super) use named_fields::{
    rewrite_named_field_access_expr, FieldOrderRefusal, FieldOrderTables,
};
#[cfg(test)]
use newtype::is_newtype_param_expr;
pub(super) use newtype::simplify_newtype_field_access_expr;
use newtype::simplify_newtype_field_access_in_contract;
pub(super) use sort_annotations::{
    annotate_expr_with_param_sorts, annotate_exprs_with_param_sorts,
};
#[cfg(test)]
use sort_annotations::{
    annotate_var_sorts, erase_box_deref_expr, normalize_turbofish_logic_fn_expr,
};
use sort_annotations::{
    erase_box_deref_in_contract, normalize_turbofish_logic_fn_args,
    propagate_param_sort_annotations,
};

/// Place every named-field constructor and pattern in ONE specification
/// expression at its DECLARED indices, against the declarations in scope at
/// `def_id`.
///
/// This is the entry point for specification text that is NOT a function
/// contract — a `#[logic]` function body, a type-invariant body — and it is
/// the same kernel `rewrite_parsed_contract_structure` uses, reached by the
/// same route. Those two bodies never travel the contract path, so without
/// this entry point the encoder's placement gate refuses every such body that
/// names a constructor's fields. The gate exists because an unplaced `{a,b}`
/// constructor would otherwise be bound positionally in SOURCE order, and a
/// logic function would read a field it did not name (D-31;
/// `tests/adversarial/cases/s82v4_logicfn_body_named_literal.rs`,
/// `s82v4_typeinv_body_field_reorder.rs`).
///
/// The FLAT name→index map is deliberately EMPTY here. That table answers
/// "what index does this field NAME have" for a field ACCESS (`x.inner`), and
/// rewriting accesses is a separate pass with its own callers and its own
/// timing; this function must change nothing but the placement of named-field
/// constructors and patterns. `rewrite_named_field_access_expr` consults the
/// flat map only in the `__trust_wp_field_*` branch, so an empty one makes
/// that branch a no-op by construction rather than by promise.
///
/// Returns the placement refusal when the expression names a constructor no
/// declaration in scope answers for. The caller may leave the expression as
/// written: the encoder's placement gate refuses anything still carrying
/// metadata, so an unplaced body costs a proof, never a wrong verdict.
pub(crate) fn place_named_field_ctors_in_expr(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    expr: &trust_wp_core::formula::PureExpr,
) -> Result<trust_wp_core::formula::PureExpr, FieldOrderRefusal> {
    // Nothing to place, and no table to build. The overwhelming majority of
    // specification expressions take this exit.
    if trust_wp_core::formula::first_unplaced_named_ctor(expr).is_none() {
        return Ok(expr.clone());
    }
    let ctors = super::struct_field_map::build_ctor_field_order(tcx, def_id);
    let flat = std::collections::HashMap::new();
    rewrite_named_field_access_expr(expr, FieldOrderTables::new(&flat, &ctors))
}

/// Apply all structural rewrites to a parsed contract before verification (#1526 Phase 5).
///
/// Bundles four rewriting passes that transform parsed contract expressions
/// to align with MIR-level representations:
///
/// 1. **Type invariant method rewriting** - `invariant()` -> type-qualified methods (#666)
/// 2. **Logic method call rewriting** - user-defined methods -> `LogicFnCall` nodes
/// 3. **Newtype field-0 simplification** - `tuple_get_0(x)` -> `x` for newtype params (#359)
/// 4. **Named struct field rewriting** - `__trust_wp_field_<name>` -> `__trust_wp_tuple_get_<index>` (#717)
///
/// The newtype simplification runs twice: once after the initial parse and again
/// after named-field rewriting (which can introduce new `tuple_get_0(result)` for
/// singleton outputs, #940).
pub(super) fn rewrite_parsed_contract_structure(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    parsed: &mut ParsedContract,
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
    logic_method_names: &HashSet<String>,
    user_shadowed_builtins: &UserShadowedBuiltins,
) -> Result<(), FieldOrderRefusal> {
    // Step 1: Type invariant method rewriting (#666).
    let (param_invariant_methods, result_invariant_method) =
        super::type_invariants::build_type_invariant_method_map(
            tcx,
            def_id,
            &parsed.arg_names,
            type_invariant_defs,
        );
    let (param_structural_exprs, result_structural_expr) =
        super::type_invariants::build_type_invariant_structural_expr_map(
            tcx,
            def_id,
            &parsed.arg_names,
            type_invariant_defs,
        );
    super::type_invariants::rewrite_parsed_contract_type_invariant_methods_with_structural(
        parsed,
        &param_invariant_methods,
        result_invariant_method.as_deref(),
        &param_structural_exprs,
        result_structural_expr.as_ref(),
    );

    // Step 2: Logic method call rewriting.
    rewrite_parsed_contract_logic_method_calls(parsed, logic_method_names);

    // Step 2b: Sort annotation propagation (#994).
    // Newtype field-0 simplification needs to distinguish by-value newtypes
    // from `&mut Newtype` params before it decides whether `tuple_get_0(x)` is
    // identity or a projection through `*x`.
    propagate_param_sort_annotations(tcx, def_id, parsed);

    // Step 2c: User-shadowed builtin method rewriting (list_reversal_lasso).
    // `recv.index_logic(i)` / `recv[i]` on an ADT with a USER #[logic] trait
    // impl routes to LogicFnCall so the encoder emits the impl's defining
    // forall. Requires Step 2b sorts; must precede Step 3 so `x.0` field
    // projections have not been collapsed onto the ADT var.
    rewrite_parsed_contract_shadowed_builtin_calls(parsed, user_shadowed_builtins);

    // Step 3: Newtype field-0 simplification (#359).
    let mut newtype_params = super::type_invariants::build_newtype_param_set(
        tcx,
        def_id,
        &parsed.arg_names,
        type_invariant_defs,
    );
    // Extend newtype set to include call result variables (call_N) whose return
    // types are single-field structs. The main extraction pipeline gives these
    // call results Datatype sorts, but build_newtype_param_set only inspects the
    // function signature. Without this, call_assumptions retain
    // `tuple_get_0(call_N)` while the variant expression (which references a
    // parameter) gets simplified to drop `tuple_get_0`, causing a mismatch in
    // recursive variant decrease proofs.
    extend_newtype_params_for_call_results(tcx, def_id, &mut newtype_params);
    simplify_newtype_field_access_in_contract(parsed, &newtype_params);

    // Step 4: Named struct field rewriting (#717), and placement of
    // named-field constructors and patterns at their DECLARED indices (D-31).
    let struct_field_map = super::struct_field_map::build_struct_field_map(tcx, def_id);
    let ctor_field_order = super::struct_field_map::build_ctor_field_order(tcx, def_id);
    let tables = FieldOrderTables::new(&struct_field_map, &ctor_field_order);
    rewrite_named_field_access_in_contract(parsed, tables)?;

    // Step 4b: Re-run newtype simplification after named-field rewrite (#940).
    // Named-field rewrite can introduce `tuple_get_0(result)` for singleton outputs.
    simplify_newtype_field_access_in_contract(parsed, &newtype_params);

    // Step 4c: Unfold a call-site invariant OBLIGATION over an aggregate the
    // caller built. `inv` is defined as its body, so this changes no
    // obligation's strength; it changes whether the obligation can be
    // discharged at all, because the defining instance reaches only a receiver
    // the caller already holds `inv` of (D-63). Runs after the named-field and
    // newtype rewrites so the body it splices in is in the same form as
    // everything around it, and before sort propagation so the splice is
    // annotated with the rest.
    unfold_constructed_invariant_obligations(parsed, type_invariant_defs);

    // Step 5: Re-run sort annotation propagation after structural rewrites.
    // Parsed contract expressions have `None` sort on Var nodes because the
    // contract parser operates on text without type information. Propagate
    // MIR-derived ExprSort annotations onto parameter and result Var nodes
    // so the ay encoder's predeclare pass can assign correct sorts.
    propagate_param_sort_annotations(tcx, def_id, parsed);
    normalize_turbofish_logic_fn_args(parsed);
    rewrite_ref_deep_model_calls_in_contract(parsed);

    // Step 5b: Erase Box deref in contracts (#3323).
    // Box<T> is transparent — ty_to_expr_sort_enriched peels it, so a
    // Box<&mut i32> param gets ExprSort::MutRef(Int). The contract parser
    // sees `*x` and emits Deref(Var("x")), but since the sort already
    // reflects the inner type, this extra Deref layer is spurious. Erase
    // it so the encoder doesn't interpret it as a MutRef deref.
    erase_box_deref_in_contract(tcx, def_id, parsed);

    // Step 6: Lower the exact two-variable FMap partition shape from
    // `ghost/fmap_iter.rs` into an equivalent single-key invariant.
    // This avoids a constructor-heavy `(get(k) == Some(v))` quantifier pair
    // when the contract is really expressing per-key contains/lookup
    // partition facts. (#2116)
    rewrite_parsed_contract_fmap_partition_get_some_invariants(parsed);

    Ok(())
}

/// Extend the newtype_params set to include `call_N` variables for Call
/// terminators in the MIR body whose return type is a single-field struct.
///
/// Without this, the newtype simplification only covers function parameters
/// and the `result` variable (from `build_newtype_param_set`), leaving
/// intermediate call results like `call_4` un-simplified. This causes a
/// mismatch when the variant expression (which references a parameter)
/// gets its `tuple_get_0` simplified away while the call_assumption (which
/// references the call result) retains it.
fn extend_newtype_params_for_call_results(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    newtype_params: &mut HashSet<String>,
) {
    use rustc_middle::{mir::TerminatorKind, ty::TyKind};

    let local_def_id = match def_id.as_local() {
        Some(id) => id,
        None => return,
    };
    if !tcx.is_mir_available(def_id) {
        return;
    }
    // Guard: skip bodyless trait method declarations (same as recursive_verify).
    if let rustc_hir::Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
        if matches!(
            item.kind,
            rustc_hir::TraitItemKind::Fn(_, rustc_hir::TraitFn::Required(_))
        ) {
            return;
        }
    }
    let root = tcx.typeck_root_def_id(def_id).expect_local();
    let _ = tcx.mir_borrowck(root);

    let body_with_facts = super::try_get_body_with_context(tcx, local_def_id);
    let Some(body_with_facts) = body_with_facts else {
        return;
    };
    let body = super::super::mir_analysis::get_mir_body(&body_with_facts);
    for bb_data in body.basic_blocks.iter() {
        let Some(ref terminator) = bb_data.terminator else {
            continue;
        };
        if let TerminatorKind::Call { destination, .. } = &terminator.kind {
            if !destination.projection.is_empty() {
                continue;
            }
            let dest_ty = body.local_decls[destination.local].ty;
            let inner_ty = match dest_ty.kind() {
                TyKind::Ref(_, inner, _) => *inner,
                _ => dest_ty,
            };
            if let TyKind::Adt(adt_def, _) = inner_ty.kind() {
                let is_single_field = adt_def.is_struct()
                    && adt_def
                        .variants()
                        .iter()
                        .next()
                        .is_some_and(|v| v.fields.len() == 1);
                if is_single_field {
                    newtype_params.insert(format!("$call_{}", destination.local.as_u32()));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
