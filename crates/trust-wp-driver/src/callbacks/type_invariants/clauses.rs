// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type invariant clause generation for verification and contract rewriting.
//!
//! Builds per-parameter and result invariant method mappings, newtype parameter
//! sets, and full pre/postcondition clause lists from function signatures and
//! type invariant definitions.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::{def_id::DefId, Attribute};
use rustc_middle::ty::{TyCtxt, TyKind};
use trust_wp_core::{
    closure::{CaptureField, ClosureCaptureInfo},
    formula::{
        internal::tuple_lowering::tuple_field_logic_fn_name, resolve_sort_name, ExprSort, PureExpr,
    },
    logic::{type_invariant_method_name, TypeInvariantDef},
};

use super::lookup::{
    adt_invariant_method_name, build_enum_invariant_match_arms, build_structural_invariant_expr,
    has_trivial_type_invariant,
};
use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

/// Build per-parameter and result invariant method mappings for a function.
///
/// Returns:
/// - `param_methods`: argument name -> qualified invariant method
/// - `result_method`: qualified invariant method for return type, if any
pub(in crate::callbacks) fn build_type_invariant_method_map(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
) -> (HashMap<String, String>, Option<String>) {
    if type_invariant_defs.is_empty() {
        return (HashMap::new(), None);
    }

    // Closures don't support fn_sig() — their signature must be retrieved
    // via args.as_closure().sig(). Since closures capture variables rather
    // than taking struct-typed parameters, type invariant method rewriting
    // does not apply. Return empty mappings.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return (HashMap::new(), None);
    }

    let invariant_type_names: HashSet<String> = type_invariant_defs
        .iter()
        .map(|d| d.type_name().to_string())
        .collect();

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();
    let output = sig.output();

    let mut param_methods = HashMap::new();
    for (i, ty) in inputs.iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        let arg_name = &arg_names[i];

        let inner_ty = match ty.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            _ => *ty,
        };
        if has_trivial_type_invariant(inner_ty) {
            continue;
        }
        let method_name = match inner_ty.kind() {
            // Only map parameters whose type has an explicit/synthetic invariant
            // definition. Transitive structural wrappers are not yet implemented,
            // and mapping `inv(x)` for them creates vacuous P=>P obligations (#886).
            TyKind::Adt(adt_def, _) => {
                adt_invariant_method_name(tcx, *adt_def, &invariant_type_names)
            }
            _ => None,
        };
        let Some(method_name) = method_name else {
            continue;
        };
        param_methods.insert(arg_name.clone(), method_name.clone());
    }

    let inner_output = match output.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => output,
    };
    let result_method = if has_trivial_type_invariant(inner_output) {
        None
    } else {
        match inner_output.kind() {
            TyKind::Adt(adt_def, _) => {
                adt_invariant_method_name(tcx, *adt_def, &invariant_type_names)
            }
            _ => None,
        }
    };

    (param_methods, result_method)
}

/// Build structural invariant expressions for parameters/result that do not
/// have a direct invariant method mapping.
pub(in crate::callbacks) fn build_type_invariant_structural_expr_map(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
) -> (HashMap<String, PureExpr>, Option<PureExpr>) {
    if type_invariant_defs.is_empty() {
        return (HashMap::new(), None);
    }
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return (HashMap::new(), None);
    }

    let invariant_type_names: HashSet<String> = type_invariant_defs
        .iter()
        .map(|d| d.type_name().to_string())
        .collect();
    let (param_methods, result_method) =
        build_type_invariant_method_map(tcx, def_id, arg_names, type_invariant_defs);

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();

    let mut param_structural = HashMap::new();
    for (i, ty) in sig.inputs().iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        let arg_name = &arg_names[i];
        if param_methods.contains_key(arg_name) {
            continue;
        }

        let receiver = PureExpr::Var(arg_name.clone(), ty_to_expr_sort_enriched(tcx, *ty));
        let Some(expr) = build_structural_invariant_expr(tcx, *ty, receiver, &invariant_type_names)
        else {
            continue;
        };
        if !matches!(expr, PureExpr::Bool(true)) {
            param_structural.insert(arg_name.clone(), expr);
        }
    }

    let result_structural = if result_method.is_some() {
        None
    } else {
        let receiver = PureExpr::Var(
            "result".to_string(),
            ty_to_expr_sort_enriched(tcx, sig.output()),
        );
        build_structural_invariant_expr(tcx, sig.output(), receiver, &invariant_type_names)
            .filter(|expr| !matches!(expr, PureExpr::Bool(true)))
    };

    (param_structural, result_structural)
}

/// Re-rewrite synthesized `inv(x)` `LogicFnCall`s into type-qualified
/// `MethodCall`s on already-transformed effective requires/ensures, then
/// discharge the residual trivial `inv(arg)` reborrow side-conditions to `true`.
///
/// `transform_contract` injects `LogicFnCall { name: "inv", ... }` preconditions
/// for `&mut` params AFTER `rewrite_parsed_contract_structure` has already run,
/// so without this second pass the synthesized preconditions keep using the bare
/// `logic_inv` SMT symbol while postconditions on `^x.invariant()` use the
/// type-qualified `method___trust_wp_invariant_<Type>` symbol — the two are
/// disconnected and the body axiom never bridges them, leaving `inv(x_final)` an
/// opaque UF and causing a spurious postcondition failure (partially_opaque #1,
/// 3b0a27b; should_fail lane confirmed false_accept_count = 0).
///
/// After the type-qualified rewrite, any bare `inv(arg)` / `inv(*arg)` left over
/// in the *requires* has a root with no registered invariant (e.g. a primitive
/// `&mut i32`, or `&mut &mut i32`): its faithful Creusot semantics is `true`.
/// Without discharging it, the encoder lowers the bare call to an unconstrained
/// placeholder UF and asserting it as a precondition trips ay's model-validation
/// guard, degrading the obligation to `Unknown`. The discharge is applied to the
/// *requires* only (the injection is requires-only), so it merely removes an
/// uninterpretable assumption — sound by construction (#8373).
pub(in crate::callbacks) fn rewrite_synthesized_invariant_calls(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
    effective_requires: &mut [PureExpr],
    effective_ensures: &mut [PureExpr],
) {
    let (param_methods, result_method) =
        build_type_invariant_method_map(tcx, def_id, arg_names, type_invariant_defs);
    let (structural_param_exprs, structural_result_expr) =
        build_type_invariant_structural_expr_map(tcx, def_id, arg_names, type_invariant_defs);

    // Only the *rewrite* is guarded on having something to rewrite; the trivial
    // discharge below still runs (with possibly-empty maps) for every contract.
    if !param_methods.is_empty()
        || result_method.is_some()
        || !structural_param_exprs.is_empty()
        || structural_result_expr.is_some()
    {
        for expr in effective_requires
            .iter_mut()
            .chain(effective_ensures.iter_mut())
        {
            *expr = super::rewrite::rewrite_type_invariant_methods_expr_with_structural(
                expr,
                &param_methods,
                result_method.as_deref(),
                &structural_param_exprs,
                structural_result_expr.as_ref(),
            );
        }
    }

    // Roots with no registered invariant after the rewrite: every arg (plus
    // `result`) minus the ones the maps just qualified. The leftover bare
    // `inv(root)` on these is trivially `true` (#8373).
    let mut known_trivial_roots: HashSet<String> = arg_names.iter().cloned().collect();
    known_trivial_roots.insert("result".to_string());
    for method_root in param_methods.keys() {
        known_trivial_roots.remove(method_root);
    }
    for structural_root in structural_param_exprs.keys() {
        known_trivial_roots.remove(structural_root);
    }
    if result_method.is_some() || structural_result_expr.is_some() {
        known_trivial_roots.remove("result");
    }
    for expr in effective_requires.iter_mut() {
        *expr = super::rewrite::discharge_trivial_inv_calls_expr(expr, &known_trivial_roots);
    }
}

/// Build a set of parameter names whose types have newtype invariants.
///
/// For newtype invariant types (single-field structs), field-0 access in the
/// logical domain is identity: `x.0 == x`. This set identifies which params
/// need their tuple_get_0 calls simplified away before verification (#359).
pub(in crate::callbacks) fn build_newtype_param_set(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
) -> HashSet<String> {
    // Closures don't support fn_sig(); return empty set.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return HashSet::new();
    }
    let newtype_type_names: HashSet<String> = type_invariant_defs
        .iter()
        .filter(|d| d.is_newtype())
        .map(|d| d.type_name().to_string())
        .collect();

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();

    // `def_path_str` returns unqualified names for local items (e.g.,
    // "NonZeroU32"), but `newtype_type_names` may contain crate-qualified
    // names (e.g., "creusot_test::NonZeroU32"). Check both forms. (#2341)
    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);

    let mut newtype_params = HashSet::new();
    for (i, ty) in inputs.iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        let inner_ty = match ty.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            _ => *ty,
        };
        if let TyKind::Adt(adt_def, _) = inner_ty.kind() {
            let type_name = super::lookup::adt_type_path(tcx, *adt_def);
            let qualified_type_name = format!("{crate_name}::{type_name}");
            // #2004: Apply the same single-field struct check used for return
            // types. Without this, contracts referencing `self.0@` produce
            // `tuple_get_0(self)` (uninterpreted function) while the MIR body
            // produces `Var("self.0")` — two disconnected SMT variables. The
            // newtype simplification collapses both to `self`, fixing the
            // divergence for single-field struct parameters.
            let is_single_field_struct = adt_def.is_struct()
                && adt_def
                    .variants()
                    .iter()
                    .next()
                    .is_some_and(|variant| variant.fields.len() == 1);
            let keeps_native_adt_sort = matches!(
                ty_to_expr_sort_enriched(tcx, inner_ty),
                Some(ExprSort::Datatype(_))
            );
            // Single-field structs bypass the keeps_native_adt_sort guard (#2669):
            // MIR-level aggregate collapse (`Self(n)` → `n`) produces scalar
            // return expressions, so field access must also be simplified to
            // scalars. Without this, `Var("self.0")` from closure-capture-style
            // field projection stays disconnected from the `self` variable.
            if is_single_field_struct
                || (!keeps_native_adt_sort
                    && (newtype_type_names.contains(&type_name)
                        || newtype_type_names.contains(&qualified_type_name)))
            {
                newtype_params.insert(arg_names[i].clone());
            }
        }
    }

    // Also check return type -- "result" is a newtype param too.
    //
    // #940: `translate_rvalue` currently collapses single-field ADT aggregates
    // to their inner expression. When contracts reference `result.field`, named
    // field rewrite produces `tuple_get_0(result)`, which must simplify back to
    // `result` for singleton outputs to stay provable end-to-end.
    let output = sig.output();
    let inner_output = match output.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => output,
    };
    if let TyKind::Adt(adt_def, _) = inner_output.kind() {
        let type_name = super::lookup::adt_type_path(tcx, *adt_def);
        let qualified_type_name = format!("{crate_name}::{type_name}");
        let is_single_field_struct = adt_def.is_struct()
            && adt_def
                .variants()
                .iter()
                .next()
                .is_some_and(|variant| variant.fields.len() == 1);
        let keeps_native_adt_sort = matches!(
            ty_to_expr_sort_enriched(tcx, inner_output),
            Some(ExprSort::Datatype(_))
        );
        // Single-field structs bypass the keeps_native_adt_sort guard (#2669),
        // matching the parameter-side fix above.
        if is_single_field_struct
            || (!keeps_native_adt_sort
                && (newtype_type_names.contains(&type_name)
                    || newtype_type_names.contains(&qualified_type_name)))
        {
            newtype_params.insert("result".to_string());
        }
    }

    newtype_params
}

/// Check if a function has the `open_inv_result` marker (#2552).
///
/// Suppresses the type invariant postcondition on the return value.
/// Detects both:
/// - Native trust-wp: `#[doc = "trust-wp:open_inv_result:"]` (from proc macro)
/// - Compat: `#[creusot::open_inv_result]` (tool attribute via harness rewrite)
fn has_open_inv_result(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    for attr in tcx.get_all_attrs(def_id) {
        // Check doc marker (native trust-wp proc macro path)
        if let Some(value) = crate::attr_utils::doc_marker_str(attr) {
            if value.as_str() == "trust-wp:open_inv_result:" {
                return true;
            }
        }
        // Check tool attribute (compat harness path)
        if let Attribute::Unparsed(item) = attr {
            // Trust: AttrPath.segments is now Box<[Symbol]>; s is a &Symbol directly.
            let segments: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
            if segments == ["creusot", "open_inv_result"] {
                return true;
            }
        }
    }
    false
}

/// Build type invariant preconditions and postconditions for a function (#359).
pub(in crate::callbacks) fn build_type_invariant_clauses(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
) -> (Vec<PureExpr>, Vec<PureExpr>) {
    if type_invariant_defs.is_empty() {
        return (vec![], vec![]);
    }
    // Closures don't support fn_sig(); return empty clauses.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return (vec![], vec![]);
    }

    let invariant_type_names: HashSet<String> = type_invariant_defs
        .iter()
        .map(|d| d.type_name().to_string())
        .collect();

    let (param_methods, result_method) =
        build_type_invariant_method_map(tcx, def_id, arg_names, type_invariant_defs);
    let (structural_param_exprs, structural_result_expr) =
        build_type_invariant_structural_expr_map(tcx, def_id, arg_names, type_invariant_defs);

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();

    let mut invariant_requires = Vec::new();
    let mut invariant_ensures = Vec::new();
    let mut existing_structural_requires = HashSet::new();

    // --- Direct ADT parameters (existing logic) ---
    for (i, ty) in inputs.iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        let arg_name = &arg_names[i];
        let Some(method_name) = param_methods.get(arg_name) else {
            continue;
        };

        let is_mut_ref = matches!(
            ty.kind(),
            TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        );
        let sort = ty_to_expr_sort_enriched(tcx, *ty);
        let receiver = if is_mut_ref {
            PureExpr::Deref(Arc::new(PureExpr::Var(arg_name.clone(), sort)))
        } else {
            PureExpr::Var(arg_name.clone(), sort)
        };

        invariant_requires.push(PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method_name.clone(),
            args: vec![],
        });
    }

    // For &mut parameters, inject `(^x).invariant()` as a postcondition.
    // This encodes the Creusot semantics: when a mutable borrow resolves,
    // the final (prophetic) value must also satisfy the type invariant.
    for (i, ty) in inputs.iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        let is_mut_ref = matches!(
            ty.kind(),
            TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        );
        if !is_mut_ref {
            continue;
        }
        let arg_name = &arg_names[i];
        let Some(method_name) = param_methods.get(arg_name) else {
            continue;
        };
        let sort = ty_to_expr_sort_enriched(tcx, *ty);
        invariant_ensures.push(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                arg_name.clone(),
                sort,
            )))),
            method: method_name.clone(),
            args: vec![],
        });
    }

    // --- Tuple parameter field decomposition (#946) ---
    //
    // For tuple parameters like `x: (NonZero, &mut NonZero)`, decompose into
    // per-field invariant clauses. Each field whose inner type (after reference
    // peeling) is an ADT with an invariant definition gets a precondition.
    // Fields that are `&mut T` also get a postcondition on the final value.
    for (i, ty) in inputs.iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        let arg_name = &arg_names[i];
        // Peel one level of reference for &(A, B) or &mut (A, B)
        let inner_ty = match ty.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            _ => *ty,
        };
        let TyKind::Tuple(fields) = inner_ty.kind() else {
            continue;
        };
        let param_is_ref = matches!(ty.kind(), TyKind::Ref(_, _, _));

        for (field_idx, field_ty) in fields.iter().enumerate() {
            let field_is_ref = matches!(field_ty.kind(), TyKind::Ref(_, _, _));
            let field_is_mut_ref = matches!(
                field_ty.kind(),
                TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            );
            let inner_field_ty = match field_ty.kind() {
                TyKind::Ref(_, inner, _) => *inner,
                _ => field_ty,
            };
            if has_trivial_type_invariant(inner_field_ty) {
                continue;
            }
            let method_name = match inner_field_ty.kind() {
                TyKind::Adt(adt_def, _) => {
                    adt_invariant_method_name(tcx, *adt_def, &invariant_type_names)
                }
                _ => None,
            };
            let Some(method_name) = method_name else {
                continue;
            };

            // Build field access: tuple_get_N(x) for by-value tuples and
            // tuple_get_N(*x) for referenced tuples (& / &mut).
            let param_sort = ty_to_expr_sort_enriched(tcx, *ty);
            let param_expr = if param_is_ref {
                PureExpr::Deref(Arc::new(PureExpr::Var(arg_name.clone(), param_sort)))
            } else {
                PureExpr::Var(arg_name.clone(), param_sort)
            };
            let field_access = PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(field_idx),
                args: vec![param_expr],
            };

            // Precondition: for reference fields (& / &mut), dereference to
            // apply the invariant to the referent value.
            let precondition_receiver = if field_is_ref {
                PureExpr::Deref(Arc::new(field_access.clone()))
            } else {
                field_access.clone()
            };
            existing_structural_requires.insert(arg_name.clone());
            invariant_requires.push(PureExpr::MethodCall {
                receiver: Arc::new(precondition_receiver),
                method: method_name.clone(),
                args: vec![],
            });

            // Postcondition: for &mut fields, require (^field).invariant()
            if field_is_mut_ref {
                let final_receiver = PureExpr::Final(Arc::new(field_access));
                invariant_ensures.push(PureExpr::MethodCall {
                    receiver: Arc::new(final_receiver),
                    method: method_name,
                    args: vec![],
                });
            }
        }
    }

    // --- Enum parameter structural decomposition (#2568) ---
    //
    // For enum parameters like `x: Result<NonZero, E>`, generate a match-based
    // invariant that propagates to per-variant payload invariants:
    //   match x { Ok(v) => inv_NonZero(v), Err(e) => inv_E(e) }
    for (i, ty) in inputs.iter().enumerate() {
        if i >= arg_names.len() {
            break;
        }
        let arg_name = &arg_names[i];
        if param_methods.contains_key(arg_name) {
            continue;
        }

        let (inner_ty, param_is_ref) = match ty.kind() {
            TyKind::Ref(_, inner, _) => (*inner, true),
            _ => (*ty, false),
        };
        let TyKind::Adt(adt_def, substs) = inner_ty.kind() else {
            continue;
        };
        if !adt_def.is_enum() {
            continue;
        }

        let arms = build_enum_invariant_match_arms(tcx, *adt_def, substs, &invariant_type_names);
        if arms.is_empty() {
            continue;
        }

        let param_sort = ty_to_expr_sort_enriched(tcx, *ty);
        let scrutinee = if param_is_ref {
            PureExpr::Deref(Arc::new(PureExpr::Var(arg_name.clone(), param_sort)))
        } else {
            PureExpr::Var(arg_name.clone(), param_sort)
        };
        existing_structural_requires.insert(arg_name.clone());
        invariant_requires.push(PureExpr::Match {
            scrutinee: Arc::new(scrutinee),
            arms,
        });
    }

    for arg_name in arg_names {
        if param_methods.contains_key(arg_name) || existing_structural_requires.contains(arg_name) {
            continue;
        }
        if let Some(expr) = structural_param_exprs.get(arg_name) {
            invariant_requires.push(expr.clone());
        }
    }

    if !has_open_inv_result(tcx, def_id) {
        if let Some(method_name) = result_method {
            let result_sort = ty_to_expr_sort_enriched(tcx, sig.output());
            invariant_ensures.push(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("result".to_string(), result_sort)),
                method: method_name,
                args: vec![],
            });
        } else if let Some(expr) = structural_result_expr {
            invariant_ensures.push(expr);
        }
    }

    (invariant_requires, invariant_ensures)
}

/// Build type invariant preconditions for closure capture variables (#2257).
///
/// For each closure captured by the parent function, checks each capture field
/// against the known type invariant definitions. When a field's `ExprSort`
/// resolves to a type with a non-trivial invariant, emits `inv_T(field_name)`
/// as a precondition assumption.
///
/// This replaces the ay-side `inject_closure_capture_type_invariants()` in
/// bootstrap.rs by moving the synthesis to the driver's clause enrichment
/// layer, matching the Creusot architectural pattern where closure invariant
/// decomposition happens during translation rather than backend bootstrap.
pub(in crate::callbacks) fn build_closure_capture_invariant_requires(
    closure_capture_infos: &[ClosureCaptureInfo],
    type_invariant_defs: &[TypeInvariantDef],
) -> Vec<PureExpr> {
    build_closure_capture_invariant_requires_with_receiver_names(
        closure_capture_infos,
        type_invariant_defs,
        |_: &ClosureCaptureInfo, _: usize, field: &CaptureField| Some(field.name().to_string()),
    )
}

/// Build current-closure type invariant preconditions over `self.N` projections.
///
/// For the closure currently being verified, explicit contract clauses are
/// rewritten to refer to captures as `self.0`, `self.1`, ... rather than their
/// outer source names. This helper mirrors that representation so the injected
/// invariant assumptions constrain the same terms used by closure contracts.
pub(in crate::callbacks) fn build_current_closure_self_invariant_requires(
    closure_capture_infos: &[ClosureCaptureInfo],
    type_invariant_defs: &[TypeInvariantDef],
) -> Vec<PureExpr> {
    build_closure_capture_invariant_requires_with_receiver_names(
        closure_capture_infos,
        type_invariant_defs,
        |info: &ClosureCaptureInfo, capture_idx: usize, _: &CaptureField| {
            matches!(info.param_name(), Some("self")).then(|| format!("self.{capture_idx}"))
        },
    )
}

fn build_closure_capture_invariant_requires_with_receiver_names<F>(
    closure_capture_infos: &[ClosureCaptureInfo],
    type_invariant_defs: &[TypeInvariantDef],
    mut receiver_name_for: F,
) -> Vec<PureExpr>
where
    F: FnMut(&ClosureCaptureInfo, usize, &CaptureField) -> Option<String>,
{
    if type_invariant_defs.is_empty() || closure_capture_infos.is_empty() {
        return Vec::new();
    }

    let invariant_type_names: HashSet<String> = type_invariant_defs
        .iter()
        .map(|d| d.type_name().to_string())
        .collect();

    let mut requires = Vec::new();
    let mut seen: HashSet<(String, String)> = HashSet::new();

    for info in closure_capture_infos {
        for (capture_idx, field) in info.captures().iter().enumerate() {
            let Some(type_name) = capture_field_type_name(field.sort()) else {
                continue;
            };

            // Find matching invariant definition.
            let matching_inv = type_invariant_defs
                .iter()
                .find(|inv| inv.type_name() == type_name);

            // Also check with crate-qualified suffix matching, mirroring
            // the pattern in adt_invariant_method_name.
            let matching_inv = matching_inv.or_else(|| {
                if type_name.contains("::") {
                    return None;
                }
                let suffix = format!("::{type_name}");
                type_invariant_defs
                    .iter()
                    .find(|inv| inv.type_name().ends_with(&suffix))
            });

            let Some(inv_def) = matching_inv else {
                continue;
            };

            // Skip trivial invariants (body == true).
            if matches!(inv_def.body(), PureExpr::Bool(true)) {
                continue;
            }

            let method_name = if invariant_type_names.contains(&type_name) {
                type_invariant_method_name(&type_name)
            } else {
                // Use the invariant def's own type_name for the method
                // (handles crate-qualified matching).
                type_invariant_method_name(inv_def.type_name())
            };

            let Some(receiver_name) = receiver_name_for(info, capture_idx, field) else {
                continue;
            };

            // Deduplicate: same receiver variable + same method across closures.
            let key = (receiver_name.clone(), method_name.clone());
            if seen.contains(&key) {
                continue;
            }
            seen.insert(key);

            // Preserve the capture's actual logical sort so the injected
            // receiver does not fall back to Int in closure contexts (#2257).
            let var_sort = Some(field.sort().clone());

            requires.push(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var(receiver_name, var_sort)),
                method: method_name,
                args: vec![],
            });
        }
    }

    requires
}

/// Extract the type name from a capture field's `ExprSort`, peeling
/// reference wrappers.
///
/// - `Datatype(id)` → `Some(resolve_sort_name(id))`
/// - `Ref(Datatype(id))` / `MutRef(Datatype(id))` → `Some(resolve_sort_name(id))`
/// - Nested `Ref`/`MutRef` wrappers are peeled recursively. Without this,
///   a closure that re-captures an already-by-ref variable from a parent
///   closure (so `sort = Ref(Ref(Datatype("Zero")))`) silently drops the
///   capture invariant and the inner `proof_assert!(y.0@ == 0)` has no
///   evidence to discharge (closures/10_tyinv).
/// - Anything else → `None`
fn capture_field_type_name(sort: &ExprSort) -> Option<String> {
    match sort {
        ExprSort::Datatype(id) => Some(resolve_sort_name(*id)),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => capture_field_type_name(inner),
        _ => None,
    }
}
