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

use rustc_attr_ir::Attribute;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Mutability, Ty, TyCtxt, TyKind};
use trust_wp_core::{
    closure::{CaptureField, CaptureInvariant, ClosureCaptureInfo},
    formula::{
        internal::tuple_lowering::tuple_field_logic_fn_name, resolve_sort_name, ExprSort, PureExpr,
    },
    logic::{type_invariant_method_name, TypeInvariantDef},
};

use super::lookup::{
    adt_invariant_method_name, adt_method_states_every_part, build_enum_invariant_match_arms,
    build_structural_invariant_expr, has_trivial_type_invariant, may_carry_invariant,
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
        let Some(method_name) = direct_invariant_method(tcx, *ty, &invariant_type_names) else {
            continue;
        };
        param_methods.insert(arg_name.clone(), method_name);
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

/// The invariant method of the ADT a value of `ty` is, by value or behind one
/// reference.
///
/// Only a type with an explicit or synthetic invariant definition has one:
/// transitive structural wrappers are stated by the structural pass instead,
/// and mapping `inv(x)` for them creates vacuous P=>P obligations (#886).
fn direct_invariant_method(
    tcx: TyCtxt<'_>,
    ty: Ty<'_>,
    invariant_type_names: &HashSet<String>,
) -> Option<String> {
    let inner_ty = match ty.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => ty,
    };
    if has_trivial_type_invariant(inner_ty) {
        return None;
    }
    match inner_ty.kind() {
        TyKind::Adt(adt_def, _) => adt_invariant_method_name(tcx, *adt_def, invariant_type_names),
        _ => None,
    }
}

/// Everything the parameter-clause builder states about ONE parameter from
/// its type alone, pass by pass.
///
/// A body holds `direct`, `type_param`, `tuple_fields`, `enum_payloads` and
/// `structural` as its premise about the parameter. A call that fixes a type
/// parameter to this type owes the same clauses over the value it hands in
/// (`type_param_invariant_at`), and it may owe them only when
/// `states_every_part` holds; otherwise it refuses.
pub(super) struct ParamClauses {
    /// The method of the ADT the value is, by value or behind a reference.
    direct_method: Option<String>,
    direct: Option<PureExpr>,
    type_param: Option<PureExpr>,
    tuple_fields: Vec<PureExpr>,
    /// `inv(^field)` of each `&mut` field the tuple pass states: goals of the
    /// body, never part of its premise.
    tuple_field_final_goals: Vec<PureExpr>,
    enum_payloads: Option<PureExpr>,
    structural: Option<PureExpr>,
    /// Nothing inside the value that may carry an invariant was passed over
    /// by the clauses above. A generic hop at a type where this is false
    /// would owe less than a body entered at that type may be granted.
    pub(super) states_every_part: bool,
}

impl ParamClauses {
    /// The premise clauses, in pass order.
    pub(super) fn premise(&self) -> Vec<PureExpr> {
        self.direct
            .iter()
            .chain(&self.type_param)
            .chain(&self.tuple_fields)
            .chain(&self.enum_payloads)
            .chain(&self.structural)
            .cloned()
            .collect()
    }
}

/// What the parameter-clause builder states about a parameter of type `ty`
/// whose value is `receiver`.
///
/// THE one reading of a parameter's type invariant. The builder states each
/// parameter's premise with it, and a call that fixes a type parameter states
/// the clause it owes with it, over the value it hands in. The completeness
/// flag is computed where each pass states or passes over a part, so it cannot
/// describe a decomposition other than the one these clauses make.
pub(super) fn param_clauses<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    receiver: &PureExpr,
    invariant_type_names: &HashSet<String>,
) -> ParamClauses {
    let (inner_ty, reference) = match ty.kind() {
        TyKind::Ref(_, inner, mutability) => (*inner, Some(*mutability)),
        _ => (ty, None),
    };
    let through_reference = || PureExpr::Deref(Arc::new(receiver.clone()));
    // A shared reference is transparent; a `&mut` is stated about its referent.
    let referent = || {
        if reference == Some(Mutability::Mut) {
            through_reference()
        } else {
            receiver.clone()
        }
    };
    // Tuple and enum decompositions read the referent behind any reference.
    let decomposed = || {
        if reference.is_some() {
            through_reference()
        } else {
            receiver.clone()
        }
    };

    let direct_method = direct_invariant_method(tcx, ty, invariant_type_names);
    let direct = direct_method.as_ref().map(|method| PureExpr::MethodCall {
        receiver: Arc::new(referent()),
        method: method.clone(),
        args: vec![],
    });
    let type_param = super::type_params::type_param_invariant_clause(ty, |access| match access {
        Some(Mutability::Mut) => through_reference(),
        _ => receiver.clone(),
    });

    let mut tuple_fields = Vec::new();
    let mut tuple_field_final_goals = Vec::new();
    let mut tuple_states_every_field = true;
    if let TyKind::Tuple(fields) = inner_ty.kind() {
        for (field_idx, field_ty) in fields.iter().enumerate() {
            let field_is_ref = matches!(field_ty.kind(), TyKind::Ref(_, _, _));
            let field_is_mut_ref = matches!(field_ty.kind(), TyKind::Ref(_, _, Mutability::Mut));
            let inner_field_ty = match field_ty.kind() {
                TyKind::Ref(_, inner, _) => *inner,
                _ => field_ty,
            };
            if has_trivial_type_invariant(inner_field_ty) {
                continue;
            }

            // Build field access: tuple_get_N(x) for by-value tuples and
            // tuple_get_N(*x) for referenced tuples (& / &mut).
            let field_access = PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(field_idx),
                args: vec![decomposed()],
            };

            // A field typed by a type parameter holds that parameter's
            // invariant over the same receiver an ADT field gets below.
            if let Some(clause) =
                super::type_params::type_param_invariant_clause(field_ty, |access| match access {
                    Some(_) => PureExpr::Deref(Arc::new(field_access.clone())),
                    None => field_access.clone(),
                })
            {
                tuple_fields.push(clause);
                continue;
            }

            let method_name = match inner_field_ty.kind() {
                TyKind::Adt(adt_def, _) => {
                    adt_invariant_method_name(tcx, *adt_def, invariant_type_names)
                }
                _ => None,
            };
            let Some(method_name) = method_name else {
                tuple_states_every_field &=
                    !may_carry_invariant(tcx, field_ty, invariant_type_names);
                continue;
            };
            tuple_states_every_field &=
                adt_method_states_every_part(tcx, inner_field_ty, invariant_type_names);

            // Precondition: for reference fields (& / &mut), dereference to
            // apply the invariant to the referent value.
            let precondition_receiver = if field_is_ref {
                PureExpr::Deref(Arc::new(field_access.clone()))
            } else {
                field_access.clone()
            };
            tuple_fields.push(PureExpr::MethodCall {
                receiver: Arc::new(precondition_receiver),
                method: method_name.clone(),
                args: vec![],
            });

            // Postcondition: for &mut fields, require (^field).invariant()
            if field_is_mut_ref {
                tuple_field_final_goals.push(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Final(Arc::new(field_access))),
                    method: method_name,
                    args: vec![],
                });
            }
        }
    }

    // For an enum like `Result<NonZero, E>`, a match that propagates to the
    // per-variant payload invariants:
    //   match x { Ok(v) => inv_NonZero(v), Err(e) => inv_E(e) }
    let mut enum_states_every_payload = true;
    let enum_payloads = match inner_ty.kind() {
        TyKind::Adt(adt_def, substs) if direct_method.is_none() && adt_def.is_enum() => {
            let decomposition =
                build_enum_invariant_match_arms(tcx, *adt_def, *substs, invariant_type_names);
            enum_states_every_payload = decomposition.states_every_payload;
            (!decomposition.arms.is_empty()).then(|| PureExpr::Match {
                scrutinee: Arc::new(decomposed()),
                arms: decomposition.arms,
            })
        }
        _ => None,
    };

    let structural =
        if direct_method.is_some() || !tuple_fields.is_empty() || enum_payloads.is_some() {
            None
        } else {
            build_structural_invariant_expr(tcx, ty, receiver.clone(), invariant_type_names)
                .filter(|expr| !matches!(expr, PureExpr::Bool(true)))
        };

    // Which pass stated the value decides what it may have passed over. The
    // structural pass is never taken as whole: it states an ADT's method
    // without asking what the ADT holds.
    let states_every_part = if !may_carry_invariant(tcx, ty, invariant_type_names) {
        true
    } else if direct.is_some() {
        adt_method_states_every_part(tcx, inner_ty, invariant_type_names)
    } else if type_param.is_some() {
        true
    } else if !tuple_fields.is_empty() {
        tuple_states_every_field
    } else if enum_payloads.is_some() {
        enum_states_every_payload
    } else {
        false
    };

    ParamClauses {
        direct_method,
        direct,
        type_param,
        tuple_fields,
        tuple_field_final_goals,
        enum_payloads,
        structural,
        states_every_part,
    }
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
    // An impl of a foreign trait's method holds no parameter premise
    // (`build_type_invariant_clauses`), the `inv(x)` / `inv(*x)` side
    // conditions `transform_contract` synthesizes for a `&mut` parameter
    // included: no route into the body owes them either (D-141).
    if implements_foreign_trait_method(tcx, def_id) {
        let every_param: HashSet<String> = arg_names.iter().cloned().collect();
        for expr in effective_requires.iter_mut() {
            *expr = super::rewrite::discharge_trivial_inv_calls_expr(expr, &every_param);
        }
    }

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
        if let TyKind::Adt(adt_def, substs) = inner_ty.kind() {
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
            // ...but not when the struct keeps its native Datatype sort AND
            // its single field is itself a compound value (a collection or
            // another ADT/tuple/array). Such a parameter is encoded at the
            // struct sort, and every body-side read of the field lowers to
            // `tuple_get_0(p)`, so collapsing `tuple_get_0(p)` to `p` in the
            // contract/call facts identifies the struct with its field. For
            // `FibCache(Vec<PredCell<..>>)` that rewrote the `Vec::index` fact
            // `ix.has_value(self@, r)` into a view of the struct and panicked
            // the encoder (`sort mismatch in apply ... got FibCache`,
            // cell/02_fib); for `W(Vec<u64>)` it left `w.0[i]` unprovable.
            // Scalar-field newtypes (`NonZero(u32)`, #2669) keep collapsing.
            let compound_native_field = keeps_native_adt_sort
                && is_single_field_struct
                && single_field_is_compound(tcx, *adt_def, *substs);
            if (is_single_field_struct && !compound_native_field)
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
    if let TyKind::Adt(adt_def, substs) = inner_output.kind() {
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
        // matching the parameter-side fix above -- including its exclusion of
        // native-Datatype structs whose single field is compound. Collapsing
        // `tuple_get_0(result)` to `result` while a parameter of the same type
        // keeps its projection would compare a struct with its field (e.g.
        // `ensures result.0@ == w.0@` for `fn(w: W) -> W { w }`).
        let compound_native_field = keeps_native_adt_sort
            && is_single_field_struct
            && single_field_is_compound(tcx, *adt_def, *substs);
        if (is_single_field_struct && !compound_native_field)
            || (!keeps_native_adt_sort
                && (newtype_type_names.contains(&type_name)
                    || newtype_type_names.contains(&qualified_type_name)))
        {
            newtype_params.insert("result".to_string());
        }
    }

    newtype_params
}

/// Whether `adt_def<args>` is a single-field struct that keeps its native
/// Datatype sort AND whose field is compound (see [`single_field_is_compound`]).
///
/// Contracts keep `tuple_get_0(p)` for such a struct (no newtype collapse),
/// but the MIR aggregate lowering still collapses `W(v)` to `v`. A body that
/// builds one by aggregate is refused by the verification guard.
pub(in crate::callbacks) fn is_compound_native_single_field_struct<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: rustc_middle::ty::AdtDef<'tcx>,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> bool {
    adt_def.is_struct()
        && adt_def.non_enum_variant().fields.len() == 1
        && matches!(
            ty_to_expr_sort_enriched(tcx, rustc_middle::ty::Ty::new_adt(tcx, adt_def, args)),
            Some(ExprSort::Datatype(_))
        )
        && single_field_is_compound(tcx, adt_def, args)
}

/// Whether the (first) field of a single-field struct is a compound value:
/// a non-`Box` ADT, a tuple, an array or a slice. Such a struct keeps a
/// distinct projection `tuple_get_0(p)` and must not be collapsed onto its
/// field by the newtype rewrite.
fn single_field_is_compound<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: rustc_middle::ty::AdtDef<'tcx>,
    substs: rustc_middle::ty::GenericArgs<'tcx>,
) -> bool {
    adt_def
        .non_enum_variant()
        .fields
        .iter()
        .next()
        .is_some_and(|field| {
            field_ty_kind_is_compound(field.ty(tcx, substs).skip_norm_wip().kind())
        })
}

/// Pure shape predicate behind [`single_field_is_compound`].
fn field_ty_kind_is_compound(kind: &TyKind<'_>) -> bool {
    matches!(kind, TyKind::Adt(field_adt, _) if !field_adt.is_box())
        || matches!(
            kind,
            TyKind::Tuple(_) | TyKind::Array(..) | TyKind::Slice(_)
        )
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
        if let Attribute::Tool(item) | Attribute::DeriveHelper(item) = attr {
            // Trust: AttrPath.segments is now Box<[Symbol]>; s is a &Symbol directly.
            let segments: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
            if segments == ["creusot", "open_inv_result"] {
                return true;
            }
        }
    }
    false
}

/// Parameter indices carrying `#[creusot::open_inv]`.
///
/// The attribute is the caller's licence to pass a value that BREAKS the type
/// invariant, so the synthesized clause must vanish from both sides at once:
/// the body gets no premise and no call site owes the obligation. Suppressing
/// it on one side only is exactly the free grant this pairing exists to close.
/// The result-side twin is `has_open_inv_result`.
fn open_inv_param_indices(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<usize> {
    let mut open = HashSet::new();
    let Some(local_def_id) = def_id.as_local() else {
        return open;
    };
    let Some(body_id) = tcx.hir_node_by_def_id(local_def_id).body_id() else {
        return open;
    };
    for (idx, param) in tcx.hir_body(body_id).params.iter().enumerate() {
        for attr in tcx.hir_attrs(param.hir_id) {
            if let Attribute::Tool(item) | Attribute::DeriveHelper(item) = attr {
                let segments: Vec<&str> = item.path.segments.iter().map(|s| s.as_str()).collect();
                if segments == ["creusot", "open_inv"] {
                    open.insert(idx);
                }
            }
        }
    }
    open
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

    let (_, result_method) =
        build_type_invariant_method_map(tcx, def_id, arg_names, type_invariant_defs);
    let (_, structural_result_expr) =
        build_type_invariant_structural_expr_map(tcx, def_id, arg_names, type_invariant_defs);

    // `#[creusot::open_inv]` licences the CALLER to pass a value that breaks
    // the invariant, so the parameter contributes no clause at all — neither
    // the premise this body would enjoy nor the obligation its callers owe.
    let open_inv_params = open_inv_param_indices(tcx, def_id);

    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();

    // What each parameter is granted is decided by ONE function, the same
    // one a call that fixes a type parameter reads (`type_param_invariant_at`):
    // the premise a body holds at a type and the clause its callers owe at
    // that type cannot drift apart. The passes are emitted pass by pass, in
    // the order the clauses have always had.
    let per_param: Vec<Option<ParamClauses>> = inputs
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            if i >= arg_names.len() || open_inv_params.contains(&i) {
                return None;
            }
            let receiver = PureExpr::Var(arg_names[i].clone(), ty_to_expr_sort_enriched(tcx, *ty));
            Some(param_clauses(tcx, *ty, &receiver, &invariant_type_names))
        })
        .collect();
    let params = || per_param.iter().flatten();

    let mut invariant_requires = Vec::new();
    let mut invariant_ensures = Vec::new();

    // --- Direct ADT parameters ---
    invariant_requires.extend(params().filter_map(|clauses| clauses.direct.clone()));

    // --- Type-parameter parameters ---
    //
    // `t: T` holds Creusot's opaque `inv_T(t)`. The premise lets this body
    // discharge the same clause where it hands `t` on (a trait call with
    // `Self = T`, another generic function), and every call that fixes `T`
    // owes the clause instantiated at the type it fixes — the grant and its
    // obligation are this one vector, instantiated at two substitutions.
    invariant_requires.extend(params().filter_map(|clauses| clauses.type_param.clone()));

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
        if !is_mut_ref || open_inv_params.contains(&i) {
            continue;
        }
        let Some(method_name) = per_param[i]
            .as_ref()
            .and_then(|clauses| clauses.direct_method.clone())
        else {
            continue;
        };
        let sort = ty_to_expr_sort_enriched(tcx, *ty);
        invariant_ensures.push(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                arg_names[i].clone(),
                sort,
            )))),
            method: method_name,
            args: vec![],
        });
    }

    // --- Tuple parameter field decomposition (#946) ---
    for clauses in params() {
        invariant_requires.extend(clauses.tuple_fields.iter().cloned());
        invariant_ensures.extend(clauses.tuple_field_final_goals.iter().cloned());
    }

    // --- Enum parameter structural decomposition (#2568) ---
    invariant_requires.extend(params().filter_map(|clauses| clauses.enum_payloads.clone()));

    // --- Structural invariant of whatever no pass above decomposed ---
    invariant_requires.extend(params().filter_map(|clauses| clauses.structural.clone()));

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

    // An impl of a FOREIGN trait's method holds no parameter premise. Code no
    // lane walks enters it — std's blanket `Into` calls `From::from`, an
    // iterator adapter calls `next`, drop glue runs `Drop::drop` — and none of
    // those routes owes the premise: the foreign declaration never promised
    // it and the std body that makes the call is verified by nobody. Its goals
    // (`inv(result)`, the final value of a `&mut`) stay owed (D-141).
    if implements_foreign_trait_method(tcx, def_id) {
        invariant_requires.clear();
    }

    (invariant_requires, invariant_ensures)
}

/// Whether `def_id` is a local impl's method of a trait declared in another
/// crate: the body std code can call without walking any lane of this crate.
pub(in crate::callbacks) fn implements_foreign_trait_method(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> bool {
    matches!(
        tcx.opt_associated_item(def_id).map(|assoc| assoc.container),
        Some(rustc_middle::ty::AssocContainer::TraitImpl(Ok(declared))) if !declared.is_local()
    )
}

/// Decide which of a closure's captures owe a type invariant, and which
/// method states it.
///
/// THE single place that pairing is made. `build_user_spec_table` calls it
/// once per closure and stores the result on the closure's spec; the premise
/// injected into the closure's body and the obligation raised where the
/// closure is CONSTRUCTED both render that one vector. A consumer that walked
/// the capture list itself would be a second computation of the pairing, and
/// the two would drift the moment either one's inputs did (#2257, D-66).
pub(in crate::callbacks) fn build_capture_invariants(
    captures: &[CaptureField],
    type_invariant_defs: &[TypeInvariantDef],
) -> Vec<CaptureInvariant> {
    if type_invariant_defs.is_empty() || captures.is_empty() {
        return Vec::new();
    }

    let invariant_type_names: HashSet<String> = type_invariant_defs
        .iter()
        .map(|d| d.type_name().to_string())
        .collect();

    let mut result = Vec::new();
    for (capture_idx, field) in captures.iter().enumerate() {
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

        result.push(CaptureInvariant::new(
            capture_idx,
            field.name(),
            // Preserve the capture's actual logical sort so the injected
            // receiver does not fall back to Int in closure contexts (#2257).
            field.sort().clone(),
            method_name,
        ));
    }
    result
}

/// Build type invariant preconditions for closure capture variables (#2257).
///
/// Renders each stored [`CaptureInvariant`] over the capture's own source
/// name, which is how the enclosing body and a closure's un-rewritten body
/// address it. The pairing is NOT decided here: it is read off the closure's
/// spec-table entry, whose other reader is the construction site that pays
/// for it.
pub(in crate::callbacks) fn build_closure_capture_invariant_requires(
    closure_capture_infos: &[ClosureCaptureInfo],
) -> Vec<PureExpr> {
    build_closure_capture_invariant_requires_with_receivers(
        closure_capture_infos,
        |_: &ClosureCaptureInfo, ci: &CaptureInvariant| Some(ci.clause_at_source_name()),
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
) -> Vec<PureExpr> {
    build_closure_capture_invariant_requires_with_receivers(
        closure_capture_infos,
        |info: &ClosureCaptureInfo, ci: &CaptureInvariant| {
            matches!(info.param_name(), Some("self")).then(|| ci.clause_at_self_field())
        },
    )
}

fn build_closure_capture_invariant_requires_with_receivers<F>(
    closure_capture_infos: &[ClosureCaptureInfo],
    mut clause_for: F,
) -> Vec<PureExpr>
where
    F: FnMut(&ClosureCaptureInfo, &CaptureInvariant) -> Option<PureExpr>,
{
    let mut requires: Vec<PureExpr> = Vec::new();

    for info in closure_capture_infos {
        for capture_inv in info.capture_invariants() {
            let Some(clause) = clause_for(info, capture_inv) else {
                continue;
            };
            // Deduplicate: the same receiver term and method reached through
            // two closures is one premise, not two.
            if !requires.contains(&clause) {
                requires.push(clause);
            }
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
