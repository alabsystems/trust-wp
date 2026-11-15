// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type invariant lookup and classification helpers.
//!
//! Pure analysis over `TyCtxt` / `TyKind` for type invariant discovery:
//! trivial-invariant checks, ADT method name resolution, container detection,
//! and enum structural match arm generation.

use std::{collections::HashSet, sync::Arc};

use rustc_middle::ty::{AdtDef, GenericArgs, TyCtxt, TyKind};
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::tuple_field_logic_fn_name, BinOp, MatchArm, Pattern, PureExpr,
    },
    logic::type_invariant_method_name,
};

/// Check if a type has a trivially true type invariant (Phase 2, #359).
///
/// Primitive types (`bool`, `i32`, `u64`, etc.) have trivial invariants -- injecting
/// `inv(x) = true` for them would bloat VCs without value. This function returns
/// `true` for types that should be skipped during type invariant injection.
///
/// For tuples, the invariant is trivial only when ALL fields have trivial
/// invariants. A tuple like `(NonZero, &mut NonZero)` is non-trivial because
/// its fields may carry type invariants that must be checked. (#946)
pub(in crate::callbacks) fn has_trivial_type_invariant(ty: rustc_middle::ty::Ty<'_>) -> bool {
    match ty.kind() {
        // Primitives: invariant is always `true`
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Never
        | TyKind::Str
        | TyKind::RawPtr(_, _)
        | TyKind::FnPtr(..)
        | TyKind::FnDef(..) => true,
        // Tuples: trivial only if every field (after reference peeling) is trivial.
        TyKind::Tuple(fields) => fields.iter().all(|field_ty| {
            let inner = match field_ty.kind() {
                TyKind::Ref(_, inner, _) => *inner,
                _ => field_ty,
            };
            has_trivial_type_invariant(inner)
        }),
        _ => false,
    }
}

/// Whether a value of `ty` may hold, anywhere inside it, something whose
/// invariant is not `true`: an ADT with an invariant, a type parameter (whose
/// `inv_T` is opaque), or a type this module cannot see into.
///
/// Conservative in one direction only. A `true` for a type that holds nothing
/// costs a refusal where a clause could have been charged; a `false` for a type
/// that holds something would let a call fixing a type parameter to it owe
/// nothing while a body entered at that type holds a premise.
pub(in crate::callbacks) fn may_carry_invariant<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    invariant_type_names: &HashSet<String>,
) -> bool {
    may_carry_invariant_within(tcx, ty, invariant_type_names, &mut HashSet::new())
}

fn may_carry_invariant_within<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    invariant_type_names: &HashSet<String>,
    // A local ADT's fields are walked once: a recursive type re-entered here
    // holds nothing its first walk did not already see, while its generic
    // arguments, which can differ on re-entry, are checked every time.
    walked: &mut HashSet<rustc_hir::def_id::DefId>,
) -> bool {
    if has_trivial_type_invariant(ty) {
        return false;
    }
    let mut carries = |ty: rustc_middle::ty::Ty<'tcx>| {
        may_carry_invariant_within(tcx, ty, invariant_type_names, walked)
    };
    match ty.kind() {
        TyKind::Param(_) => true,
        TyKind::Ref(_, inner, _) | TyKind::Array(inner, _) | TyKind::Slice(inner) => {
            carries(*inner)
        }
        TyKind::Tuple(fields) => fields.iter().any(carries),
        TyKind::Adt(adt_def, substs) => {
            adt_invariant_method_name(tcx, *adt_def, invariant_type_names).is_some()
                || substs.types().any(&mut carries)
                || adt_local_fields_carry(tcx, *adt_def, *substs, invariant_type_names, walked)
        }
        // The one body granted anything about a closure VALUE is the closure's
        // own, and its capture grant is paid where the closure is built (D-76).
        TyKind::Closure(..) => false,
        _ => true,
    }
}

/// Whether a LOCAL ADT's fields, at `substs`, may carry an invariant. A foreign
/// ADT's private fields can hold a local type only through its generic
/// arguments, which the caller checks.
fn adt_local_fields_carry<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: AdtDef<'tcx>,
    substs: GenericArgs<'tcx>,
    invariant_type_names: &HashSet<String>,
    walked: &mut HashSet<rustc_hir::def_id::DefId>,
) -> bool {
    if !adt_def.did().is_local() || !walked.insert(adt_def.did()) {
        return false;
    }
    adt_def.all_fields().any(|field| {
        may_carry_invariant_within(
            tcx,
            field.ty(tcx, substs).skip_norm_wip(),
            invariant_type_names,
            walked,
        )
    })
}

/// Whether the invariant METHOD of an ADT is all there is to state about a
/// value of it: nothing inside it — a generic argument, or a field of a local
/// type — may carry an invariant the method does not name. A sequence
/// container never qualifies: its synthetic method is keyed on the container's
/// short name, not on its element type, so it names one element invariant for
/// every instantiation.
pub(in crate::callbacks) fn adt_method_states_every_part<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    invariant_type_names: &HashSet<String>,
) -> bool {
    let TyKind::Adt(adt_def, substs) = ty.kind() else {
        return false;
    };
    if is_known_seq_container(&adt_type_path(tcx, *adt_def)) {
        return false;
    }
    let mut walked = HashSet::new();
    !substs
        .types()
        .any(|arg| may_carry_invariant_within(tcx, arg, invariant_type_names, &mut walked))
        && !adt_local_fields_carry(tcx, *adt_def, *substs, invariant_type_names, &mut walked)
}

/// Return the full def-path for an ADT definition.
pub(in crate::callbacks) fn adt_type_path(
    tcx: TyCtxt<'_>,
    adt_def: rustc_middle::ty::AdtDef<'_>,
) -> String {
    tcx.def_path_str(adt_def.did())
}

/// Return the type-qualified invariant method name for an ADT when present.
pub(in crate::callbacks) fn adt_invariant_method_name(
    tcx: TyCtxt<'_>,
    adt_def: rustc_middle::ty::AdtDef<'_>,
    invariant_type_names: &HashSet<String>,
) -> Option<String> {
    let type_name = adt_type_path(tcx, adt_def);
    if invariant_type_names.contains(&type_name) {
        return Some(type_invariant_method_name(&type_name));
    }

    // #1370: `def_path_str()` omits the crate qualifier for local types (e.g.,
    // returns "SumTo10" instead of "creusot_test::SumTo10"), but
    // `extract_invariant_type_name` preserves the crate prefix from rustc's
    // path formatting. Check if any crate-qualified entry matches.
    if !type_name.contains("::") {
        let suffix = format!("::{type_name}");
        for inv_name in invariant_type_names {
            if inv_name.ends_with(&suffix) {
                return Some(type_invariant_method_name(inv_name));
            }
        }
    }

    // Synthetic container invariant defs use short names ("Vec", "VecDeque")
    // so parameter precondition injection and ay bridge matching share the
    // same symbol family regardless of ADT def-path spelling.
    let short_name = type_path_short_name(&type_name);
    if is_known_seq_container(&type_name) && invariant_type_names.contains(short_name) {
        return Some(type_invariant_method_name(short_name));
    }

    None
}

/// Known container type short names that support View (Seq) semantics.
///
/// These are the ADT types whose `@` (view) produces a `Seq` value. When a
/// container parameter contains an invariant-bearing element type, the encoder
/// can assert a quantified element invariant over the Seq view. (#869)
const KNOWN_SEQ_CONTAINERS: &[&str] = &["Vec", "VecDeque"];

pub(in crate::callbacks) fn type_path_short_name(type_path: &str) -> &str {
    type_path.rsplit("::").next().unwrap_or(type_path)
}

/// Check if an ADT def path represents a known Seq container.
pub(in crate::callbacks) fn is_known_seq_container(type_path: &str) -> bool {
    let short_name = type_path_short_name(type_path);
    KNOWN_SEQ_CONTAINERS.contains(&short_name)
}

/// Find the invariant method name for the direct element type of an ADT's type args.
///
/// For `Vec<T>` or `Vec<&mut T>`, if T has an invariant def, returns the
/// invariant method name. Handles one level of reference peeling.
pub(in crate::callbacks) fn find_element_invariant_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    substs: rustc_middle::ty::GenericArgs<'tcx>,
    invariant_type_names: &HashSet<String>,
) -> Option<String> {
    for arg_ty in substs.types() {
        let inner = match arg_ty.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            _ => arg_ty,
        };
        if let TyKind::Adt(adt_def, _) = inner.kind() {
            if let Some(method) = adt_invariant_method_name(tcx, *adt_def, invariant_type_names) {
                return Some(method);
            }
        }
    }
    None
}

/// The arms decomposing an enum's structural invariant, and whether each
/// payload they state is stated whole.
pub(in crate::callbacks) struct EnumPayloadArms {
    /// Empty when the enum has nothing to state, or a payload the arms cannot.
    pub(in crate::callbacks) arms: Vec<MatchArm>,
    /// No stated payload holds anything its arm does not name (see
    /// [`adt_method_states_every_part`]).
    pub(in crate::callbacks) states_every_payload: bool,
}

/// Build match arms that decompose an enum's structural type invariant.
///
/// For single-field variants whose payload type has a direct invariant method,
/// this emits an arm like `Ok(v) => v.__trust_wp_invariant_T()`. Variants without
/// non-trivial payload invariants still get a trivially-true arm so the match
/// stays exhaustive while multi-field decomposition remains deferred. (#2568)
pub(in crate::callbacks) fn build_enum_invariant_match_arms<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: AdtDef<'tcx>,
    substs: GenericArgs<'tcx>,
    invariant_type_names: &HashSet<String>,
) -> EnumPayloadArms {
    let mut arms = Vec::new();
    let mut has_non_trivial = false;
    let mut has_unsupported_non_trivial = false;
    let mut states_every_payload = true;

    for variant in adt_def.variants() {
        let variant_name = variant.name.as_str().to_string();
        let (pattern_inner, body) = match variant.fields.len() {
            0 => (None, PureExpr::Bool(true)),
            1 => {
                let field = variant
                    .fields
                    .iter()
                    .next()
                    .expect("single-field variant must have one field");
                let field_ty = field.ty(tcx, substs).skip_norm_wip();
                let field_is_ref = matches!(field_ty.kind(), TyKind::Ref(_, _, _));
                let inner_field_ty = match field_ty.kind() {
                    TyKind::Ref(_, inner, _) => *inner,
                    _ => field_ty,
                };
                let binding_name = format!("$inv_{}_payload", variant.name.as_str().to_lowercase());
                let type_param_clause =
                    super::type_params::type_param_invariant_clause(field_ty, |access| {
                        let binding = PureExpr::Var(binding_name.clone(), None);
                        match access {
                            Some(_) => PureExpr::Deref(Arc::new(binding)),
                            None => binding,
                        }
                    });
                if has_trivial_type_invariant(inner_field_ty) {
                    (Some(Box::new(Pattern::Wildcard)), PureExpr::Bool(true))
                } else if let Some(clause) = type_param_clause {
                    // A payload typed by a type parameter holds its opaque
                    // invariant, instantiated where the parameter is fixed.
                    has_non_trivial = true;
                    (Some(Box::new(Pattern::Binding(binding_name))), clause)
                } else {
                    let method_name = match inner_field_ty.kind() {
                        TyKind::Adt(field_adt_def, _) => {
                            adt_invariant_method_name(tcx, *field_adt_def, invariant_type_names)
                        }
                        _ => None,
                    };
                    if let Some(method_name) = method_name {
                        {
                            has_non_trivial = true;
                            states_every_payload &= adt_method_states_every_part(
                                tcx,
                                inner_field_ty,
                                invariant_type_names,
                            );
                            let receiver = if field_is_ref {
                                PureExpr::Deref(Arc::new(PureExpr::Var(binding_name.clone(), None)))
                            } else {
                                PureExpr::Var(binding_name.clone(), None)
                            };
                            (
                                Some(Box::new(Pattern::Binding(binding_name))),
                                PureExpr::MethodCall {
                                    receiver: Arc::new(receiver),
                                    method: method_name,
                                    args: vec![],
                                },
                            )
                        }
                    } else {
                        {
                            has_unsupported_non_trivial = true;
                            (Some(Box::new(Pattern::Wildcard)), PureExpr::Bool(true))
                        }
                    }
                }
            }
            field_count => {
                if variant.fields.iter().any(|field| {
                    let field_ty = field.ty(tcx, substs).skip_norm_wip();
                    let inner_field_ty = match field_ty.kind() {
                        TyKind::Ref(_, inner, _) => *inner,
                        _ => field_ty,
                    };
                    !has_trivial_type_invariant(inner_field_ty)
                }) {
                    has_unsupported_non_trivial = true;
                }
                (
                    Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Wildcard;
                        field_count
                    ]))),
                    PureExpr::Bool(true),
                )
            }
        };
        arms.push(MatchArm {
            pattern: Pattern::Constructor {
                name: variant_name,
                inner: pattern_inner,
            },
            body,
        });
    }

    if has_non_trivial && !has_unsupported_non_trivial {
        EnumPayloadArms {
            arms,
            states_every_payload,
        }
    } else {
        EnumPayloadArms {
            arms: vec![],
            states_every_payload: false,
        }
    }
}

fn expr_is_true(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Bool(true))
}

fn conjoin_invariant_terms(terms: Vec<PureExpr>) -> PureExpr {
    terms
        .into_iter()
        .filter(|expr| !expr_is_true(expr))
        .reduce(|lhs, rhs| PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)))
        .unwrap_or(PureExpr::Bool(true))
}

/// Build a structural invariant expression for a concrete subject.
///
/// This is the expression-level analogue of Creusot's `structural_invariant()`
/// expansion. It recurses through tuples and enum variants, delegating back to
/// direct invariant methods when a type has an explicit invariant definition.
pub(in crate::callbacks) fn build_structural_invariant_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    subject: PureExpr,
    invariant_type_names: &HashSet<String>,
) -> Option<PureExpr> {
    if has_trivial_type_invariant(ty) {
        return Some(PureExpr::Bool(true));
    }

    match ty.kind() {
        TyKind::Ref(_, inner, _) => build_structural_invariant_expr(
            tcx,
            *inner,
            PureExpr::Deref(Arc::new(subject)),
            invariant_type_names,
        ),
        TyKind::Tuple(fields) => {
            let mut clauses = Vec::with_capacity(fields.len());
            for (field_idx, field_ty) in fields.iter().enumerate() {
                let field_expr = PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(field_idx),
                    args: vec![subject.clone()],
                };
                clauses.push(build_structural_invariant_expr(
                    tcx,
                    field_ty,
                    field_expr,
                    invariant_type_names,
                )?);
            }
            Some(conjoin_invariant_terms(clauses))
        }
        TyKind::Adt(adt_def, substs) => {
            if let Some(method_name) =
                adt_invariant_method_name(tcx, *adt_def, invariant_type_names)
            {
                return Some(PureExpr::MethodCall {
                    receiver: Arc::new(subject),
                    method: method_name,
                    args: vec![],
                });
            }
            if !adt_def.is_enum() {
                return None;
            }

            let mut arms = Vec::with_capacity(adt_def.variants().len());
            let mut has_non_trivial = false;

            for variant in adt_def.variants() {
                let variant_name = variant.name.as_str().to_string();
                let (pattern_inner, body, arm_non_trivial) = match variant.fields.len() {
                    0 => (None, PureExpr::Bool(true), false),
                    1 => {
                        let field = variant
                            .fields
                            .iter()
                            .next()
                            .expect("single-field variant must have one field");
                        let binding_name =
                            format!("$inv_{}_field0", variant.name.as_str().to_lowercase());
                        let field_inv = build_structural_invariant_expr(
                            tcx,
                            field.ty(tcx, *substs).skip_norm_wip(),
                            PureExpr::Var(binding_name.clone(), None),
                            invariant_type_names,
                        )?;
                        (
                            Some(Box::new(Pattern::Binding(binding_name))),
                            field_inv.clone(),
                            !expr_is_true(&field_inv),
                        )
                    }
                    field_count => {
                        let mut patterns = Vec::with_capacity(field_count);
                        let mut clauses = Vec::with_capacity(field_count);
                        let mut arm_non_trivial = false;
                        for (field_idx, field) in variant.fields.iter().enumerate() {
                            let binding_name = format!(
                                "$inv_{}_field{}",
                                variant.name.as_str().to_lowercase(),
                                field_idx
                            );
                            let field_inv = build_structural_invariant_expr(
                                tcx,
                                field.ty(tcx, *substs).skip_norm_wip(),
                                PureExpr::Var(binding_name.clone(), None),
                                invariant_type_names,
                            )?;
                            arm_non_trivial |= !expr_is_true(&field_inv);
                            patterns.push(Pattern::Binding(binding_name));
                            clauses.push(field_inv);
                        }
                        (
                            Some(Box::new(Pattern::Tuple(patterns))),
                            conjoin_invariant_terms(clauses),
                            arm_non_trivial,
                        )
                    }
                };

                has_non_trivial |= arm_non_trivial;
                arms.push(MatchArm {
                    pattern: Pattern::Constructor {
                        name: variant_name,
                        inner: pattern_inner,
                    },
                    body,
                });
            }

            Some(if has_non_trivial {
                PureExpr::Match {
                    scrutinee: Arc::new(subject),
                    arms,
                }
            } else {
                PureExpr::Bool(true)
            })
        }
        _ => None,
    }
}
