// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive variant decrease verification.
//!
//! Verifies strict decrease of recursive variants at each recursive call
//! site to prove termination. Extracted from `verification.rs` (#1669).
//!
//! ## WellFounded variant support (#2665)
//!
//! For variant expressions whose type implements `WellFounded` (custom struct
//! types), the decrease condition uses componentwise field comparison instead
//! of integer `<`. For a struct with N integer fields, the check verifies
//! that ALL fields strictly decrease. This is sound (conservative) and
//! sufficient for the `CustomVariant` pattern from Creusot tests.

use std::{collections::HashMap, sync::Arc};

use rustc_hir::{def_id::DefId, Node, TraitFn, TraitItemKind};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use tracing::debug;
use trust_wp_ay::{
    verify_function_with_modes_outcome, VerificationOutcome, VerificationRequest,
    VerificationResult,
};
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::{
            tuple_field_logic_fn_index, tuple_field_logic_fn_name, tuple_logic_fn_arity,
        },
        BinOp, ExprSort, PureExpr,
    },
    logic::{LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};

use super::super::{
    super::{
        contracts::FunctionContract,
        mir_analysis::{extract_recursive_call_args, get_mir_body},
    },
    ghost_context::rustc_span_to_source_span,
    helpers::report_counterexample,
    parsing::ParsedContract,
    reporting::{
        emit_verification_diagnostic_if_requested, handle_recursive_variant_mir_unavailable,
        verified_evidence_gap_reason, VerificationCounters,
    },
    try_get_body_with_context,
    type_invariants::build_type_invariant_clauses,
};

/// Context for recursive variant-decrease verification.
///
/// This bundles function-local data so the helper signature stays focused and
/// avoids clippy's argument count limit.
pub(in crate::callbacks) struct RecursiveVariantCheckConfig<'a, 'tcx> {
    pub(in crate::callbacks) tcx: TyCtxt<'tcx>,
    pub(in crate::callbacks) contract: &'a FunctionContract,
    pub(in crate::callbacks) parsed: &'a ParsedContract,
    /// Base requires (post-transform, pre-call-assumption-merge) for variant
    /// verification. Uses the transformed clause view rather than raw
    /// `parsed.requires` which may differ after closure-capture rewrites.
    pub(in crate::callbacks) base_requires: &'a [PureExpr],
    /// Postconditions of intermediate (non-recursive) calls made before the
    /// recursive call site. These constrain the return values of helper
    /// methods (e.g., `decr()`) so the variant decrease proof has enough
    /// information about the actual argument passed to the recursive call.
    pub(in crate::callbacks) call_assumptions: &'a [PureExpr],
    pub(in crate::callbacks) logic_fns_opt: Option<&'a [LogicFnDef]>,
    pub(in crate::callbacks) mode_overrides_opt: Option<&'a [LogicMode]>,
    pub(in crate::callbacks) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    pub(in crate::callbacks) type_constants: Option<&'a HashMap<String, PureExpr>>,
    pub(in crate::callbacks) track_level: TrackLevel,
    pub(in crate::callbacks) timeout: Option<std::time::Duration>,
    pub(in crate::callbacks) verbose: bool,
    pub(in crate::callbacks) def_path: &'a str,
    pub(in crate::callbacks) loc: &'a str,
}

pub(in crate::callbacks) fn record_recursive_variant_evidence_gap_if_any(
    outcome: &VerificationOutcome,
    def_path: &str,
    loc: &str,
    site_idx: usize,
    counters: &mut VerificationCounters,
) -> bool {
    let Some(reason) = verified_evidence_gap_reason(outcome) else {
        return false;
    };
    counters.evidence_gaps += 1;
    counters.warnings += 1;
    eprintln!(
        "trust-wp: {def_path} evidence gap (variant decrease at call site {site_idx}: {reason})"
    );
    eprintln!("  at {loc}");
    true
}

pub(in crate::callbacks) fn record_recursive_structural_variant_evidence_gap(
    def_path: &str,
    loc: &str,
    site_idx: usize,
    root_name: &str,
    counters: &mut VerificationCounters,
) {
    counters.evidence_gaps += 1;
    counters.warnings += 1;
    eprintln!(
        "trust-wp: {def_path} evidence gap (structural variant decrease at call site {site_idx}: no solver outcome/provenance)"
    );
    eprintln!("  at {loc}");
    eprintln!("  structural variant `{root_name}` decrease is syntactic only");
}

pub(in crate::callbacks) fn merge_recursive_variant_requires(
    requires: &[PureExpr],
    call_assumptions: &[PureExpr],
    invariant_requires: Vec<PureExpr>,
    path_conditions: &[PureExpr],
) -> Vec<PureExpr> {
    let mut variant_requires = Vec::with_capacity(
        requires.len() + call_assumptions.len() + invariant_requires.len() + path_conditions.len(),
    );
    variant_requires.extend(requires.iter().cloned());
    variant_requires.extend(call_assumptions.iter().cloned());
    variant_requires.extend(invariant_requires);
    variant_requires.extend(path_conditions.iter().cloned());
    variant_requires
}

pub(in crate::callbacks) fn build_recursive_variant_requires(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
    requires: &[PureExpr],
    call_assumptions: &[PureExpr],
    path_conditions: &[PureExpr],
    type_invariants_opt: Option<&[TypeInvariantDef]>,
) -> Vec<PureExpr> {
    let invariant_requires = type_invariants_opt
        .map(|type_invariants| {
            build_type_invariant_clauses(tcx, def_id, arg_names, type_invariants).0
        })
        .unwrap_or_default();
    merge_recursive_variant_requires(
        requires,
        call_assumptions,
        invariant_requires,
        path_conditions,
    )
}

/// Describes a variant type for decrease-condition generation.
pub(in crate::callbacks) enum VariantKind {
    /// Integer-typed variant: use `call_variant < variant`.
    Integer,
    /// Struct with all-integer fields: use componentwise field decrease (#2665).
    ///
    /// The field names are stored for constructing field projections.
    /// The optional `constructor_name` is the LogicFnCall name produced by the
    /// rvalue translator for the ADT aggregate (e.g., `"CustomVariant"`). When
    /// the call site builds the recursive argument with this constructor, the
    /// decrease condition can beta-reduce field projections instead of falling
    /// back to opaque `tuple_get_N(constructor(...))` applications.
    IntegerFieldStruct {
        field_names: Vec<String>,
        constructor_name: Option<String>,
    },
    /// Recursive ADT/reference/Box variant: prove recursive calls use a direct
    /// recursive field of the current variant root.
    StructuralSubterm {
        root_name: String,
        recursive_fields: Vec<StructuralRecursiveField>,
    },
    /// Non-integer variant type that we cannot decompose. The decrease check
    /// will be skipped and counted as an error with a diagnostic note.
    Unsupported { type_name: String },
}

/// A recursive field that may be used as a structural subterm variant.
pub(in crate::callbacks) struct StructuralRecursiveField {
    pub(in crate::callbacks) index: usize,
    pub(in crate::callbacks) allow_field0_carriers: bool,
}

/// Classify the variant expression's type for decrease-condition generation.
///
/// Looks up the type of the variant expression from the function signature.
/// For simple `Var` expressions, checks the corresponding parameter type.
/// Returns `Integer` for integer types, `IntegerFieldStruct` for structs
/// with all-integer fields, and `Unsupported` otherwise.
pub(in crate::callbacks) fn classify_variant_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    variant: &PureExpr,
    arg_names: &[String],
) -> VariantKind {
    // Only handle simple Var variants — complex expressions (arithmetic,
    // Ite, etc.) are already covered by the integer-variant path.
    let PureExpr::Var(ref var_name, _) = variant else {
        return VariantKind::Integer;
    };

    // Find which parameter this variable corresponds to.
    let param_idx = match arg_names.iter().position(|n| n == var_name) {
        Some(idx) => idx,
        None => return VariantKind::Integer, // Not a parameter, assume integer
    };

    // Look up the parameter type from the function signature.
    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let inputs = sig.inputs();
    if param_idx >= inputs.len() {
        return VariantKind::Integer;
    }
    let param_ty = inputs[param_idx];

    let kind = match param_ty.kind() {
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Char => VariantKind::Integer,
        TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
            // Check if ALL fields are integer-typed.
            let variant_def = adt_def.non_enum_variant();
            let mut field_names = Vec::new();
            for field in variant_def.fields.iter() {
                let field_ty = field.ty(tcx, substs).skip_norm_wip();
                match field_ty.kind() {
                    TyKind::Int(_) | TyKind::Uint(_) => {
                        field_names.push(field.name.to_string());
                    }
                    _ => {
                        // Non-integer field — can't do componentwise comparison.
                        let type_name = tcx.def_path_str(adt_def.did());
                        return VariantKind::Unsupported { type_name }
                            .or_else_structural(tcx, param_ty, var_name);
                    }
                }
            }
            if field_names.is_empty() {
                let type_name = tcx.def_path_str(adt_def.did());
                VariantKind::Unsupported { type_name }
            } else {
                // The rvalue translator emits ADT aggregate constructors as
                // `LogicFnCall { name: <ItemName>, ... }` (see
                // `translate_rvalue_typed`). Remember the bare item name so the
                // decrease-condition builder can beta-reduce field projections
                // through the constructor at the recursive call site.
                let constructor_name = Some(tcx.item_name(adt_def.did()).to_string());
                VariantKind::IntegerFieldStruct {
                    field_names,
                    constructor_name,
                }
            }
        }
        _ => {
            let type_name = format!("{param_ty}");
            VariantKind::Unsupported { type_name }
        }
    };
    kind.or_else_structural(tcx, param_ty, var_name)
}

/// Build the decrease condition for a variant at a recursive call site.
///
/// For integer variants: `call_variant < variant` (standard).
/// For struct variants with integer fields: conjunction of per-field
/// strict decrease (`variant.fi > call_variant.fi` for each field `fi`).
/// This is the componentwise strict decrease used by `WellFounded` impls
/// like `CustomVariant` from Creusot's termination tests (#2665).
fn build_decrease_condition(
    variant: &PureExpr,
    call_variant: &PureExpr,
    kind: &VariantKind,
) -> Option<PureExpr> {
    match kind {
        VariantKind::Integer => Some(PureExpr::BinOp(
            Arc::new(call_variant.clone()),
            BinOp::Lt,
            Arc::new(variant.clone()),
        )),
        VariantKind::IntegerFieldStruct {
            field_names,
            constructor_name,
        } => {
            // Build: call_variant.f0 < variant.f0 && call_variant.f1 < variant.f1 && ...
            //
            // This is componentwise strict decrease — the strongest possible
            // WellFounded relation. It matches `CustomVariant::well_founded_relation`
            // which requires all fields to strictly decrease.
            //
            // When `call_variant` is the struct's aggregate constructor (e.g.,
            // `CustomVariant(x.0-1, x.1-1)` lowered to
            // `LogicFnCall { name: "CustomVariant", args: [...] }` by the rvalue
            // translator, or `__trust_wp_tuple_N(x.0-1, x.1-1)` from the synthetic
            // tuple lowering), we beta-reduce inline: extract the N-th
            // constructor argument directly instead of wrapping in
            // `tuple_get_N(call_variant)`. Without this, the ay solver sees
            // `tuple_get_N` applied to an opaque uninterpreted-sort value and
            // cannot prove decrease. (#2665)
            //
            // For the original variant, strip the Datatype sort annotation so
            // the ay encoder falls back to Int sort. This prevents
            // `tuple_get_N(x)` from returning an uninterpreted sort when `x`
            // carries an ExprSort::Datatype annotation from MIR type enrichment.
            let variant_unsorted = strip_datatype_sort(variant);
            let arity = field_names.len();
            let mut conjuncts = Vec::with_capacity(field_names.len());
            for field_name in field_names {
                let field_index: usize = field_name.parse().unwrap_or(0);
                let getter_name = tuple_field_logic_fn_name(field_index);
                let variant_field = PureExpr::LogicFnCall {
                    name: getter_name.clone(),
                    args: vec![variant_unsorted.clone()],
                };
                // Beta-reduce: if call_variant is the struct's own constructor
                // (or a synthetic tuple constructor) with matching arity,
                // extract the field directly.
                let call_variant_field = beta_reduce_struct_field(
                    call_variant,
                    field_index,
                    arity,
                    constructor_name.as_deref(),
                )
                .unwrap_or_else(|| PureExpr::LogicFnCall {
                    name: getter_name,
                    args: vec![call_variant.clone()],
                });
                conjuncts.push(PureExpr::BinOp(
                    Arc::new(call_variant_field),
                    BinOp::Lt,
                    Arc::new(variant_field),
                ));
            }
            // Combine with AND
            let mut result = conjuncts.remove(0);
            for conjunct in conjuncts {
                result = PureExpr::BinOp(Arc::new(result), BinOp::And, Arc::new(conjunct));
            }
            Some(result)
        }
        VariantKind::StructuralSubterm { .. } => None,
        VariantKind::Unsupported { .. } => None,
    }
}

trait StructuralVariantFallback<'tcx> {
    fn or_else_structural(self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, root_name: &str) -> Self;
}

impl<'tcx> StructuralVariantFallback<'tcx> for VariantKind {
    fn or_else_structural(self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, root_name: &str) -> Self {
        match self {
            VariantKind::Unsupported { .. } => {
                classify_structural_variant(tcx, ty, root_name).unwrap_or(self)
            }
            _ => self,
        }
    }
}

fn classify_structural_variant<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    root_name: &str,
) -> Option<VariantKind> {
    let peeled = peel_ref_box_ty(tcx, ty);
    let TyKind::Adt(root_adt, root_args) = peeled.kind() else {
        return None;
    };
    if !root_adt.is_enum() && !root_adt.is_struct() {
        return None;
    }

    let mut recursive_fields = Vec::new();
    for variant in root_adt.variants() {
        for (idx, field) in variant.fields.iter().enumerate() {
            let (field_ty, used_box) =
                peel_ref_box_ty_with_box_flag(tcx, field.ty(tcx, root_args).skip_norm_wip());
            if matches!(field_ty.kind(), TyKind::Adt(field_adt, _) if field_adt.did() == root_adt.did())
                && recursive_fields
                    .iter()
                    .all(|field: &StructuralRecursiveField| field.index != idx)
            {
                recursive_fields.push(StructuralRecursiveField {
                    index: idx,
                    allow_field0_carriers: used_box,
                });
            }
        }
    }

    if recursive_fields.is_empty() {
        None
    } else {
        Some(VariantKind::StructuralSubterm {
            root_name: root_name.to_string(),
            recursive_fields,
        })
    }
}

fn peel_ref_box_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    peel_ref_box_ty_with_box_flag(tcx, ty).0
}

fn peel_ref_box_ty_with_box_flag<'tcx>(tcx: TyCtxt<'tcx>, mut ty: Ty<'tcx>) -> (Ty<'tcx>, bool) {
    let mut used_box = false;
    loop {
        match ty.kind() {
            TyKind::Ref(_, inner, _) => ty = *inner,
            TyKind::Adt(adt_def, args)
                if matches!(
                    tcx.def_path_str(adt_def.did()).as_str(),
                    "alloc::boxed::Box" | "std::boxed::Box"
                ) =>
            {
                let Some(inner) = args.types().next() else {
                    return (ty, used_box);
                };
                used_box = true;
                ty = inner;
            }
            _ => return (ty, used_box),
        }
    }
}

pub(in crate::callbacks) fn structural_variant_decreases(
    call_variant: &PureExpr,
    root_name: &str,
    recursive_fields: &[StructuralRecursiveField],
) -> bool {
    let Some(path) = structural_projection_path(call_variant, root_name) else {
        return false;
    };
    let Some((&field_index, carrier_indices)) = path.split_first() else {
        return false;
    };
    recursive_fields.iter().any(|field| {
        field.index == field_index
            && (carrier_indices.is_empty()
                || (field.allow_field0_carriers && carrier_indices.iter().all(|idx| *idx == 0)))
    })
}

fn structural_projection_path(expr: &PureExpr, root_name: &str) -> Option<Vec<usize>> {
    let expr = strip_transparent_deref_layers(expr);
    match expr {
        PureExpr::Var(name, _) if name == root_name => Some(Vec::new()),
        PureExpr::LogicFnCall { name, args }
            if name == "__trust_wp_field_pointer" && args.len() == 1 =>
        {
            structural_projection_path(&args[0], root_name)
        }
        PureExpr::LogicFnCall { name, args } if args.len() == 1 => {
            let field_index = tuple_field_logic_fn_index(name)?;
            let mut path = structural_projection_path(&args[0], root_name)?;
            path.push(field_index);
            Some(path)
        }
        PureExpr::Deref(inner) => structural_projection_path(inner, root_name),
        _ => None,
    }
}

fn strip_transparent_deref_layers(mut expr: &PureExpr) -> &PureExpr {
    while let PureExpr::Deref(inner) = expr {
        expr = inner;
    }
    expr
}

/// Inline tuple beta-reduction: if `expr` is a tuple constructor
/// (`__trust_wp_tupleN(a0, a1, ...)`) with matching arity, extract field
/// `field_index` directly. Returns `None` if not applicable. (#2665)
fn beta_reduce_tuple_field(expr: &PureExpr, field_index: usize) -> Option<PureExpr> {
    if let PureExpr::LogicFnCall { name, args } = expr {
        let arity = tuple_logic_fn_arity(name)?;
        if arity == args.len() && field_index < args.len() {
            return Some(args[field_index].clone());
        }
    }
    None
}

/// Inline beta-reduction for struct-typed `IntegerFieldStruct` variants.
///
/// Recognises both the synthetic tuple constructor (`__trust_wp_tupleN`) and the
/// named ADT aggregate constructor produced by `translate_rvalue_typed` (e.g.
/// `LogicFnCall { name: "CustomVariant", args: [...] }`). When the call_variant
/// expression matches either form with the expected arity, returns the field
/// argument directly so the decrease condition avoids opaque
/// `tuple_get_N(constructor(...))` applications. (#2665)
fn beta_reduce_struct_field(
    expr: &PureExpr,
    field_index: usize,
    expected_arity: usize,
    constructor_name: Option<&str>,
) -> Option<PureExpr> {
    if let Some(reduced) = beta_reduce_tuple_field(expr, field_index) {
        return Some(reduced);
    }
    let constructor_name = constructor_name?;
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    if name == constructor_name && args.len() == expected_arity && field_index < args.len() {
        return Some(args[field_index].clone());
    }
    None
}

/// Strip `ExprSort::Datatype` annotations from a `PureExpr::Var`.
///
/// When MIR type enrichment annotates a variant variable `x` with
/// `ExprSort::Datatype(...)`, the ay encoder creates `x` as an uninterpreted
/// sort. This makes `tuple_get_N(x)` return an uninterpreted value, breaking
/// integer comparisons. Stripping the Datatype annotation lets the encoder
/// fall back to Int sort inference for the tuple field accessors. (#2665)
fn strip_datatype_sort(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Var(name, Some(ExprSort::Datatype(_))) => PureExpr::Var(name.clone(), None),
        other => other.clone(),
    }
}

/// Recursively strip `ExprSort::Datatype` annotations from a specific
/// variable name throughout an expression tree.
///
/// When verifying variant decrease for `IntegerFieldStruct` variants, all
/// references to the struct-typed variant variable must have their Datatype
/// sort annotation removed. Otherwise the ay encoder declares the variable
/// with an uninterpreted sort, causing `tuple_get_N(x)` to return a non-Int
/// value and breaking integer comparison in the decrease condition.
///
/// This walks the entire expression tree, stripping Datatype annotations
/// from ALL occurrences of `var_name`, including inside path conditions,
/// preconditions, and nested subexpressions. (#2665)
fn strip_datatype_sort_deep(expr: &PureExpr, var_name: &str) -> PureExpr {
    match expr {
        PureExpr::Var(name, Some(ExprSort::Datatype(_))) if name == var_name => {
            PureExpr::Var(name.clone(), None)
        }
        PureExpr::BinOp(lhs, op, rhs) => {
            let new_lhs = strip_datatype_sort_deep(lhs, var_name);
            let new_rhs = strip_datatype_sort_deep(rhs, var_name);
            PureExpr::BinOp(Arc::new(new_lhs), *op, Arc::new(new_rhs))
        }
        PureExpr::UnOp(op, inner) => {
            let new_inner = strip_datatype_sort_deep(inner, var_name);
            PureExpr::UnOp(*op, Arc::new(new_inner))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let new_cond = strip_datatype_sort_deep(cond, var_name);
            let new_then = strip_datatype_sort_deep(then_expr, var_name);
            let new_else = strip_datatype_sort_deep(else_expr, var_name);
            PureExpr::Ite(Arc::new(new_cond), Arc::new(new_then), Arc::new(new_else))
        }
        PureExpr::LogicFnCall { name, args } => {
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|a| strip_datatype_sort_deep(a, var_name))
                .collect();
            PureExpr::LogicFnCall {
                name: name.clone(),
                args: new_args,
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let new_receiver = strip_datatype_sort_deep(receiver, var_name);
            let new_args: Vec<PureExpr> = args
                .iter()
                .map(|a| strip_datatype_sort_deep(a, var_name))
                .collect();
            PureExpr::MethodCall {
                receiver: Arc::new(new_receiver),
                method: method.clone(),
                args: new_args,
            }
        }
        PureExpr::Deref(inner) => {
            PureExpr::Deref(Arc::new(strip_datatype_sort_deep(inner, var_name)))
        }
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(strip_datatype_sort_deep(inner, var_name))),
        PureExpr::Final(inner) => {
            PureExpr::Final(Arc::new(strip_datatype_sort_deep(inner, var_name)))
        }
        PureExpr::View(inner) => {
            PureExpr::View(Arc::new(strip_datatype_sort_deep(inner, var_name)))
        }
        // Leaf nodes and complex nodes that don't contain the variable
        // (Int, Bool, Var with different name, etc.) — return unchanged.
        other => other.clone(),
    }
}

/// Apply the same newtype `tuple_get_0(param)` → `param` simplification used
/// for contracts to MIR-extracted recursive call sites.
///
/// MIR analysis emits `LogicFnCall("__trust_wp_tuple_get_0", [Var(p)])` for
/// `p.0` field projections on newtype params, but doesn't know that the
/// logical newtype identity collapses field-0 access. Contracts already get
/// this rewrite via `simplify_newtype_field_access_in_contract`, but
/// MIR-extracted call_args and path_conditions bypass that pass — leaving
/// raw `tuple_get_0(i)` on `i: Datatype("NonNeg")`. The encoder then
/// declares `i` with the Tuple-axiom domain (`Sort::Uninterpreted("Tuple1")`)
/// instead of its proper Datatype, and the variant view picks up the same
/// opaque carrier, producing spurious counter-examples like
/// `i = @Tuple1!0`. This pre-pass aligns MIR-extracted exprs with contract
/// exprs so the encoder sees consistent newtype identity throughout. (#5)
fn simplify_call_sites_for_newtype_params(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    arg_names: &[String],
    type_invariants_opt: Option<&[TypeInvariantDef]>,
    call_sites: Vec<crate::mir_analysis::RecursiveCallSite>,
) -> Vec<crate::mir_analysis::RecursiveCallSite> {
    use crate::callbacks::{
        contract_rewrite::simplify_newtype_field_access_expr,
        type_invariants::build_newtype_param_set,
    };

    let Some(type_invariants) = type_invariants_opt else {
        return call_sites;
    };
    let newtype_params = build_newtype_param_set(tcx, def_id, arg_names, type_invariants);
    if newtype_params.is_empty() {
        return call_sites;
    }
    call_sites
        .into_iter()
        .map(|site| crate::mir_analysis::RecursiveCallSite {
            call_args: site
                .call_args
                .into_iter()
                .map(|e| simplify_newtype_field_access_expr(&e, &newtype_params))
                .collect(),
            path_conditions: site
                .path_conditions
                .into_iter()
                .map(|e| simplify_newtype_field_access_expr(&e, &newtype_params))
                .collect(),
        })
        .collect()
}

/// Verify strict decrease of recursive variants at each recursive call site.
///
/// Returns true when normal body verification should be skipped for this
/// function (e.g., variant-only contracts or MIR unavailable).
pub(in crate::callbacks) fn verify_recursive_variant_decrease(
    cfg: &RecursiveVariantCheckConfig<'_, '_>,
    counters: &mut VerificationCounters,
) -> bool {
    // Trigger MIR borrowck to populate cache (guard for body-less items).
    if cfg
        .tcx
        .is_mir_available(cfg.contract.local_def_id.to_def_id())
    {
        // Skip bodyless trait method declarations (#2205). `is_mir_available`
        // returns true for these but `mir_borrowck` panics in `body_owned_by`.
        if let Node::TraitItem(item) = cfg.tcx.hir_node_by_def_id(cfg.contract.local_def_id) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                return true;
            }
        }
        let root = cfg
            .tcx
            .typeck_root_def_id(cfg.contract.local_def_id.to_def_id())
            .expect_local();
        let _ = cfg.tcx.mir_borrowck(root);
    }

    let Some(body_with_facts) = try_get_body_with_context(cfg.contract.local_def_id) else {
        // MIR body extraction failed for recursive function with variants.
        // Skip normal verification so variant-only contracts cannot fall
        // through to trivial postcondition verification (#825).
        handle_recursive_variant_mir_unavailable(cfg.def_path, cfg.loc, counters);
        return true;
    };

    let mir_body = get_mir_body(body_with_facts);
    let call_sites = extract_recursive_call_args(
        mir_body,
        &cfg.parsed.arg_names,
        cfg.contract.def_id,
        Some(cfg.tcx),
    );
    // MIR-extracted call sites still carry raw `tuple_get_0(param)` field
    // projections for newtype params (the MIR walk doesn't know about logical
    // newtype identity). Apply the same simplification used for contracts so
    // path conditions and call_args agree with the contract requires/ensures —
    // otherwise the encoder declares `param` with `Sort::Uninterpreted("Tuple1")`
    // (driven by the unsimplified `tuple_get_0(param)` axiom domain) and the
    // variant view becomes opaque-uninterpreted, producing spurious counter-
    // examples like `i = @Tuple1!0, i_view = @Tuple1!0`. (#5, spans::quux,
    // result/own::as_mut)
    let call_sites = simplify_call_sites_for_newtype_params(
        cfg.tcx,
        cfg.contract.def_id,
        &cfg.parsed.arg_names,
        cfg.type_invariants_opt,
        call_sites,
    );
    if call_sites.is_empty() {
        // Self-recursion detected by callgraph but no call sites found by
        // MIR extraction — shouldn't happen. Count as error so the variant
        // obligation is not silently dropped (#824, Path 4).
        counters.errors += 1;
        eprintln!(
            "trust-wp: {} error: detected as recursive but no call sites found in MIR",
            cfg.def_path
        );
        eprintln!("  at {}", cfg.loc);
        eprintln!("  termination variant check skipped");
        return false;
    }

    // For each variant expression, verify strict decrease at each call site.
    let mut all_variants_verified = true;
    let mut any_assumed = false;
    let mut any_structural_evidence_gap = false;
    for variant in &cfg.parsed.loop_fields.variants {
        // Classify the variant type once per variant expression (#2665).
        let kind =
            classify_variant_type(cfg.tcx, cfg.contract.def_id, variant, &cfg.parsed.arg_names);
        if let VariantKind::Unsupported { ref type_name } = kind {
            // Non-integer, non-struct variant type — skip with diagnostic.
            counters.errors += 1;
            eprintln!(
                "trust-wp: {} error: variant type `{type_name}` is not supported for decrease checking",
                cfg.def_path
            );
            eprintln!("  at {}", cfg.loc);
            eprintln!("  only integer types and structs with all-integer fields are supported");
            all_variants_verified = false;
            break;
        }
        for (site_idx, site) in call_sites.iter().enumerate() {
            // Build substitution: param_name -> call_arg
            let mut subs = HashMap::new();
            for (i, name) in cfg.parsed.arg_names.iter().enumerate() {
                if i < site.call_args.len() {
                    subs.insert(name.clone(), site.call_args[i].clone());
                }
            }
            // call_variant = variant[call_args/params]
            let call_variant = variant.substitute(&subs);
            if let VariantKind::StructuralSubterm {
                root_name,
                recursive_fields,
            } = &kind
            {
                if structural_variant_decreases(&call_variant, root_name, recursive_fields) {
                    any_structural_evidence_gap = true;
                    record_recursive_structural_variant_evidence_gap(
                        cfg.def_path,
                        cfg.loc,
                        site_idx,
                        root_name,
                        counters,
                    );
                    if cfg.verbose {
                        debug!(
                            "trust-wp:   structural variant decrease accepted with evidence gap at call site {site_idx}"
                        );
                    }
                    continue;
                }
                all_variants_verified = false;
                counters.failed += 1;
                eprintln!(
                    "trust-wp: {} FAILED \u{2717} (variant decrease)",
                    cfg.def_path
                );
                eprintln!("  at {}", cfg.loc);
                eprintln!(
                    "  structural variant `{root_name}` does not decrease at recursive call site {site_idx}"
                );
                break;
            }
            // Build the decrease condition based on variant type (#2665).
            let decrease_cond = match build_decrease_condition(variant, &call_variant, &kind) {
                Some(cond) => cond,
                None => {
                    // Should not happen — Unsupported is handled above.
                    counters.errors += 1;
                    all_variants_verified = false;
                    break;
                }
            };

            // Verify: requires ∧ call_assumptions ∧ call_site_path => call_variant < variant
            let variant_requires = build_recursive_variant_requires(
                cfg.tcx,
                cfg.contract.def_id,
                &cfg.parsed.arg_names,
                cfg.base_requires,
                cfg.call_assumptions,
                &site.path_conditions,
                cfg.type_invariants_opt,
            );
            let variant_ensures = vec![decrease_cond];

            // For IntegerFieldStruct variants, strip Datatype sort annotations
            // from the variant variable across ALL expressions in the verification
            // request. Without this, the ay encoder declares the variant variable
            // (e.g., `x: CustomVariant`) as an uninterpreted sort, making
            // `tuple_get_N(x)` return a non-Int value and breaking the integer
            // comparison in the decrease condition. (#2665)
            let (variant_requires, variant_ensures) =
                if let VariantKind::IntegerFieldStruct { .. } = kind {
                    if let PureExpr::Var(ref vname, _) = variant {
                        let rewritten_requires: Vec<PureExpr> = variant_requires
                            .iter()
                            .map(|e| strip_datatype_sort_deep(e, vname))
                            .collect();
                        let rewritten_ensures: Vec<PureExpr> = variant_ensures
                            .iter()
                            .map(|e| strip_datatype_sort_deep(e, vname))
                            .collect();
                        (rewritten_requires, rewritten_ensures)
                    } else {
                        (variant_requires, variant_ensures)
                    }
                } else {
                    (variant_requires, variant_ensures)
                };

            let result = verify_function_with_modes_outcome(
                VerificationRequest::new(&variant_requires, &variant_ensures)
                    .logic_fns(cfg.logic_fns_opt)
                    .mode_overrides(cfg.mode_overrides_opt)
                    .type_invariants(cfg.type_invariants_opt)
                    .type_constants(cfg.type_constants)
                    .track(Some(cfg.track_level))
                    .timeout(cfg.timeout),
            )
            .map_err(|e| {
                match rustc_span_to_source_span(
                    cfg.tcx.sess.source_map(),
                    cfg.tcx.def_span(cfg.contract.def_id),
                ) {
                    Some(src_span) => e.with_span(src_span),
                    None => e,
                }
            });
            if let Ok(outcome) = &result {
                let diagnostic_path = format!("{}::variant_decrease[{site_idx}]", cfg.def_path);
                emit_verification_diagnostic_if_requested(
                    &diagnostic_path,
                    "recursive_variant",
                    outcome,
                );
            }

            match result {
                Ok(outcome)
                    if record_recursive_variant_evidence_gap_if_any(
                        &outcome,
                        cfg.def_path,
                        cfg.loc,
                        site_idx,
                        counters,
                    ) =>
                {
                    all_variants_verified = false;
                }
                Ok(VerificationOutcome {
                    result: VerificationResult::Verified(_),
                    ..
                }) => {
                    if cfg.verbose {
                        debug!(
                            "trust-wp:   variant decrease verified at call site {site_idx} ({} path condition(s))",
                            site.path_conditions.len()
                        );
                    }
                }
                Ok(VerificationOutcome {
                    result: VerificationResult::Assumed(_),
                    ..
                }) => {
                    // Variant decrease assumed but not proven — termination
                    // soundness gap (#2121). Track separately from verified.
                    any_assumed = true;
                    eprintln!(
                        "trust-wp: {} variant decrease ASSUMED (not proven) at call site {site_idx} (#2121)",
                        cfg.def_path
                    );
                    eprintln!("  at {}", cfg.loc);
                }
                Ok(VerificationOutcome {
                    result: VerificationResult::Failed(counterexample),
                    ..
                }) => {
                    all_variants_verified = false;
                    counters.failed += 1;
                    eprintln!(
                        "trust-wp: {} FAILED \u{2717} (variant decrease)",
                        cfg.def_path
                    );
                    eprintln!("  at {}", cfg.loc);
                    eprintln!("  variant does not decrease at recursive call site {site_idx}");
                    report_counterexample(&counterexample);
                }
                Ok(VerificationOutcome {
                    result: VerificationResult::Unknown(ref reason),
                    ..
                }) => {
                    // Vacuous variant decrease: the preconditions + path
                    // conditions are contradictory, making this call site
                    // unreachable. The variant decrease is trivially true.
                    // This is acceptable for variant checks on unreachable
                    // paths — but we no longer label it "verified" (#2663).
                    let is_vacuous = matches!(
                        reason,
                        trust_wp_ay::UnknownReason::SolverMessage(msg) if msg.contains("vacuous proof")
                    );
                    if is_vacuous {
                        if cfg.verbose {
                            debug!(
                                "trust-wp:   variant decrease vacuous (unreachable call site {site_idx})"
                            );
                        }
                    } else {
                        all_variants_verified = false;
                        counters.errors += 1;
                        // Track demotions from the unsoundness demotion
                        // pipeline (#2106).
                        if matches!(reason, trust_wp_ay::UnknownReason::Demoted(_)) {
                            counters.demoted += 1;
                        }
                        eprintln!(
                            "trust-wp: {} unknown (variant decrease: {reason})",
                            cfg.def_path
                        );
                        eprintln!("  at {}", cfg.loc);
                    }
                }
                Ok(_) => {
                    all_variants_verified = false;
                    counters.errors += 1;
                    eprintln!(
                        "trust-wp: {} error (variant decrease): unrecognized verification result",
                        cfg.def_path
                    );
                    eprintln!("  at {}", cfg.loc);
                }
                Err(ref e) => {
                    all_variants_verified = false;
                    counters.errors += 1;
                    counters.encoding_errors.record(e);
                    eprintln!("trust-wp: {} error (variant decrease): {e}", cfg.def_path);
                    eprintln!("  at {}", cfg.loc);
                }
            }

            if !all_variants_verified {
                break;
            }
        }
        if !all_variants_verified {
            break;
        }
    }

    if all_variants_verified && any_assumed {
        counters.assumed += 1;
        eprintln!(
            "trust-wp: {} assumed (termination — not all call sites proven) (#2121)",
            cfg.def_path
        );
    } else if all_variants_verified && !any_structural_evidence_gap {
        counters.verified += 1;
        eprintln!("trust-wp: {} verified \u{2713} (termination)", cfg.def_path);
    } else if all_variants_verified {
        eprintln!(
            "trust-wp: {} unverified (termination — structural variant decrease lacks solver evidence)",
            cfg.def_path
        );
    }

    // If the function has no ensures clauses, variant verification is the only
    // required obligation for this function.
    cfg.contract.ensures.is_empty()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{
        intern_sort_name,
        internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
        BinOp, ExprSort, PureExpr,
    };

    use super::{
        beta_reduce_struct_field, beta_reduce_tuple_field, build_decrease_condition,
        strip_datatype_sort, strip_datatype_sort_deep, structural_variant_decreases,
        StructuralRecursiveField, VariantKind,
    };

    #[test]
    fn test_beta_reduce_tuple_field_extracts_constructor_args() {
        // __trust_wp_tuple2(a, b) → field 0 = a, field 1 = b
        let a = PureExpr::Var("a".into(), None);
        let b = PureExpr::Var("b".into(), None);
        let tuple = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![a.clone(), b.clone()],
        };
        assert_eq!(beta_reduce_tuple_field(&tuple, 0), Some(a));
        assert_eq!(beta_reduce_tuple_field(&tuple, 1), Some(b));
    }

    #[test]
    fn test_beta_reduce_tuple_field_out_of_bounds_returns_none() {
        let tuple = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        };
        assert_eq!(beta_reduce_tuple_field(&tuple, 2), None);
    }

    #[test]
    fn test_beta_reduce_tuple_field_non_tuple_returns_none() {
        let var = PureExpr::Var("x".into(), None);
        assert_eq!(beta_reduce_tuple_field(&var, 0), None);

        // Logic fn call that is NOT a tuple constructor
        let non_tuple = PureExpr::LogicFnCall {
            name: "some_fn".into(),
            args: vec![PureExpr::Int(1)],
        };
        assert_eq!(beta_reduce_tuple_field(&non_tuple, 0), None);
    }

    #[test]
    fn test_strip_datatype_sort_removes_datatype_annotation() {
        let id = intern_sort_name("CustomVariant");
        let expr = PureExpr::Var("x".into(), Some(ExprSort::Datatype(id)));
        let stripped = strip_datatype_sort(&expr);
        assert_eq!(stripped, PureExpr::Var("x".into(), None));
    }

    #[test]
    fn test_strip_datatype_sort_preserves_int_sort() {
        let expr = PureExpr::Var("x".into(), Some(ExprSort::Int));
        let stripped = strip_datatype_sort(&expr);
        assert_eq!(stripped, PureExpr::Var("x".into(), Some(ExprSort::Int)));
    }

    #[test]
    fn test_strip_datatype_sort_preserves_no_sort() {
        let expr = PureExpr::Var("x".into(), None);
        let stripped = strip_datatype_sort(&expr);
        assert_eq!(stripped, PureExpr::Var("x".into(), None));
    }

    #[test]
    fn test_strip_datatype_sort_preserves_non_var() {
        let expr = PureExpr::Int(42);
        let stripped = strip_datatype_sort(&expr);
        assert_eq!(stripped, PureExpr::Int(42));
    }

    #[test]
    fn test_build_decrease_condition_integer_variant() {
        let variant = PureExpr::Var("n".into(), None);
        let call_variant = PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".into(), None)),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        );
        let cond = build_decrease_condition(&variant, &call_variant, &VariantKind::Integer);
        assert!(cond.is_some());
        // Should be: (n - 1) < n
        let cond = cond.unwrap();
        assert!(matches!(cond, PureExpr::BinOp(_, BinOp::Lt, _)));
    }

    #[test]
    fn test_build_decrease_condition_struct_with_beta_reduction() {
        // Simulates CustomVariant(x.0-1, x.1-1) < CustomVariant(x.0, x.1)
        let id = intern_sort_name("CustomVariant");
        let variant = PureExpr::Var("x".into(), Some(ExprSort::Datatype(id)));
        // call_variant = __trust_wp_tuple2(x.0-1, x.1-1)
        let call_variant = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![
                PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x_0".into(), None)),
                    BinOp::Sub,
                    Arc::new(PureExpr::Int(1)),
                ),
                PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x_1".into(), None)),
                    BinOp::Sub,
                    Arc::new(PureExpr::Int(1)),
                ),
            ],
        };
        let kind = VariantKind::IntegerFieldStruct {
            field_names: vec!["0".into(), "1".into()],
            constructor_name: None,
        };
        let cond = build_decrease_condition(&variant, &call_variant, &kind);
        assert!(
            cond.is_some(),
            "should produce decrease condition for IntegerFieldStruct"
        );
        // Result should be: (x_0-1) < tuple_get_0(x) && (x_1-1) < tuple_get_1(x)
        // The call_variant fields are beta-reduced (extracted directly from constructor)
        // The variant fields use tuple_get_N on the unsorted variant
        let cond = cond.unwrap();
        // Top-level should be And of two Lt comparisons
        assert!(matches!(cond, PureExpr::BinOp(_, BinOp::And, _)));
    }

    #[test]
    fn test_build_decrease_condition_unsupported_returns_none() {
        let variant = PureExpr::Var("x".into(), None);
        let call_variant = PureExpr::Var("y".into(), None);
        let kind = VariantKind::Unsupported {
            type_name: "SomeType".into(),
        };
        assert!(build_decrease_condition(&variant, &call_variant, &kind).is_none());
    }

    #[test]
    fn test_build_decrease_condition_struct_variant_stripped_sorts() {
        // Verify that Datatype sort is stripped from the variant expression
        // when building field accessors, preventing uninterpreted sort propagation
        let id = intern_sort_name("CV");
        let variant = PureExpr::Var("v".into(), Some(ExprSort::Datatype(id)));
        let call_variant = PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(1),
            args: vec![PureExpr::Int(5)],
        };
        let kind = VariantKind::IntegerFieldStruct {
            field_names: vec!["0".into()],
            constructor_name: None,
        };
        let cond = build_decrease_condition(&variant, &call_variant, &kind).unwrap();
        // Should be: 5 < tuple_get_0(Var("v", None))
        // The Datatype annotation on "v" should be stripped
        if let PureExpr::BinOp(lhs, BinOp::Lt, rhs) = &cond {
            // lhs = beta-reduced: Int(5)
            assert_eq!(**lhs, PureExpr::Int(5));
            // rhs = LogicFnCall { name: tuple_get_0, args: [Var("v", None)] }
            if let PureExpr::LogicFnCall { name, args } = &**rhs {
                assert_eq!(*name, tuple_field_logic_fn_name(0));
                assert_eq!(args.len(), 1);
                // Verify sort is stripped (None, not Datatype)
                assert_eq!(args[0], PureExpr::Var("v".into(), None));
            } else {
                panic!("expected LogicFnCall for variant field, got {rhs:?}");
            }
        } else {
            panic!("expected BinOp Lt, got {cond:?}");
        }
    }

    #[test]
    fn test_beta_reduce_struct_field_handles_named_constructor() {
        // Simulates the rvalue translator output for `CustomVariant(a, b)`:
        // `LogicFnCall { name: "CustomVariant", args: [a, b] }`. The synthetic
        // `__trust_wp_tupleN` matcher does not recognise this — the helper must
        // fall back to the named-constructor branch.
        let a = PureExpr::Var("a".into(), None);
        let b = PureExpr::Var("b".into(), None);
        let call_variant = PureExpr::LogicFnCall {
            name: "CustomVariant".into(),
            args: vec![a.clone(), b.clone()],
        };
        assert_eq!(
            beta_reduce_struct_field(&call_variant, 0, 2, Some("CustomVariant")),
            Some(a)
        );
        assert_eq!(
            beta_reduce_struct_field(&call_variant, 1, 2, Some("CustomVariant")),
            Some(b)
        );
        // Wrong constructor name → no reduction.
        assert_eq!(
            beta_reduce_struct_field(&call_variant, 0, 2, Some("Other")),
            None
        );
        // No constructor name available → no reduction (matches the synthetic
        // tuple path only).
        assert_eq!(beta_reduce_struct_field(&call_variant, 0, 2, None), None);
    }

    #[test]
    fn test_build_decrease_condition_named_struct_constructor_beta_reduces() {
        // Production path: variant `x: CustomVariant`, call site
        // `custom_variant(CustomVariant(x.0-1, x.1-1))`.
        // The rvalue translator emits the call argument as a named-constructor
        // LogicFnCall. The decrease check must beta-reduce so the solver sees
        // `(x.0-1) < tuple_get_0(x) && (x.1-1) < tuple_get_1(x)` rather than
        // opaque `tuple_get_N(CustomVariant(...))` applications. (#2665)
        let id = intern_sort_name("CustomVariant");
        let variant = PureExpr::Var("x".into(), Some(ExprSort::Datatype(id)));
        let arg0 = PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![PureExpr::Var("x".into(), None)],
            }),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        );
        let arg1 = PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![PureExpr::Var("x".into(), None)],
            }),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        );
        let call_variant = PureExpr::LogicFnCall {
            name: "CustomVariant".into(),
            args: vec![arg0.clone(), arg1.clone()],
        };
        let kind = VariantKind::IntegerFieldStruct {
            field_names: vec!["0".into(), "1".into()],
            constructor_name: Some("CustomVariant".into()),
        };
        let cond = build_decrease_condition(&variant, &call_variant, &kind).unwrap();
        // Top-level: And of two Lt comparisons.
        let PureExpr::BinOp(lhs, BinOp::And, rhs) = &cond else {
            panic!("expected And, got {cond:?}");
        };
        // First conjunct: (x.0 - 1) < tuple_get_0(x)
        let PureExpr::BinOp(left0, BinOp::Lt, _right0) = &**lhs else {
            panic!("expected Lt, got {lhs:?}");
        };
        assert_eq!(**left0, arg0, "first conjunct LHS must beta-reduce to arg0");
        // Second conjunct: (x.1 - 1) < tuple_get_1(x)
        let PureExpr::BinOp(left1, BinOp::Lt, _right1) = &**rhs else {
            panic!("expected Lt, got {rhs:?}");
        };
        assert_eq!(
            **left1, arg1,
            "second conjunct LHS must beta-reduce to arg1"
        );
    }

    #[test]
    fn test_strip_datatype_sort_deep_strips_in_binop() {
        let id = intern_sort_name("CustomVariant");
        // tuple_get_0(Var("x", Datatype(CV))) != Int(0)
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![PureExpr::Var("x".into(), Some(ExprSort::Datatype(id)))],
            }),
            BinOp::Ne,
            Arc::new(PureExpr::Int(0)),
        );
        let stripped = strip_datatype_sort_deep(&expr, "x");
        // Should strip the Datatype annotation from "x" inside the LogicFnCall
        let expected = PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![PureExpr::Var("x".into(), None)],
            }),
            BinOp::Ne,
            Arc::new(PureExpr::Int(0)),
        );
        assert_eq!(stripped, expected);
    }

    #[test]
    fn test_strip_datatype_sort_deep_preserves_other_vars() {
        let id = intern_sort_name("OtherType");
        // BinOp with "y" having Datatype sort — should NOT be stripped when var_name="x"
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".into(), Some(ExprSort::Datatype(id)))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        );
        let stripped = strip_datatype_sort_deep(&expr, "x");
        // "y" annotation should be preserved since we only strip "x"
        assert_eq!(stripped, expr);
    }

    #[test]
    fn test_strip_datatype_sort_deep_handles_method_call() {
        let id = intern_sort_name("CV");
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Datatype(id)))),
            method: "invariant".into(),
            args: vec![],
        };
        let stripped = strip_datatype_sort_deep(&expr, "x");
        let expected = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".into(), None)),
            method: "invariant".into(),
            args: vec![],
        };
        assert_eq!(stripped, expected);
    }

    #[test]
    fn test_structural_variant_decreases_on_recursive_tail_field() {
        let tail = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                "self".into(),
                None,
            )))],
        };
        assert!(structural_variant_decreases(
            &tail,
            "self",
            &[StructuralRecursiveField {
                index: 1,
                allow_field0_carriers: false,
            }]
        ));
    }

    #[test]
    fn test_structural_variant_decreases_through_box_field0_carriers() {
        let tail = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(1),
                    args: vec![PureExpr::Deref(Arc::new(PureExpr::Var(
                        "self".into(),
                        None,
                    )))],
                }],
            }],
        };
        assert!(structural_variant_decreases(
            &tail,
            "self",
            &[StructuralRecursiveField {
                index: 1,
                allow_field0_carriers: true,
            }]
        ));
        assert!(!structural_variant_decreases(
            &tail,
            "self",
            &[StructuralRecursiveField {
                index: 1,
                allow_field0_carriers: false,
            }]
        ));
    }

    #[test]
    fn test_structural_variant_decrease_rejects_same_root_and_nonrecursive_field() {
        assert!(!structural_variant_decreases(
            &PureExpr::Var("self".into(), None),
            "self",
            &[StructuralRecursiveField {
                index: 1,
                allow_field0_carriers: false,
            }]
        ));
        let head = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::Var("self".into(), None)],
        };
        assert!(!structural_variant_decreases(
            &head,
            "self",
            &[StructuralRecursiveField {
                index: 1,
                allow_field0_carriers: false,
            }]
        ));
    }
}
