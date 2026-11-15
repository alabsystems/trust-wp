// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mutable-borrow function contract verification (RustHorn-style).
//!
//! Contains [`verify_mut_borrow_function_with_modes`] for verifying postconditions
//! of functions that take `&mut` parameters. These use
//! (current, final) variable pairs following the RustHorn encoding:
//!
//! - `*v` in contracts maps to `v_current` (value at function entry)
//! - `^v` in contracts maps to `v_final` (value when borrow ends)
//! - `old(*v)` maps to `v_current` (same as `*v` in postcondition context)
//!
//! # Submodules
//!
//! - [`bindings`]: per-parameter final-value variable declarations and alias equations
//! - [`collapse`]: `old(...)` wrapper normalization for mut-borrow postconditions
//! - [`helpers`]: Pure `PureExpr` canonicalization (bare Var→Deref rewriting, result projection detection)
//! - [`obligation`]: Per-slice obligation verification within push/pop scope
//! - [`resolve`]: dataflow-precise resolve assertions and prophecy writebacks

mod bindings;
pub(crate) mod collapse;
mod debug;
pub(crate) mod helpers;
mod obligation;
mod resolve;

use std::{
    collections::{HashMap, HashSet},
    panic::AssertUnwindSafe,
    sync::Arc,
};

use ay_dpll::api::Sort;
use tracing::debug;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_index, BorrowFinality, BorrowIdOrigin, ExprSort,
    ProjectedFinalPin, PureExpr, PureExprDepthLimitedTraversalExt as _,
};

pub(crate) use self::collapse::collapse_old_over_mut_ref_currents;
use self::{
    debug::debug_log_request,
    helpers::{
        canonicalize_mut_ref_vars, expr_has_non_projection_result_var, expr_has_result_projection,
    },
    obligation::verify_mut_borrow_single_obligation_slice_indexed,
};
use super::{
    catch_ay_sort_panics_outcome, expr_contains_result_var,
    pipeline::{run_verification_pipeline, PipelineOptions},
    process_isolation, result_is_bool_by_postcondition_with_context, Counterexample,
    MutBorrowRequest, UnknownReason, VerificationOutcome, VerificationResult,
};
use crate::{
    encoder::{
        effective_expr_annotation, extract_inner_var_annotation,
        sort_context::{ay_sort_to_expr_sort, resolve_nameable_expr},
        unsoundness, AYEncoder, MAX_ENCODING_DEPTH,
    },
    error::EncodingError,
};

fn preserve_temporal_wrappers_for_mut_borrow(
    expr: &PureExpr,
    temporal_params: &HashSet<String>,
) -> PureExpr {
    expr.rewrite_bottom_up_with_depth_limit(MAX_ENCODING_DEPTH, |node| match node {
        PureExpr::Deref(inner) => {
            PureExpr::Deref(preserve_temporal_wrapper_inner(inner, temporal_params))
        }
        PureExpr::Final(inner) => {
            PureExpr::Final(preserve_temporal_wrapper_inner(inner, temporal_params))
        }
        other => other,
    })
}

fn preserve_temporal_wrapper_inner(
    inner: Arc<PureExpr>,
    temporal_params: &HashSet<String>,
) -> Arc<PureExpr> {
    let PureExpr::Var(name, Some(sort)) = inner.as_ref() else {
        return inner;
    };
    if !temporal_params.contains(name) || matches!(sort, ExprSort::MutRef(_)) {
        return inner;
    }
    Arc::new(PureExpr::Var(name.clone(), None))
}

fn bind_whole_mut_ref_result(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
    result_sort: &Sort,
    result_var: ay_dpll::api::Term,
    mut_ref_inner_hint: Option<&ExprSort>,
    final_values: &HashMap<String, PureExpr>,
) -> Result<bool, EncodingError> {
    // Use effective_expr_annotation to account for Deref wrappers that peel
    // reference layers. For `Deref(Var("x", MutRef(MutRef(Int))))` (unnest
    // pattern), extract_inner_var_annotation returns MutRef(MutRef(Int)) but
    // the effective annotation after the Deref is MutRef(Int). (#2583)
    //
    // For ITE (conditional) result expressions like `if b { p.0 } else { p.1 }`,
    // effective_expr_annotation returns None because ITE is not a named expression.
    // Delegate to bind_whole_mut_ref_result_ite which constructs conditional
    // bindings for result_current, result_final, and result_id. (#2673)
    if let PureExpr::Ite(cond, then_branch, else_branch) = result_expr {
        return bind_whole_mut_ref_result_ite(
            encoder,
            cond,
            then_branch,
            else_branch,
            result_sort,
            result_var,
            mut_ref_inner_hint,
            final_values,
        );
    }

    let Some(ExprSort::MutRef(inner)) = effective_expr_annotation(result_expr) else {
        return Ok(false);
    };
    let Some(source_name) = resolve_nameable_expr(result_expr, None) else {
        return Ok(false);
    };

    let inner_sort = encoder.sort_from_expr_sort((**inner).clone());
    let result_current = encoder.get_or_declare_var("result_current", inner_sort.clone())?;
    let result_current_term =
        encoder.encode_pure(&PureExpr::Deref(Arc::new(result_expr.clone())))?;
    encoder.assert_eq(result_current, result_current_term);

    let result_final = encoder.get_or_declare_var("result_final", inner_sort.clone())?;
    // Only a returned borrow VARIABLE has `Final(result_expr)` as its prophecy.
    // For a reborrow through an outer layer (`&mut **x`), `Final(*x)` is the
    // inner borrow's prophecy, not the reborrow's; leave it unbound.
    if final_of_expr_is_result_prophecy(result_expr) {
        let result_final_term =
            encoder.encode_pure(&PureExpr::Final(Arc::new(result_expr.clone())))?;
        encoder.assert_eq(result_final, result_final_term);
    }

    let result_id = encoder.get_or_declare_var("result_id", Sort::Int)?;
    let source_id = encoder.get_or_declare_var(&format!("{source_name}_id"), Sort::Int)?;
    encoder.assert_eq(result_id, source_id);

    encoder.bind_whole_mut_ref(
        result_sort,
        &inner_sort,
        result_var,
        result_current,
        result_final,
        result_id,
    )?;
    Ok(true)
}

/// Handle ITE (conditional) result expressions for whole-borrow binding.
///
/// For `if cond { branch_a } else { branch_b }` where both branches are &mut,
/// constructs:
///   result_current = if cond then Deref(branch_a) else Deref(branch_b)
///   result_final   = if cond then Final(branch_a) else Final(branch_b)
///   result_id      = if cond then branch_a_id    else branch_b_id
///
/// This enables the solver to prove whole-borrow equalities like `result == p.0`
/// in the then-branch and `result == p.1` in the else-branch, which is exactly
/// what `pair_bor_mut` requires. (#2673)
///
/// `mut_ref_inner_hint` provides the inner T sort when neither branch carries
/// an explicit MutRef annotation but the result is known to be &mut T from a
/// `Var("result", Some(MutRef(inner)))` use in the postcondition. This rescues
/// the `pair_bor_mut` shape `if c { p.0 } else { p.1 }` where the driver lowers
/// `p.0` to a `LogicFnCall("__trust_wp_tuple_get_0", [Var("p", Tuple(N))])` with
/// no return-type annotation. (#5)
fn bind_whole_mut_ref_result_ite(
    encoder: &mut AYEncoder,
    cond: &PureExpr,
    then_branch: &PureExpr,
    else_branch: &PureExpr,
    result_sort: &Sort,
    result_var: ay_dpll::api::Term,
    mut_ref_inner_hint: Option<&ExprSort>,
    final_values: &HashMap<String, PureExpr>,
) -> Result<bool, EncodingError> {
    // Determine the inner T sort. Preferred sources, in order:
    //   1. then_branch annotation: e.g., Var("a", Some(MutRef(inner))).
    //   2. else_branch annotation: same shape, used when only one side carries.
    //   3. postcondition-derived hint: triggered when both branches are
    //      tuple-field projections of a mut-borrow tuple param (the
    //      `pair_bor_mut` shape) and the annotation is on a
    //      `Var("result", Some(MutRef(_)))` use in `ensures`.
    let then_field_name = tuple_field_branch_name(then_branch);
    let else_field_name = tuple_field_branch_name(else_branch);
    let inner: ExprSort = match effective_expr_annotation(then_branch) {
        Some(ExprSort::MutRef(inner)) => (**inner).clone(),
        _ => match effective_expr_annotation(else_branch) {
            Some(ExprSort::MutRef(inner)) => (**inner).clone(),
            _ => match (
                then_field_name.as_deref(),
                else_field_name.as_deref(),
                mut_ref_inner_hint,
            ) {
                (Some(then_field), Some(else_field), Some(hint))
                    if final_values.contains_key(then_field)
                        && final_values.contains_key(else_field) =>
                {
                    hint.clone()
                }
                _ => return Ok(false),
            },
        },
    };

    // Both branches must resolve to nameable expressions so we can look up _id vars.
    let then_name = match resolve_nameable_expr(then_branch, None) {
        Some(name) => name,
        None => match then_field_name.clone() {
            Some(name) => name,
            None => return Ok(false),
        },
    };
    let else_name = match resolve_nameable_expr(else_branch, None) {
        Some(name) => name,
        None => match else_field_name.clone() {
            Some(name) => name,
            None => return Ok(false),
        },
    };

    let cond_term = encoder.encode_pure(cond)?;
    let inner_sort = encoder.sort_from_expr_sort(inner.clone());
    let whole_field_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(inner.clone())));

    // For tuple-getter branches, pre-declare the per-field MutRef whole carrier
    // and tie it to the tuple-get application via mut_ref accessors. This is
    // what lets postcondition equalities `result == p.0` (encoded as MutRef
    // equality) decompose into the per-field current/final/id components.
    //
    // Without this, `tuple_get_X_MutRef(p_current)` is an unconstrained MutRef
    // term whose accessors have no relation to `p.X_current`/`p.X_final`/
    // `p.X_id`, leaving the prophecy/postcondition equality unprovable.
    if let Some(then_field) = then_field_name.as_deref() {
        bridge_tuple_field_to_mut_ref_carrier(
            encoder,
            then_branch,
            then_field,
            &whole_field_sort,
            &inner_sort,
        )?;
    }
    if let Some(else_field) = else_field_name.as_deref() {
        bridge_tuple_field_to_mut_ref_carrier(
            encoder,
            else_branch,
            else_field,
            &whole_field_sort,
            &inner_sort,
        )?;
    }

    // result_current = ite(cond, Deref(then_branch), Deref(else_branch))
    //
    // For tuple-getter branches, the structural Deref-push would yield
    // `tuple_get_X(p_current)` of MutRef sort — not the inner T value we need.
    // Use the per-field `p.X_current` directly to access the inner value.
    let then_current = if let Some(then_field) = then_field_name.as_deref() {
        encoder.get_or_declare_var(&format!("{then_field}_current"), inner_sort.clone())?
    } else {
        encoder.encode_pure(&PureExpr::Deref(Arc::new(then_branch.clone())))?
    };
    let else_current = if let Some(else_field) = else_field_name.as_deref() {
        encoder.get_or_declare_var(&format!("{else_field}_current"), inner_sort.clone())?
    } else {
        encoder.encode_pure(&PureExpr::Deref(Arc::new(else_branch.clone())))?
    };
    let result_current = encoder.get_or_declare_var("result_current", inner_sort.clone())?;
    // Use safe_ite for sort-safe ITE with panic isolation. (#2699)
    let ite_current = encoder.safe_ite(cond_term, then_current, else_current);
    encoder.assert_eq(result_current, ite_current);

    // result_final = ite(cond, Final(then_branch), Final(else_branch))
    let then_final = if let Some(then_field) = then_field_name.as_deref() {
        encoder.get_or_declare_var(&format!("{then_field}_final"), inner_sort.clone())?
    } else {
        encoder.encode_pure(&PureExpr::Final(Arc::new(then_branch.clone())))?
    };
    let else_final = if let Some(else_field) = else_field_name.as_deref() {
        encoder.get_or_declare_var(&format!("{else_field}_final"), inner_sort.clone())?
    } else {
        encoder.encode_pure(&PureExpr::Final(Arc::new(else_branch.clone())))?
    };
    let result_final = encoder.get_or_declare_var("result_final", inner_sort.clone())?;
    let ite_final = encoder.safe_ite(cond_term, then_final, else_final);
    encoder.assert_eq(result_final, ite_final);

    // result_id = ite(cond, then_name_id, else_name_id)
    let then_id = encoder.get_or_declare_var(&format!("{then_name}_id"), Sort::Int)?;
    let else_id = encoder.get_or_declare_var(&format!("{else_name}_id"), Sort::Int)?;
    let result_id = encoder.get_or_declare_var("result_id", Sort::Int)?;
    let ite_id = encoder.safe_ite(cond_term, then_id, else_id);
    encoder.assert_eq(result_id, ite_id);

    encoder.bind_whole_mut_ref(
        result_sort,
        &inner_sort,
        result_var,
        result_current,
        result_final,
        result_id,
    )?;
    Ok(true)
}

/// Recognize a tuple-field projection branch like
/// `LogicFnCall("__trust_wp_tuple_get_N", [Var(param, ...)])` and return the
/// canonical field-key name `"param.N"`. Returns None for non-tuple-getter
/// shapes or when the inner receiver is not a `Var`. Accepts the inner Var
/// being wrapped in `Deref` (from `canonicalize_mut_ref_vars`). (#5)
fn tuple_field_branch_name(branch: &PureExpr) -> Option<String> {
    let PureExpr::LogicFnCall { name, args } = branch else {
        return None;
    };
    let field_idx = tuple_field_logic_fn_index(name)?;
    if args.len() != 1 {
        return None;
    }
    let receiver = match &args[0] {
        PureExpr::Var(receiver, _) => receiver.as_str(),
        PureExpr::Deref(inner) | PureExpr::Old(inner) => match inner.as_ref() {
            PureExpr::Var(receiver, _) => receiver.as_str(),
            _ => return None,
        },
        _ => return None,
    };
    Some(format!("{receiver}.{field_idx}"))
}

/// Bridge a tuple-getter result back to a per-field whole MutRef carrier so
/// the encoder can decompose postcondition equalities like `result == p.0`.
///
/// Declares (if not present) a whole-MutRef variable `p.X` and an explicit
/// MutRef-returning `tuple_get_X` UF placeholder, then asserts the bridge
/// equalities:
///   `tuple_get_X_MutRef(p) == p.X`,
///   `tuple_get_X_MutRef(p_current) == p.X`,
///   `tuple_get_X_MutRef(p_final) == p.X`,
///   `tuple_get_X_MutRef(p_current_current) == p.X`,
///   `tuple_get_X_MutRef(p_current_final) == p.X`,
/// across every receiver-form variant that the negated-goal builder may
/// emit for the postcondition. Finally calls `bind_whole_mut_ref` to wire
/// `mut_ref_current(p.X)`/`_final`/`_id` to the per-field
/// `p.X_current`/`p.X_final`/`p.X_id` carriers declared by
/// `bind_final_values`.
///
/// This is the missing connection that lets `result == p.0` (encoded as a
/// MutRef equality between `result` and `tuple_get_0_MutRef(p_current)`) get
/// decomposed via `try_decompose_mut_ref_equality` into per-component
/// equalities that the per-field bindings can discharge. (#5)
fn bridge_tuple_field_to_mut_ref_carrier(
    encoder: &mut AYEncoder,
    branch: &PureExpr,
    field_key: &str,
    whole_field_sort: &Sort,
    inner_sort: &Sort,
) -> Result<(), EncodingError> {
    // Skip if the field MutRef carrier was already bridged with a conflicting
    // sort (idempotent on matching sort).
    if let Some(existing_sort) = encoder.var_sort(field_key).cloned() {
        if existing_sort != *whole_field_sort {
            return Ok(());
        }
    }
    let (getter_name, receiver_name) = match branch {
        PureExpr::LogicFnCall { name, args } if args.len() == 1 => match &args[0] {
            PureExpr::Var(receiver, _) => (name.as_str(), receiver.as_str()),
            _ => return Ok(()),
        },
        _ => return Ok(()),
    };
    let field_carrier = encoder.get_or_declare_var(field_key, whole_field_sort.clone())?;
    let param_sort = encoder
        .var_sort(receiver_name)
        .cloned()
        .unwrap_or(Sort::Int);
    let smt_name = trust_wp_core::logic::logic_fn_smt_name(getter_name);
    let param_sorts = vec![param_sort.clone()];
    let placeholder_key =
        mutref_tuple_getter_placeholder_smt_name(&smt_name, &param_sorts, whole_field_sort);
    let func_decl =
        encoder.get_or_declare_logic_func(&placeholder_key, &param_sorts, whole_field_sort.clone());
    // Bridge against every receiver-name view that the postcondition encoding
    // may produce. The negated-goal builder can lower the same tuple-getter to
    // `tuple_get_X(p)`, `tuple_get_X(p_current)`, `tuple_get_X(p_final)`, or
    // `tuple_get_X(p_current_current)` / `tuple_get_X(p_current_final)` depending
    // on which wrapper combination it sees; we anchor all of them to the field
    // carrier so the decomposed MutRef equality reduces to per-field current/
    // final/id components regardless of which view appears in the obligation.
    let mut bridge_receivers = Vec::with_capacity(5);
    if let Some(term) = encoder.var_term(receiver_name) {
        bridge_receivers.push(term);
    }
    for suffix in ["_current", "_final", "_current_current", "_current_final"] {
        let name = format!("{receiver_name}{suffix}");
        if encoder.var_sort(&name).is_some() {
            if let Ok(term) = encoder.get_or_declare_var(&name, param_sort.clone()) {
                bridge_receivers.push(term);
            }
        }
    }
    for receiver_term in bridge_receivers {
        let lhs_term = encoder.solver_mut().apply(&func_decl, &[receiver_term]);
        let bridge_term = encoder.eq_term(lhs_term, field_carrier);
        encoder.assert_term(bridge_term);
    }

    // Declare the per-field current/final/id components (already declared by
    // bind_final_values for mut-borrow tuple parameters; idempotent here).
    let current_term =
        encoder.get_or_declare_var(&format!("{field_key}_current"), inner_sort.clone())?;
    let final_term =
        encoder.get_or_declare_var(&format!("{field_key}_final"), inner_sort.clone())?;
    let id_term = encoder.get_or_declare_var(&format!("{field_key}_id"), Sort::Int)?;

    encoder.bind_whole_mut_ref(
        whole_field_sort,
        inner_sort,
        field_carrier,
        current_term,
        final_term,
        id_term,
    )
}

/// Compute the placeholder SMT name for a `tuple_get_X` UF returning a MutRef
/// carrier sort. Mirrors `AYEncoder::placeholder_smt_name` (which is
/// crate-private), avoiding a dependency on that internal helper. (#5)
fn mutref_tuple_getter_placeholder_smt_name(
    smt_name: &str,
    param_sorts: &[Sort],
    return_sort: &Sort,
) -> String {
    fn sort_tag(sort: &Sort) -> String {
        fn encode_tag(raw: &str) -> String {
            let mut encoded = String::new();
            for byte in raw.as_bytes() {
                let _ = std::fmt::Write::write_fmt(&mut encoded, format_args!("{byte:02x}"));
            }
            encoded
        }
        match sort {
            Sort::Bool => "b".to_string(),
            Sort::Int => "i".to_string(),
            Sort::Uninterpreted(name) => format!("u{}", encode_tag(name)),
            Sort::Datatype(dt) => format!("d{}", encode_tag(&dt.name)),
            other => format!("x{}", encode_tag(&format!("{other:?}"))),
        }
    }
    let params = if param_sorts.is_empty() {
        "nullary".to_string()
    } else {
        param_sorts
            .iter()
            .map(sort_tag)
            .collect::<Vec<_>>()
            .join("_")
    };
    let ret = sort_tag(return_sort);
    format!("{smt_name}__placeholder_{params}__ret_{ret}")
}

fn bind_final_nested_reborrow_result(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
    final_values: &HashMap<String, PureExpr>,
) -> Result<bool, EncodingError> {
    let Some(target_expr) = final_nested_reborrow_target(result_expr, final_values) else {
        return Ok(false);
    };

    let target_term = encoder.encode_pure(&target_expr)?;
    let target_sort = resolve_nameable_expr(&target_expr, None)
        .and_then(|name| encoder.var_sort(&name).cloned())
        .unwrap_or_else(|| encoder.infer_expr_sort_with_context(&target_expr, None));
    let result_current = encoder.get_or_declare_var("result_current", target_sort.clone())?;
    // `result_final` is deliberately left unbound: equating it with the same
    // term as `result_current` asserts `*result == ^result`, which is false
    // whenever the caller writes through the returned reborrow. (soundness)
    let _result_final = encoder.get_or_declare_var("result_final", target_sort)?;
    encoder.assert_eq(result_current, target_term);
    encoder.propagate_seq_value(target_term, result_current);
    Ok(true)
}

fn final_nested_reborrow_target(
    result_expr: &PureExpr,
    final_values: &HashMap<String, PureExpr>,
) -> Option<PureExpr> {
    let (base_name, base_sort, deref_depth) = peel_deref_var_chain(result_expr)?;
    let base_sort = base_sort?;
    let reference_layers = reference_like_layer_count(&base_sort);
    if reference_layers == 0 || deref_depth <= reference_layers {
        return None;
    }
    if !final_values
        .get(base_name)
        .is_some_and(|final_expr| resolve::is_identity_final_value(base_name, final_expr))
    {
        return None;
    }

    let mut target = PureExpr::Final(Arc::new(PureExpr::Var(
        base_name.to_string(),
        Some(base_sort),
    )));
    for _ in 1..reference_layers {
        target = PureExpr::Deref(Arc::new(target));
    }
    Some(target)
}

fn peel_deref_var_chain(expr: &PureExpr) -> Option<(&str, Option<ExprSort>, usize)> {
    let mut current = expr;
    let mut depth = 0usize;
    while let PureExpr::Deref(inner) = current {
        depth = depth.saturating_add(1);
        current = inner;
    }
    match current {
        PureExpr::Var(name, sort) => Some((name.as_str(), sort.clone(), depth)),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum ProjectionComponent {
    Current,
    Final,
}

fn projection_component_expr(expr: &PureExpr, component: ProjectionComponent) -> PureExpr {
    match expr {
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::clone(value),
            body: Arc::new(projection_component_expr(body, component)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::clone(assumption),
            body: Arc::new(projection_component_expr(body, component)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::clone(obligation),
            body: Arc::new(projection_component_expr(body, component)),
        },
        _ => match component {
            ProjectionComponent::Current => PureExpr::Deref(Arc::new(expr.clone())),
            ProjectionComponent::Final => PureExpr::Final(Arc::new(expr.clone())),
        },
    }
}

fn bind_result_projection_component(
    encoder: &mut AYEncoder,
    name: &str,
    expr: &PureExpr,
) -> Result<(), EncodingError> {
    let term = encoder.encode_pure(expr)?;
    let sort = encoder.solver().get_sort(term);
    let result_component = encoder.get_or_declare_var(name, sort)?;
    encoder.assert_eq(result_component, term);
    Ok(())
}

/// Defence in depth for borrows lent into the return value.
///
/// A `&mut` parameter whose borrow (whole, a tuple-field reborrow, or a
/// reborrow through an outer borrow layer) sits in a borrow position of the
/// return expression is written by the caller through `result`; its prophecy
/// is not the callee's to pin. Treat every such name (and its `name.*` field
/// entries) as mutation-continued so no `final_values` entry is asserted as a
/// fact and the structural gates never read it. Only removes premises.
fn continue_params_lent_into_return(
    mutation_continued_params: Option<HashSet<String>>,
    return_expr: Option<&PureExpr>,
    final_values: &HashMap<String, PureExpr>,
) -> Option<HashSet<String>> {
    let mut lent: Vec<String> = Vec::new();
    if let Some(ret) = return_expr {
        collect_return_lent_borrow_names(ret, &mut lent, 0);
    }
    if lent.is_empty() {
        return mutation_continued_params;
    }
    let mut params = mutation_continued_params.unwrap_or_default();
    for name in lent {
        let field_prefix = format!("{name}.");
        for key in final_values.keys() {
            if key.starts_with(&field_prefix) {
                params.insert(key.clone());
            }
        }
        params.insert(name);
    }
    Some(params)
}

fn collect_return_lent_borrow_names(expr: &PureExpr, out: &mut Vec<String>, depth: usize) {
    if depth > crate::encoder::MAX_ENCODING_DEPTH {
        return;
    }
    match expr {
        PureExpr::Var(name, Some(ExprSort::MutRef(_))) => out.push(name.clone()),
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => {
            collect_return_lent_borrow_names(body, out, depth + 1);
        }
        PureExpr::Ite(_, then_branch, else_branch) => {
            collect_return_lent_borrow_names(then_branch, out, depth + 1);
            collect_return_lent_borrow_names(else_branch, out, depth + 1);
        }
        PureExpr::LogicFnCall { name, args } if name.starts_with("__trust_wp_tuple") => {
            for arg in args {
                match arg {
                    // A field projection of a borrow is a field reborrow.
                    PureExpr::Var(base, Some(ExprSort::MutRef(_))) => out.push(base.clone()),
                    other => collect_return_lent_borrow_names(other, out, depth + 1),
                }
            }
        }
        PureExpr::Deref(_) => {
            if let Some((base, Some(sort), deref_depth)) = peel_deref_var_chain(expr) {
                if deref_depth < reference_like_layer_count(&sort) {
                    out.push(base.to_string());
                }
            }
        }
        _ => {}
    }
}

/// Does `expr` mention a borrow carrier (a `MutRef`-sorted variable) or a
/// parameter with tracked finality? Such an expression's `transform_postcondition_for_mut_refs`
/// image is not a sound description of the returned borrow's prophecy.
fn expr_mentions_borrow_state(expr: &PureExpr, final_values: &HashMap<String, PureExpr>) -> bool {
    let mut found = false;
    let _ = expr.rewrite_bottom_up_with_depth_limit(crate::encoder::MAX_ENCODING_DEPTH, |node| {
        if let PureExpr::Var(name, sort) = &node {
            let base = name.split('.').next().unwrap_or(name);
            if matches!(sort, Some(ExprSort::MutRef(_)))
                || final_values.contains_key(name.as_str())
                || final_values.contains_key(base)
            {
                found = true;
            }
        }
        node
    });
    found
}

/// `Final(expr)` is the returned borrow's prophecy only when `expr` IS the
/// borrow (a variable, or a branch-merge of variables). For a field or deeper
/// reborrow, `Final(tuple_get_i(x))` / `Final(*x)` names a DIFFERENT prophecy
/// (and collapses to the current value when `x` has an identity final).
fn final_of_expr_is_result_prophecy(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(..) => true,
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => final_of_expr_is_result_prophecy(body),
        PureExpr::Ite(_, then_branch, else_branch) => {
            final_of_expr_is_result_prophecy(then_branch)
                && final_of_expr_is_result_prophecy(else_branch)
        }
        _ => false,
    }
}

fn reference_like_layer_count(sort: &ExprSort) -> usize {
    match sort {
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => 1 + reference_like_layer_count(inner),
        _ => 0,
    }
}

/// Verify a mutable-borrow function contract with optional per-function mode overrides.
///
/// Accepts a [`MutBorrowRequest`] bundle to avoid long positional argument lists.
/// Supports `mode_overrides` to change the
/// effective visibility mode of logic functions without deep-cloning
/// `LogicFnDef` structs. Used by the driver for module-level scoping. (#564)
#[tracing::instrument(
    name = "trust_wp::verify_mut_borrow",
    level = "debug",
    skip_all,
    fields(
        requires = request.base.requires.len(),
        ensures = request.base.ensures.len(),
        track = ?request.base.track
    )
)]
pub fn verify_mut_borrow_function_with_modes(
    request: MutBorrowRequest<'_>,
) -> Result<VerificationResult, EncodingError> {
    Ok(legacy_result_from_outcome(
        verify_mut_borrow_function_with_modes_outcome(request)?,
    ))
}

fn legacy_result_from_outcome(outcome: VerificationOutcome) -> VerificationResult {
    if !matches!(outcome.result, VerificationResult::Verified(_)) {
        return outcome.result;
    }
    if verified_outcome_has_accepted_evidence(&outcome) {
        return outcome.result;
    }
    VerificationResult::Unknown(legacy_verified_evidence_gap_reason(&outcome, "mut_borrow"))
}

fn verified_outcome_has_accepted_evidence(outcome: &VerificationOutcome) -> bool {
    outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .is_some_and(|evidence| evidence.accepted_for_consumer)
}

fn legacy_verified_evidence_gap_reason(
    outcome: &VerificationOutcome,
    scope: &str,
) -> UnknownReason {
    let detail = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .map_or_else(
            || "missing solver evidence".to_string(),
            |evidence| {
                evidence
                    .consumer_rejection
                    .clone()
                    .unwrap_or_else(|| "solver evidence was not accepted for consumers".to_string())
            },
        );
    UnknownReason::SolverMessage(format!(
        "verified {scope} result lacks accepted solver evidence: {detail}"
    ))
}

/// Verify a mutable-borrow function contract and return solver provenance.
#[tracing::instrument(
    name = "trust_wp::verify_mut_borrow_outcome",
    level = "debug",
    skip_all,
    fields(
        requires = request.base.requires.len(),
        ensures = request.base.ensures.len(),
        track = ?request.base.track
    )
)]
pub fn verify_mut_borrow_function_with_modes_outcome(
    request: MutBorrowRequest<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    let retry = request.clone();
    let original = verify_mut_borrow_function_with_modes_outcome_single(request)?;
    Ok(super::guard_split::retry_with_guard_split(
        retry.base.requires,
        retry.base.ensures,
        original,
        |requires, ensures| {
            let mut sub = retry.clone();
            sub.base.requires = requires;
            sub.base.ensures = ensures;
            verify_mut_borrow_function_with_modes_outcome_single(sub)
        },
    ))
}

/// One unsplit mutable-borrow query (see [`super::guard_split`]).
fn verify_mut_borrow_function_with_modes_outcome_single(
    request: MutBorrowRequest<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    // Read BEFORE the request moves into the child: see the same gate on the
    // pure-function boundary.
    let injected_fail_closed_goal = request.base.injected_fail_closed_goal;
    let gate_goals: Vec<PureExpr> = request.base.ensures.to_vec();
    // Silently drop mode_overrides when lengths don't match (#2316, #2700).
    let mut request = request;
    if let (Some(logic_fns), Some(mode_overrides)) =
        (request.base.logic_fns, request.base.mode_overrides)
    {
        if mode_overrides.len() != logic_fns.len() {
            tracing::debug!(
                modes_len = mode_overrides.len(),
                fns_len = logic_fns.len(),
                "mode_overrides length mismatch in verify_mut_borrow — dropping overrides (#2316)"
            );
            request.base.mode_overrides = None;
        }
    }

    // Demotion (Verified → Unknown for encoding approximations) is
    // applied INSIDE verify_mut_borrow_function_with_modes_inner using a
    // post-bootstrap snapshot as the baseline. This absorbs false-positive
    // SortFallbackToIntFromLogicFn increments from sort hint collection
    // (bootstrap calls infer_expr_sort on LogicFnCall subexpressions before
    // declarations exist). (#994, #2106, #2365)
    let has_type_invariant_obligation = request
        .base
        .ensures
        .iter()
        .any(is_type_invariant_obligation_expr);

    // THE PLACEMENT GATE — see `super::placement_gate`.
    let timeout = request.base.timeout;
    let request = crate::verify::placement_gate::CheckPlacement::into_placed(request)?;

    let result = process_isolation::run_outcome_in_child(timeout, || {
        catch_ay_sort_panics_outcome(AssertUnwindSafe(|| {
            verify_mut_borrow_function_with_modes_inner(request)
        }))
    });
    let outcome = match result {
        Ok(mut outcome)
            if has_type_invariant_obligation
                && matches!(
                    &outcome.result,
                    VerificationResult::Unknown(UnknownReason::SolverPanic(reason))
                        if reason.contains("IncrementalTheoryState::pop() underflow")
                ) =>
        {
            debug!(
                "mut-borrow type-invariant obligation hit ay pop-underflow; \
                 returning conservative Failed result"
            );
            outcome.result = VerificationResult::Failed(Counterexample::empty());
            outcome
        }
        other => other?,
    };
    Ok(outcome
        .apply_mandatory_proof_authority()
        .apply_injected_goal_refutation_authority(injected_fail_closed_goal, &gate_goals)
        .apply_opaque_type_param_goal_refutation_authority(&gate_goals))
}

fn is_type_invariant_obligation_expr(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { method, .. } if trust_wp_core::logic::is_invariant_method_name(method)
    )
}

/// Walk `ensures` looking for the declared `ExprSort` annotation on the
/// `result` variable. The driver annotates `result` in postconditions with the
/// MIR-declared return type (`mir_body.return_ty()`), so the first such
/// annotation reflects the *declared* return type — which is authoritative for
/// deciding whether the function returns a value by-value or a mutable borrow.
///
/// Used to detect the by-value-deref-of-reborrow shape: a function whose body
/// returns `*borrow` (a `Copy` deref of a reborrow) but whose return expression
/// is tracked as the `MutRef` carrier. There the declared return type is a
/// non-reference `T`, even though the return expression is `MutRef(T)`.
fn declared_result_annotation(ensures: &[PureExpr]) -> Option<ExprSort> {
    fn walk(expr: &PureExpr) -> Option<ExprSort> {
        match expr {
            PureExpr::Var(name, Some(sort)) if name == "result" => Some(sort.clone()),
            PureExpr::BinOp(l, _, r) => walk(l).or_else(|| walk(r)),
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => walk(inner),
            PureExpr::Ite(c, t, e) => walk(c).or_else(|| walk(t)).or_else(|| walk(e)),
            PureExpr::MethodCall { receiver, args, .. } => {
                walk(receiver).or_else(|| args.iter().find_map(walk))
            }
            PureExpr::LogicFnCall { args, .. } => args.iter().find_map(walk),
            PureExpr::Match { scrutinee, arms } => {
                walk(scrutinee).or_else(|| arms.iter().find_map(|arm| walk(&arm.body)))
            }
            PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => walk(body),
            PureExpr::Let { value, body, .. } => walk(value).or_else(|| walk(body)),
            PureExpr::LetAssume {
                assumption, body, ..
            } => walk(assumption).or_else(|| walk(body)),
            PureExpr::LetObligation {
                obligation, body, ..
            } => walk(obligation).or_else(|| walk(body)),
            _ => None,
        }
    }
    ensures.iter().find_map(walk)
}

/// Whether an `ExprSort` denotes a non-reference value type. References
/// (`MutRef`/`Ref`) are excluded; everything else (including type parameters,
/// datatypes, tuples, and primitive views) is treated as a by-value type.
fn expr_sort_is_non_reference(sort: &ExprSort) -> bool {
    !matches!(sort, ExprSort::MutRef(_) | ExprSort::Ref(_))
}

/// Walk `ensures` looking for a `Var("result", Some(MutRef(inner)))` annotation
/// and return the `inner` ExprSort. Used to recover the function's return-type
/// MutRef carrier when the return expression itself does not carry a MutRef
/// annotation (e.g., when the body returns `tuple_get_X(p)` from a tuple of
/// mut-refs). (#5)
fn find_result_var_mut_ref_inner(ensures: &[PureExpr]) -> Option<ExprSort> {
    fn walk(expr: &PureExpr) -> Option<ExprSort> {
        match expr {
            PureExpr::Var(name, Some(ExprSort::MutRef(inner))) if name == "result" => {
                Some((**inner).clone())
            }
            PureExpr::BinOp(l, _, r) => walk(l).or_else(|| walk(r)),
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => walk(inner),
            PureExpr::Ite(c, t, e) => walk(c).or_else(|| walk(t)).or_else(|| walk(e)),
            PureExpr::MethodCall { receiver, args, .. } => {
                walk(receiver).or_else(|| args.iter().find_map(walk))
            }
            PureExpr::LogicFnCall { args, .. } => args.iter().find_map(walk),
            PureExpr::Match { scrutinee, arms } => {
                walk(scrutinee).or_else(|| arms.iter().find_map(|arm| walk(&arm.body)))
            }
            PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => walk(body),
            PureExpr::Let { value, body, .. } => walk(value).or_else(|| walk(body)),
            PureExpr::LetAssume {
                assumption, body, ..
            } => walk(assumption).or_else(|| walk(body)),
            PureExpr::LetObligation {
                obligation, body, ..
            } => walk(obligation).or_else(|| walk(body)),
            _ => None,
        }
    }
    ensures.iter().find_map(walk)
}

fn bind_result_expr(
    encoder: &mut AYEncoder,
    result_expr: &PureExpr,
    ensures: &[PureExpr],
    final_values: &HashMap<String, PureExpr>,
) -> Result<(), EncodingError> {
    // Context-aware inference for result sort detection. (#1965)
    let inferred_result_is_bool =
        encoder.infer_expr_sort_with_context(result_expr, None) == Sort::Bool;
    // result_is_bool_by_postcondition_with_context probes postconditions using
    // encoder sort state plus a structural Bool oracle. Bracket with snapshot
    // save/restore so this analytical pass does not pollute the demotion
    // baseline if it touches conservative fallback lanes. (#994, #2365, #2624)
    let analytical_snap = unsoundness::snapshot();
    let postcondition_says_bool = result_is_bool_by_postcondition_with_context(encoder, ensures);
    unsoundness::restore(&analytical_snap);
    let result_is_bool =
        encoder.is_bool_var("result") || postcondition_says_bool || inferred_result_is_bool;
    if result_is_bool {
        if let PureExpr::Var(alias, _) = result_expr {
            encoder.mark_bool_var(alias);
        }
    }
    let inferred_result_sort = if result_is_bool {
        Sort::Bool
    } else {
        let inferred = super::shared_constraints::infer_result_sort(encoder, result_expr);
        // Consult ExprSort annotation from result_expr and sort hints
        // when syntactic inference defaults to Int. (#994 Phase 2d)
        if inferred == Sort::Int {
            let ann = extract_inner_var_annotation(result_expr);
            encoder.resolve_var_sort_or_int_with_annotation("result", ann)
        } else {
            inferred
        }
    };
    let projection_only_result = ensures.iter().any(expr_has_result_projection)
        && !ensures.iter().any(expr_has_non_projection_result_var);
    let preserve_whole_result = should_preserve_whole_result_expr(
        result_expr,
        ensures,
        final_values,
        projection_only_result,
    );
    let result_expr_is_whole_mut_ref = effective_expr_annotation(result_expr)
        .is_some_and(|sort| matches!(sort, ExprSort::MutRef(_)));

    // By-value-deref-of-reborrow shape (bug/final_borrows::box_reborrow_indirect):
    // the function body returns `*borrow` — the `Copy` deref of a reborrow — so
    // the source-level return value is the *current value* of the borrow, type
    // `T`. But the return expression is tracked as the `MutRef(T)` carrier. When
    // the MIR-declared return type (recovered from the postcondition annotation
    // on `result`) is a non-reference `T`, bind `result` at `T` to the borrow's
    // current value (`Deref(borrow)` → `mut_ref_current(borrow)`), rather than to
    // the whole mut-ref carrier. Without this, `result` is declared at sort
    // `MutRef(T)` while the postcondition's `result` is `T`, and the resulting
    // `result == **x` equality hits sort coercion (a fresh unconstrained const),
    // disconnecting the obligation and producing a spurious counterexample.
    //
    // Guarded strictly on a non-reference declared return type so genuine
    // mut-ref-returning functions (reborrow_id, unnesting_non_extensional,
    // select_field, reborrow_in_box, …) — whose declared `result` is `MutRef` —
    // are untouched.
    let value_deref_of_reborrow = result_expr_is_whole_mut_ref
        && !projection_only_result
        && declared_result_annotation(ensures)
            .is_some_and(|sort| expr_sort_is_non_reference(&sort));

    let direct_whole_result_target = if result_expr_is_whole_mut_ref {
        None
    } else {
        direct_whole_result_equality_target(ensures, final_values, projection_only_result)
    };
    let derefed_binding_expr;
    let binding_expr = if value_deref_of_reborrow {
        derefed_binding_expr = PureExpr::Deref(Arc::new(result_expr.clone()));
        &derefed_binding_expr
    } else {
        direct_whole_result_target.unwrap_or(result_expr)
    };
    // Recover MutRef inner sort from the postcondition's
    // `Var("result", Some(MutRef(_)))` annotation when the result expression is
    // an Ite over tuple-getters (the `pair_bor_mut` shape: branches are
    // `LogicFnCall("__trust_wp_tuple_get_X", [Var(p, Tuple)])` with no MutRef
    // annotation). (#5)
    let result_mut_ref_inner_hint = if !projection_only_result
        && matches!(binding_expr, PureExpr::Ite(_, _, _))
        && effective_expr_annotation(binding_expr).is_none()
    {
        find_result_var_mut_ref_inner(ensures)
    } else {
        None
    };
    let whole_mut_ref_result_sort = match effective_expr_annotation(binding_expr) {
        Some(sort @ ExprSort::MutRef(_)) if !projection_only_result => {
            Some(encoder.sort_from_expr_sort(sort.clone()))
        }
        _ => result_mut_ref_inner_hint
            .as_ref()
            .map(|inner| encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(inner.clone())))),
    };
    let param_names: HashSet<&str> = final_values.keys().map(String::as_str).collect();
    let canonicalized = if preserve_whole_result {
        binding_expr.clone()
    } else {
        canonicalize_mut_ref_vars(binding_expr, &param_names)
    };
    let body_term = encoder.encode_pure(&canonicalized)?;
    let body_sort = encoder.solver().get_sort(body_term);
    let result_sort = if projection_only_result {
        // For `&mut T` returns whose contracts mention only `*result`/`^result`,
        // bind `result_current`/`result_final` at the referent sort from the
        // encoded body. The source `result` annotation is the whole-borrow
        // carrier and would otherwise leak into projection aliases.
        body_sort.clone()
    } else if value_deref_of_reborrow {
        // By-value return of `*borrow`: bind `result` at the referent sort `T`
        // from the encoded `mut_ref_current(borrow)` body, NOT the MutRef carrier
        // that `inferred_result_sort` would derive from the return expression.
        body_sort.clone()
    } else if let Some(sort) = whole_mut_ref_result_sort {
        sort
    } else {
        inferred_result_sort
    };
    let result_var = encoder.get_or_declare_var("result", result_sort.clone())?;
    encoder.assert_eq(result_var, body_term);
    encoder.propagate_seq_value(body_term, result_var);
    encoder.propagate_body_view_seq_value_to_result(result_expr);
    // Skip rebinding when the result is a tuple-getter-Ite over a mut-borrow
    // tuple (`pair_bor_mut` shape): `result` is the MutRef carrier, `body_term`
    // is the Int ITE aux from the tuple-getter ITE — rebinding would discard
    // the MutRef carrier identity and break MutRef-sort equalities in the
    // postcondition encoding. (#5)
    let suppress_rebind_for_mut_ref_ite_hint =
        result_mut_ref_inner_hint.is_some() && matches!(result_expr, PureExpr::Ite(..));
    if should_rebind_result_var_body(result_expr) && !suppress_rebind_for_mut_ref_ite_hint {
        if matches!(result_expr, PureExpr::Var(..)) {
            debug!(
                "[TRUST_WP_DEBUG] rebinding mut-borrow result to call-result alias: {result_expr:?}"
            );
        }
        encoder.rebind_var_with_authenticated_witness(
            "result",
            body_term,
            result_sort.clone(),
            result_var,
        );
    }

    if bind_final_nested_reborrow_result(encoder, &canonicalized, final_values)? {
        return Ok(());
    }

    if bind_whole_mut_ref_result(
        encoder,
        binding_expr,
        &result_sort,
        result_var,
        result_mut_ref_inner_hint.as_ref(),
        final_values,
    )? {
        return Ok(());
    }

    if ensures.iter().any(expr_has_result_projection) {
        if matches!(ay_sort_to_expr_sort(&body_sort), Some(ExprSort::MutRef(_))) {
            let result_current_expr =
                projection_component_expr(&canonicalized, ProjectionComponent::Current);
            bind_result_projection_component(encoder, "result_current", &result_current_expr)?;

            if final_of_expr_is_result_prophecy(&canonicalized) {
                let result_final_expr =
                    projection_component_expr(&canonicalized, ProjectionComponent::Final);
                bind_result_projection_component(encoder, "result_final", &result_final_expr)?;
            }
        } else {
            let result_current =
                encoder.get_or_declare_var("result_current", result_sort.clone())?;
            encoder.assert_eq(result_current, body_term);

            // A field/projection of a `&mut` param returned as a borrow: its
            // prophecy is NOT the current-state term with `*x` rewritten to
            // `^x` (which leaves `Var(x, MutRef)` unchanged and so equates
            // `^result` with `*result`). Leave it unbound in that case.
            if !expr_mentions_borrow_state(&canonicalized, final_values) {
                let mut_ref_param_names: HashSet<String> = final_values.keys().cloned().collect();
                let result_final_expr =
                    canonicalized.transform_postcondition_for_mut_refs(&mut_ref_param_names);
                let result_final =
                    encoder.get_or_declare_var("result_final", result_sort.clone())?;
                let result_final_term = encoder.encode_pure(&result_final_expr)?;
                encoder.assert_eq(result_final, result_final_term);
            }
        }
    }

    Ok(())
}

fn should_preserve_whole_result_expr(
    result_expr: &PureExpr,
    ensures: &[PureExpr],
    final_values: &HashMap<String, PureExpr>,
    projection_only_result: bool,
) -> bool {
    if projection_only_result {
        return false;
    }
    if effective_expr_annotation(result_expr)
        .is_some_and(|sort| matches!(sort, ExprSort::MutRef(_)))
    {
        return true;
    }
    let PureExpr::Var(name, _) = result_expr else {
        return false;
    };
    final_values.contains_key(name.as_str())
        && ensures
            .iter()
            .any(|ensure| is_direct_result_equality(ensure, result_expr))
}

fn direct_whole_result_equality_target<'a>(
    ensures: &'a [PureExpr],
    final_values: &HashMap<String, PureExpr>,
    projection_only_result: bool,
) -> Option<&'a PureExpr> {
    if projection_only_result {
        return None;
    }
    ensures.iter().find_map(|ensure| {
        let target = direct_result_equality_target(ensure)?;
        let PureExpr::Var(name, Some(ExprSort::MutRef(_))) = target else {
            return None;
        };
        final_values.contains_key(name.as_str()).then_some(target)
    })
}

fn direct_result_equality_target(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::BinOp(left, trust_wp_core::formula::BinOp::Eq, right) => {
            if matches!(left.as_ref(), PureExpr::Var(name, _) if name == "result") {
                Some(right.as_ref())
            } else if matches!(right.as_ref(), PureExpr::Var(name, _) if name == "result") {
                Some(left.as_ref())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_direct_result_equality(expr: &PureExpr, rhs: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(left, trust_wp_core::formula::BinOp::Eq, right) => {
            (matches!(left.as_ref(), PureExpr::Var(name, _) if name == "result")
                && right.as_ref() == rhs)
                || (matches!(right.as_ref(), PureExpr::Var(name, _) if name == "result")
                    && left.as_ref() == rhs)
        }
        _ => false,
    }
}

fn should_rebind_result_var_body(result_expr: &PureExpr) -> bool {
    super::function::result_binding::should_rebind_result_var(result_expr)
}

/// Groups borrow-related parameters shared across mut-borrow verification paths.
struct BorrowContext<'a> {
    final_values: &'a HashMap<String, PureExpr>,
    resolve_assumptions: Option<&'a Vec<String>>,
    prophecy_writebacks: Option<&'a HashMap<String, String>>,
    borrow_finality: Option<&'a HashMap<String, BorrowFinality>>,
    borrow_id_origins: Option<&'a HashMap<String, BorrowIdOrigin>>,
    mutation_continued_params: Option<&'a HashSet<String>>,
    slice_length_stable_vars: Option<&'a Vec<String>>,
    /// Caller-side projected expiry pins (#prophecy-slots M5).
    projected_final_pins: Option<&'a Vec<ProjectedFinalPin>>,
}

#[derive(Clone, Copy)]
enum FreshMutBorrowBaseMode {
    Full,
    AxiomLight,
}

fn apply_mut_borrow_base_assertions(
    encoder: &mut AYEncoder,
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    borrow: &BorrowContext<'_>,
) -> Result<(), EncodingError> {
    bindings::bind_final_values(
        encoder,
        borrow.final_values,
        borrow.mutation_continued_params,
    )?;

    // #prophecy-slots M5: the caller-side expiry pins go in beside the
    // parameter finals, BEFORE the resolve assertions — a pin names a borrow
    // the resolve lane never sees (it has no parameter name), so the two
    // cannot contradict each other by construction.
    if let Some(pins) = borrow.projected_final_pins {
        bindings::bind_projected_final_values(encoder, pins)?;
    }

    resolve::emit_resolve_assertions(
        encoder,
        borrow.resolve_assumptions,
        borrow.mutation_continued_params,
        borrow.final_values,
        ensures,
    );
    if let Some(slice_vars) = borrow.slice_length_stable_vars {
        for var_name in slice_vars {
            resolve::emit_slice_length_preservation(encoder, var_name);
        }
    }
    resolve::emit_prophecy_writebacks(
        encoder,
        borrow.prophecy_writebacks,
        borrow.borrow_finality,
        borrow.resolve_assumptions,
        borrow.borrow_id_origins,
        borrow.mutation_continued_params,
        Some(borrow.final_values),
    );
    resolve::emit_borrow_id_constraints(
        encoder,
        borrow.borrow_id_origins,
        borrow.prophecy_writebacks,
    )?;

    if let Some(result_expr) = return_expr {
        bind_result_expr(encoder, result_expr, ensures, borrow.final_values)?;
        // Path condition propagation for proof_assert (#1457):
        // bind_result_expr encodes LetAssume as implication (assumption => body)
        // and binds result to that value. The assumption itself is not asserted
        // as a standalone fact, so postconditions that do not reference `result`
        // (typical for proof_assert VCs) cannot use branch conditions, let-binding
        // equalities, or pattern-match discriminant constraints. Assert them
        // directly so the solver has them available.
        super::shared_constraints::assert_body_let_assume_path_conditions(encoder, result_expr)?;
    } else if ensures.iter().any(expr_contains_result_var) {
        // return_expr is None but postconditions reference `result`.
        //
        // Before giving up and marking result as unconstrained, try to synthesize
        // a result expression from the postcondition structure. This handles
        // patterns like `pair_bor_mut` where the driver fails to extract the
        // conditional field-projection return expression from MIR, but the
        // postcondition contains `result == <expr>` in ITE branches. (#2673)
        if let Some(synthesized) = helpers::synthesize_result_expr_from_postconditions(ensures) {
            debug!("[TRUST_WP_DEBUG] synthesized result_expr from postcondition: {synthesized:?}");

            bind_result_expr(encoder, &synthesized, ensures, borrow.final_values)?;
        } else {
            // `result` will be an unconstrained free SMT variable. Increment
            // the unsoundness counter so demotion can catch it. (#2364, #2663)
            unsoundness::increment(unsoundness::UnsoundnessCategory::UnconstrainedResultVar);
        }
    }
    Ok(())
}

fn fresh_mut_borrow_base_recheck(
    base: &super::types::VerificationBase<'_>,
    context_exprs: &[&PureExpr],
    borrow: &BorrowContext<'_>,
    mode: FreshMutBorrowBaseMode,
) -> Result<VerificationResult, EncodingError> {
    let setup_result =
        super::setup::setup_verification_encoder(&super::setup::VerificationSetup {
            requires: base.requires,
            ensures: base.ensures,
            context_exprs,
            result_expr: base.return_expr,
            ghost_context: base.ghost_context,
            logic_fns: base.logic_fns,
            mode_overrides: base.mode_overrides,
            type_invariants: base.type_invariants,
            track: base.track.unwrap_or_default(),
            timeout: base.timeout,
            type_constants: base.type_constants,
            closure_captures: base.closure_captures,
            adt_decls: base.adt_decls.as_ref(),
            adt_field_ranges: base.adt_field_ranges.as_ref(),
        })?;
    let mut encoder = setup_result.encoder;
    encoder.set_total_int_arithmetic(base.total_int_arithmetic);
    encoder.set_logic_ground_mode(base.logic_ground_mode);
    if let Some(ranges) = base.adt_field_ranges.clone() {
        encoder.set_adt_field_ranges(ranges);
    }

    if let Some(ghost_exprs) = base.ghost_context {
        for ghost_expr in ghost_exprs {
            let term = encoder.encode_pure(ghost_expr)?;
            encoder.assert_term(term);
        }
        super::shared_constraints::flatten_ghost_implications(&mut encoder, ghost_exprs)?;
        super::shared_constraints::instantiate_precondition_foralls_for_ghost(
            &mut encoder,
            base.requires,
            base.ensures,
            ghost_exprs,
        )?;
        super::shared_constraints::assert_ghost_alias_method_congruence(
            &mut encoder,
            base.requires,
            base.ensures,
            ghost_exprs,
        )?;
    }
    super::assert_container_element_invariants(&mut encoder, base.requires, base.type_invariants)?;

    apply_mut_borrow_base_assertions(&mut encoder, base.ensures, base.return_expr, borrow)?;

    if let Some(captures) = base.closure_captures {
        super::assert_closure_capture_projections(&mut encoder, captures, "[mut_borrow] ")?;
        super::assert_captured_param_type_invariants(
            &mut encoder,
            captures,
            base.type_invariants,
            base.requires,
        )?;
    }

    super::shared_constraints::assert_current_chain_alias_constraints(&mut encoder)?;
    let body_assumptions = base
        .return_expr
        .map(super::solver_tail::collect_body_let_assume_assumptions)
        .unwrap_or_default();
    if matches!(mode, FreshMutBorrowBaseMode::Full) {
        super::solver_tail::assert_standard_axioms(&mut encoder, base.requires, &body_assumptions)?;
        encoder.maybe_assert_logic_ground_instances()?;
    }

    Ok(match mode {
        // The AxiomLight recheck classifies literal-`false` / unconstrained
        // closure-capture obligations: its SAT base IS the refutation, so it
        // must leave a validated model behind (see
        // `resolve_base_sat_result_with_witness`).
        FreshMutBorrowBaseMode::AxiomLight => {
            super::solver_tail::resolve_base_sat_result_with_witness(&mut encoder)
        }
        FreshMutBorrowBaseMode::Full => {
            super::solver_tail::resolve_base_sat_result_with_tight_timeout(&mut encoder)
        }
    })
}

fn verify_mut_borrow_function_with_modes_inner(
    request: crate::verify::placement_gate::Placed<MutBorrowRequest<'_>>,
) -> Result<VerificationOutcome, EncodingError> {
    let request = request.into_inner();
    let MutBorrowRequest {
        mut base,
        final_values,
        resolve_assumptions,
        prophecy_writebacks,
        borrow_finality,
        borrow_id_origins,
        mutation_continued_params,
        slice_length_stable_vars,
        projected_final_pins,
    } = request;
    let mutation_continued_params =
        continue_params_lent_into_return(mutation_continued_params, base.return_expr, final_values);
    let original_requires = base.requires;
    let original_ensures = base.ensures;
    let original_ghost_context = base.ghost_context;
    let original_return_expr = base.return_expr;
    let track = base.track.unwrap_or_default();

    debug_log_request(
        &track,
        original_requires,
        original_ensures,
        final_values,
        original_return_expr,
        original_ghost_context,
        mutation_continued_params.as_ref(),
    );

    let mut_ref_param_names: HashSet<String> = final_values.keys().cloned().collect();
    let normalized_requires: Vec<PureExpr> = original_requires
        .iter()
        .map(|req| preserve_temporal_wrappers_for_mut_borrow(req, &mut_ref_param_names))
        .collect();
    let normalized_ensures: Vec<PureExpr> = original_ensures
        .iter()
        .map(|ens| {
            let collapsed = collapse_old_over_mut_ref_currents(ens, &mut_ref_param_names);
            preserve_temporal_wrappers_for_mut_borrow(&collapsed, &mut_ref_param_names)
        })
        .collect();
    let normalized_ghost_context: Option<Vec<PureExpr>> = original_ghost_context.map(|ghosts| {
        ghosts
            .iter()
            .map(|ghost| preserve_temporal_wrappers_for_mut_borrow(ghost, &mut_ref_param_names))
            .collect()
    });
    let normalized_return_expr = original_return_expr
        .map(|ret| preserve_temporal_wrappers_for_mut_borrow(ret, &mut_ref_param_names));
    let synthesized_return_expr = if normalized_return_expr.is_none()
        && normalized_ensures.iter().any(expr_contains_result_var)
    {
        helpers::synthesize_result_expr_from_postconditions(&normalized_ensures)
    } else {
        None
    };
    let normalized_final_values: HashMap<String, PureExpr> = final_values
        .iter()
        .map(|(name, expr)| {
            (
                name.clone(),
                preserve_temporal_wrappers_for_mut_borrow(expr, &mut_ref_param_names),
            )
        })
        .collect();
    let final_values = &normalized_final_values;
    base.requires = normalized_requires.as_slice();
    base.ensures = normalized_ensures.as_slice();
    base.ghost_context = normalized_ghost_context.as_deref();
    base.return_expr = normalized_return_expr
        .as_ref()
        .or(synthesized_return_expr.as_ref());

    let mut context_exprs: Vec<&PureExpr> = final_values.values().collect();
    if let Some(ret) = base.return_expr {
        context_exprs.push(ret);
    }
    let borrow_ctx = BorrowContext {
        final_values,
        resolve_assumptions: resolve_assumptions.as_ref(),
        prophecy_writebacks: prophecy_writebacks.as_ref(),
        borrow_finality: borrow_finality.as_ref(),
        borrow_id_origins: borrow_id_origins.as_ref(),
        mutation_continued_params: mutation_continued_params.as_ref(),
        slice_length_stable_vars: slice_length_stable_vars.as_ref(),
        projected_final_pins: projected_final_pins.as_ref(),
    };
    let fresh_base_recheck_base = base.clone();
    // Memoized: the fresh base recheck depends only on the BASE, which is
    // identical for every obligation slice — one rebuild+solve per function.
    let fresh_base_recheck_cache: std::cell::RefCell<Option<VerificationResult>> =
        std::cell::RefCell::new(None);
    let fresh_base_recheck = || {
        if let Some(cached) = fresh_base_recheck_cache.borrow().clone() {
            return Ok(cached);
        }
        let result = fresh_mut_borrow_base_recheck(
            &fresh_base_recheck_base,
            &context_exprs,
            &borrow_ctx,
            FreshMutBorrowBaseMode::Full,
        )?;
        // Only memoize decisive verdicts; transient solver-limited Unknowns
        // must not poison later slices' rescues.
        if !matches!(&result, VerificationResult::Unknown(_))
            || matches!(
                &result,
                VerificationResult::Unknown(UnknownReason::SolverMessage(_))
            )
        {
            *fresh_base_recheck_cache.borrow_mut() = Some(result.clone());
        }
        Ok(result)
    };
    let literal_false_base_recheck = || {
        fresh_mut_borrow_base_recheck(
            &fresh_base_recheck_base,
            &context_exprs,
            &borrow_ctx,
            FreshMutBorrowBaseMode::AxiomLight,
        )
    };

    let pipeline_options = PipelineOptions {
        context_exprs: &context_exprs,
        mut_borrow_final_values: Some(final_values),
        mutation_continued_params: mutation_continued_params.as_ref(),
        closure_capture_debug_prefix: "[mut_borrow] ",
        axiom_debug_label: "mut-borrow function",
        fresh_base_recheck: Some(&fresh_base_recheck),
        literal_false_base_recheck: Some(&literal_false_base_recheck),
        structural_verified_shortcuts: false,
        slice_length_stable_vars: slice_length_stable_vars.as_ref(),
        // Certificates must carry the PreparedAssertion-side claim text the
        // reporting firewall recomputes — not the temporal-wrapper-normalized
        // form above, whose `Var` sort-annotation erasure would make every
        // certificate a "source claim mismatch" once ay certifies the proof.
        proof_assert_prepared_source: Some((original_ensures, original_requires)),
    };
    let induction_logic_fns = base.logic_fns;
    let induction_mode_overrides = base.mode_overrides;
    let (result, provenance) = run_verification_pipeline(
        base,
        &pipeline_options,
        |ctx| {
            apply_mut_borrow_base_assertions(
                ctx.encoder,
                ctx.ensures,
                ctx.return_expr,
                &borrow_ctx,
            )?;
            // Bounded structural-induction lemma for recursive-datatype
            // `get`/`len` logic fns: a `&mut List` postcondition such as
            // `forall i. 0<=i<len(l) ==> get(^l, i) == Some(_)` needs the
            // "every in-range index is defined" fact, discharged via the
            // datatype's induction principle (base + step sub-proofs) plus the
            // Option payload bridges. SOUND — emits only genuine theorems,
            // inert otherwise. (#all_zero Obl1)
            ctx.encoder.emit_bounded_get_some_structural_induction(
                ctx.ensures,
                induction_logic_fns,
                induction_mode_overrides,
            );
            // Assert `_current`-chain alias constraints so that derived
            // variables like `p_current_current` (created when encoding
            // `Deref(Deref(Var("p")))` in postconditions) are equated to
            // their parent `p_current`. Without this, value-type parameters
            // containing inner `&mut` fields (e.g., `p: (&mut T, &mut T)`)
            // produce unconstrained `_current_current` variables that the
            // solver cannot connect back to the base binding, causing
            // "incomplete/unknown" verification results. (#2673)
            //
            // The recheck path (fresh_mut_borrow_base_recheck) already calls
            // this, but the main pipeline was missing it.
            super::shared_constraints::assert_current_chain_alias_constraints(ctx.encoder)?;
            Ok(())
        },
        || (),
        verify_mut_borrow_single_obligation_slice_indexed,
    )?;
    Ok(VerificationOutcome::new(result, provenance))
}

#[cfg(test)]
mod bindings_tests;
#[cfg(test)]
mod projected_pin_tests;
#[cfg(test)]
mod quantified_negation_tests;
#[cfg(test)]
mod resolve_mutation_tests;
#[cfg(test)]
mod resolve_prophecy_tests;
#[cfg(test)]
mod resolve_ssa_tests;
#[cfg(test)]
mod slice3_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod type_param_tests;
