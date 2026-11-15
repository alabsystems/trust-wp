// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared verification bootstrap used across function and loop setup paths.

use std::{collections::HashMap, time::Duration};

use ay_dpll::api::{DatatypeSort, Sort};
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::tuple_logic_fn_arity, PureExpr,
        PureExprDepthLimitedTraversalExt as _,
    },
    logic::{
        type_invariant_method_name, AdtDecls, AdtFieldRanges, LogicFnDef, LogicMode,
        TypeInvariantDef,
    },
    TrackLevel,
};

use super::{
    detect_logic_requirements, filter_logic_functions_for_goal, filter_type_invariants_for_goal,
    formula_exprs_with_type_invariant_bodies,
};
use crate::{
    encoder::{
        closure_sorts::closure_symbol_suffix,
        match_enc::{datatype_constructor_matches, short_constructor_name, MatchDatatypeKind},
        sort_context::{
            expr_sort_to_ay_sort, extract_base_var_name,
            preseed::{
                collect_active_logic_fn_param_name_sorts, collect_declared_fn_domain_sorts_batch,
                collect_logic_fn_def_domain_sorts,
            },
            var_collection::{
                collect_variable_usage, collect_variable_usage_as_formula, determine_sort,
            },
            SortPlan, SortPlanBuilder,
        },
        AYEncoder, MAX_ENCODING_DEPTH,
    },
    error::EncodingError,
    expr::expr_has_mut_ref_carrier,
    verify::{
        new_encoder_for_track_with_arrays, option_datatype_from_constructor_expr,
        register_type_invariants_on_encoder, result_match_datatype_from_postcondition,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::verify) enum ExprRole {
    Formula,
    Value,
}

#[derive(Clone, Copy, Debug)]
pub(in crate::verify) struct ExprSlice<'a> {
    pub(in crate::verify) exprs: &'a [PureExpr],
    pub(in crate::verify) role: ExprRole,
}

impl<'a> ExprSlice<'a> {
    #[must_use]
    pub(in crate::verify) fn formula(exprs: &'a [PureExpr]) -> Self {
        Self {
            exprs,
            role: ExprRole::Formula,
        }
    }

    #[must_use]
    pub(in crate::verify) fn value(exprs: &'a [PureExpr]) -> Self {
        Self {
            exprs,
            role: ExprRole::Value,
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
pub(in crate::verify) enum LogicFnInput<'a> {
    FilterForGoal(&'a [LogicFnDef]),
    FilterForGoalGroundOnly(&'a [LogicFnDef]),
    /// Already filtered by the caller — skip re-filtering.
    Prefiltered(&'a [LogicFnDef]),
    /// Already filtered by the caller and registered without global quantified
    /// defining axioms.
    ///
    /// Used by the loop path where `filter_logic_fns_for_loop_ctx` pre-filters
    /// once against all loop expressions, then each sub-check reuses the
    /// pre-filtered set and relies on ground instances for observed calls.
    PrefilteredGroundOnly(&'a [LogicFnDef]),
}

#[derive(Clone, Copy, Debug)]
pub(in crate::verify) enum TypeInvariantInput<'a> {
    FilterForGoal(&'a [TypeInvariantDef]),
    /// Already selected by the caller — register without filtering.
    Prefiltered(&'a [TypeInvariantDef]),
}

#[derive(Clone, Copy)]
pub(in crate::verify) struct BootstrapRequest<'a> {
    pub(in crate::verify) expr_slices: &'a [ExprSlice<'a>],
    pub(in crate::verify) result_postconditions: Option<&'a [PureExpr]>,
    pub(in crate::verify) result_expr: Option<&'a PureExpr>,
    pub(in crate::verify) logic_fns: Option<LogicFnInput<'a>>,
    pub(in crate::verify) mode_overrides: Option<&'a [LogicMode]>,
    pub(in crate::verify) type_invariants: Option<TypeInvariantInput<'a>>,
    pub(in crate::verify) track: TrackLevel,
    pub(in crate::verify) timeout: Option<Duration>,
    pub(in crate::verify) type_constants: Option<&'a HashMap<String, PureExpr>>,
    pub(in crate::verify) closure_captures: Option<&'a [super::super::ClosureCaptureInfo]>,
    pub(in crate::verify) adt_decls: Option<&'a AdtDecls>,
    /// Per-ADT integer field range constraints (e.g. `u32` fields are
    /// non-negative and bounded). Applied before datatypes are declared so the
    /// encoder's ground field-range assumptions
    /// (`assert_adt_field_range_ground_assumptions` + the `rebind_var` hook)
    /// can emit `field(x) >= 0` guards. Threaded into the loop VC path
    /// (#2702) — previously only the function-level pipeline set these, so
    /// loop obligations over structs with unsigned fields (e.g. a
    /// `CustomVariant(u32, u32)` loop variant) lacked the field
    /// non-negativity facts their postcondition/variant VCs need.
    pub(in crate::verify) adt_field_ranges: Option<&'a AdtFieldRanges>,
}

fn flatten_expr_slices<'a>(expr_slices: &'a [ExprSlice<'a>]) -> (Vec<PureExpr>, Vec<&'a PureExpr>) {
    let formula_len = expr_slices
        .iter()
        .filter(|slice| slice.role == ExprRole::Formula)
        .map(|slice| slice.exprs.len())
        .sum();
    let value_len = expr_slices
        .iter()
        .filter(|slice| slice.role == ExprRole::Value)
        .map(|slice| slice.exprs.len())
        .sum();

    let mut formula_exprs = Vec::with_capacity(formula_len);
    let mut value_exprs = Vec::with_capacity(value_len);
    for slice in expr_slices {
        match slice.role {
            ExprRole::Formula => formula_exprs.extend(slice.exprs.iter().cloned()),
            ExprRole::Value => value_exprs.extend(slice.exprs.iter()),
        }
    }
    (formula_exprs, value_exprs)
}

#[allow(clippy::type_complexity)]
fn prepare_logic_functions(
    logic_fns: Option<LogicFnInput<'_>>,
    mode_overrides: Option<&[LogicMode]>,
    formula_exprs: &[PureExpr],
    value_exprs: &[&PureExpr],
) -> Result<(Option<Vec<LogicFnDef>>, Option<Vec<LogicMode>>), EncodingError> {
    match logic_fns {
        Some(LogicFnInput::FilterForGoal(fns)) => filter_logic_functions_for_goal(
            Some(fns),
            mode_overrides,
            formula_exprs,
            &[],
            value_exprs,
        ),
        Some(LogicFnInput::FilterForGoalGroundOnly(fns)) => filter_logic_functions_for_goal(
            Some(fns),
            mode_overrides,
            formula_exprs,
            &[],
            value_exprs,
        ),
        Some(LogicFnInput::Prefiltered(fns)) => {
            if fns.is_empty() {
                Ok((None, None))
            } else {
                Ok((
                    Some(fns.to_vec()),
                    mode_overrides.map(<[trust_wp_core::logic::LogicMode]>::to_vec),
                ))
            }
        }
        Some(LogicFnInput::PrefilteredGroundOnly(fns)) => {
            if fns.is_empty() {
                Ok((None, None))
            } else {
                Ok((
                    Some(fns.to_vec()),
                    mode_overrides.map(<[trust_wp_core::logic::LogicMode]>::to_vec),
                ))
            }
        }
        None => Ok((None, None)),
    }
}

fn logic_fn_input_ground_only(logic_fns: Option<LogicFnInput<'_>>) -> bool {
    matches!(
        logic_fns,
        Some(LogicFnInput::FilterForGoalGroundOnly(_))
            | Some(LogicFnInput::PrefilteredGroundOnly(_))
    )
}

fn prepare_type_invariants(
    type_invariants: Option<TypeInvariantInput<'_>>,
    formula_exprs: &[PureExpr],
    value_exprs: &[&PureExpr],
) -> Option<Vec<TypeInvariantDef>> {
    match type_invariants {
        Some(TypeInvariantInput::FilterForGoal(invs)) => {
            filter_type_invariants_for_goal(Some(invs), formula_exprs, &[], value_exprs)
        }
        Some(TypeInvariantInput::Prefiltered(invs)) => {
            if invs.is_empty() {
                None
            } else {
                Some(invs.to_vec())
            }
        }
        None => None,
    }
}

pub(in crate::verify) fn build_bootstrap_sort_plan(
    encoder: &AYEncoder,
    formula_exprs: &[PureExpr],
    value_exprs: &[&PureExpr],
    result_expr: Option<&PureExpr>,
    result_postconditions: Option<&[PureExpr]>,
    logic_fns: Option<&[LogicFnDef]>,
    type_invariants: Option<&[TypeInvariantDef]>,
    closure_captures: Option<&[super::super::ClosureCaptureInfo]>,
) -> SortPlan {
    let mut builder = SortPlanBuilder::new();

    if !formula_exprs.is_empty() {
        builder.collect_registered_sort_hints(formula_exprs);
        builder.merge_variable_usage(collect_variable_usage_as_formula(formula_exprs));
        builder.collect_formula_logic_fn_return_hints(formula_exprs);
    }
    if !value_exprs.is_empty() {
        builder.collect_registered_sort_hints_from_refs(value_exprs);
    }

    for expr in value_exprs {
        builder.merge_variable_usage(collect_variable_usage(std::slice::from_ref(*expr)));
    }

    if let Some(fns) = logic_fns {
        for logic_fn in fns {
            builder.merge_variable_usage(collect_variable_usage(std::slice::from_ref(
                logic_fn.body(),
            )));
            if !logic_fn.requires().is_empty() {
                builder
                    .merge_variable_usage(collect_variable_usage_as_formula(logic_fn.requires()));
            }
            if !logic_fn.ensures().is_empty() {
                let mut batch = collect_variable_usage_as_formula(logic_fn.ensures());
                batch.remove("result");
                builder.merge_variable_usage(batch);
            }
        }
    }

    if let Some(invariants) = type_invariants {
        for invariant in invariants {
            builder.merge_variable_usage(collect_variable_usage_as_formula(std::slice::from_ref(
                invariant.body(),
            )));
        }
        let invariant_call_exprs = formula_exprs
            .iter()
            .chain(value_exprs.iter().copied())
            .collect::<Vec<_>>();
        for invariant in invariants {
            let Some(receiver_sort) = infer_type_invariant_self_sort(invariant) else {
                continue;
            };
            let method_name = type_invariant_method_name(invariant.type_name());
            for expr in &invariant_call_exprs {
                collect_type_invariant_receiver_sort(
                    &mut builder,
                    expr,
                    &method_name,
                    &receiver_sort,
                );
            }
        }
    }

    // Closure captures introduce sort evidence via capture type names
    // and invariant bodies that reference captured variables. (#2567)
    // Only pre-declare well-known encoding sorts (Bool, Seq, FMap, Datatype,
    // ClosureEnv_*, Tuple*, MutRef). User ADTs without registered Datatype
    // declarations would create disconnected Uninterpreted variables if
    // pre-declared — those are handled by ADT registration instead.
    if let Some(captures) = closure_captures {
        for info in captures {
            if let Some(param_name) = info.param_name() {
                let closure_sort = encoder
                    .closure_struct_sort_cloned(info.def_id())
                    .map(|entry| entry.sort)
                    .unwrap_or_else(|| {
                        Sort::Uninterpreted(format!(
                            "ClosureEnv_{}",
                            closure_symbol_suffix(info.def_id())
                        ))
                    });
                builder.record_source_sort(param_name.to_string(), closure_sort);
            }
            for field in info.captures() {
                let sort = expr_sort_to_ay_sort(field.sort());
                let should_predeclare = match &sort {
                    Sort::Int => false,
                    Sort::Bool | Sort::Seq(_) | Sort::Datatype(_) | Sort::Real => true,
                    Sort::Uninterpreted(name) => {
                        matches!(name.as_str(), "Seq" | "FMap" | "Unit" | "Mapping")
                            || name.starts_with("Tuple")
                            || name.starts_with("ClosureEnv_")
                            || name.starts_with("__trust_wp_mutref::")
                    }
                    _ => false,
                };
                if should_predeclare {
                    builder.record_source_sort(field.name().to_string(), sort);
                }
            }
        }
    }

    let mut input_exprs: Vec<&PureExpr> = formula_exprs.iter().collect();
    input_exprs.extend(value_exprs.iter().copied());

    let registered_datatypes = encoder
        .decls()
        .datatypes_iter()
        .cloned()
        .collect::<Vec<_>>();
    builder.extend_source_sorts(
        super::datatype_predecl::collect_bootstrap_datatype_var_sorts(
            &input_exprs,
            result_postconditions,
            logic_fns,
            &registered_datatypes,
        )
        .into_iter()
        .map(|(name, dt)| (name, Sort::Datatype(dt))),
    );

    let goal_exprs: Vec<&PureExpr> = formula_exprs.iter().collect();
    let mut domain_exprs = input_exprs;
    if let Some(fns) = logic_fns {
        for logic_fn in fns {
            domain_exprs.push(logic_fn.body());
            domain_exprs.extend(logic_fn.requires().iter());
            domain_exprs.extend(logic_fn.ensures().iter());
        }
    }
    builder.extend_source_sorts(collect_declared_fn_domain_sorts_batch(
        encoder.decls(),
        &domain_exprs,
    ));

    // Supplement with domain sorts from LogicFnDef::param_sorts for logic
    // functions that have not yet been declared on the encoder. At bootstrap
    // time the definitions are available but not yet registered, so
    // collect_declared_fn_domain_sorts_batch (which queries encoder.decls())
    // cannot see them. This bridges the gap so call-site argument names
    // (including View-derived `_view` names) get their declared sort.
    if let Some(fns) = logic_fns {
        builder.extend_source_sorts(collect_active_logic_fn_param_name_sorts(&goal_exprs, fns));
        builder.extend_source_sorts(collect_logic_fn_def_domain_sorts(&domain_exprs, fns));
    }

    let mut plan = builder.build(encoder.decls());
    let result_value_exprs = result_expr.into_iter().collect::<Vec<_>>();
    // Constructor-based `result` sort inference draws on the dedicated
    // `result_expr` (the function's return value) when available. When it is
    // absent, callers historically fell back to ALL value-role exprs so a
    // result constructor flowing in via a value slice could still be detected.
    //
    // That fallback is unsound for loop verification VCs (preservation,
    // variant, initialization), which pass `result_expr: None` and route the
    // loop body effects through value slices. A by-value struct field write
    // such as `x.0 -= 1` records a bare datatype-constructor body effect
    // (`CustomVariant(x.0 - 1, x.1)`); the fallback would then misattribute
    // that constructor to `result`, declaring the (typically `u32`) loop
    // accumulator with a datatype sort and forcing spurious Int<->datatype
    // coercions that break every loop VC mentioning `result` (#2702).
    //
    // Restrict the constructor heuristics to the explicit `result_expr`: when
    // none is provided there is no genuine return value, so `result` must keep
    // its declared/Int sort rather than borrow an unrelated body effect's
    // constructor. This only narrows where `result`'s sort is guessed; it never
    // changes a value, so it cannot make a goal spuriously provable.
    let result_value_exprs = result_value_exprs.as_slice();

    if let Some(kind) = merge_result_datatype_kind_with_body(
        result_postconditions.and_then(result_match_datatype_from_postcondition),
        result_option_datatype_from_constructor_values(result_value_exprs),
    ) {
        // Constructor-based postconditions (`result == Some(..)`, `result == Ok(..)`, etc.)
        // provide stronger sort evidence for `result` than its raw Rust annotation
        // (`Option`, `Result`) and prevent bootstrap from freezing a weak
        // carrier that later needs a phantom upgrade during result binding.
        plan.source_var_sorts
            .insert("result".to_string(), Sort::Datatype(kind.datatype()));
        for alias in synthetic_call_alias_value_exprs(result_value_exprs) {
            plan.source_var_sorts
                .insert(alias.to_string(), Sort::Datatype(kind.datatype()));
        }
    } else if let Some(dt) =
        result_datatype_from_constructor_value(result_value_exprs, &registered_datatypes)
    {
        plan.source_var_sorts
            .insert("result".to_string(), Sort::Datatype(dt));
    } else if let Some(tuple_sort) = result_tuple_sort_from_value_exprs(result_value_exprs) {
        if should_use_tuple_result_sort(plan.source_var_sorts.get("result")) {
            plan.source_var_sorts
                .insert("result".to_string(), tuple_sort.clone());
        }
        for alias in synthetic_call_alias_value_exprs(result_value_exprs) {
            plan.source_var_sorts
                .entry(alias.to_string())
                .or_insert_with(|| tuple_sort.clone());
        }
    }
    plan
}

fn should_use_tuple_result_sort(existing: Option<&Sort>) -> bool {
    match existing {
        None | Some(Sort::Int) => true,
        Some(Sort::Uninterpreted(name)) => tuple_sort_arity(name).is_some(),
        _ => false,
    }
}

fn tuple_sort_arity(name: &str) -> Option<usize> {
    name.strip_prefix("Tuple")?.parse().ok()
}

fn result_tuple_sort_from_value_exprs(value_exprs: &[&PureExpr]) -> Option<Sort> {
    let arity = value_exprs
        .iter()
        .filter_map(|expr| tuple_constructor_arity(expr))
        .max()?;
    Some(Sort::Uninterpreted(format!("Tuple{arity}")))
}

fn tuple_constructor_arity(expr: &PureExpr) -> Option<usize> {
    match expr {
        PureExpr::LogicFnCall { name, .. } => tuple_logic_fn_arity(name),
        PureExpr::LetAssume { body, .. } | PureExpr::LetObligation { body, .. } => {
            tuple_constructor_arity(body)
        }
        _ => None,
    }
}

fn result_option_datatype_from_constructor_values(
    value_exprs: &[&PureExpr],
) -> Option<MatchDatatypeKind> {
    value_exprs.iter().fold(None, |merged, expr| {
        merge_result_datatype_kind_with_body(merged, option_datatype_from_constructor_expr(expr))
    })
}

fn merge_result_datatype_kind_with_body(
    postcondition_kind: Option<MatchDatatypeKind>,
    body_kind: Option<MatchDatatypeKind>,
) -> Option<MatchDatatypeKind> {
    match (postcondition_kind, body_kind) {
        (Some(MatchDatatypeKind::OptionInt), Some(MatchDatatypeKind::OptionPayload(payload))) => {
            Some(MatchDatatypeKind::OptionPayload(payload))
        }
        (Some(MatchDatatypeKind::OptionPayload(payload)), Some(MatchDatatypeKind::OptionInt)) => {
            Some(MatchDatatypeKind::OptionPayload(payload))
        }
        (
            None,
            Some(kind @ (MatchDatatypeKind::OptionInt | MatchDatatypeKind::OptionPayload(_))),
        ) => Some(kind),
        (Some(kind), _) => Some(kind),
        (None, Some(kind)) => Some(kind),
        (None, None) => None,
    }
}

fn infer_type_invariant_self_sort(inv: &TypeInvariantDef) -> Option<Sort> {
    let usage = collect_variable_usage_as_formula(std::slice::from_ref(inv.body()));
    let self_usage = usage.get(inv.self_param())?;
    let sort = determine_sort(self_usage);
    (sort != Sort::Int).then_some(sort)
}

fn collect_type_invariant_receiver_sort(
    builder: &mut SortPlanBuilder,
    expr: &PureExpr,
    method_name: &str,
    receiver_sort: &Sort,
) {
    expr.for_each_recursive_with_depth_limit(MAX_ENCODING_DEPTH, |node| {
        let PureExpr::MethodCall {
            receiver, method, ..
        } = node
        else {
            return;
        };
        if method != method_name {
            return;
        }
        if let Some(receiver_name) = extract_base_var_name(receiver) {
            builder.record_source_sort(receiver_name.to_string(), receiver_sort.clone());
        }
    });
}

fn result_datatype_from_constructor_value(
    value_exprs: &[&PureExpr],
    registered_datatypes: &[DatatypeSort],
) -> Option<DatatypeSort> {
    value_exprs.iter().find_map(|expr| {
        let PureExpr::LogicFnCall { name, args } = expr else {
            return None;
        };
        let short_name = short_constructor_name(name);
        registered_datatypes.iter().find_map(|dt| {
            dt.constructors
                .iter()
                .any(|ctor| {
                    datatype_constructor_matches(dt, &ctor.name, &short_name)
                        && ctor.fields.len() == args.len()
                })
                .then(|| dt.clone())
        })
    })
}

fn synthetic_call_alias_value_exprs<'a>(
    value_exprs: &'a [&'a PureExpr],
) -> impl Iterator<Item = &'a str> {
    value_exprs.iter().filter_map(|expr| match *expr {
        PureExpr::Var(name, _) if is_synthetic_call_alias(name) => Some(name.as_str()),
        _ => None,
    })
}

fn is_synthetic_call_alias(name: &str) -> bool {
    name.starts_with("$call_") || name.starts_with("$_call_")
}

fn build_bootstrap_hint_plan(
    encoder: &AYEncoder,
    formula_exprs: &[PureExpr],
    value_exprs: &[&PureExpr],
) -> SortPlan {
    let mut builder = SortPlanBuilder::new();
    if !formula_exprs.is_empty() {
        builder.collect_registered_sort_hints(formula_exprs);
        builder.collect_formula_logic_fn_return_hints(formula_exprs);
    }
    if !value_exprs.is_empty() {
        builder.collect_registered_sort_hints_from_refs(value_exprs);
    }
    builder.build(encoder.decls())
}

pub(in crate::verify) fn bootstrap_encoder(
    request: BootstrapRequest<'_>,
) -> Result<AYEncoder, EncodingError> {
    let (formula_exprs, value_exprs) = flatten_expr_slices(request.expr_slices);
    let logic_fn_defining_axioms_ground_only = logic_fn_input_ground_only(request.logic_fns);
    let filtered_type_invariants =
        prepare_type_invariants(request.type_invariants, &formula_exprs, &value_exprs);
    let logic_formula_exprs = formula_exprs_with_type_invariant_bodies(
        &formula_exprs,
        filtered_type_invariants.as_deref(),
    );
    let (filtered_logic_fns, filtered_modes) = prepare_logic_functions(
        request.logic_fns,
        request.mode_overrides,
        &logic_formula_exprs,
        &value_exprs,
    )?;

    let (use_quantifiers, needs_array_theory, needs_custom_sorts) = detect_logic_requirements(
        &logic_formula_exprs,
        &[],
        &value_exprs,
        filtered_logic_fns.as_deref(),
        filtered_type_invariants.as_deref(),
        request.adt_decls,
    );

    let mut encoder = if needs_custom_sorts {
        AYEncoder::try_new_all()?
    } else {
        new_encoder_for_track_with_arrays(request.track, use_quantifiers, needs_array_theory)?
    };
    encoder.set_timeout(request.timeout);
    if let Some(constants) = request.type_constants {
        encoder.set_type_constants(constants.clone());
    }
    encoder.set_logic_fn_defining_axioms_ground_only(logic_fn_defining_axioms_ground_only);
    // Field ranges must be set BEFORE datatypes are declared and variables
    // are bound (via register_adt_decls below or any later
    // ensure_datatype_declared / rebind_var), because the ground field-range
    // assumption hooks read self.adt_field_ranges at declaration/binding time
    // and the declaration-time sweep only fires once per datatype. (#2702)
    if let Some(field_ranges) = request.adt_field_ranges {
        encoder.set_adt_field_ranges(field_ranges.clone());
    }
    if let Some(adt_decls) = request.adt_decls {
        // Upgrade ADT field sorts when match patterns reveal nested stdlib
        // constructors (e.g., `OwnResult::Ok(Some(x))` → Ok field is OptionInt,
        // not Int). Without this, TypeParam fields default to Int, causing sort
        // mismatches when Skolemized postconditions encode `Some(sk_t)` natively
        // as OptionInt but OwnResult::Ok expects Int. (#1296)
        let all_exprs: Vec<&PureExpr> = formula_exprs
            .iter()
            .chain(value_exprs.iter().copied())
            .collect();
        if !all_exprs.is_empty() {
            if crate::trust_wp_debug_enabled() {
                eprintln!(
                    "  [bootstrap] upgrading ADT field sorts from {} exprs, {} adt_decls",
                    all_exprs.len(),
                    adt_decls.len()
                );
            }
            let mut upgraded = adt_decls.clone();
            super::datatype_predecl::upgrade_adt_field_sorts_from_patterns(
                &mut upgraded,
                &all_exprs,
            );
            encoder.register_adt_decls(&upgraded);
        } else {
            encoder.register_adt_decls(adt_decls);
        }
    }

    if let Some(captures) = request.closure_captures {
        for info in captures {
            if !info.captures().is_empty() {
                encoder.register_closure_struct_sort(info.def_id(), info.captures())?;
            }
        }
    }

    // Sort plan build+apply runs as early as possible so receiver names and
    // capture fields are predeclared before any prescan or invariant encoding
    // can fall back to Int. (#2567)
    let sort_plan = build_bootstrap_sort_plan(
        &encoder,
        &formula_exprs,
        &value_exprs,
        request.result_expr,
        request.result_postconditions,
        filtered_logic_fns.as_deref(),
        filtered_type_invariants.as_deref(),
        request.closure_captures,
    );
    sort_plan.apply(&mut encoder)?;

    build_bootstrap_hint_plan(&encoder, &formula_exprs, &value_exprs).apply(&mut encoder)?;

    if let Some(fns) = filtered_logic_fns.as_deref() {
        encoder.prescan_and_register_logic_fns(fns, filtered_modes.as_deref())?;
    }

    register_type_invariants_on_encoder(&mut encoder, filtered_type_invariants.as_deref())?;

    if let Some(captures) = request.closure_captures {
        for info in captures {
            if !info.captures().is_empty() {
                encoder.register_closure_struct_sort(info.def_id(), info.captures())?;
            }
            encoder.register_closure_body(info);
        }
    }

    // Keep the matching FnMut companion declared before any goal encoding when
    // the bootstrap context already contains mut-ref carrier evidence. This
    // avoids the compat path falling back to an unconstrained placeholder UF
    // before `assert_fn_closure_laws` has a chance to assert the bridge. (#6)
    let needs_closure_mut_companion = formula_exprs
        .iter()
        .chain(value_exprs.iter().copied())
        .any(expr_has_mut_ref_carrier);
    encoder.predeclare_closure_postcondition_mut_companions(needs_closure_mut_companion);

    // Closure capture type invariant assumptions are now injected in the
    // driver's clause enrichment pipeline as regular `requires` clauses
    // (build_closure_capture_invariant_requires in type_invariants/clauses.rs).
    // This replaced the ay-side inject_closure_capture_type_invariants()
    // that ran here (#2257).

    Ok(encoder)
}

// inject_closure_capture_type_invariants and capture_field_type_name were
// removed in #2257. Closure capture invariant synthesis now happens in the
// driver's clause enrichment pipeline (build_closure_capture_invariant_requires
// in type_invariants/clauses.rs).
