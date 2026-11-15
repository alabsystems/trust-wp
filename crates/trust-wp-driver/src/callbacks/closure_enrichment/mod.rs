// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure enrichment infrastructure for verification.
//!
//! Contains closure capture analysis, existential enrichment with concrete
//! ensures clauses, forall precondition rule instantiation, trivial closure
//! precondition rewriting, and capture variable substitution.

mod body_extraction;
mod capture_info;
mod existential_witness;
mod forall_enrichment;
mod forall_rules;
mod receiver_identity;
mod substitute;
mod trivial_rewrite;

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use capture_info::build_closure_capture_info;
pub(in crate::callbacks) use capture_info::closure_capture_fields;
pub(super) use existential_witness::{
    trivialize_closure_env_resolves_in_assumptions, witness_existential_postcondition_goals,
};
pub(super) use forall_enrichment::enrich_forall_goals_with_closure_ensures;
#[cfg(test)]
pub(super) use forall_enrichment::try_ground_forall_obligation;
pub(super) use forall_rules::{
    instantiate_forall_precondition_rules, prune_materialized_forall_precondition_rules,
};
pub(super) use receiver_identity::{
    closure_env_ctor_arity, closure_receiver_base_name, collect_closure_receiver_bindings,
    collect_sole_env_owners,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{Body, Rvalue, StatementKind},
    ty::TyCtxt,
};
pub(super) use substitute::substitute_captures_inline;
#[cfg(test)]
pub(super) use trivial_rewrite::ContractFreeClosureReceivers;
pub(super) use trivial_rewrite::{
    collect_contract_free_closure_receivers, rewrite_contract_free_closure_precondition_goal,
    ClosurePreconditions,
};
use trust_wp_core::{
    closure::{CaptureKind, ClosureCaptureInfo},
    formula::{
        internal::tuple_lowering::{
            tuple_field_logic_fn_index, tuple_field_logic_fn_name, tuple_logic_fn_arity,
        },
        BinOp, ExprSort, PureExpr,
    },
};
use trust_wp_driver::StdSpec;

use super::{
    super::mir_analysis::{get_mir_body, resolve_arg_names_or_warn},
    try_get_body_with_context,
};

/// Closure enrichment data structures.
pub(super) type CaptureBindings = Vec<(usize, String)>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ClosureEnsuresEntry {
    pub(super) receiver_name: String,
    pub(super) param_names: Vec<String>,
    pub(super) capture_bindings: CaptureBindings,
    pub(super) ensures_exprs: Vec<PureExpr>,
    /// The capture count this closure is the SOLE owner of in its parent
    /// body (`collect_sole_env_owners`): a `__trust_wp_tuple<N>(..)` receiver
    /// of that arity denotes it. `None`: no environment term does.
    pub(super) env_arity: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ClosureSpec {
    pub(super) receiver_name: String,
    pub(super) param_names: Vec<String>,
    pub(super) capture_bindings: CaptureBindings,
    pub(super) requires_exprs: Vec<PureExpr>,
    pub(super) ensures_exprs: Vec<PureExpr>,
    /// As `ClosureEnsuresEntry::env_arity`.
    pub(super) env_arity: Option<usize>,
}

pub(super) fn substitute_closure_params_with_args(
    expr: &PureExpr,
    param_names: &[String],
    args_expr: &PureExpr,
) -> PureExpr {
    let substitutions = closure_arg_substitutions(param_names, args_expr);
    if substitutions.is_empty() {
        expr.clone()
    } else {
        expr.substitute(&substitutions)
    }
}

fn closure_arg_substitutions(
    param_names: &[String],
    args_expr: &PureExpr,
) -> HashMap<String, PureExpr> {
    let mut substitutions = HashMap::new();
    if param_names.is_empty() {
        return substitutions;
    }

    if let PureExpr::LogicFnCall { name, args } = args_expr {
        if tuple_logic_fn_arity(name) == Some(args.len()) && args.len() == param_names.len() {
            for (param_name, arg) in param_names.iter().zip(args.iter()) {
                substitutions.insert(param_name.clone(), arg.clone());
            }
            return substitutions;
        }
    }

    if param_names.len() == 1 {
        substitutions.insert(param_names[0].clone(), args_expr.clone());
        return substitutions;
    }

    for (idx, param_name) in param_names.iter().enumerate() {
        substitutions.insert(
            param_name.clone(),
            PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(idx),
                args: vec![args_expr.clone()],
            },
        );
    }
    substitutions
}

/// Collect [`ClosureCaptureInfo`] for closures defined in the function body.
///
/// Scans the parent function's MIR for closure aggregate definitions and builds
/// capture information needed by the ay encoder to register structural closure
/// sorts (Layer 2, #1489). Each closure gets a `ClosureCaptureInfo` with its
/// DefId string and typed capture fields.
///
/// Only closures with user-annotated specs are included — closures without specs
/// don't participate in postcondition projection.
///
/// Phase 2 (#2151): When MIR body extraction succeeds and the closure body is
/// below the complexity threshold, populates `body_expr` and `param_names` for
/// inline encoding. The ay encoder uses these to emit ground terms instead of
/// UF+axioms, eliminating quantifier load.
///
/// When `parent_local_def_id` is itself a closure, seeds the current closure's
/// own capture info with `param_name = "self"` before scanning for nested
/// closures so closure verification sees the current environment as well (#2257).
pub(super) fn collect_closure_capture_infos(
    tcx: TyCtxt<'_>,
    parent_local_def_id: LocalDefId,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Vec<ClosureCaptureInfo> {
    let Some(body_with_facts) = try_get_body_with_context(tcx, parent_local_def_id) else {
        return Vec::new();
    };
    let mir_body: &Body<'_> = get_mir_body(&body_with_facts);
    let env_owners = collect_sole_env_owners(tcx, parent_local_def_id);

    let mut result = Vec::new();

    if tcx.def_kind(parent_local_def_id.to_def_id()) == rustc_hir::def::DefKind::Closure {
        if let Some(info) = build_closure_capture_info(
            tcx,
            parent_local_def_id.to_def_id(),
            Some("self".to_string()),
            user_specs,
            trait_specs,
            extern_specs,
        ) {
            result.push(info);
        }
    }

    for bb_data in mir_body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((
                place,
                Rvalue::Aggregate(rustc_middle::mir::AggregateKind::Closure(def_id, _substs), _),
            )) = &stmt.kind
            {
                // Extract the local variable name the closure is assigned to.
                // This becomes the param_name for capture projection (e.g., "c"
                // in `let mut c = || { x += 1; 5 }`).
                // Use var_debug_info to find the source name for the local.
                let param_name = mir_body.var_debug_info.iter().find_map(|info| {
                    if let rustc_middle::mir::VarDebugInfoContents::Place(dbg_place) = &info.value {
                        if dbg_place.local == place.local && dbg_place.projection.is_empty() {
                            return Some(info.name.as_str().to_string());
                        }
                    }
                    None
                });

                let Some(info) = build_closure_capture_info(
                    tcx,
                    *def_id,
                    param_name,
                    user_specs,
                    trait_specs,
                    extern_specs,
                ) else {
                    continue;
                };
                let info = info.with_env_arity(env_owners.get(def_id).copied());
                if !result
                    .iter()
                    .any(|existing| existing.def_id() == info.def_id())
                {
                    result.push(info);
                }
            }
        }
    }

    result
}

/// The caller-side POST-CALL value of a capture that is a tuple field of a
/// caller local: `p.1` after the call is `^(p.1)`, the prophecy of the borrow
/// the capture took.
///
/// The single producer of that term. The capture's place advance and the
/// closure postcondition's credit are computed in different passes from
/// different inputs, and a credit that lands on any other symbol than the one
/// the place moved to proves nothing about the place while the caller's entry
/// premise still describes it.
pub(crate) fn projected_capture_post_state(
    owner: &str,
    field_idx: usize,
    sort: Option<ExprSort>,
) -> PureExpr {
    PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(field_idx),
        args: vec![PureExpr::Var(owner.to_string(), sort)],
    }))
}

/// The `(owner, field)` of every capture that is a numeric field projection of
/// a caller local.
///
/// A named struct field (`_ref__s__a`) is deliberately absent: no post-state
/// symbol denotes it, so its clause must stay unattributed rather than be
/// credited to the owner's entry value.
fn projected_captures_of(tcx: TyCtxt<'_>, closure_def_id: DefId) -> Vec<(String, usize)> {
    let Some(local) = closure_def_id.as_local() else {
        return Vec::new();
    };
    tcx.closure_captures(local)
        .iter()
        .filter_map(|capture| {
            let owner = capture.var_ident.as_str().to_string();
            let symbol = capture.to_symbol().to_string();
            let stripped = symbol.strip_prefix("_ref__").unwrap_or(symbol.as_str());
            let field_idx = stripped
                .strip_prefix(owner.as_str())?
                .strip_prefix("__")?
                .parse::<usize>()
                .ok()?;
            Some((owner, field_idx))
        })
        .collect()
}

/// Re-attribute a closure's own `#[ensures]` from the capture owner's entry
/// symbol to the value the capture's place holds after the call. `old(p.1)`
/// keeps naming the entry value, which is what it means.
fn attribute_projected_capture_ensures(expr: &PureExpr, projected: &[(String, usize)]) -> PureExpr {
    if projected.is_empty() {
        return expr.clone();
    }
    expr.rewrite_bottom_up_prune(
        |node| !matches!(node, PureExpr::Old(_)),
        |node| {
            let PureExpr::LogicFnCall { ref name, ref args } = node else {
                return node;
            };
            let Some(field_idx) = tuple_field_logic_fn_index(name) else {
                return node;
            };
            let [PureExpr::Var(owner_name, _)] = args.as_slice() else {
                return node;
            };
            if projected
                .iter()
                .any(|(owner, field)| owner == owner_name && *field == field_idx)
            {
                projected_capture_post_state(owner_name, field_idx, None)
            } else {
                node.clone()
            }
        },
    )
}

/// Enrich call-site existential assumptions with concrete closure ensures (#970).
///
/// ay-dpll performs only one round of E-matching per check_sat (ay#1018).
/// A universally-quantified postcondition_mut axiom would need multi-round
/// E-matching to chain with tuple destructor axioms. Instead, this function
/// embeds the closure's concrete ensures clause directly INTO the existential
/// assumptions, so that after Skolemization all constraints are ground facts.
///
/// For each `postcondition_mut(PRE, arg, POST, res)` call inside an existential
/// assumption, appends the concrete ensures clause (with captures substituted
/// using PRE/POST/res tuple projections) as an additional conjunction. After
/// Skolemization, this becomes a ground arithmetic fact.
///
/// Example transformation:
/// ```text
/// Before: exists st1: closure.postcondition_mut((), st1, r) AND ...
/// After:  exists st1: closure.postcondition_mut((), st1, r)
///                AND (tuple_get_0(st1) == tuple_get_0(closure) + 1) AND ...
/// ```
pub(super) fn enrich_existentials_with_closure_ensures(
    tcx: TyCtxt<'_>,
    parent_local_def_id: LocalDefId,
    user_specs: &HashMap<DefId, StdSpec>,
    assumptions: &mut [PureExpr],
    synthesized_ensures: &[ClosureEnsuresEntry],
) -> usize {
    // One entry per contracted closure of the body that a receiver can be
    // identified with: by its source name (`collect_closure_receiver_bindings`)
    // and/or as the sole owner of its environment arity
    // (`collect_sole_env_owners`). A closure built inside a block
    // (`let c = { #[ensures(..)] |x| .. };`) lands in a temporary and has no
    // source name, so the arity route is the only one that can give it an
    // entry; without one its calls have no identified ensures (D-30).
    let env_owners = collect_sole_env_owners(tcx, parent_local_def_id);
    let bindings = collect_closure_receiver_bindings(tcx, parent_local_def_id);
    let mut identified: Vec<(DefId, String)> = bindings
        .into_iter()
        .map(|binding| (binding.def_id, binding.receiver_name))
        .collect();
    let mut owners_sorted: Vec<(&DefId, &usize)> = env_owners.iter().collect();
    owners_sorted.sort_by_key(|(def_id, _)| tcx.def_path_str(**def_id));
    for (def_id, _) in owners_sorted {
        if identified.iter().any(|(known, _)| known == def_id) {
            continue;
        }
        // `$` occurs in no source identifier, so this name matches no receiver
        // variable: the entry is reachable through its environment arity only.
        identified.push((*def_id, format!("$env:{}", tcx.def_path_str(*def_id))));
    }
    let mut closure_ensures: Vec<ClosureEnsuresEntry> = Vec::new();
    for (def_id, receiver_name) in identified {
        let spec = match user_specs.get(&def_id) {
            Some(s) if !s.ensures.is_empty() => s,
            _ => continue,
        };
        let Some(closure_local_def_id) = def_id.as_local() else {
            continue;
        };
        let captures = tcx.closure_captures(closure_local_def_id);
        let capture_bindings: Vec<(usize, String)> = captures
            .iter()
            .enumerate()
            .map(|(idx, cap)| (idx, cap.var_ident.as_str().to_string()))
            .collect();
        let param_names = resolve_arg_names_or_warn(tcx, def_id, spec.param_names.as_ref());

        let projected = projected_captures_of(tcx, def_id);
        let mut ensures_exprs = Vec::new();
        for ensures_str in &spec.ensures {
            if let Ok(ensures_expr) = trust_wp_core::contract_parser::parse_contract(ensures_str) {
                ensures_exprs.push(attribute_projected_capture_ensures(
                    &ensures_expr,
                    &projected,
                ));
            }
        }
        if !ensures_exprs.is_empty() {
            closure_ensures.push(ClosureEnsuresEntry {
                receiver_name,
                param_names,
                capture_bindings,
                ensures_exprs,
                env_arity: env_owners.get(&def_id).copied(),
            });
        }
    }

    // Merge synthesized ensures from body effect analysis (#2151 Phase 3).
    // For unannotated FnMut closures, ensures are synthesized from MIR
    // projected write facts rather than parsed from user annotations.
    let spec_receivers: HashSet<String> = closure_ensures
        .iter()
        .map(|entry| entry.receiver_name.clone())
        .collect();
    closure_ensures.extend(
        synthesized_ensures
            .iter()
            .filter(|entry| !spec_receivers.contains(&entry.receiver_name))
            .cloned(),
    );

    if closure_ensures.is_empty() {
        return 0;
    }

    // Transform each assumption: for existentials containing postcondition_mut,
    // inject concrete ensures as additional conjuncts
    let mut enrichment_count = 0;
    for assumption in assumptions.iter_mut() {
        if enrich_existential_body(assumption, &closure_ensures) {
            enrichment_count += 1;
        }
    }

    enrichment_count
}

/// Extract synthesized ensures entries from closure capture infos.
///
/// Converts `ClosureCaptureInfo::ensures_exprs` into `ClosureEnsuresEntry` format
/// for use by the enrichment mechanism. Only includes entries where `ensures_exprs`
/// is `Some` with non-empty content and the closure has a known receiver name.
pub(super) fn synthesized_ensures_from_capture_infos(
    capture_infos: &[ClosureCaptureInfo],
) -> Vec<ClosureEnsuresEntry> {
    capture_infos
        .iter()
        .filter_map(|ci| {
            let receiver_name = ci.param_name()?.to_string();
            let ensures = ci.ensures_exprs()?;
            if ensures.is_empty() {
                return None;
            }
            let capture_bindings: CaptureBindings = ci
                .captures()
                .iter()
                .enumerate()
                .map(|(idx, field)| (idx, field.name().to_string()))
                .collect();
            Some(ClosureEnsuresEntry {
                receiver_name,
                param_names: ci.param_names().map_or_else(Vec::new, <[String]>::to_vec),
                capture_bindings,
                ensures_exprs: ensures.to_vec(),
                env_arity: ci.env_arity(),
            })
        })
        .collect()
}

/// Extract concrete mutable-capture final values from synthesized current-closure
/// effects.
///
/// `try_extract_closure_body_with_effects` represents a body write such as
/// `x += 1` as `x == old(x) + 1`. For closure-body verification, that fact must
/// feed the RustHorn final-value path as `x_final == x_current + 1`; otherwise
/// the solver sees the capture post-state as unconstrained and reports unknown.
///
/// Only the BODY may mint a capture's final value. Reading the clause slot here
/// let a closure's own `#[ensures(y == 100)]` define `y`'s post-state as `100`
/// and then discharge itself against it — the grant and the obligation the same
/// source text. A capture the body does not determine has no final value and
/// its postcondition stays unproved.
pub(super) fn synthesized_final_values_from_current_closure(
    capture_infos: &[ClosureCaptureInfo],
) -> HashMap<String, PureExpr> {
    let mut final_values = HashMap::new();
    for info in capture_infos {
        if info.param_name() != Some("self") {
            continue;
        }
        let Some(ensures) = info.synthesized_effects() else {
            continue;
        };
        for ensure in ensures {
            if let Some((name, value)) = final_value_from_synthesized_ensure(ensure, info) {
                if let Some((capture_idx, _)) = info
                    .captures()
                    .iter()
                    .enumerate()
                    .find(|(_, field)| field.name() == name)
                {
                    let self_field = format!("self.{capture_idx}");
                    final_values.insert(
                        self_field.clone(),
                        replace_current_capture_name(&value, &name, &self_field),
                    );
                }
                final_values.insert(name, value);
            }
        }
    }
    final_values
}

/// Normalize annotated current-closure postconditions so captured `&mut`
/// variables use closure semantics: bare capture names refer to post-state,
/// while `old(capture)` refers to the body-entry state.
pub(super) fn normalize_current_closure_capture_postconditions(
    capture_infos: &[ClosureCaptureInfo],
    ensures: &mut [PureExpr],
) -> usize {
    let mut rewritten = 0;
    for info in capture_infos {
        if info.param_name() != Some("self") {
            continue;
        }
        let Some(body_expr) = info.body_expr() else {
            continue;
        };
        // The function-level transform `normalize_immutable_ref_param_vars`
        // canonicalizes `Deref(Var(p, Ref(T)))` to `Var(p, T)` for immutable
        // `&T` params in ensures. The closure body extracted from MIR is NOT
        // run through that pass, so for closures with `&T` / `&&T` params the
        // body_expr keeps the raw `Deref(Var(p, Ref(...)))` shape while the
        // already-transformed ensures use the canonical shape. Substituting an
        // un-canonicalized body_expr for `result` re-introduces the mismatch
        // and breaks reflexive `result == <body>` postconditions
        // (e.g., filter closure `#[ensures(result == **b)] |b: &&bool| **b`).
        // Canonicalize body_expr here using the closure's own non-mut param
        // names so the substituted ensure stays in the same canonical form.
        // Part of #5 — cc/iter test_filter closure body extraction.
        let immutable_ref_params: HashSet<String> = info
            .param_names()
            .map(|names| {
                names
                    .iter()
                    .filter(|n| n.as_str() != "self")
                    .cloned()
                    .collect()
            })
            .unwrap_or_default();
        let canonical_body = if immutable_ref_params.is_empty() {
            body_expr.clone()
        } else {
            crate::callbacks::verification::contract_transform::normalize_immutable_ref_param_vars(
                body_expr,
                &immutable_ref_params,
            )
        };
        for ensure in ensures.iter_mut() {
            let normalized = substitute_result_with_current_closure_body(ensure, &canonical_body);
            if normalized != *ensure {
                *ensure = normalized;
                rewritten += 1;
            }
        }
    }

    let synthesized_final_values = synthesized_final_values_from_current_closure(capture_infos);
    for info in capture_infos {
        if info.param_name() != Some("self")
            || !info
                .captures()
                .iter()
                .any(|field| matches!(field.kind(), CaptureKind::ByMutRef))
        {
            continue;
        }

        let capture_names: HashSet<String> = info
            .captures()
            .iter()
            .enumerate()
            .filter(|(_, field)| matches!(field.kind(), CaptureKind::ByMutRef))
            .flat_map(|(idx, field)| [field.name().to_string(), format!("self.{idx}")])
            .collect();

        for ensure in ensures.iter_mut() {
            let mut normalized = normalize_capture_post_state_refs(ensure, &capture_names, false);
            if postcondition_contradicts_synthesized_final_value(
                &normalized,
                &synthesized_final_values,
            ) {
                normalized = PureExpr::Bool(false);
            }
            if normalized != *ensure {
                *ensure = normalized;
                rewritten += 1;
            }
        }
    }
    rewritten
}

fn substitute_result_with_current_closure_body(
    ensure: &PureExpr,
    body_expr: &PureExpr,
) -> PureExpr {
    let mut substitutions = HashMap::new();
    substitutions.insert("result".to_string(), body_expr.clone());
    ensure.substitute(&substitutions)
}

fn normalize_capture_post_state_refs(
    expr: &PureExpr,
    capture_names: &HashSet<String>,
    inside_old: bool,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, sort) if capture_names.contains(name) => {
            let current = PureExpr::Deref(Arc::new(PureExpr::Var(name.clone(), sort.clone())));
            if inside_old {
                current
            } else {
                PureExpr::Final(Arc::new(current))
            }
        }
        PureExpr::Deref(inner) => {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                if capture_names.contains(name) {
                    let current = PureExpr::Deref(inner.clone());
                    return if inside_old {
                        current
                    } else {
                        PureExpr::Final(Arc::new(current))
                    };
                }
            }
            PureExpr::Deref(Arc::new(normalize_capture_post_state_refs(
                inner,
                capture_names,
                inside_old,
            )))
        }
        PureExpr::Old(inner) => {
            let references_capture = expr_references_capture(inner, capture_names);
            let normalized = normalize_capture_post_state_refs(inner, capture_names, true);
            if references_capture {
                normalized
            } else {
                PureExpr::Old(Arc::new(normalized))
            }
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(normalize_capture_post_state_refs(
                left,
                capture_names,
                inside_old,
            )),
            *op,
            Arc::new(normalize_capture_post_state_refs(
                right,
                capture_names,
                inside_old,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(normalize_capture_post_state_refs(
                inner,
                capture_names,
                inside_old,
            )),
        ),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(normalize_capture_post_state_refs(
            inner,
            capture_names,
            true,
        ))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(normalize_capture_post_state_refs(
            inner,
            capture_names,
            inside_old,
        ))),
        _ => expr.clone(),
    }
}

fn expr_references_capture(expr: &PureExpr, capture_names: &HashSet<String>) -> bool {
    let mut references_capture = false;
    expr.for_each_recursive(|node| {
        if let PureExpr::Var(name, _) = node {
            references_capture |= capture_names.contains(name);
        }
    });
    references_capture
}

fn postcondition_contradicts_synthesized_final_value(
    ensure: &PureExpr,
    final_values: &HashMap<String, PureExpr>,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    final_capture_name(left)
        .and_then(|name| final_values.get(name).map(|value| (value, right.as_ref())))
        .is_some_and(|(value, expected)| affine_exprs_contradict(value, expected))
        || final_capture_name(right)
            .and_then(|name| final_values.get(name).map(|value| (value, left.as_ref())))
            .is_some_and(|(value, expected)| affine_exprs_contradict(value, expected))
}

fn final_capture_name(expr: &PureExpr) -> Option<&str> {
    let PureExpr::Final(inner) = expr else {
        return None;
    };
    match inner.as_ref() {
        PureExpr::Var(name, _) => Some(name),
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name),
            _ => None,
        },
        _ => None,
    }
}

fn affine_exprs_contradict(left: &PureExpr, right: &PureExpr) -> bool {
    let (Some((left_base, left_offset)), Some((right_base, right_offset))) =
        (affine_base_offset(left), affine_base_offset(right))
    else {
        return false;
    };
    left_offset != right_offset && expr_eq_ignoring_var_sorts(left_base, right_base)
}

fn affine_base_offset(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    match expr {
        PureExpr::BinOp(left, BinOp::Add, right) => match right.as_ref() {
            PureExpr::Int(offset) => Some((left.as_ref(), *offset)),
            _ => None,
        },
        PureExpr::BinOp(left, BinOp::Sub, right) => match right.as_ref() {
            PureExpr::Int(offset) => Some((left.as_ref(), -*offset)),
            _ => None,
        },
        _ => Some((expr, 0)),
    }
}

fn expr_eq_ignoring_var_sorts(left: &PureExpr, right: &PureExpr) -> bool {
    match (left, right) {
        (PureExpr::Var(left_name, _), PureExpr::Var(right_name, _)) => left_name == right_name,
        (PureExpr::Deref(left), PureExpr::Deref(right))
        | (PureExpr::Final(left), PureExpr::Final(right))
        | (PureExpr::Old(left), PureExpr::Old(right))
        | (PureExpr::View(left), PureExpr::View(right)) => expr_eq_ignoring_var_sorts(left, right),
        (PureExpr::BinOp(left_l, left_op, left_r), PureExpr::BinOp(right_l, right_op, right_r)) => {
            left_op == right_op
                && expr_eq_ignoring_var_sorts(left_l, right_l)
                && expr_eq_ignoring_var_sorts(left_r, right_r)
        }
        _ => left == right,
    }
}

fn final_value_from_synthesized_ensure(
    ensure: &PureExpr,
    info: &ClosureCaptureInfo,
) -> Option<(String, PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = ensure else {
        return None;
    };
    if let Some(name) = capture_var_name(lhs, info) {
        return Some((name.clone(), old_to_current_deref(rhs, &name)));
    }
    if let Some(name) = capture_var_name(rhs, info) {
        return Some((name.clone(), old_to_current_deref(lhs, &name)));
    }
    None
}

fn capture_var_name(expr: &PureExpr, info: &ClosureCaptureInfo) -> Option<String> {
    let PureExpr::Var(name, _) = expr else {
        return None;
    };
    info.captures()
        .iter()
        .find(|field| field.name() == name && matches!(field.kind(), CaptureKind::ByMutRef))
        .map(|field| field.name())
        .map(str::to_string)
}

fn replace_current_capture_name(expr: &PureExpr, from: &str, to: &str) -> PureExpr {
    match expr {
        PureExpr::Var(name, sort) if name == from => PureExpr::Var(to.to_string(), sort.clone()),
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(replace_current_capture_name(left, from, to)),
            *op,
            Arc::new(replace_current_capture_name(right, from, to)),
        ),
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(replace_current_capture_name(inner, from, to)))
        }
        PureExpr::Deref(inner) => {
            PureExpr::Deref(Arc::new(replace_current_capture_name(inner, from, to)))
        }
        PureExpr::Final(inner) => {
            PureExpr::Final(Arc::new(replace_current_capture_name(inner, from, to)))
        }
        PureExpr::View(inner) => {
            PureExpr::View(Arc::new(replace_current_capture_name(inner, from, to)))
        }
        PureExpr::Old(inner) => {
            PureExpr::Old(Arc::new(replace_current_capture_name(inner, from, to)))
        }
        _ => expr.clone(),
    }
}

fn old_to_current_deref(expr: &PureExpr, capture_name: &str) -> PureExpr {
    match expr {
        PureExpr::Old(inner) => match inner.as_ref() {
            PureExpr::Var(name, sort) if name == capture_name => {
                PureExpr::Deref(Arc::new(PureExpr::Var(name.clone(), sort.clone())))
            }
            _ => old_to_current_deref(inner, capture_name),
        },
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(old_to_current_deref(left, capture_name)),
            *op,
            Arc::new(old_to_current_deref(right, capture_name)),
        ),
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(old_to_current_deref(inner, capture_name)))
        }
        PureExpr::Deref(inner) => {
            PureExpr::Deref(Arc::new(old_to_current_deref(inner, capture_name)))
        }
        PureExpr::Final(inner) => {
            PureExpr::Final(Arc::new(old_to_current_deref(inner, capture_name)))
        }
        PureExpr::View(inner) => {
            PureExpr::View(Arc::new(old_to_current_deref(inner, capture_name)))
        }
        _ => expr.clone(),
    }
}

/// Names in scope while enriching one existential assumption.
///
/// `bound` holds every variable an enclosing `exists<..>` binds; `owners` maps
/// a bound STATE variable to the index of the `ClosureEnsuresEntry` whose call
/// produced it (`c.postcondition_mut(a, st1, r)` makes `c`'s entry the owner
/// of `st1`). Both are scoped: entering an `exists<v>` shadows any outer `v`.
#[derive(Clone, Default)]
struct EnrichScope {
    bound: HashSet<String>,
    owners: HashMap<String, usize>,
}

/// The closure whose ensures may be injected at a `postcondition_mut` /
/// `postcondition_once` call, resolved by IDENTITY, or `None`:
///
/// * a receiver naming a source local (`c`, `*c`, `^c`) is the closure bound
///   to exactly one `closure_ensures` entry under that name — entries are
///   keyed by the parent body's `let` binding and
///   `collect_closure_receiver_bindings` drops a name two closures share;
/// * a receiver naming an existentially bound STATE variable (`st1` in
///   `c.postcondition_mut(a, st1, r) && st1.postcondition_mut(a, st2, r2)`)
///   is the closure whose call produced that state, recorded in
///   `scope.owners` from the producing call of the same existential. A bound
///   name is never looked up among the source-local entries: a `let st = ..`
///   closure does not own `exists<st> ..`'s `st`.
///
/// * a closure-environment constructor receiver (`__trust_wp_tuple<N>(..)`,
///   the lowered captures of a closure aggregated in this body) is the
///   closure that is the SOLE owner of that arity in the body
///   (`ClosureEnsuresEntry::env_arity`, from `collect_sole_env_owners`).
///
/// Anything else has no identity here and receives NOTHING: an environment
/// term whose arity two closures of the body share (both `|_| 1` and `|_| 2`
/// lower to `__trust_wp_tuple0()`), a bound name no call in scope produced,
/// a name matching no entry or several. Falling back to the single entry
/// present would hand a call on an UNCONTRACTED sibling closure the
/// contracted closure's ensures — an exit-0 false accept (D-30;
/// `tests/adversarial/cases/s71_closure_ensures_*`).
fn resolve_ensures_owner(
    receiver: &PureExpr,
    closure_ensures: &[ClosureEnsuresEntry],
    scope: &EnrichScope,
) -> Option<usize> {
    if let Some(arity) = closure_env_ctor_arity(receiver) {
        let mut owners = closure_ensures
            .iter()
            .enumerate()
            .filter(|(_, entry)| entry.env_arity == Some(arity));
        return match (owners.next(), owners.next()) {
            (Some((index, _)), None) => Some(index),
            _ => None,
        };
    }
    let name = closure_receiver_base_name(receiver)?;
    if scope.bound.contains(name) {
        return scope.owners.get(name).copied();
    }
    let mut matching = closure_ensures
        .iter()
        .enumerate()
        .filter(|(_, entry)| entry.receiver_name == name);
    match (matching.next(), matching.next()) {
        (Some((index, _)), None) => Some(index),
        _ => None,
    }
}

/// `(receiver, state)` of every `postcondition_mut(args, state, result)` call
/// in `expr` that lies in the SAME existential scope: conjunctions and the
/// consequent of an implication are walked, a nested `exists` is not (its
/// body is seeded when the enrichment reaches it, with its own binder).
fn collect_state_producers<'e>(expr: &'e PureExpr, out: &mut Vec<(&'e PureExpr, &'e PureExpr)>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_state_producers(left, out);
            collect_state_producers(right, out);
        }
        PureExpr::BinOp(_, BinOp::Implies, right) => collect_state_producers(right, out),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "postcondition_mut" && args.len() == 3 => {
            out.push((receiver.as_ref(), &args[1]));
        }
        _ => {}
    }
}

/// Record, in `scope.owners`, the owner of every bound state variable some
/// call in `body` produces from an identified receiver. Iterated to a fixed
/// point so a chain resolves regardless of the order its calls are written.
fn seed_state_owners(
    body: &PureExpr,
    closure_ensures: &[ClosureEnsuresEntry],
    scope: &mut EnrichScope,
) {
    let mut producers = Vec::new();
    collect_state_producers(body, &mut producers);
    loop {
        let mut changed = false;
        for (receiver, state) in &producers {
            let PureExpr::Var(state_name, _) = state else {
                continue;
            };
            if !scope.bound.contains(state_name) || scope.owners.contains_key(state_name) {
                continue;
            }
            if let Some(owner) = resolve_ensures_owner(receiver, closure_ensures, scope) {
                scope.owners.insert(state_name.clone(), owner);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Replace `expr` (a `postcondition_mut`/`postcondition_once` call on the
/// closure `entry` describes) with `expr AND concrete_ensures`, the entry's
/// ensures instantiated at the call's arguments with captures projected out
/// of the pre/post states. Returns true if a conjunct was injected.
fn inject_concrete_ensures(
    expr: &mut PureExpr,
    entry: &ClosureEnsuresEntry,
    pre_expr: &PureExpr,
    args_expr: &PureExpr,
    post_expr: &PureExpr,
    res_expr: &PureExpr,
) -> bool {
    let concrete_parts: Vec<PureExpr> = entry
        .ensures_exprs
        .iter()
        .map(|expr_part| {
            let expr_part =
                substitute_closure_params_with_args(expr_part, &entry.param_names, args_expr);
            substitute_captures_inline(
                &expr_part,
                &entry.capture_bindings,
                pre_expr,
                post_expr,
                res_expr,
                false,
            )
        })
        .collect();
    if concrete_parts.is_empty() {
        return false;
    }

    let concrete = concrete_parts
        .into_iter()
        .reduce(|acc, p| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(p)))
        .expect("non-empty after is_empty guard");
    let original = std::mem::replace(expr, PureExpr::Bool(true));
    *expr = PureExpr::BinOp(Arc::new(original), BinOp::And, Arc::new(concrete));
    true
}

/// Recursively walk an existential and inject concrete ensures for postcondition_mut calls.
fn enrich_existential_body(expr: &mut PureExpr, closure_ensures: &[ClosureEnsuresEntry]) -> bool {
    enrich_existential_body_in(expr, closure_ensures, &EnrichScope::default())
}

fn enrich_existential_body_in(
    expr: &mut PureExpr,
    closure_ensures: &[ClosureEnsuresEntry],
    scope: &EnrichScope,
) -> bool {
    match expr {
        PureExpr::Exists { var, body, .. } => {
            let mut inner = scope.clone();
            inner.owners.remove(var.as_str());
            inner.bound.insert(var.clone());
            seed_state_owners(body, closure_ensures, &mut inner);
            enrich_existential_body_in(Arc::make_mut(body), closure_ensures, &inner)
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            let l = enrich_existential_body_in(Arc::make_mut(left), closure_ensures, scope);
            let r = enrich_existential_body_in(Arc::make_mut(right), closure_ensures, scope);
            l || r
        }
        // A callee's postcondition is assumed at the call site GUARDED by its
        // precondition — `f.precondition(args) ==> exists<st, r>
        // f.postcondition_mut(args, st, r)` — so the existential lives in
        // the consequent. Enriching there is the same definitional expansion
        // as under a conjunction: `A ==> E` becomes `A ==> (E && Def)` with
        // `Def` the ensures of the closure the call's RECEIVER IS (resolved
        // by identity in `resolve_ensures_owner`; an unidentified receiver
        // gets nothing) instantiated at `E`'s arguments, which that closure's
        // `postcondition_mut` denotes by definition. The antecedent is never
        // touched: a precondition is an obligation on the caller, not a place
        // to assume anything.
        PureExpr::BinOp(_, BinOp::Implies, right) => {
            enrich_existential_body_in(Arc::make_mut(right), closure_ensures, scope)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "postcondition_mut" && args.len() == 3 => {
            let Some(owner) = resolve_ensures_owner(receiver, closure_ensures, scope) else {
                tracing::debug!(
                    receiver = ?receiver,
                    "closure ensures NOT injected: postcondition_mut receiver is not an \
                     identified contracted closure"
                );
                return false;
            };
            let pre_expr = receiver.as_ref().clone();
            let args_expr = args[0].clone();
            let post_expr = args[1].clone();
            let res_expr = args[2].clone();
            inject_concrete_ensures(
                expr,
                &closure_ensures[owner],
                &pre_expr,
                &args_expr,
                &post_expr,
                &res_expr,
            )
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "postcondition_once" && args.len() >= 2 => {
            let Some(owner) = resolve_ensures_owner(receiver, closure_ensures, scope) else {
                tracing::debug!(
                    receiver = ?receiver,
                    "closure ensures NOT injected: postcondition_once receiver is not an \
                     identified contracted closure"
                );
                return false;
            };
            // FnOnce::call_once consumes the closure — no explicit post-state.
            // Post-state distributes Final to each capture individually for
            // tuple-shaped closure environments, not wrapping the whole tuple.
            // See #2668 for details on FnOnce nested capture edge cases.
            let pre_expr = receiver.as_ref().clone();
            let args_expr = args[0].clone();
            let post_expr = final_receiver_state_expr(&pre_expr);
            let res_expr = args.last().cloned().unwrap_or(PureExpr::Bool(false));
            inject_concrete_ensures(
                expr,
                &closure_ensures[owner],
                &pre_expr,
                &args_expr,
                &post_expr,
                &res_expr,
            )
        }
        _ => false,
    }
}

#[cfg(test)]
pub(super) fn enrich_existential_body_for_test(
    expr: &mut PureExpr,
    closure_ensures: &[ClosureEnsuresEntry],
) -> bool {
    enrich_existential_body(expr, closure_ensures)
}

pub(crate) fn strip_receiver_state_wrappers(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Deref(inner) | PureExpr::Final(inner) => strip_receiver_state_wrappers(inner),
        _ => expr.clone(),
    }
}

pub(crate) fn strip_deref_wrappers(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::Deref(inner) => strip_deref_wrappers(inner),
        _ => expr.clone(),
    }
}

pub(crate) fn final_receiver_state_expr(self_expr: &PureExpr) -> PureExpr {
    let base = strip_receiver_state_wrappers(self_expr);
    match base {
        PureExpr::LogicFnCall { name, args } if tuple_logic_fn_arity(&name) == Some(args.len()) => {
            let advanced_args = args
                .into_iter()
                .map(|arg| PureExpr::Final(Arc::new(arg)))
                .collect();
            PureExpr::LogicFnCall {
                name,
                args: advanced_args,
            }
        }
        _ => PureExpr::Final(Arc::new(strip_deref_wrappers(self_expr))),
    }
}
