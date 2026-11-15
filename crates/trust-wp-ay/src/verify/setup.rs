// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared setup for function and mutable-borrow verification paths.
//!
//! Submodules:
//! - [`bootstrap`]: shared encoder bootstrap for function and loop paths.
//! - [`datatype_predecl`]: Datatype variable pre-declaration (match scrutinee sort inference).
//! - [`requirements`]: logic-requirement detection and goal filtering.

mod bootstrap;
mod datatype_predecl;
mod requirements;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    sync::Arc,
    time::Duration,
};

use trust_wp_core::{
    formula::{BinOp, PureExpr},
    logic::{AdtDecls, LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};

#[cfg(test)]
pub(in crate::verify) use self::requirements::any_expr_matches;
pub(in crate::verify) use self::{
    bootstrap::{bootstrap_encoder, BootstrapRequest, ExprSlice, LogicFnInput, TypeInvariantInput},
    requirements::{
        detect_logic_requirements, filter_logic_functions_for_goal,
        filter_type_invariants_for_goal, formula_exprs_with_type_invariant_bodies,
    },
};
#[cfg(test)]
use crate::encoder::sort_context::var_collection::{
    collect_variable_usage, collect_variable_usage_as_formula, determine_sort, VarUsage,
};
use crate::{
    encoder::{
        ground_pool::AxiomKind, simplify_ground, sort_context::resolve_nameable_expr, unsoundness,
        AYEncoder, AssertionPhase,
    },
    error::EncodingError,
    expr::{
        instantiate_standard_precondition_foralls, is_grounding_exempt_standard_forall,
        is_standard_data_structure_precondition_forall,
    },
};

/// Catch ay panics during a setup phase, restoring unsoundness counters on
/// failure. Uses the tightened trust-wp-side classifier (#1977). See
/// [`super::pipeline::catch_verification_phase_ay_panics`] for the rationale
/// on counter rollback. (#2623)
fn catch_setup_phase_ay_panics<T, F>(phase: &str, f: F) -> Result<T, EncodingError>
where
    F: FnOnce() -> Result<T, EncodingError> + std::panic::UnwindSafe,
{
    let pre_snapshot = unsoundness::snapshot();
    let result = super::catch_ay_panics_tightened(f, |reason| {
        Err(EncodingError::solver_error(format!(
            "ay solver panic during {phase}: {reason}"
        )))
    });
    if result.is_err() {
        unsoundness::restore(&pre_snapshot);
    }
    result
}

/// Shared inputs for setting up a contract verification encoder.
pub(super) struct VerificationSetup<'a> {
    pub requires: &'a [PureExpr],
    pub ensures: &'a [PureExpr],
    pub context_exprs: &'a [&'a PureExpr],
    /// The expression that defines synthetic `result`, if any. This is a
    /// narrower signal than `context_exprs`, which may contain unrelated
    /// mut-borrow final values.
    pub result_expr: Option<&'a PureExpr>,
    /// Ghost context expressions (formula assertions from callee specs).
    /// These ARE formulas and need `register_formula_sort_hints` — unlike
    /// return_expr/final_values in `context_exprs` which are value expressions. (#1927)
    pub ghost_context: Option<&'a [PureExpr]>,
    pub logic_fns: Option<&'a [LogicFnDef]>,
    pub mode_overrides: Option<&'a [LogicMode]>,
    pub type_invariants: Option<&'a [TypeInvariantDef]>,
    pub track: TrackLevel,
    pub timeout: Option<Duration>,
    pub type_constants: Option<&'a HashMap<String, PureExpr>>,
    pub closure_captures: Option<&'a [super::ClosureCaptureInfo]>,
    pub adt_decls: Option<&'a AdtDecls>,
    /// Per-ADT integer field range constraints, applied during bootstrap
    /// (before datatypes are declared) so the ground field-range assumptions
    /// (`assert_adt_field_range_ground_assumptions` + the `rebind_var` hook)
    /// fire for struct/enum fields. Previously the function pipeline set these
    /// only AFTER setup, i.e. after the datatype was already declared, so the
    /// range facts (`field(x) >= 0`) were silently dropped for the
    /// function-level postcondition VC (#2702).
    pub adt_field_ranges: Option<&'a trust_wp_core::logic::AdtFieldRanges>,
}

/// Return value from [`setup_verification_encoder`]: the configured encoder
/// plus a snapshot taken after bootstrap but before precondition encoding.
///
/// The `post_bootstrap_snapshot` captures unsoundness counter state after
/// sort-hint registration, logic function declaration, and type invariant
/// registration, but BEFORE `encode_and_assert_requires` runs. This lets
/// the caller distinguish bootstrap false-positive increments (e.g.,
/// `SortFallbackToIntFromLogicFn` from sort-hint inference encountering
/// `LogicFnCall` nodes before declarations exist) from real precondition-
/// phase increments. (#2623)
pub(super) struct SetupResult {
    pub(super) encoder: AYEncoder,
    /// Goal-filtered logic functions with effective visibility modes applied.
    pub(super) filtered_logic_fns: Option<Vec<LogicFnDef>>,
    /// Mode overrides aligned with `filtered_logic_fns`.
    pub(super) filtered_mode_overrides: Option<Vec<LogicMode>>,
    /// Snapshot after bootstrap, before precondition encoding.
    pub(super) post_bootstrap_snapshot: unsoundness::Snapshot,
}

/// Build and initialize an encoder with shared verification setup steps.
///
/// This centralizes the setup used by both function and mutable-borrow
/// verification paths:
/// 1. filter logic functions + mode overrides for the current goal,
/// 2. detect whether quantifier-capable encoder is required,
/// 3. create and configure encoder (track/timeout/type constants),
/// 4. register sort hints and logic/type-invariant declarations,
/// 5. assert preconditions.
///
/// Returns a [`SetupResult`] containing the encoder and a post-bootstrap
/// unsoundness snapshot (taken between steps 4 and 5). (#2623)
pub(super) fn setup_verification_encoder(
    setup: &VerificationSetup<'_>,
) -> Result<SetupResult, EncodingError> {
    let VerificationSetup {
        requires,
        ensures,
        context_exprs,
        result_expr,
        ghost_context,
        logic_fns,
        mode_overrides,
        type_invariants,
        track,
        timeout,
        type_constants,
        closure_captures,
        adt_decls,
        adt_field_ranges,
    } = setup;

    let mut expr_slices = vec![ExprSlice::formula(requires), ExprSlice::formula(ensures)];
    for expr in *context_exprs {
        expr_slices.push(ExprSlice::value(std::slice::from_ref(*expr)));
    }
    if let Some(ghost_exprs) = ghost_context {
        expr_slices.push(ExprSlice::formula(ghost_exprs));
    }

    let mut formula_exprs = Vec::new();
    formula_exprs.extend(requires.iter().cloned());
    formula_exprs.extend(ensures.iter().cloned());
    if let Some(ghost_exprs) = ghost_context {
        formula_exprs.extend(ghost_exprs.iter().cloned());
    }
    let value_exprs: Vec<&PureExpr> = context_exprs.to_vec();
    let filtered_type_invariants_for_logic_filter =
        filter_type_invariants_for_goal(*type_invariants, &formula_exprs, &[], &value_exprs);
    let logic_formula_exprs = formula_exprs_with_type_invariant_bodies(
        &formula_exprs,
        filtered_type_invariants_for_logic_filter.as_deref(),
    );
    let (filtered_logic_fns, filtered_mode_overrides) = filter_logic_functions_for_goal(
        *logic_fns,
        *mode_overrides,
        &logic_formula_exprs,
        &[],
        &value_exprs,
    )?;

    let logic_fn_input = logic_fns.map(|fns| {
        if postconditions_contain_universal(ensures)
            || value_exprs_contain_logic_proof_call(&value_exprs, fns)
        {
            LogicFnInput::FilterForGoalGroundOnly(fns)
        } else {
            LogicFnInput::FilterForGoal(fns)
        }
    });

    let mut encoder = catch_setup_phase_ay_panics(
        "setup_verification_encoder::bootstrap_encoder",
        std::panic::AssertUnwindSafe(|| {
            bootstrap_encoder(BootstrapRequest {
                expr_slices: &expr_slices,
                result_postconditions: Some(ensures),
                result_expr: *result_expr,
                logic_fns: logic_fn_input,
                mode_overrides: *mode_overrides,
                type_invariants: type_invariants.map(TypeInvariantInput::FilterForGoal),
                track: *track,
                timeout: *timeout,
                type_constants: *type_constants,
                closure_captures: *closure_captures,
                adt_decls: *adt_decls,
                // Apply field ranges during bootstrap so the range axioms fire
                // when the datatype is first declared. The function path's later
                // `set_adt_field_ranges` call is redundant for axiom
                // emission but harmless (it re-sets the same ranges). (#2702)
                adt_field_ranges: *adt_field_ranges,
            })
        }),
    )?;

    // Snapshot AFTER bootstrap (sort hints, logic fn decls, type invariants,
    // closure sorts) but BEFORE precondition encoding. This captures only
    // bootstrap false-positive unsoundness increments, not real precondition-
    // phase increments. (#2623)
    let post_bootstrap_snapshot = unsoundness::snapshot();

    // Eliminate top-level equalities that merely give a free Seq carrier a
    // name (for example, `v == final(call_4)`) by binding that source name to
    // the exact target term before any premise is encoded. This is ordinary
    // equality substitution: later premises, ghost facts, and goals all see
    // the same term through the encoder environment, while the defining
    // equality becomes reflexive. Keeping the raw equality leaves two free
    // non-string Seq constants in the SAT base, which ay correctly refuses to
    // call model-validated when neither class has a concrete Seq value.
    //
    // The planner is deliberately narrow: only annotated Seq variables and
    // nameable Var/Old/Deref/Final carriers participate, and installation is
    // gated to ghost-declared sources used nowhere except top-level alias
    // equalities. It resolves alias chains, rejects occurs-check/dependency
    // cycles, and leaves temporal/program-variable uses, disequalities, and
    // non-variable equalities untouched. (#2616)
    encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
        catch_setup_phase_ay_panics(
            "setup_verification_encoder::install_free_seq_carrier_aliases",
            std::panic::AssertUnwindSafe(|| {
                install_free_seq_carrier_aliases(
                    encoder,
                    requires,
                    ensures,
                    context_exprs,
                    *ghost_context,
                )
            }),
        )
    })?;

    // Pre-seed concrete (ground) SeqValues for LONG chained push_back patterns
    // BEFORE per-assumption encoding (#1317 pre-seed). The push_back call-site
    // assumptions (`View(Final(x)) == View(x).push_back(N)`) can arrive before
    // the base `View(x).len() == 0` fact, so when each push_back is encoded its
    // receiver still resolves through UF projectors and the encoder emits a
    // SYMBOLIC-index store shape constraint
    // (`store(seq_array(x), seq_offset(x) + seq_len(x), N)`). A whole chain of
    // such symbolic-index stores drives ay's Array theory into an expensive
    // (timeout-inducing) read-over-write search even though the verification
    // goal is decided by trivial linear arithmetic. Materializing the ground
    // store-chain first means the registry-first projectors
    // (`seq_array_term`/`seq_offset_term`/`seq_len_term`) return concrete
    // components, so each push_back encodes to a GROUND-index store that ay's
    // const-array/store normalizer collapses cheaply. The pre-seed is gated to
    // chains of >= 2 push_back edges (the only ones that trigger the Array
    // timeout) and the post-encoding reconstruction below is skipped for any
    // base the pre-seed already materialized, so this adds no facts the
    // post-pass would not have added: it cannot turn a SAT goal into a (false)
    // UNSAT.
    encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
        catch_setup_phase_ay_panics(
            "setup_verification_encoder::preseed_long_chained_push_back_chain",
            std::panic::AssertUnwindSafe(|| {
                encoder.preseed_long_chained_push_back_chain(requires, None)
            }),
        )
    })?;

    encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
        catch_setup_phase_ay_panics(
            "setup_verification_encoder::encode_and_assert_requires",
            std::panic::AssertUnwindSafe(|| encode_and_assert_requires(encoder, requires)),
        )
    })?;

    // Off-loop general recursive-logic-fn defining-equation unfolder
    // (#recursive-unfolder): supply the bounded defining equations of recursive
    // structural logic fns (len/get/...) appearing in the premises, so
    // recursive-datatype obligations can derive structural facts (e.g.
    // `len(l)>1 => is_some(l.1)`) that are otherwise absent (recursive fns get
    // no global defining axiom). SOUND: each fact is a true instance of the fn's
    // own definition; coercing facts are dropped. Env-gated during rollout.
    if std::env::var_os("TRUST_WP_OFFLOOP").is_some() {
        let offloop_fns = filtered_logic_fns.clone();
        encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
            catch_setup_phase_ay_panics(
                "setup_verification_encoder::assert_offloop_recursive_defining_unfoldings",
                std::panic::AssertUnwindSafe(|| {
                    super::loops::recursive_unfolding::assert_offloop_recursive_defining_unfoldings(
                        encoder,
                        requires,
                        offloop_fns.as_deref(),
                    )
                }),
            )
        })?;
    }

    // After all preconditions are encoded, reconstruct chained SeqValues
    // from flat push_back assumption patterns (#1317). When the driver
    // produces non-chained assumptions (all push_back ops use the same base
    // variable), the normal encoding produces partial/conflicting SeqValues.
    // This pass detects the full pattern (len==0 + N push_back assignments)
    // and synthesizes the intended chained Array via store operations,
    // overriding any partial SeqValues. This runs BEFORE postcondition
    // encoding so that seq_len_term/seq_index_term use the complete chain.
    catch_setup_phase_ay_panics(
        "setup_verification_encoder::try_reconstruct_flat_push_back_chain",
        std::panic::AssertUnwindSafe(|| {
            encoder.try_reconstruct_flat_push_back_chain(requires, None)
        }),
    )?;

    // The same push_back facts may already be chained but arrive before the
    // base len==0 fact. Rebuild those chains after all requires are known so
    // indexed postconditions use concrete Array/store SeqValues.
    catch_setup_phase_ay_panics(
        "setup_verification_encoder::try_reconstruct_chained_push_back_chain",
        std::panic::AssertUnwindSafe(|| {
            encoder.try_reconstruct_chained_push_back_chain(requires, None)
        }),
    )?;

    Ok(SetupResult {
        encoder,
        filtered_logic_fns,
        filtered_mode_overrides,
        post_bootstrap_snapshot,
    })
}

fn annotated_seq_var(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, Some(trust_wp_core::formula::ExprSort::Seq)) => Some(name),
        _ => None,
    }
}

fn is_nameable_carrier(expr: &PureExpr) -> bool {
    crate::encoder::sort_context::resolve_nameable_expr(expr, None).is_some()
}

/// Plan exact substitutions for top-level free Seq carrier equalities.
///
/// Variable-variable equalities form undirected equivalence classes. A
/// nameable non-variable target attached to any class becomes the target for
/// the whole class; otherwise all but one deterministic representative are
/// eliminated. Dependencies between classes are then expanded, with an
/// occurs/dependency cycle causing every alias that depends on it to be
/// refused.
fn plan_free_seq_carrier_aliases(requires: &[PureExpr]) -> BTreeMap<String, PureExpr> {
    let mut adjacency: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut targets: BTreeMap<String, Vec<(usize, PureExpr)>> = BTreeMap::new();

    for (index, requirement) in requires.iter().enumerate() {
        let PureExpr::BinOp(left, BinOp::Eq, right) = requirement else {
            continue;
        };
        let left_var = annotated_seq_var(left);
        let right_var = annotated_seq_var(right);
        match (left_var, right_var) {
            (Some(left_name), Some(right_name)) if left_name != right_name => {
                adjacency
                    .entry(left_name.to_string())
                    .or_default()
                    .insert(right_name.to_string());
                adjacency
                    .entry(right_name.to_string())
                    .or_default()
                    .insert(left_name.to_string());
            }
            (Some(source), None) if is_nameable_carrier(right) => {
                adjacency.entry(source.to_string()).or_default();
                targets
                    .entry(source.to_string())
                    .or_default()
                    .push((index, right.as_ref().clone()));
            }
            (None, Some(source)) if is_nameable_carrier(left) => {
                adjacency.entry(source.to_string()).or_default();
                targets
                    .entry(source.to_string())
                    .or_default()
                    .push((index, left.as_ref().clone()));
            }
            _ => {}
        }
    }

    let mut raw_aliases = BTreeMap::new();
    let mut visited = BTreeSet::new();
    for root in adjacency.keys() {
        if visited.contains(root) {
            continue;
        }
        let mut pending = vec![root.clone()];
        let mut component = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if !visited.insert(name.clone()) {
                continue;
            }
            component.insert(name.clone());
            if let Some(neighbors) = adjacency.get(&name) {
                pending.extend(neighbors.iter().cloned());
            }
        }

        let mut candidates = Vec::new();
        for member in &component {
            if let Some(member_targets) = targets.get(member) {
                candidates.extend(member_targets.iter().cloned());
            }
        }
        candidates.sort_by_key(|(index, _)| *index);
        let target = candidates.into_iter().find_map(|(_, candidate)| {
            let free = candidate.free_vars();
            free.iter()
                .all(|name| !component.contains(name))
                .then_some(candidate)
        });

        if let Some(target) = target {
            for member in component {
                raw_aliases.insert(member, target.clone());
            }
        } else if component.len() > 1 {
            let representative = component
                .iter()
                .next()
                .expect("non-empty Seq alias component")
                .clone();
            for member in component {
                if member != representative {
                    raw_aliases.insert(
                        member,
                        PureExpr::Var(
                            representative.clone(),
                            Some(trust_wp_core::formula::ExprSort::Seq),
                        ),
                    );
                }
            }
        }
    }

    fn resolve_one(
        name: &str,
        raw: &BTreeMap<String, PureExpr>,
        visiting: &mut BTreeSet<String>,
        memo: &mut BTreeMap<String, Option<PureExpr>>,
    ) -> Option<PureExpr> {
        if let Some(cached) = memo.get(name) {
            return cached.clone();
        }
        if !visiting.insert(name.to_string()) {
            return None;
        }

        let resolved = raw.get(name).and_then(|target| {
            let mut substitutions = HashMap::new();
            let mut dependencies: Vec<String> = target
                .free_vars()
                .iter()
                .filter(|dependency| raw.contains_key(*dependency))
                .cloned()
                .collect();
            dependencies.sort();
            for dependency in dependencies {
                substitutions.insert(
                    dependency.clone(),
                    resolve_one(&dependency, raw, visiting, memo)?,
                );
            }
            Some(target.substitute(&substitutions))
        });

        visiting.remove(name);
        memo.insert(name.to_string(), resolved.clone());
        resolved
    }

    let mut resolved = BTreeMap::new();
    let mut memo = BTreeMap::new();
    for name in raw_aliases.keys() {
        if let Some(target) = resolve_one(name, &raw_aliases, &mut BTreeSet::new(), &mut memo) {
            if !target.free_vars().contains(name) {
                resolved.insert(name.clone(), target);
            }
        }
    }
    resolved
}

fn install_free_seq_carrier_aliases(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
    ghost_context: Option<&[PureExpr]>,
) -> Result<(), EncodingError> {
    let aliases = plan_free_seq_carrier_aliases(requires);
    for (source, target) in aliases {
        // This substitution is reserved for fresh ghost carrier names: the
        // source must be declared by a top-level ghost alias and every use of
        // it in the setup context must itself be a top-level alias equality.
        // In particular, a program variable mentioned through `Final`, `Old`,
        // a method call, or a goal is not rebound across temporal states.
        let is_alias_use = |expr: &PureExpr| {
            let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
                return false;
            };
            annotated_seq_var(left).is_some_and(|name| name == source)
                || annotated_seq_var(right).is_some_and(|name| name == source)
        };
        let declared_by_ghost = ghost_context.is_some_and(|exprs| {
            exprs
                .iter()
                .any(|expr| expr.free_vars().contains(&source) && is_alias_use(expr))
        });
        let only_alias_uses = requires
            .iter()
            .chain(ensures)
            .chain(context_exprs.iter().copied())
            .chain(ghost_context.into_iter().flatten())
            .all(|expr| !expr.free_vars().contains(&source) || is_alias_use(expr));
        if !declared_by_ghost || !only_alias_uses {
            continue;
        }

        let Some(source_sort) = encoder.var_sort(&source).cloned() else {
            continue;
        };
        if !crate::encoder::sort_context::is_seq_family_sort(&source_sort) {
            continue;
        }
        let target_term = encoder.encode_pure(&target)?;
        let target_sort = encoder.solver.get_sort(target_term);
        if target_sort != source_sort {
            continue;
        }
        encoder.rebind_var(&source, target_term, source_sort);
        encoder.record_var_expr_alias(&source, target);
    }
    Ok(())
}

fn postconditions_contain_universal(ensures: &[PureExpr]) -> bool {
    ensures
        .iter()
        .any(|expr| expr.any_recursive(|node| matches!(node, PureExpr::Forall { .. })))
}

fn value_exprs_contain_logic_proof_call(
    value_exprs: &[&PureExpr],
    logic_fns: &[LogicFnDef],
) -> bool {
    value_exprs
        .iter()
        .any(|expr| expr_contains_logic_proof_call(expr, logic_fns))
}

fn expr_contains_logic_proof_call(expr: &PureExpr, logic_fns: &[LogicFnDef]) -> bool {
    match expr {
        PureExpr::Let { var, value, body } => {
            if !body.free_vars().contains(var) {
                if let PureExpr::LogicFnCall { name, args } = value.as_ref() {
                    if logic_fns.iter().any(|logic_fn| {
                        logic_fn.name() == name
                            && logic_fn.params().len() == args.len()
                            && !logic_fn.ensures().is_empty()
                    }) {
                        return true;
                    }
                }
            }
            expr_contains_logic_proof_call(body, logic_fns)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_contains_logic_proof_call(assumption, logic_fns)
                || expr_contains_logic_proof_call(body, logic_fns)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_contains_logic_proof_call(obligation, logic_fns)
                || expr_contains_logic_proof_call(body, logic_fns)
        }
        PureExpr::Ite(cond, then_branch, else_branch) => {
            expr_contains_logic_proof_call(cond, logic_fns)
                || expr_contains_logic_proof_call(then_branch, logic_fns)
                || expr_contains_logic_proof_call(else_branch, logic_fns)
        }
        PureExpr::BinOp(left, _, right) => {
            expr_contains_logic_proof_call(left, logic_fns)
                || expr_contains_logic_proof_call(right, logic_fns)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_contains_logic_proof_call(inner, logic_fns),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            // Method-syntax call to a logic fn with ensures (e.g.
            // `l.lemma_sum_nonneg()`). Receiver counts as the first param,
            // so `params().len()` should equal `args.len() + 1`. Required
            // so recursive `&self` lemmas whose induction step is a
            // method-call inside a `match` arm are recognized as logic
            // proof calls.
            if logic_fns.iter().any(|logic_fn| {
                logic_fn.name() == method
                    && logic_fn.params().len() == args.len() + 1
                    && !logic_fn.ensures().is_empty()
            }) {
                return true;
            }
            expr_contains_logic_proof_call(receiver, logic_fns)
                || args
                    .iter()
                    .any(|arg| expr_contains_logic_proof_call(arg, logic_fns))
        }
        PureExpr::LogicFnCall { name, args } => {
            logic_fns.iter().any(|logic_fn| {
                logic_fn.name() == name
                    && logic_fn.params().len() == args.len()
                    && !logic_fn.ensures().is_empty()
            }) || args
                .iter()
                .any(|arg| expr_contains_logic_proof_call(arg, logic_fns))
        }
        PureExpr::Match { scrutinee, arms } => {
            // Descend into match arm bodies so recursive lemma calls inside
            // pattern arms (the canonical structural-induction shape) are
            // recognized as logic proof calls.
            expr_contains_logic_proof_call(scrutinee, logic_fns)
                || arms
                    .iter()
                    .any(|arm| expr_contains_logic_proof_call(&arm.body, logic_fns))
        }
        _ => false,
    }
}

/// Encode and assert preconditions with existential Skolemization.
pub(in crate::verify) fn encode_and_assert_requires(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    // Preconditions are ASSUMPTION-position expressions: shift-amount range
    // obligations embedded in them (driver-injected body facts, e.g. the
    // proof_assert lane's leading path conditions) are owned — path-guarded —
    // by the body VALUE encoding and must not be re-collected unguarded here.
    // (ledger int-shift-full)
    encoder.with_assumption_position(|encoder| encode_and_assert_requires_inner(encoder, requires))
}

fn encode_and_assert_requires_inner(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    let simplified_requires: Vec<PureExpr> = requires.iter().map(simplify_ground).collect();
    let grounded_standard_foralls = instantiate_standard_precondition_foralls(&simplified_requires);
    for instance in &grounded_standard_foralls {
        tracing::trace!(
            ?instance,
            "asserting grounded standard-library quantified precondition fact"
        );
        let term = encoder.encode_pure(instance)?;
        // Defensive Bool-coercion: grounded standard-library forall instances
        // (e.g. spec'd `such_that` assumptions like `(*predicate).get(*x)`)
        // can return Int-sorted terms when the chained Mapping closure body
        // loses its Bool context. Coerce via `!= 0` to recover the truth
        // value. (#5)
        let bool_term = encoder.coerce_bool_operand(term);
        encoder.assert_term(bool_term);
    }
    if !grounded_standard_foralls.is_empty() {
        tracing::debug!(
            count = grounded_standard_foralls.len(),
            "grounded standard-library quantified precondition facts"
        );
    }

    for (index, req) in requires.iter().enumerate() {
        // Pre-simplify: reduce match expressions with known-constructor
        // scrutinees before encoding. This handles patterns like
        // `match *None() { Some(v) => ..., None => call == Err(true) }`
        // which arise from match-style postconditions substituted with
        // concrete Option/Result values. Without this, the encoder produces
        // an ITE chain whose constructor-tester conditions may not simplify
        // in ay, causing spurious counterexamples. (#2675)
        let req_ref = &simplified_requires[index];
        if is_standard_data_structure_precondition_forall(req_ref) {
            // Ground-then-drop coherence (ghost_set):
            // the instantiator EXEMPTS negative-contains foralls (e.g. FSet
            // EMPTY's `forall<k> !result.contains(k)`) from grounding, so
            // skipping them here would drop the premise entirely — neither
            // grounded nor asserted. Assert exempted foralls; skip only the
            // foralls the grounding pass actually consumed.
            if !is_grounding_exempt_standard_forall(req_ref) {
                tracing::debug!(
                    index,
                    "skipping quantified standard-library precondition after grounding"
                );
                continue;
            }
            tracing::debug!(
                index,
                "asserting grounding-exempt negative-contains standard forall"
            );
        }
        let expanded_req = expand_transparent_logic_fn_precondition(encoder, req_ref);
        let phase = format!("encode_and_assert_requires[{index}] {req_ref:?}");
        catch_setup_phase_ay_panics(
            &phase,
            std::panic::AssertUnwindSafe(|| {
                // Existentials containing postcondition_mut must be Skolemized rather
                // than encoded as ay existential quantifiers. ay-dpll cannot handle
                // existential quantifiers, causing "unknown (quantifiers)" (#970).
                // Skolemization creates fresh constants and registers all inner
                // variables (Final/Deref) so postcondition goals can reference them.
                let is_skolemizable = matches!(&expanded_req, PureExpr::Exists { var, body, .. }
                if AYEncoder::body_has_postcondition_mut_with_var(body, var.as_str())
                    || AYEncoder::body_has_any_postcondition_mut(body));
                let term = if is_skolemizable {
                    encoder.encode_with_recursive_existential_skolemization(&expanded_req)?
                } else {
                    encoder.encode_pure(&expanded_req)?
                };
                // Defensive Bool-coercion at the precondition/assumption
                // boundary. Chained `Mapping<_, Bool>::get(...)` calls (e.g.
                // the second `such_that` witness in `such_that.rs`) can produce
                // Int-sorted terms when sort inference loses the Bool context
                // through Deref+MethodCall. Coercing via `!= 0` recovers the
                // right Bool truth value. (#5)
                let term = encoder.coerce_bool_operand(term);
                encoder.assert_term(term);
                record_positive_nameable_view_aliases(encoder, &expanded_req);

                // After encoding each precondition, try to synthesize SeqValues for
                // patterns that the normal encoding path misses (#1317):
                //
                // 1. len==0 → empty SeqValue: When call-site assumptions include
                //    `View(Var("x")).len() == 0`, create a concrete empty SeqValue
                //    for `x_view`. This enables subsequent push_back assumptions to
                //    produce ground Array terms (via `seq_array_term` fast-path),
                //    making contradictory flat assumptions UNSAT in Array theory.
                //
                // 2. IndexMut point-write → store-based SeqValue: When a
                //    `View(Final(var)).index_logic(idx) == val` pattern appears,
                //    synthesize a SeqValue for `final_var_view` using Array `store`.
                encoder.try_synthesize_asserted_len_zero_seq_value(&expanded_req, None)?;
                encoder.try_synthesize_index_mut_seq_value(&expanded_req, None)?;
                encoder.try_synthesize_asserted_len_zero_seq_value(req, None)?;
                encoder.try_synthesize_index_mut_seq_value(req, None)?;
                Ok(())
            }),
        )?;
    }
    Ok(())
}

const MAX_PRECONDITION_LOGIC_FN_INLINE_DEPTH: usize = 32;

fn expand_transparent_logic_fn_precondition(encoder: &AYEncoder, expr: &PureExpr) -> PureExpr {
    expand_transparent_logic_fn_precondition_with_depth(encoder, expr, 0, &[])
}

/// Inline transparent (non-recursive, requires-free, body-available) logic
/// functions in a postcondition GOAL expression, mirroring the precondition
/// path. Sound: replaces `f(args)` with its defining body `body[params:=args]`,
/// which is definitionally equal, so the obligation is logically unchanged.
///
/// This is needed for postconditions like `#[ensures(result.wf())]` whose logic
/// fn body contains a nested universal quantifier: left opaque, the goal is
/// `not(wf(result))` over an uninterpreted `wf` whose definition is only
/// available as a quantified bi-implication — ay-dpll cannot skolemize the
/// hidden `forall` to instantiate the supporting per-element facts. Inlining the
/// body exposes the quantifier at the top level so the negated-postcondition
/// router Skolemizes it and the supporting facts E-match. (#2170)
pub(crate) fn expand_transparent_logic_fn_goal(encoder: &AYEncoder, expr: &PureExpr) -> PureExpr {
    expand_transparent_logic_fn_precondition_with_depth(encoder, expr, 0, &[])
}

/// Inline a postcondition-goal clause's transparent logic functions ONLY when
/// doing so newly surfaces a universal quantifier that the opaque call hid.
/// Returns the clause unchanged otherwise, so every postcondition that doesn't
/// fit this pattern is byte-identical (no behavioural change off this path).
/// (#2170)
pub(crate) fn expand_transparent_logic_fn_goal_if_surfaces_quantifier(
    encoder: &AYEncoder,
    expr: &PureExpr,
) -> PureExpr {
    use crate::verify::function::axiom_detection::expr_contains_embedded_universal;
    // Already exposes a quantifier — nothing hidden to surface; leave as-is.
    if matches!(expr, PureExpr::Forall { .. }) || expr_contains_embedded_universal(expr) {
        return expr.clone();
    }
    let expanded = expand_transparent_logic_fn_goal(encoder, expr);
    let changed = format!("{expr:?}") != format!("{expanded:?}");
    let surfaced =
        matches!(expanded, PureExpr::Forall { .. }) || expr_contains_embedded_universal(&expanded);
    if changed && surfaced {
        expanded
    } else {
        expr.clone()
    }
}

fn expand_transparent_logic_fn_precondition_with_depth(
    encoder: &AYEncoder,
    expr: &PureExpr,
    depth: usize,
    active_symbols: &[String],
) -> PureExpr {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            let expanded_args: Vec<PureExpr> = args
                .iter()
                .map(|arg| {
                    expand_transparent_logic_fn_precondition_with_depth(
                        encoder,
                        arg,
                        depth,
                        active_symbols,
                    )
                })
                .collect();
            if depth >= MAX_PRECONDITION_LOGIC_FN_INLINE_DEPTH {
                return PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: expanded_args,
                };
            }
            let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
            if smt_name == "logic_good__bucket" {
                return PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: expanded_args,
                };
            }
            if active_symbols.iter().any(|symbol| symbol == &smt_name) {
                return PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: expanded_args,
                };
            }
            let axiom = encoder.ground_pool_axioms().iter().find(|axiom| {
                axiom.kind == AxiomKind::Defining
                    && axiom.fn_symbol == smt_name
                    && axiom.requires.is_empty()
                    && axiom.params.len() == expanded_args.len()
            });
            let Some(axiom) = axiom else {
                return PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: expanded_args,
                };
            };
            let substitutions: HashMap<String, PureExpr> =
                axiom.params.iter().cloned().zip(expanded_args).collect();
            let expanded = axiom.body.substitute(&substitutions);
            let mut next_active = active_symbols.to_vec();
            next_active.push(smt_name);
            expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                &expanded,
                depth + 1,
                &next_active,
            )
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                left,
                depth,
                active_symbols,
            )),
            *op,
            Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                right,
                depth,
                active_symbols,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                inner,
                depth,
                active_symbols,
            )),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                cond,
                depth,
                active_symbols,
            )),
            Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                then_expr,
                depth,
                active_symbols,
            )),
            Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                else_expr,
                depth,
                active_symbols,
            )),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(
            expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                inner,
                depth,
                active_symbols,
            ),
        )),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(
            expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                inner,
                depth,
                active_symbols,
            ),
        )),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(
            expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                inner,
                depth,
                active_symbols,
            ),
        )),
        PureExpr::View(inner) => PureExpr::View(Arc::new(
            expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                inner,
                depth,
                active_symbols,
            ),
        )),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                receiver,
                depth,
                active_symbols,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| {
                    expand_transparent_logic_fn_precondition_with_depth(
                        encoder,
                        arg,
                        depth,
                        active_symbols,
                    )
                })
                .collect(),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                assumption,
                depth,
                active_symbols,
            )),
            body: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                body,
                depth,
                active_symbols,
            )),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                obligation,
                depth,
                active_symbols,
            )),
            body: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                body,
                depth,
                active_symbols,
            )),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                body,
                depth,
                active_symbols,
            )),
            triggers: triggers.clone(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                body,
                depth,
                active_symbols,
            )),
            triggers: triggers.clone(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                scrutinee,
                depth,
                active_symbols,
            )),
            arms: arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: expand_transparent_logic_fn_precondition_with_depth(
                        encoder,
                        &arm.body,
                        depth,
                        active_symbols,
                    ),
                })
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                value,
                depth,
                active_symbols,
            )),
            body: Arc::new(expand_transparent_logic_fn_precondition_with_depth(
                encoder,
                body,
                depth,
                active_symbols,
            )),
        },
        other => other.clone(),
    }
}

fn record_positive_nameable_view_aliases(encoder: &mut AYEncoder, expr: &PureExpr) {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return;
    };
    record_positive_nameable_view_alias_side(encoder, left, right);
    record_positive_nameable_view_alias_side(encoder, right, left);
}

fn record_positive_nameable_view_alias_side(
    encoder: &mut AYEncoder,
    alias_side: &PureExpr,
    target_side: &PureExpr,
) {
    if !matches!(alias_side, PureExpr::Deref(_) | PureExpr::Final(_)) {
        return;
    }
    if resolve_nameable_expr(target_side, None).is_some() {
        return;
    }
    let Some(alias_name) = resolve_nameable_expr(alias_side, None) else {
        return;
    };
    encoder.record_var_expr_alias(&alias_name, target_side.clone());
}

/// Pre-declare variables with sorts determined from complete expression
/// context, eliminating first-declaration-wins ordering sensitivity.
///
/// Collects all variable usage from requires, ensures, context_exprs,
/// ghost_context, logic function bodies, and type invariant bodies, then
/// determines each variable's sort from the union of all evidence.
/// Variables whose sort resolves to non-Int are pre-declared before any
/// `encode_pure` call, ensuring `get_or_declare_var` finds the correct
/// sort on first encounter. (#1965)
#[cfg(test)]
fn predeclare_collected_vars(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    context_exprs: &[&PureExpr],
    ghost_context: Option<&[PureExpr]>,
    logic_fns: Option<&[LogicFnDef]>,
    type_invariants: Option<&[TypeInvariantDef]>,
) -> Result<(), EncodingError> {
    fn peel_mutref(sort: trust_wp_core::formula::ExprSort) -> trust_wp_core::formula::ExprSort {
        match sort {
            trust_wp_core::formula::ExprSort::MutRef(inner) => {
                if matches!(
                    inner.as_ref(),
                    trust_wp_core::formula::ExprSort::TypeParam(_)
                ) {
                    trust_wp_core::formula::ExprSort::MutRef(inner)
                } else {
                    peel_mutref(*inner)
                }
            }
            other => other,
        }
    }
    fn resolve_predeclare_sort(encoder: &mut AYEncoder, usage: &VarUsage) -> ay_dpll::api::Sort {
        // Datatype annotations need the encoder's declared-sort registry, not
        // the pure structural mapper. Otherwise bootstrap can freeze a
        // user-defined ADT variable as Uninterpreted("Type") before the first
        // encode path resolves it to the registered DatatypeSort. (#1982)
        if let Some(annotation) = usage.annotation.clone() {
            // Peel MutRef layers before sort conversion: the RustHorn encoding
            // represents &mut T variables as (current, final) pairs of the
            // inner sort T, not as a composite MutRef SMT sort. Without
            // peeling, MutRef(TypeParam(T)) predeclares "result" as
            // Uninterpreted("MutRef_T"), causing sort mismatches when
            // bind_result_expr later declares it as Int. (#2673)
            let peeled = peel_mutref(annotation);
            let sort = encoder.sort_from_expr_sort(peeled);
            if sort != ay_dpll::api::Sort::Int {
                return sort;
            }
        }
        if let Some(quantifier_sort) = usage.quantifier_sort.clone() {
            let sort = encoder.sort_from_expr_sort(quantifier_sort);
            if sort != ay_dpll::api::Sort::Int {
                return sort;
            }
        }
        determine_sort(usage)
    }

    // Collect usage across all expression sources.
    let mut all_usage: HashMap<String, VarUsage> = HashMap::new();

    let merge_batch = |batch: HashMap<String, VarUsage>, target: &mut HashMap<String, VarUsage>| {
        for (name, usage) in batch {
            target.entry(name).or_default().merge(usage);
        }
    };

    // Requires and ensures are formula-position expressions (they ARE
    // booleans). A bare `Var("b")` in ensures means `b` is Bool. Use
    // formula-position collection to capture this. (#1965)
    merge_batch(collect_variable_usage_as_formula(requires), &mut all_usage);
    merge_batch(collect_variable_usage_as_formula(ensures), &mut all_usage);

    // context_exprs is &[&PureExpr] — collect each individually.
    for expr in context_exprs {
        let batch = collect_variable_usage(std::slice::from_ref(*expr));
        merge_batch(batch, &mut all_usage);
    }

    if let Some(ghost_exprs) = ghost_context {
        merge_batch(
            collect_variable_usage_as_formula(ghost_exprs),
            &mut all_usage,
        );
    }

    // Logic function bodies/requires/ensures contain sort evidence for
    // variables that may also appear in the caller's contracts. Scanning
    // them gives the pre-declaration pass a more complete picture. (#1965)
    if let Some(fns) = logic_fns {
        for lf in fns {
            merge_batch(
                collect_variable_usage(std::slice::from_ref(lf.body())),
                &mut all_usage,
            );
            if !lf.requires().is_empty() {
                merge_batch(
                    collect_variable_usage_as_formula(lf.requires()),
                    &mut all_usage,
                );
            }
            if !lf.ensures().is_empty() {
                let mut batch = collect_variable_usage_as_formula(lf.ensures());
                // Exclude "result" from logic function ensures scanning.
                // Each logic function's `result` is a per-function synthetic
                // name for the return value. Merging it into the shared usage
                // map causes cross-function pollution: e.g., `pigeon`'s
                // `#[ensures(result)]` (Bool) leaks a Bool sort for `result`
                // into the pre-declaration context, conflicting with
                // `find_ptr_in_seq`'s OptionInt return type. (#994)
                batch.remove("result");
                merge_batch(batch, &mut all_usage);
            }
        }
    }

    // Type invariant bodies are boolean predicates (formula-position).
    // They reference self_param with sort evidence from the invariant's
    // expression structure. (#1965)
    if let Some(invs) = type_invariants {
        for inv in invs {
            merge_batch(
                collect_variable_usage_as_formula(std::slice::from_ref(inv.body())),
                &mut all_usage,
            );
        }
    }

    // Pre-declare variables with non-Int sorts. Skip Int-sorted variables
    // since Int is the default and pre-declaring them would just waste
    // solver namespace without fixing any ordering issues.
    let mut predeclared = 0u32;
    let mut non_int_total = 0u32;
    for (name, usage) in &all_usage {
        let sort = resolve_predeclare_sort(encoder, usage);
        if sort != ay_dpll::api::Sort::Int {
            non_int_total += 1;
            // Only pre-declare if the variable hasn't already been declared
            // (e.g., by predeclare_datatype_vars or closure struct sorts).
            if encoder.var_sort(name).is_none() {
                tracing::trace!(var = %name, ?sort, "predeclare_collected_vars: declaring");
                encoder.get_or_declare_var(name, sort)?;
                predeclared += 1;
            }
        }
    }

    if predeclared > 0 || non_int_total > 0 {
        tracing::debug!(
            predeclared,
            non_int_total,
            total_vars = all_usage.len(),
            "predeclare_collected_vars"
        );
    }

    Ok(())
}

// Re-export datatype predeclaration helpers for tests.
#[cfg(test)]
use datatype_predecl::{
    build_logic_fn_param_dt_map, collect_call_site_dt_vars, collect_datatype_scrutinee_vars,
    resolve_call_site_var_name,
};

#[cfg(test)]
mod tests;
