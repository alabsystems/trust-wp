// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR-location keyed proof_assert snapshot construction.
//!
//! A snapshot captures the driver-side symbolic state at a single proof_assert
//! program point. `prepare_proof_assert` consumes this immutable snapshot and
//! no longer reaches into thread-local extraction side channels.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{
        Body, BorrowKind, Local, Location, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind, VarDebugInfoContents,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_mir_dataflow::Analysis;
use trust_wp_core::{
    contract_parser::parse_contract,
    formula::{internal::tuple_lowering::tuple_field_logic_fn_name, BinOp, ExprSort, PureExpr},
};
use trust_wp_driver::StdSpec;

use super::{
    super::{ghost::GhostBlock, proof_assert::ProofAssert},
    discovery::source_parsing::collect_loop_contract_attrs,
    ghost_context::{
        closure_capture_names, extract_ghost_closure_effects, find_ghost_closure_def_ids_in_mir,
        ghost_block_contains_cutoff, ghost_block_precedes_cutoff,
        rewrite_ghost_closure_capture_vars,
    },
    proof_assert_extract::{
        apply_projected_writes_to_substitutions, collapse_idempotent_views,
        extract_body_for_proof_assert, extract_call_effects, get_arg_names_for_proof_assert_body,
        is_projected_write_repair_assumption, preserve_transparent_adapter_view_witness,
        resolve_internal_references_at_current_state, substitution_assumptions,
        transparent_adapter_inner, without_current_pointee_keys, ProofAssertExtractionParams,
    },
    proof_assert_snapshot_facts::{
        collect_scalar_wrapper_aliases, derive_snapshot_deref_alias_substitutions,
        substitute_snapshot_facts,
    },
    verification_context::ProofAssertContext,
};
use crate::{
    ghost::source_assignments::collect_ghost_source_assignments,
    mir_analysis::{
        clear_qualified_assoc_const_definitions, detect_loops, effects::MappingClosureInfo,
        extract::PROOF_ASSERT_STATE_MARKER_NAME, extract_loop_body, get_mir_body,
        normalize_immutable_ref_param_derefs, resolve_arg_names_or_warn,
        take_qualified_assoc_const_definitions, CallSpecContext, NameSubstitutions,
    },
};

/// Driver-side symbolic state snapshot for one proof assertion.
#[derive(Debug, Clone)]
pub(super) struct AssertionSnapshot {
    pub(super) assertion: ProofAssert,
    pub(super) call_effect_expr: Option<PureExpr>,
    pub(super) return_expr: Option<PureExpr>,
    pub(super) substitutions: NameSubstitutions,
    pub(super) assumed_facts: Vec<PureExpr>,
    pub(super) substitution_facts: Vec<PureExpr>,
    pub(super) call_assumptions: Vec<PureExpr>,
    pub(super) call_obligations: Vec<PureExpr>,
    pub(super) has_mutating_call_effect: bool,
    pub(super) mapping_closures: Vec<MappingClosureInfo>,
    pub(super) assoc_const_substitutions: HashMap<String, PureExpr>,
    /// Closure-local loop continuation assumptions for proof_asserts inside
    /// ghost closures that follow a loop. (#2584)
    pub(super) post_loop_assumptions: Vec<PureExpr>,
    /// The names the loop lane's exit facts may not mention at this
    /// assertion, or `None` when they do not hold at it
    /// ([`function_exit_fact_stale_names`], D-189).
    pub(super) exit_fact_stale_names: Option<HashSet<String>>,
    /// The by-value parameters whose entry value this assertion reads by a
    /// symbol of its own (D-241).
    pub(super) entry_versions: ParamEntryVersions,
}

/// Snapshot construction failure.
#[derive(Debug, Clone)]
pub(super) struct AssertionSnapshotError {
    pub(super) assertion: ProofAssert,
    pub(super) reason: String,
}

impl AssertionSnapshotError {
    fn missing_location(assertion: &ProofAssert, fn_path: &str) -> Self {
        Self {
            assertion: assertion.clone(),
            reason: format!("proof_assert in {fn_path} missing MIR location"),
        }
    }
}

/// Build immutable snapshots for each proof_assert in one function.
pub(super) fn build_assertion_snapshots_for_function(
    tcx: TyCtxt<'_>,
    assertions: &[ProofAssert],
    ghost_blocks: &[GhostBlock],
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
    local_crate_name: &str,
) -> Vec<Result<AssertionSnapshot, AssertionSnapshotError>> {
    let mut body_arg_names: HashMap<LocalDefId, Vec<String>> = HashMap::new();
    assertions
        .iter()
        .map(|assertion| {
            let fn_path_local = tcx.def_path_str(assertion.containing_fn);
            let fn_path = format!("{local_crate_name}::{fn_path_local}");
            let Some(location) = assertion.location else {
                return Err(AssertionSnapshotError::missing_location(
                    assertion, &fn_path,
                ));
            };
            let arg_names = body_arg_names
                .entry(assertion.containing_fn)
                .or_insert_with(|| {
                    get_arg_names_for_proof_assert_body(tcx, assertion.containing_fn)
                });
            let containing_ghost_block = ghost_blocks
                .iter()
                .filter(|block| {
                    block.containing_fn == assertion.containing_fn
                        && ghost_block_contains_cutoff(block.span, assertion.span)
                })
                .max_by_key(|block| block.span.source_callsite().lo());
            clear_qualified_assoc_const_definitions();
            let pa_extraction_params = ProofAssertExtractionParams {
                containing_fn: assertion.containing_fn,
                proof_assert_span: assertion.span,
                proof_assert_location: location,
                proof_assert_ghost_block: containing_ghost_block,
            };
            let (
                return_expr,
                mut substitutions,
                phase1_assumptions,
                phase1_obligations,
                has_mutating_call_effect,
                mapping_closures,
            ) = extract_body_for_proof_assert(
                tcx,
                &pa_extraction_params,
                arg_names,
                user_specs,
                ctx,
                &fn_path,
            );
            let assoc_const_substitutions = take_qualified_assoc_const_definitions();
            let call_effect_expr = return_expr.clone();
            let (return_expr, raw_call_assumptions, raw_call_obligations) =
                extract_call_effects(return_expr.as_ref());
            let return_expr = match return_expr {
                Some(PureExpr::Var(name, _)) if name == PROOF_ASSERT_STATE_MARKER_NAME => None,
                Some(expr) => Some(preserve_snapshot_substitution_value(expr)),
                None => None,
            };
            let mut plain_reborrow_aliases = Vec::new();
            if let Some(body_with_facts) = super::try_get_body_with_context(tcx, assertion.containing_fn)
            {
                let mir_body = get_mir_body(&body_with_facts);
                plain_reborrow_aliases = derive_plain_reborrow_carrier_aliases(
                    tcx,
                    mir_body,
                    arg_names,
                    // fact-source: reborrow_carrier_rename
                    &mut substitutions,
                );
                // fact-source: snapshot_deref_aliases
                derive_projected_snapshot_deref_aliases(tcx, mir_body, &mut substitutions);
            }
            let raw_phase1_obligations: Vec<PureExpr> = phase1_obligations
                .into_iter()
                .map(collapse_idempotent_views)
                .collect();
            // Entry memory (a parameter's pointee, a capture) a write may
            // have changed before the assertion (D-185):
            // its `*name` substitution is its CURRENT value, which neither
            // resolves into another binding (each was read at its own
            // program point, an entry read before the write as `Deref(Var
            // name)`) nor becomes a fact `*name == v` (the entry pointee and
            // the current one share the symbol `name_current`, so the fact
            // makes every `#[requires]` about the entry pointee a fact about
            // the written value). The assertion still reads it through the
            // substitution. The body extraction states the same store as a
            // write fact `*name == v` beside the call effects; it goes too.
            let (written_memory, memory_written_anywhere): (HashSet<String>, HashSet<String>) =
                super::try_get_body_with_context(tcx, assertion.containing_fn)
                    .map(|body_with_facts| {
                        let body = get_mir_body(&body_with_facts);
                        (
                            crate::mir_analysis::deref_store_staleness::entry_memory_names_written_before(
                                tcx, body, location,
                            ),
                            crate::mir_analysis::deref_store_staleness::names_read_through_written_memory(
                                tcx, body, location,
                            )
                            .into_iter()
                            .filter(|(_, state)| {
                                *state
                                    == crate::mir_analysis::deref_store_staleness::CurrentState::Untracked
                            })
                            .map(|(name, _)| name)
                            .collect(),
                        )
                    })
                    .unwrap_or_default();
            // The body extraction's effect facts (a store's write fact `*r ==
            // v`, a callee's postcondition) each speak of memory as it was at
            // their own program point, under a path guard (`c ==> *x == 5`),
            // and the snapshot substitution below rewrites `*name` in them to
            // its value at the assertion: `*x = 0; if c { *x = 5; }` left `c ==>
            // *x == 0` and `c ==> *x == 5` beside each other, which together
            // say `!c` (D-186). Such a fact is no fact at the assertion: a
            // write fact about entry memory under any path guard
            // (`written_memory`), and any fact reading memory no ONE store
            // defines at the assertion (`memory_written_anywhere`: two stores
            // join, a back edge carries one, an alias or a call writes it).
            // A local borrow one store defines keeps its facts: D-171's legacy
            // write fact is what makes the doubled post-write value of `*b +=
            // 1` contradictory (deref_write_through_local_borrow_read_as_applied_twice).
            let raw_call_assumptions: Vec<PureExpr> = raw_call_assumptions
                .into_iter()
                .filter(|fact| {
                    !reads_written_memory_at_another_state(
                        fact,
                        &written_memory,
                        &memory_written_anywhere,
                    )
                })
                .map(collapse_idempotent_views)
                .collect();
            let raw_phase1_assumptions: Vec<PureExpr> = phase1_assumptions
                .into_iter()
                .filter(|fact| {
                    !reads_written_memory_at_another_state(
                        fact,
                        &written_memory,
                        &memory_written_anywhere,
                    )
                })
                .map(collapse_idempotent_views)
                .collect();
            let raw_call_obligations: Vec<PureExpr> = raw_call_obligations
                .into_iter()
                .map(collapse_idempotent_views)
                .collect();
            let wrapper_aliases = collect_scalar_wrapper_aliases(&raw_call_assumptions);
            if !substitutions.is_empty() {
                let projected_write_repair_facts = projected_write_substitution_repair_facts(
                    tcx,
                    assertion,
                    ghost_blocks,
                    user_specs,
                    ctx,
                    &raw_call_assumptions,
                    &raw_phase1_assumptions,
                );
                if !projected_write_repair_facts.is_empty() {
                    // fact-source: projected_write_overrides, ghost_closure_projected_writes, body_effect_facts, call_postconditions
                    apply_projected_writes_to_substitutions(
                        &mut substitutions,
                        &projected_write_repair_facts,
                    );
                }
            }
            if !wrapper_aliases.is_empty() {
                // fact-source: wrapper_alias_substitutions
                derive_snapshot_deref_alias_substitutions(&mut substitutions, &wrapper_aliases);
            }
            // A re-bound by-value parameter's own name inside every value the
            // walks recorded is its ENTRY value; read by the entry symbol it
            // is no longer resolved into, or substituted by, the parameter's
            // binding at the assertion (D-241).
            let entry_versions =
                param_entry_versions(tcx, assertion, location, &substitutions);
            let (
                raw_call_assumptions,
                raw_phase1_assumptions,
                raw_call_obligations,
                raw_phase1_obligations,
                wrapper_aliases,
                return_expr,
            ) = if entry_versions.renamed.is_empty() {
                (
                    raw_call_assumptions,
                    raw_phase1_assumptions,
                    raw_call_obligations,
                    raw_phase1_obligations,
                    wrapper_aliases,
                    return_expr,
                )
            } else {
                // fact-source: current_state_rewrite
                for value in substitutions.values_mut() {
                    *value = entry_versions.to_entry_values(value);
                }
                let to_entry = |facts: Vec<PureExpr>| -> Vec<PureExpr> {
                    facts
                        .iter()
                        .map(|fact| entry_versions.to_entry_values(fact))
                        .collect()
                };
                (
                    to_entry(raw_call_assumptions),
                    to_entry(raw_phase1_assumptions),
                    to_entry(raw_call_obligations),
                    to_entry(raw_phase1_obligations),
                    wrapper_aliases
                        .into_iter()
                        .map(|(wrapper, scalar)| (wrapper, entry_versions.to_entry_values(&scalar)))
                        .collect::<HashMap<_, _>>(),
                    return_expr.map(|expr| entry_versions.to_entry_values(&expr)),
                )
            };
            if !substitutions.is_empty() {
                // fact-source: current_state_rewrite
                resolve_internal_references_at_current_state(&mut substitutions, &written_memory);
                for expr in substitutions.values_mut() {
                    *expr = preserve_snapshot_substitution_value(expr.clone());
                }
            }
            // Rebind ghost locals mutated by whole-value deref writes (`*g =
            // value`) inside preceding ghost blocks. MIR erases these into a
            // `deref_mut` write chain, so the local-rebind tracking leaves `g`
            // pinned to its initial value; overriding the substitution here
            // supersedes that stale value with the written one. (ghost/typing)
            for (name, rhs) in
                whole_value_ghost_deref_write_substitutions(tcx, assertion, ghost_blocks, location)
            {
                // fact-source: ghost_deref_write_overrides
                substitutions.insert(name, rhs);
            }
            let mut assumption_substitution_facts: Vec<PureExpr> = substitution_assumptions(
                &without_current_pointee_keys(&substitutions, &written_memory),
            )
            .into_iter()
            .map(preserve_snapshot_fact_value)
            .map(collapse_idempotent_views)
            .collect();
            // fact-source: stale_alias_withdrawal
            filter_mutated_final_alias_facts(&mut assumption_substitution_facts);
            // When a `snapshot!(*x)` froze `*x`'s CURRENT value (a substitution
            // value `Deref(Var(x))` = `x_current`), the POST-call deref read
            // substitution (`*x -> call_N`) emits `Deref(Var(x)) == call_N` =
            // `x_current == call_N`. That equates the frozen pre-call current
            // (precondition-pinned) with the post-call value, poisoning the
            // snapshot. The post-call `*x` is still resolvable via the `*x`
            // substitution itself; only this conflating equality must be
            // dropped. (#682)
            // fact-source: stale_alias_withdrawal
            drop_frozen_current_post_call_equalities(
                &mut assumption_substitution_facts,
                &substitutions,
            );
            // `*<snapshot>` of a value snapshot resolves to the frozen scalar
            // via the `*<snapshot>` substitution (used to rewrite the assertion).
            // Emitting it as an equality fact, however, builds the sort-invalid
            // `Deref(Var(<snapshot>, Int))` (a deref of a scalar). Such ill-formed
            // facts make the encoder abort the whole solve. REPAIR rather than
            // drop: a `Snapshot<T>` / frozen scalar derefs to itself identically,
            // so `Deref(Var(x, Int))` IS `Var(x, Int)`. Rewriting the subterm
            // fixes the sort while PRESERVING the fact (and its solver atom);
            // dropping the whole fact instead starved the mut-borrow proof_assert
            // solve of assumptions (0 atoms asserted → unknown). (#682)
            for fact in &mut assumption_substitution_facts {
                *fact = repair_scalar_var_deref(fact.clone());
            }
            // fact-source: substitution_facts
            let mut substitution_facts = assumption_substitution_facts.clone();
            // fact-source: stale_alias_withdrawal
            filter_non_alias_final_update_facts(&mut substitution_facts);
            let mut snapshot_fact_substitutions = substitutions.clone();
            for (wrapper, scalar) in &wrapper_aliases {
                snapshot_fact_substitutions
                    .entry(wrapper.clone())
                    .or_insert_with(|| scalar.clone());
            }
            let mut phase1_assumptions =
                substitute_snapshot_facts(&raw_phase1_assumptions, &snapshot_fact_substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .collect::<Vec<_>>();
            if !plain_reborrow_aliases.is_empty() {
                phase1_assumptions
                    .retain(|fact| !is_plain_reborrow_parent_alias(fact, &plain_reborrow_aliases));
                // fact-source: reborrow_parent_finals
                extend_final_plain_reborrow_parent_aliases(
                    &mut phase1_assumptions,
                    &plain_reborrow_aliases,
                );
            }
            // A callee's postcondition references the dereferenced argument
            // state AT THE CALL (the pre-call value the callee observed), e.g.
            // `add_some`'s `^a > *a` carries `*a` = the value passed in. The
            // proof-assert substitution map holds `*a` advanced to the POST-call
            // read (a fresh call-result symbol). Applying that post-call deref
            // rewrite to the callee's pre-call `*a` collapses `^a > *a` and the
            // result link `result == a` into the contradictory `^a > ^a`,
            // corrupting an otherwise consistent context. Keep the callee's
            // pre-call deref carriers intact by dropping post-call `*x` deref
            // remappings from the substitution used for call assumptions. (#682)
            let call_assumption_substitutions =
                drop_post_call_deref_remappings(&snapshot_fact_substitutions);
            let call_assumptions =
                substitute_snapshot_facts(&raw_call_assumptions, &call_assumption_substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .collect::<Vec<_>>();
            // fact-source: stale_alias_withdrawal
            filter_mutated_final_alias_facts_with_evidence(
                &mut substitution_facts,
                &call_assumptions,
            );
            // The callee's PRECONDITION obligation references the dereferenced
            // argument AT THE CALL — the PRE-call value the caller passes in.
            // For `add_some`'s `#[requires((*a)@ <= u64::MAX/2)]`, that `*a` is
            // `Deref(Var("a"))` = `a_current` (pinned to 3 by foo's
            // precondition). Two substitution effects would corrupt it:
            //   - the full map remaps `*a -> call_N` (a fresh, otherwise-
            //     UNCONSTRAINED post-call read symbol) → `call_N <= K` SAT, and
            //   - the self-advancement `a -> Final(a)` rewrites the surviving
            //     `Deref(Var("a"))` to `Deref(Final(Var("a")))` = the POST-call
            //     pointee `a_final_current` (also unconstrained).
            // Both move the obligation off the actual argument value. Use a
            // substitution that drops post-call `*x` remappings AND the
            // self-advancement of any mut-ref root that the obligation
            // dereferences, so `*a` stays the pre-call `a_current`.
            // SOUND: this pins the obligation to the actual (more constrained)
            // pre-call value the callee observed instead of a free symbol — it
            // can only make a VALID precondition provable, never a false one.
            // (#682)
            let call_obligation_substitutions = drop_self_advancement_for_dereffed_roots(
                &call_assumption_substitutions,
                &raw_call_obligations,
            );
            let call_obligations =
                substitute_snapshot_facts(&raw_call_obligations, &call_obligation_substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .collect::<Vec<_>>();
            let phase1_obligations =
                substitute_snapshot_facts(&raw_phase1_obligations, &snapshot_fact_substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .collect::<Vec<_>>();
            let mut call_obligations = call_obligations;
            for obligation in phase1_obligations {
                if !call_obligations.contains(&obligation) {
                    call_obligations.push(obligation);
                }
            }
            let snapshot_call_facts = if let Some(body_with_facts) =
                super::try_get_body_with_context(tcx, assertion.containing_fn)
            {
                let mir_body = get_mir_body(&body_with_facts);
                synthesize_snapshot_call_facts(tcx, mir_body, &substitutions, location)
            } else {
                Vec::new()
            };
            // fact-source: substitution_facts
            let mut assumed_facts = assumption_substitution_facts;
            // fact-source: body_effect_facts
            assumed_facts.extend(phase1_assumptions);
            // fact-source: call_postconditions
            assumed_facts.extend(call_assumptions.iter().cloned());
            // fact-source: rc_call_result_facts
            assumed_facts.extend(snapshot_call_facts);
            if let Some(body_with_facts) = super::try_get_body_with_context(tcx, assertion.containing_fn)
            {
                let mir_body = get_mir_body(&body_with_facts);
                let normalize_ref_derefs =
                    normalize_immutable_ref_param_derefs(tcx, mir_body, arg_names);
                for fact in &mut assumed_facts {
                    *fact = normalize_ref_derefs(fact);
                }
            }
            // fact-source: stale_alias_withdrawal
            filter_mutated_final_alias_facts(&mut assumed_facts);

            // Extract closure-local loop continuation assumptions for proof_asserts
            // inside ghost closures. When the ghost closure contains a loop with
            // invariants, the invariants hold at loop exit and should be available
            // as preconditions for any proof_assert after the loop. (#2584)
            // fact-source: ghost_closure_loop_facts
            let mut post_loop_assumptions = extract_ghost_closure_loop_assumptions(
                tcx,
                assertion,
                containing_ghost_block,
                user_specs,
                ctx,
            );
            let exit_fact_stale_names =
                function_exit_fact_stale_names(tcx, assertion, user_specs, ctx);
            if containing_ghost_block.is_none() {
                for assumption in
                    extract_function_local_post_loop_assumptions(tcx, assertion, user_specs, ctx)
                {
                    if !post_loop_assumptions.contains(&assumption) {
                        // fact-source: post_loop_facts
                        post_loop_assumptions.push(assumption);
                    }
                }
                // In-body loop assumptions: for proof_asserts inside loop body
                // blocks, inject the (positive) loop condition and the loop's
                // user invariants. The post-loop pass above explicitly skips
                // these locations.
                for assumption in
                    extract_function_local_in_body_assumptions(tcx, assertion, user_specs, ctx)
                {
                    if !post_loop_assumptions.contains(&assumption) {
                        // fact-source: in_body_loop_facts
                        post_loop_assumptions.push(assumption);
                    }
                }
            }

            Ok(AssertionSnapshot {
                assertion: assertion.clone(),
                call_effect_expr,
                return_expr,
                substitutions,
                assumed_facts,
                substitution_facts,
                call_assumptions,
                call_obligations,
                has_mutating_call_effect,
                mapping_closures,
                assoc_const_substitutions,
                post_loop_assumptions,
                exit_fact_stale_names,
                entry_versions,
            })
        })
        .collect()
}

/// The symbol a by-value parameter's ENTRY value is read by once the body
/// re-binds the parameter (D-241).
pub(super) fn param_entry_value_name(name: &str) -> String {
    format!("{name}{}", crate::mir_analysis::PARAM_ENTRY_VALUE_SUFFIX)
}

/// The by-value parameters whose ENTRY value this assertion reads by a symbol
/// of its own (D-241).
///
/// The walks to the assertion start each parameter at `Var(name)`, its entry
/// value, and every value they record reads the parameter as it was at that
/// program point: a copy taken before a re-bind (`let y = x; x = 5;`) is
/// `y -> x`, a write that reads the old value (`x = x + 1`) is `x -> x + 1`,
/// and a callee's postcondition is stated over the argument as it was passed
/// (`$call == x + 1`). The key `x` of the substitution map, though, is the
/// binding at the assertion, and the internal-reference resolution, the
/// substitution facts (`y == x`, `x == 5`) and the snapshot substitution of
/// the body's effect facts read the `x` inside another value as that
/// binding: the copy followed the write
/// (proof_assert_param_copy_reads_later_rebind.rs,
/// proof_assert_param_copy_reads_later_write.rs), `x == x + 1` made the
/// premises contradictory, and a callee's fact was applied twice.
#[derive(Debug, Clone, Default)]
pub(super) struct ParamEntryVersions {
    /// The parameters whose own name inside a recorded value is renamed to
    /// the entry symbol: a by-value parameter of a function item the
    /// substitution re-binds (its binding at the assertion is not its own
    /// name, view or prophecy) whose own name inside every recorded value is
    /// its entry value and nothing else
    /// ([`crate::mir_analysis::params_with_renamable_entry`]: no loop may run
    /// before the assertion, every write is a store the walks record, no
    /// borrow names it as a reference identity, no other binding shares its
    /// name). A ghost block's own walk and its closures' effects read a
    /// parameter's name as its value at the block, which
    /// `augment_proof_assert_ghost_block_substitutions` and
    /// `extract_body_for_proof_assert` replace by the main walk's binding
    /// before they join the map.
    pub(super) renamed: HashSet<String>,
    /// Those of [`Self::renamed`] of plain data: their `#[requires]` facts
    /// and type invariant are stated of the entry symbol, which every
    /// recorded value reads, instead of being withdrawn. For the others (a
    /// type parameter's type) the entry symbol is constrained by nothing and
    /// the entry facts are withdrawn (D-140, D-241).
    pub(super) versioned: HashSet<String>,
    /// The parameters of plain data whose every write before the assertion
    /// the walks record: [`Self::versioned`], and those whose binding at the
    /// assertion is still their own name (`x = x;`, or a write the path to
    /// the assertion does not take), whose value there IS the entry value. No
    /// withdrawal is owed for either.
    pub(super) exact: HashSet<String>,
}

impl ParamEntryVersions {
    /// `expr` with each renamed parameter's own name read as its entry
    /// symbol, keeping each occurrence's sort.
    pub(super) fn to_entry_values(&self, expr: &PureExpr) -> PureExpr {
        rename_to_entry_values(expr, &self.renamed)
    }
}

pub(super) fn rename_to_entry_values(expr: &PureExpr, names: &HashSet<String>) -> PureExpr {
    let free = expr.free_vars();
    let mut renamed = expr.clone();
    for name in names {
        if free.contains(name) {
            renamed = trust_wp_core::formula::rename_free_var(
                &renamed,
                name,
                &param_entry_value_name(name),
                &trust_wp_core::formula::CaptureAvoidingSubstOptions::default(),
            );
        }
    }
    renamed
}

/// The [`ParamEntryVersions`] of `assertion`, from the walk's substitution
/// map at it.
///
/// The candidates are exactly the parameters the walk to the assertion
/// re-binds to the functional update of their value on a field store
/// ([`crate::mir_analysis::params_with_renamable_entry`] at the same
/// location): a candidate the lane did not rename would have a copy of its
/// entry value read at the stored value.
fn param_entry_versions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    location: Location,
    substitutions: &NameSubstitutions,
) -> ParamEntryVersions {
    let mut versions = ParamEntryVersions::default();
    let def_id = assertion.containing_fn.to_def_id();
    if tcx.is_closure_like(def_id) {
        return versions;
    }
    let Some(body_with_facts) = super::try_get_body_with_context(tcx, assertion.containing_fn)
    else {
        return versions;
    };
    let body = get_mir_body(&body_with_facts);
    let renamable = crate::mir_analysis::params_with_renamable_entry(tcx, body, location);
    if renamable.is_empty() {
        return versions;
    }
    let arg_names = super::parsing::get_arg_names_from_def_id(tcx, def_id).unwrap_or_default();
    for (index, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(1 + index);
        let Some(&plain) = renamable.get(&local) else {
            continue;
        };
        // No key is the identity binding: the map leaves out a name bound to
        // itself.
        let binding = substitutions.get(name);
        let rebound = binding
            .is_some_and(|value| !super::proof_assert_verify::names_its_own_binding(name, value));
        if !rebound {
            if plain
                && binding.is_none_or(|value| matches!(value, PureExpr::Var(var, _) if var == name))
            {
                versions.exact.insert(name.clone());
            }
            continue;
        }
        versions.renamed.insert(name.clone());
        if plain {
            versions.versioned.insert(name.clone());
            versions.exact.insert(name.clone());
        }
    }
    versions
}

fn projected_write_substitution_repair_facts(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_blocks: &[GhostBlock],
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
    raw_call_assumptions: &[PureExpr],
    raw_phase1_assumptions: &[PureExpr],
) -> Vec<PureExpr> {
    let mut facts = Vec::new();
    facts.extend(raw_call_assumptions.iter().cloned());
    facts.extend(
        raw_phase1_assumptions
            .iter()
            .filter(|fact| is_projected_write_repair_assumption(fact))
            .cloned(),
    );
    facts.extend(prior_ghost_projected_write_repair_facts(
        tcx,
        assertion,
        ghost_blocks,
        user_specs,
        ctx,
    ));
    facts.extend(prior_ghost_source_projected_write_repair_facts(
        tcx,
        assertion,
        ghost_blocks,
    ));

    let mut seen = HashSet::new();
    facts.retain(|fact| seen.insert(format!("{fact}")));
    facts
}

fn prior_ghost_projected_write_repair_facts(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_blocks: &[GhostBlock],
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    if ghost_blocks.is_empty() {
        return Vec::new();
    }
    let Some(body_with_facts) = super::try_get_body_with_context(tcx, assertion.containing_fn)
    else {
        return Vec::new();
    };
    let mir_body = get_mir_body(&body_with_facts);
    let Some(location) = assertion.location else {
        return Vec::new();
    };
    let scope = crate::mir_analysis::fact_scope::FactScope::new(mir_body);
    let mut facts = Vec::new();
    for block in ghost_blocks {
        if block.containing_fn != assertion.containing_fn
            || !ghost_block_precedes_cutoff(block.span, assertion.span)
        {
            continue;
        }
        // The block's writes hold at the assertion only where its end
        // dominates it, and never over a name written on a path between
        // (D-190).
        let Some(stale) = scope.stale_names_after_region(block.span, location) else {
            continue;
        };
        let closure_def_ids = find_ghost_closure_def_ids_in_mir(mir_body, block.span);
        for closure_def_id in closure_def_ids {
            let capture_names = closure_capture_names(tcx, closure_def_id);
            let effects = extract_ghost_closure_effects(
                tcx,
                closure_def_id,
                None,
                user_specs,
                ctx.trait_specs,
                ctx.extern_specs,
            );
            facts.extend(
                effects
                    .assumptions
                    .into_iter()
                    .map(|fact| rewrite_ghost_closure_capture_vars(&fact, &capture_names))
                    .map(collapse_idempotent_views)
                    .filter(is_projected_write_repair_assumption)
                    .filter(|fact| !fact.free_vars().iter().any(|name| stale.contains(name))),
            );
        }
    }
    facts
}

/// Substitution overrides for whole-value ghost dereference writes
/// (`*g = value`) inside ghost blocks preceding the assertion.
///
/// A ghost deref-mutation lowers to a `DerefMut::deref_mut` write chain in MIR
/// (`_t = <Ghost<T> as DerefMut>::deref_mut(&mut g); (*_t) = value`), so the
/// local-rebind tracking that records `g`'s post-block value never observes it —
/// `g`'s substitution stays pinned to its *initial* ghost value. Recover the
/// mutation from the HIR source-assignment collector and rebind `g`'s
/// substitution: to the written value where the LAST such write (in source
/// order) holds at the assertion ([`GhostWritePlacement::holds`], D-190),
/// and otherwise to a value nothing constrains. A write in a branch the
/// assertion does not need to pass, or one a later write on some path
/// replaces, would otherwise make its value a fact
/// (v24_ghost_write_value_read_where_the_write_does_not_reach.rs). Plain
/// rebinds and tuple-field writes are excluded: they are handled by MIR
/// tracking and the projected-write repair path respectively.
fn whole_value_ghost_deref_write_substitutions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_blocks: &[GhostBlock],
    location: Location,
) -> Vec<(String, PureExpr)> {
    let mut last_writes: HashMap<String, Option<PureExpr>> = HashMap::new();
    let mut assignments = collect_ghost_source_assignments(tcx, ghost_blocks);
    assignments.sort_by_key(|assignment| assignment.assignment_span.source_callsite().lo());
    let retained = super::try_get_body_with_context(tcx, assertion.containing_fn);
    let placement = GhostWritePlacement::new(retained.as_deref().map(get_mir_body), location);
    for assignment in assignments {
        if assignment.containing_fn != assertion.containing_fn
            || !ghost_block_precedes_cutoff(assignment.ghost_block_span, assertion.span)
        {
            continue;
        }
        if !assignment.is_deref || !assignment.lhs_tuple_fields.is_empty() {
            continue;
        }
        // A write whose binding among several of its name is not known may
        // have changed any of them (D-237).
        if assignment.lhs_binding_unresolved {
            for name in bindings_of_source_name(tcx, assertion, &assignment.lhs_name) {
                last_writes.insert(name, None);
            }
            continue;
        }
        // Source order is preserved by the sort above; a later write to the
        // same target supersedes an earlier one, even one whose value is not
        // known.
        let value = assignment
            .rhs_expr
            .clone()
            .filter(|rhs| placement.holds(&assignment, rhs));
        last_writes.insert(assignment.lhs_name, value);
    }
    last_writes
        .into_iter()
        .map(|(name, value)| {
            let value = value.unwrap_or_else(|| unplaced_ghost_write_value(&name, None));
            (name, value)
        })
        .collect()
}

fn prior_ghost_source_projected_write_repair_facts(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_blocks: &[GhostBlock],
) -> Vec<PureExpr> {
    let mut projected_writes: HashMap<(String, usize), PureExpr> = HashMap::new();
    let mut assignments = collect_ghost_source_assignments(tcx, ghost_blocks);
    assignments.sort_by_key(|assignment| assignment.assignment_span.source_callsite().lo());
    let retained = super::try_get_body_with_context(tcx, assertion.containing_fn);
    let placement = assertion
        .location
        .map(|location| GhostWritePlacement::new(retained.as_deref().map(get_mir_body), location));
    for assignment in assignments {
        if assignment.containing_fn != assertion.containing_fn
            || !ghost_block_precedes_cutoff(assignment.ghost_block_span, assertion.span)
        {
            continue;
        }
        if assignment.lhs_binding_unresolved {
            // Any binding of the name may have been written (D-237).
            let names = bindings_of_source_name(tcx, assertion, &assignment.lhs_name);
            projected_writes.retain(|(name, _), _| !names.contains(name));
            if let Some(&field_idx) = assignment.lhs_tuple_fields.first() {
                for name in names {
                    projected_writes.insert(
                        (name.clone(), field_idx),
                        unplaced_ghost_write_value(&name, Some(field_idx)),
                    );
                }
            }
            continue;
        }
        if assignment.lhs_tuple_fields.is_empty() {
            projected_writes.retain(|(name, _), _| name != &assignment.lhs_name);
            continue;
        }
        let field_idx = assignment.lhs_tuple_fields[0];
        // The field's value at the assertion is the last write's only where
        // that write holds there (D-190); a write to a field of the field, or
        // one whose value is not known, leaves it unconstrained.
        let value = match (assignment.lhs_tuple_fields.as_slice(), &assignment.rhs_expr) {
            ([_], Some(rhs))
                if placement
                    .as_ref()
                    .is_some_and(|placement| placement.holds(&assignment, rhs)) =>
            {
                rhs.clone()
            }
            _ => unplaced_ghost_write_value(&assignment.lhs_name, Some(field_idx)),
        };
        projected_writes.insert((assignment.lhs_name, field_idx), value);
    }

    projected_writes
        .into_iter()
        .map(|((name, field_idx), rhs)| {
            PureExpr::BinOp(
                Arc::new(PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(field_idx),
                    args: vec![PureExpr::Var(name, None)],
                }),
                BinOp::Eq,
                Arc::new(rhs),
            )
        })
        .collect()
}

/// Every debug name the assertion's body gives a binding of `source_name`
/// (each binding of a shadowed name is named apart, D-237).
fn bindings_of_source_name(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    source_name: &str,
) -> Vec<String> {
    let mut names = vec![source_name.to_string()];
    if let Some(retained) = super::try_get_body_with_context(tcx, assertion.containing_fn) {
        for debug in &retained.body.var_debug_info {
            let name = debug.name.as_str();
            if crate::mir_analysis::binding_identity::source_name_of(name) == source_name
                && !names.iter().any(|known| known == name)
            {
                names.push(name.to_string());
            }
        }
    }
    names
}

/// A value nothing constrains, standing for what a ghost write left in
/// `name` (or its field `field`) where the write is not known to hold.
fn unplaced_ghost_write_value(name: &str, field: Option<usize>) -> PureExpr {
    let suffix = field.map_or_else(String::new, |field| format!("${field}"));
    PureExpr::Var(format!("{name}{suffix}$unplaced_ghost_write"), None)
}

/// Whether a ghost source write's value holds at the assertion (D-190).
struct GhostWritePlacement<'a, 'tcx> {
    body: Option<&'a Body<'tcx>>,
    scope: Option<crate::mir_analysis::fact_scope::FactScope<'a, 'tcx>>,
    location: Location,
}

impl<'a, 'tcx> GhostWritePlacement<'a, 'tcx> {
    fn new(body: Option<&'a Body<'tcx>>, location: Location) -> Self {
        Self {
            body,
            scope: body.map(crate::mir_analysis::fact_scope::FactScope::new),
            location,
        }
    }

    /// The write holds at the assertion when the one MIR store it lowers to
    /// ([`ghost_source_write_store`]) dominates the assertion and neither the
    /// written name nor a name its value reads is written on a path from just
    /// after the store to the assertion
    /// ([`crate::mir_analysis::fact_scope::FactScope::stale_names`]).
    fn holds(
        &self,
        assignment: &crate::ghost::source_assignments::GhostSourceAssignment,
        rhs: &PureExpr,
    ) -> bool {
        let (Some(body), Some(scope)) = (self.body, self.scope.as_ref()) else {
            return false;
        };
        let Some(store) = ghost_source_write_store(body, assignment.assignment_span) else {
            return false;
        };
        let after = Location {
            block: store.block,
            statement_index: store.statement_index + 1,
        };
        let Some(stale) = scope.stale_names(after, self.location) else {
            return false;
        };
        !stale.contains(&assignment.lhs_name)
            && !rhs.free_vars().iter().any(|name| stale.contains(name))
    }
}

/// The one MIR store through a projection (`(*_t) = v`, `(*_t).0 = v`) whose
/// span lies inside a ghost source write's span, or `None` when there is not
/// exactly one.
fn ghost_source_write_store(body: &Body<'_>, write_span: rustc_span::Span) -> Option<Location> {
    let mut found = None;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign((place, _)) = &statement.kind else {
                continue;
            };
            if place.projection.is_empty() || !write_span.contains(statement.source_info.span) {
                continue;
            }
            if found
                .replace(Location {
                    block,
                    statement_index,
                })
                .is_some()
            {
                return None;
            }
        }
    }
    found
}

/// Facts about the result of an `Rc`/`Arc` `clone` or `ptr_eq` call (and
/// `FMap::new`) the assertion at `location` reads.
///
/// A clone's `result == receiver` and a `ptr_eq`'s `result ==> a == b` (one
/// direction only: an `Rc` is read as its value, with no allocation identity,
/// so equal values are no evidence of one allocation; D-190) hold
/// just after the call, of the operands' values THERE, while the operands are
/// read here by name at the assertion. So each is stated only when the call's
/// return point dominates the assertion and neither its destination, nor an
/// operand, nor the place an operand borrows is written on a path between
/// (D-190, [`crate::mir_analysis::fact_scope::FactScope`]):
/// `let r2 = r.clone(); r = Rc::new(2);` made `r == r2` a fact
/// (v24_call_result_fact_reads_its_operand_at_the_assertion.rs). The
/// `fmap_new` fact holds of every value the destination ever takes, so it
/// needs no point.
fn synthesize_snapshot_call_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    substitutions: &NameSubstitutions,
    location: Location,
) -> Vec<PureExpr> {
    let scope = crate::mir_analysis::fact_scope::FactScope::new(body);
    let predecessors = body.basic_blocks.predecessors();
    let mut facts = Vec::new();
    for (bb, block) in body.basic_blocks.iter_enumerated() {
        let terminator = block.terminator();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        let Some(def_id) = call_func_def_id(func) else {
            continue;
        };
        let result = call_result_var(tcx, body, destination.local);
        let path = tcx.def_path_str(def_id);
        if is_fmap_new_path(&path) {
            push_unique_fact(
                &mut facts,
                eq_expr(
                    result.clone(),
                    PureExpr::LogicFnCall {
                        name: "fmap_new".to_string(),
                        args: vec![],
                    },
                ),
            );
        }
        if !substitution_values_contain_var(substitutions, &result) {
            continue;
        }
        let result_is_rc_arc = expr_has_rc_arc_sort(&result);
        let is_clone =
            is_rc_arc_clone_path(&path) || (path.ends_with("::clone") && result_is_rc_arc);
        let is_ptr_eq = is_rc_arc_ptr_eq_path(&path) && args.len() >= 2;
        if !is_clone && !is_ptr_eq {
            continue;
        }
        // The point just after the call returns: the start of its return
        // block, when the call is that block's only way in.
        let Some(returned) = target.filter(|target| predecessors[*target].as_slice() == [bb])
        else {
            continue;
        };
        let established = Location {
            block: returned,
            statement_index: 0,
        };
        let (Some(written), Some(stale)) = (
            scope.written_since(established, location),
            scope.stale_names(established, location),
        ) else {
            continue;
        };
        let operands_unwritten = args.iter().all(|arg| {
            operand_place_locals(body, bb, &arg.node)
                .iter()
                .all(|local| !written.contains(local))
        });
        if written.contains(&destination.local) || !operands_unwritten {
            continue;
        }
        let fact = if is_clone {
            let Some(receiver) = args
                .first()
                .and_then(|arg| operand_source_expr(tcx, body, bb, &arg.node, substitutions))
            else {
                continue;
            };
            eq_expr(result, receiver)
        } else {
            let Some(left) = operand_source_expr(tcx, body, bb, &args[0].node, substitutions)
            else {
                continue;
            };
            let Some(right) = operand_source_expr(tcx, body, bb, &args[1].node, substitutions)
            else {
                continue;
            };
            PureExpr::BinOp(
                Arc::new(result),
                BinOp::Implies,
                Arc::new(eq_expr(left, right)),
            )
        };
        if fact.free_vars().iter().any(|name| stale.contains(name)) {
            continue;
        }
        push_unique_fact(&mut facts, fact);
    }
    facts
}

/// The locals [`operand_source_expr`] reads an operand through: the operand's
/// own local and, for a borrow made in the call's block, the borrowed place's.
fn operand_place_locals<'tcx>(
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    operand: &Operand<'tcx>,
) -> Vec<Local> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return Vec::new();
    };
    let mut locals = vec![place.local];
    let mut current = *place;
    while let Some(borrowed) = borrowed_place_of(body, bb, &current) {
        if locals.contains(&borrowed.local) {
            break;
        }
        locals.push(borrowed.local);
        current = borrowed;
    }
    locals
}

/// The place a borrow made in `bb` refers to, read through `place`: `_t`
/// itself where `_t = &p` (the reference stands for `p`), or `*_t` where
/// `_t = &p` (the reborrow `&*_t` a by-reference argument is passed as).
fn borrowed_place_of<'tcx>(
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    place: &Place<'tcx>,
) -> Option<Place<'tcx>> {
    match place.projection.as_slice() {
        [] | [ProjectionElem::Deref] => local_ref_source_place(body, bb, place.local),
        _ => None,
    }
}

fn call_func_def_id(func: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(deref!(constant)) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

fn is_rc_arc_clone_path(path: &str) -> bool {
    is_rc_arc_path(path) && path.ends_with("::clone")
}

fn is_rc_arc_ptr_eq_path(path: &str) -> bool {
    is_rc_arc_path(path) && path.ends_with("::ptr_eq")
}

fn is_fmap_new_path(path: &str) -> bool {
    path.contains("::FMap") && path.ends_with("::new")
}

fn is_rc_arc_path(path: &str) -> bool {
    path.contains("rc::Rc") || path.contains("sync::Arc")
}

fn expr_has_rc_arc_sort(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(_, Some(sort)) if sort_is_rc_arc(sort))
}

fn sort_is_rc_arc(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::Datatype(id) | ExprSort::TypeParam(id) => {
            let name = trust_wp_core::formula::resolve_sort_name(*id);
            name.contains("rc::Rc") || name.contains("sync::Arc")
        }
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => sort_is_rc_arc(inner),
        _ => false,
    }
}

fn call_result_var<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, local: Local) -> PureExpr {
    let sort = body
        .local_decls
        .get(local)
        .and_then(|decl| crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, decl.ty));
    PureExpr::Var(format!("$call_{}", local.as_u32()), sort)
}

fn substitution_values_contain_var(substitutions: &NameSubstitutions, needle: &PureExpr) -> bool {
    substitutions.values().any(|expr| expr == needle)
}

fn operand_source_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    operand: &Operand<'tcx>,
    substitutions: &NameSubstitutions,
) -> Option<PureExpr> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    place_source_expr(tcx, body, bb, place, substitutions)
}

fn place_source_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    place: &Place<'tcx>,
    substitutions: &NameSubstitutions,
) -> Option<PureExpr> {
    if let Some(borrowed_place) = borrowed_place_of(body, bb, place) {
        return place_source_expr(tcx, body, bb, &borrowed_place, substitutions);
    }
    if !place.projection.is_empty() {
        return None;
    }
    let debug_names = debug_names_by_local(body);
    if let Some(names) = debug_names.get(&place.local) {
        for name in names {
            if let Some(expr) = substitutions.get(name) {
                return Some(expr.clone());
            }
        }
        if let Some(name) = names.first() {
            let sort = substitutions
                .name_sorts
                .get(name)
                .cloned()
                .flatten()
                .or_else(|| {
                    body.local_decls.get(place.local).and_then(|decl| {
                        crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, decl.ty)
                    })
                });
            return Some(PureExpr::Var(name.clone(), sort));
        }
    }
    let local_var = PureExpr::Var(
        format!("$call_{}", place.local.as_u32()),
        body.local_decls.get(place.local).and_then(|decl| {
            crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, decl.ty)
        }),
    );
    Some(local_var)
}

fn eq_expr(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), BinOp::Eq, Arc::new(right))
}

fn push_unique_fact(facts: &mut Vec<PureExpr>, fact: PureExpr) {
    if !facts.contains(&fact) {
        facts.push(fact);
    }
}

fn filter_mutated_final_alias_facts(facts: &mut Vec<PureExpr>) {
    filter_mutated_final_alias_facts_with_evidence(facts, &[]);
}

fn filter_mutated_final_alias_facts_with_evidence(
    facts: &mut Vec<PureExpr>,
    evidence: &[PureExpr],
) {
    let mut snapshot = facts.clone();
    snapshot.extend(evidence.iter().cloned());
    facts.retain(|fact| {
        let Some((name, depth)) = base_to_nested_final_alias(fact) else {
            return true;
        };
        !has_non_alias_final_update(&snapshot, &name, depth)
    });
}

fn filter_non_alias_final_update_facts(facts: &mut Vec<PureExpr>) {
    facts.retain(|fact| non_alias_final_update_fact_base(fact).is_none());
}

fn non_alias_final_update_fact_base(fact: &PureExpr) -> Option<String> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return None;
    };
    non_alias_final_update_side(left, right).or_else(|| non_alias_final_update_side(right, left))
}

fn non_alias_final_update_side(final_side: &PureExpr, other_side: &PureExpr) -> Option<String> {
    let (name, depth) = final_base_and_depth(final_side)?;
    if depth == 0 {
        return None;
    }
    if matches!(
        final_base_and_depth(other_side),
        Some((other_name, other_depth)) if other_name == name && other_depth < depth
    ) {
        return None;
    }
    Some(name)
}

fn base_to_nested_final_alias(fact: &PureExpr) -> Option<(String, usize)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (PureExpr::Var(name, _), rhs) => {
            let (rhs_name, depth) = final_base_and_depth(rhs)?;
            (name == &rhs_name && depth > 0).then_some((name.clone(), depth))
        }
        (lhs, PureExpr::Var(name, _)) => {
            let (lhs_name, depth) = final_base_and_depth(lhs)?;
            (name == &lhs_name && depth > 0).then_some((name.clone(), depth))
        }
        _ => None,
    }
}

fn has_non_alias_final_update(facts: &[PureExpr], name: &str, alias_depth: usize) -> bool {
    facts.iter().any(|fact| {
        // A call postcondition scoped under its own preconditions
        // (`pre ==> ^x == e`) is still evidence that `x` is updated: keeping
        // the stale `x == ^x` alias beside it would make the premises
        // contradict whenever `pre` holds (a vacuous context). Dropping the
        // alias only removes a premise.
        let fact = match fact {
            PureExpr::BinOp(_, BinOp::Implies, post) => post.as_ref(),
            other => other,
        };
        let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
            return false;
        };
        final_update_side(left, right, name, alias_depth)
            || final_update_side(right, left, name, alias_depth)
    })
}

fn final_update_side(
    final_side: &PureExpr,
    other_side: &PureExpr,
    name: &str,
    alias_depth: usize,
) -> bool {
    let Some((final_name, depth)) = final_base_and_depth(final_side) else {
        return false;
    };
    if final_name != name || depth == 0 || depth > alias_depth {
        return false;
    }
    !matches!(
        final_base_and_depth(other_side),
        Some((other_name, other_depth)) if other_name == name && other_depth < alias_depth
    )
}

fn final_base_and_depth(expr: &PureExpr) -> Option<(String, usize)> {
    match expr {
        PureExpr::Var(name, _) => Some((name.clone(), 0)),
        PureExpr::Final(inner) => {
            let (name, depth) = final_base_and_depth(inner)?;
            Some((name, depth + 1))
        }
        _ => None,
    }
}

/// Extract loop-exit assumptions for a proof_assert that appears after a
/// completed nested loop while still inside an outer loop.
///
/// The broader contracted proof_assert driver already injects function-level
/// loop-exit assumptions when a proof_assert is after all loops. That misses
/// shapes like `hashmap_list::resize`, where the proof_assert follows an inner
/// `while let` and is still inside the outer loop body. At that program point,
/// the inner loop rule gives the inner invariants plus the negated loop
/// condition, and those facts are needed to prove local assertions.
fn extract_function_local_post_loop_assumptions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    let Some(location) = assertion.location else {
        return Vec::new();
    };
    let Some(body_with_facts) = super::try_get_body_with_context(tcx, assertion.containing_fn)
    else {
        return Vec::new();
    };
    let mir_body = get_mir_body(&body_with_facts);
    let loop_analysis = detect_loops(mir_body);
    if loop_analysis.loops.is_empty() {
        return Vec::new();
    }

    let (_, _, per_loop_invariant_texts, _, all_loop_spans) =
        collect_loop_contract_attrs(tcx, assertion.containing_fn);
    if per_loop_invariant_texts.is_empty() || all_loop_spans.is_empty() {
        return Vec::new();
    }

    let per_loop_invariants = parse_per_loop_invariants(&per_loop_invariant_texts);
    if per_loop_invariants.is_empty() {
        return Vec::new();
    }

    let arg_names = resolve_arg_names_or_warn(tcx, assertion.containing_fn.to_def_id(), None);
    let call_spec_ctx = CallSpecContext {
        tcx,
        user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
    };

    let scope = crate::mir_analysis::fact_scope::FactScope::new(mir_body);
    let mut assumptions = Vec::new();
    for loop_info in &loop_analysis.loops {
        if loop_info.body_blocks.contains(&location.block) {
            continue;
        }

        let header_byte_pos = mir_body.basic_blocks[loop_info.header]
            .terminator()
            .source_info
            .span
            .lo()
            .0;
        let Some((loop_start, loop_end, invariants)) =
            find_matching_loop_invariants(&per_loop_invariants, &all_loop_spans, header_byte_pos)
        else {
            continue;
        };
        // An invariant names the bindings visible at its loop (D-237).
        let invariants = crate::mir_analysis::binding_identity::resolve_loop_clauses(
            mir_body,
            loop_info.header,
            invariants,
        );
        if !loop_precedes_nested_proof_assert(assertion.span, loop_start, loop_end, &all_loop_spans)
        {
            continue;
        }

        let loop_body = extract_loop_body(
            mir_body,
            &arg_names,
            loop_info,
            Some(&loop_analysis.loops),
            Some(&call_spec_ctx),
        );
        // The invariants and the negated condition hold at the assertion
        // only when every path took the exit arm, and only over names no
        // write on any path from the loop's head makes stale (D-189).
        let Some(stale) = exit_fact_stale_names(
            &scope,
            mir_body,
            &loop_analysis.loops,
            loop_info,
            &loop_body,
            location,
        ) else {
            continue;
        };
        let negated = loop_body.condition.map(|condition| {
            PureExpr::UnOp(
                trust_wp_core::formula::UnOp::Not,
                Arc::new(collapse_idempotent_views(condition)),
            )
        });
        for fact in invariants.into_iter().chain(negated) {
            if fact.free_vars().iter().any(|name| stale.contains(name)) {
                continue;
            }
            if !assumptions.contains(&fact) {
                assumptions.push(fact);
            }
        }
    }

    assumptions
}

/// Extract in-body loop assumptions for a proof_assert whose MIR location is
/// inside one or more loop body blocks.
///
/// At the entry of a loop body, the loop invariants hold AND the (positive)
/// loop condition holds. The existing `extract_function_local_post_loop_assumptions`
/// pass explicitly skips loops whose `body_blocks` contain the assertion's
/// location and is responsible for the post-loop (negated condition) case.
///
/// This complement pass handles in-body asserts, e.g.:
/// ```text
/// #[invariant(i <= length)]
/// while i < length {
///     proof_assert!(i@ < length@); // needs loop condition assumption
///     ...
/// }
/// ```
///
/// For nested loops, each enclosing loop contributes both its user-declared
/// invariants and its positive loop condition. The conditions are also emitted
/// in an integer-view form (`View(lhs) cmp View(rhs)`) when both sides are
/// scalar integer expressions, so that user assertions written with `@` syntax
/// can match the structural fact directly.
fn extract_function_local_in_body_assumptions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    let Some(location) = assertion.location else {
        return Vec::new();
    };
    let Some(body_with_facts) = super::try_get_body_with_context(tcx, assertion.containing_fn)
    else {
        return Vec::new();
    };
    let mir_body = get_mir_body(&body_with_facts);
    let loop_analysis = detect_loops(mir_body);
    if loop_analysis.loops.is_empty() {
        return Vec::new();
    }

    let (_, _, per_loop_invariant_texts, _, all_loop_spans) =
        collect_loop_contract_attrs(tcx, assertion.containing_fn);
    if all_loop_spans.is_empty() {
        return Vec::new();
    }

    let per_loop_invariants = parse_per_loop_invariants(&per_loop_invariant_texts);

    let arg_names = resolve_arg_names_or_warn(tcx, assertion.containing_fn.to_def_id(), None);
    let call_spec_ctx = CallSpecContext {
        tcx,
        user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
    };

    // Find the TIGHTEST enclosing loop: the loop whose body_blocks contain
    // the proof_assert's MIR block AND which has no other enclosing loop
    // also containing the block with a smaller body footprint.
    let enclosing_loops: Vec<&_> = loop_analysis
        .loops
        .iter()
        .filter(|li| li.body_blocks.contains(&location.block))
        .collect();
    let Some(tightest) = enclosing_loops
        .iter()
        .min_by_key(|li| li.body_blocks.len())
        .copied()
    else {
        return Vec::new();
    };

    // Skip in-body injection when the proof_assert follows a completed nested
    // loop inside the same enclosing loop. In that case the post-loop pass
    // (`extract_function_local_post_loop_assumptions`) is the owner of the
    // appropriate nested-loop-exit facts; injecting the still-active outer
    // loop condition here would duplicate context that the post-loop pass
    // intentionally omits.
    // (See nested_loop_proof_assert_snapshot_injects_inner_loop_exit_assumptions.)
    let pa_raw_start = assertion.span.lo().0;
    let pa_callsite_start = assertion.span.source_callsite().lo().0;
    let any_inner_loop_completed_before_pa =
        all_loop_spans.iter().any(|(inner_start, inner_end)| {
            let inner_ends_before_pa =
                *inner_end <= pa_raw_start || *inner_end <= pa_callsite_start;
            if !inner_ends_before_pa {
                return false;
            }
            // There must be another loop (the outer one) whose span strictly
            // contains the proof_assert; otherwise the inner loop is at
            // function scope and `post_loop` mode (proof_assert_after_all_loops)
            // handles it.
            all_loop_spans.iter().any(|(parent_s, parent_e)| {
                (*parent_s, *parent_e) != (*inner_start, *inner_end)
                    && ((*parent_s <= pa_raw_start && pa_raw_start < *parent_e)
                        || (*parent_s <= pa_callsite_start && pa_callsite_start < *parent_e))
            })
        });
    if any_inner_loop_completed_before_pa {
        return Vec::new();
    }

    // The loop's invariants and its condition speak of the loop HEAD: the
    // value a local the loop changes has at the start of an arbitrary
    // iteration, which the program-point walk binds to the local's loop-head
    // symbol (D-187). Each name such a local is bound to is read as that
    // symbol; an assumption that reads one where no single symbol is meant
    // (a name two locals share, a read under `old`/`^`) is not stated.
    let scope = crate::mir_analysis::fact_scope::FactScope::new(mir_body);
    let head = LoopHeadNames::new(tcx, mir_body, &loop_analysis, tightest, location, &scope);

    let mut assumptions = Vec::new();
    let header_byte_pos = mir_body.basic_blocks[tightest.header]
        .terminator()
        .source_info
        .span
        .lo()
        .0;

    // Per-loop user invariants are best-effort: a loop without an invariant
    // attribute still allows the positive condition assumption below since
    // the structural fact "we are inside the loop body" entails the
    // condition.
    if let Some((_, _, invariants)) =
        find_matching_loop_invariants(&per_loop_invariants, &all_loop_spans, header_byte_pos)
    {
        // An invariant names the bindings visible at its loop (D-237).
        let invariants = crate::mir_analysis::binding_identity::resolve_loop_clauses(
            mir_body,
            tightest.header,
            invariants,
        );
        for invariant in invariants {
            let Some(invariant) = head.at_loop_head(&invariant, false) else {
                continue;
            };
            if !assumptions.contains(&invariant) {
                assumptions.push(invariant);
            }
        }
    }

    let loop_body = extract_loop_body(
        mir_body,
        &arg_names,
        tightest,
        Some(&loop_analysis.loops),
        Some(&call_spec_ctx),
    );
    // The condition holds at the assertion only when every path reaching it
    // took the condition switch's in-body arm in this iteration: an
    // assertion placed before the test (`loop { proof_assert!(i < n); if i
    // >= n { break; } .. }`, a `while { proof_assert!(..); i < n }` block)
    // runs on the iteration whose test fails too.
    let condition_established = loop_body.condition_switch.is_some_and(|switch| {
        crate::mir_analysis::loop_condition_block(mir_body, tightest) == Some(switch)
            && crate::mir_analysis::switch_arm_dominating(
                mir_body,
                tightest,
                &loop_analysis.loops,
                switch,
                |target| tightest.body_blocks.contains(&target),
                location.block,
            )
            .is_some()
    });
    if let Some(condition) = loop_body.condition {
        // Body-break loops check their condition AFTER the body executes,
        // so at body entry the condition may not yet hold. Skip those.
        if let (false, true, Some(condition)) = (
            loop_body.condition_is_body_break,
            condition_established,
            head.at_loop_head(&condition, true),
        ) {
            let positive = collapse_idempotent_views(condition);
            if !assumptions.contains(&positive) {
                assumptions.push(positive.clone());
            }
            // Also add the integer-view form when both operands are scalar
            // integer expressions. User assertions like
            // `proof_assert!(i@ < n@)` use the View form, and
            // `View(x) cmp View(y)` is logically equivalent to `x cmp y`
            // for primitive integers — adding both gives the SMT a direct
            // syntactic match without requiring a dedicated view-projection
            // axiom at this layer.
            if let Some(viewed) = viewed_integer_comparison(&positive) {
                if !assumptions.contains(&viewed) {
                    assumptions.push(viewed);
                }
            }
        }
    }

    assumptions
}

/// The names a loop's exit facts (its invariants, its negated condition) may
/// not mention at `location`, or `None` when no exit fact holds there (D-189).
///
/// The negated condition is established on the condition switch's exit arm,
/// so every path reaching the assertion must have left through that arm: not
/// through a `break` or `return`, nor from code before the loop's test
/// ([`crate::mir_analysis::loop_exit_arm_dominating`]). Both kinds of fact are
/// then read from the loop's head, where the invariant holds and from which
/// the condition's locals reach the switch: a name is stale when a local it
/// names is written on a path from the head to the assertion that does not
/// pass the head again ([`crate::mir_analysis::fact_scope::FactScope::stale_names`]),
/// which takes in a write between the head and the switch (a `for` loop's
/// `next`), between the exit and the assertion, and after the assertion in a
/// later loop whose back edge carries it round to the assertion again.
fn exit_fact_stale_names(
    scope: &crate::mir_analysis::fact_scope::FactScope<'_, '_>,
    body: &rustc_middle::mir::Body<'_>,
    all_loops: &[crate::mir_analysis::LoopInfo],
    loop_info: &crate::mir_analysis::LoopInfo,
    loop_body: &crate::mir_analysis::LoopBodyExpr,
    location: rustc_middle::mir::Location,
) -> Option<HashSet<String>> {
    let switch = loop_body.condition_switch?;
    if crate::mir_analysis::loop_condition_block(body, loop_info) != Some(switch) {
        return None;
    }
    crate::mir_analysis::loop_exit_arm_dominating(body, loop_info, all_loops, location.block)?;
    scope.stale_names(loop_head_location(loop_info), location)
}

/// The point before the first statement of `loop_info`'s header.
fn loop_head_location(loop_info: &crate::mir_analysis::LoopInfo) -> rustc_middle::mir::Location {
    rustc_middle::mir::Location {
        block: loop_info.header,
        statement_index: 0,
    }
}

/// The names every loop of the assertion's function that does not contain
/// it leaves stale at the assertion ([`exit_fact_stale_names`]), or `None`
/// when some such loop's exit facts do not hold there. The loop lane's exit
/// facts, which the driver offers an assertion after all loops, are stated
/// only where this is `Some`, and never over one of these names.
fn function_exit_fact_stale_names(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Option<HashSet<String>> {
    let location = assertion.location?;
    let body_with_facts = super::try_get_body_with_context(tcx, assertion.containing_fn)?;
    let mir_body = get_mir_body(&body_with_facts);
    let loop_analysis = detect_loops(mir_body);
    let arg_names = resolve_arg_names_or_warn(tcx, assertion.containing_fn.to_def_id(), None);
    let call_spec_ctx = CallSpecContext {
        tcx,
        user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
    };
    let scope = crate::mir_analysis::fact_scope::FactScope::new(mir_body);
    let mut stale = HashSet::new();
    for loop_info in &loop_analysis.loops {
        if loop_info.body_blocks.contains(&location.block) {
            return None;
        }
        let loop_body = extract_loop_body(
            mir_body,
            &arg_names,
            loop_info,
            Some(&loop_analysis.loops),
            Some(&call_spec_ctx),
        );
        stale.extend(exit_fact_stale_names(
            &scope,
            mir_body,
            &loop_analysis.loops,
            loop_info,
            &loop_body,
            location,
        )?);
    }
    Some(stale)
}

/// The names a loop's invariants and condition read, as values at the loop's
/// head (D-187): a local the loop may change is bound there to its loop-head
/// symbol ([`crate::mir_analysis::loop_head_symbol`]), the symbol the
/// program-point walk re-binds it to on entering the header.
struct LoopHeadNames {
    /// Source name -> the loop-head symbol of the one local it names.
    symbols: HashMap<String, PureExpr>,
    /// Names no single loop-head symbol stands for: a name bound to two
    /// locals one of which the loop changes.
    ambiguous: HashSet<String>,
    /// Names of locals the loop changes before its condition is decided: the
    /// condition reads their value after that write, not at the head.
    written_before_condition: HashSet<String>,
    /// Names written on a path from the loop's head to the assertion
    /// ([`crate::mir_analysis::fact_scope::FactScope::stale_names`], D-189):
    /// a name the loop-head symbols do not replace must still hold its head
    /// value there. `None`: the head does not dominate the assertion.
    stale_at_assertion: Option<HashSet<String>>,
}

impl LoopHeadNames {
    fn new<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &rustc_middle::mir::Body<'tcx>,
        analysis: &crate::mir_analysis::LoopAnalysis,
        tightest: &crate::mir_analysis::LoopInfo,
        location: rustc_middle::mir::Location,
        scope: &crate::mir_analysis::fact_scope::FactScope<'_, 'tcx>,
    ) -> Self {
        let rebinds = crate::mir_analysis::loop_head_rebinds(
            body,
            body.arg_count,
            analysis,
            &HashSet::from([location.block]),
        );
        let changed: HashSet<rustc_middle::mir::Local> = rebinds
            .get(&tightest.header)
            .map(|locals| locals.iter().copied().collect())
            .unwrap_or_default();
        // The condition is decided at its switch, on the values the path
        // from the head leaves there.
        let head = loop_head_location(tightest);
        let before_condition = crate::mir_analysis::loop_condition_block(body, tightest)
            .and_then(|switch| scope.stale_names(head, body.terminator_loc(switch)));
        let stale_at_assertion = scope.stale_names(head, location);
        let mut bound: HashMap<String, HashSet<rustc_middle::mir::Local>> = HashMap::new();
        let mut projected: HashSet<String> = HashSet::new();
        for debug in &body.var_debug_info {
            let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value else {
                continue;
            };
            bound
                .entry(debug.name.to_string())
                .or_default()
                .insert(place.local);
            if !place.projection.is_empty() {
                // A name bound to a projection of a local (a closure's
                // capture) is no value of that local.
                projected.insert(debug.name.to_string());
            }
        }
        let mut symbols = HashMap::new();
        let mut ambiguous = HashSet::new();
        let mut written_before_condition = HashSet::new();
        for (name, locals) in bound {
            if !locals.iter().any(|local| changed.contains(local)) {
                continue;
            }
            if before_condition
                .as_ref()
                .is_none_or(|written| written.contains(&name))
            {
                written_before_condition.insert(name.clone());
            }
            match locals.iter().copied().collect::<Vec<_>>().as_slice() {
                [local] if !projected.contains(&name) => {
                    let sort = crate::mir_analysis::translate::ty_to_expr_sort_enriched(
                        tcx,
                        body.local_decls[*local].ty,
                    );
                    symbols.insert(
                        name,
                        PureExpr::Var(
                            crate::mir_analysis::loop_head_symbol(tightest.header, *local),
                            sort,
                        ),
                    );
                }
                _ => {
                    ambiguous.insert(name);
                }
            }
        }
        Self {
            symbols,
            ambiguous,
            written_before_condition,
            stale_at_assertion,
        }
    }

    /// `expr` (an invariant, or the loop condition when `is_condition`) with
    /// each name of a local the loop changes read as its loop-head symbol;
    /// `None` when it reads such a name in a way no symbol stands for.
    fn at_loop_head(&self, expr: &PureExpr, is_condition: bool) -> Option<PureExpr> {
        let free = expr.free_vars();
        if free.iter().any(|name| {
            self.ambiguous.contains(name)
                || (is_condition && self.written_before_condition.contains(name))
        }) {
            return None;
        }
        // A read under `old(..)` or `^..` names the entry or the final value,
        // which no loop-head symbol is.
        let mut temporal_read = false;
        let _ = expr.rewrite_bottom_up_prune(
            |node| !matches!(node, PureExpr::Old(_) | PureExpr::Final(_)),
            |node| {
                if let PureExpr::Old(inner) | PureExpr::Final(inner) = &node {
                    temporal_read |= inner
                        .free_vars()
                        .iter()
                        .any(|name| self.symbols.contains_key(name));
                }
                node
            },
        );
        if temporal_read {
            return None;
        }
        let at_head = expr.substitute(&self.symbols);
        let stale = self.stale_at_assertion.as_ref()?;
        if at_head.free_vars().iter().any(|name| stale.contains(name)) {
            return None;
        }
        Some(at_head)
    }
}

/// If `expr` is a comparison `BinOp(lhs, cmp, rhs)` whose operator is one of
/// the integer comparisons (`<`, `<=`, `>`, `>=`, `==`, `!=`) and whose
/// operands are scalar integer terms (Var or integer literal), return the
/// parallel comparison `BinOp(View(lhs), cmp, View(rhs))`. Returns None for
/// any non-matching shape so callers can skip the augmentation safely.
fn viewed_integer_comparison(expr: &PureExpr) -> Option<PureExpr> {
    let (lhs, op, rhs) = match expr {
        PureExpr::BinOp(l, op, r) => (l.as_ref(), *op, r.as_ref()),
        _ => return None,
    };
    if !matches!(
        op,
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne
    ) {
        return None;
    }
    if !is_scalar_view_target(lhs) || !is_scalar_view_target(rhs) {
        return None;
    }
    let view_or_self = |e: &PureExpr| -> PureExpr {
        if matches!(e, PureExpr::View(_)) {
            e.clone()
        } else {
            PureExpr::View(Arc::new(e.clone()))
        }
    };
    Some(PureExpr::BinOp(
        Arc::new(view_or_self(lhs)),
        op,
        Arc::new(view_or_self(rhs)),
    ))
}

/// Return true when `expr` is a simple scalar integer term safe to wrap with
/// `View`. We restrict this to forms where wrapping is type-safe and adds a
/// useful integer-view fact:
///
/// - `Var(_, Some(Int))`: explicit integer-sort variable.
/// - `Int(_)`: integer literal.
/// - `View(_)`: already an integer view (View is idempotent here).
///
/// `Var(_, None)` is intentionally excluded — without sort information we
/// cannot guarantee the variable refers to a primitive integer scalar, and
/// wrapping a non-scalar variable with `View` may introduce a fact the SMT
/// cannot reason about.
fn is_scalar_view_target(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(ExprSort::Int)) => true,
        PureExpr::Int(_) => true,
        PureExpr::View(_) => true,
        _ => false,
    }
}

fn parse_per_loop_invariants(
    per_loop_invariant_texts: &[(u32, u32, Vec<String>)],
) -> Vec<(u32, u32, Vec<PureExpr>)> {
    per_loop_invariant_texts
        .iter()
        .filter_map(|(start, end, texts)| {
            let invariants: Vec<PureExpr> = texts
                .iter()
                .filter_map(|text| match parse_contract(text) {
                    Ok(expr) => Some(expr),
                    Err(err) => {
                        tracing::debug!(
                            "failed to parse local post-loop invariant '{}': {}",
                            text,
                            err
                        );
                        None
                    }
                })
                .collect();
            (!invariants.is_empty()).then_some((*start, *end, invariants))
        })
        .collect()
}

fn find_matching_loop_invariants(
    per_loop_invariants: &[(u32, u32, Vec<PureExpr>)],
    all_loop_spans: &[(u32, u32)],
    header_byte_pos: u32,
) -> Option<(u32, u32, Vec<PureExpr>)> {
    let mut best: Option<(u32, u32, u32, Vec<PureExpr>)> = None;
    for (start, end, invariants) in per_loop_invariants {
        if *start <= header_byte_pos && header_byte_pos < *end {
            let span_size = end - start;
            match &best {
                None => best = Some((*start, *end, span_size, invariants.clone())),
                Some((_, _, best_size, _)) if span_size < *best_size => {
                    best = Some((*start, *end, span_size, invariants.clone()));
                }
                _ => {}
            }
        }
    }

    let (best_start, best_end, best_size, invariants) = best?;
    let mut tightest_loop_size = u32::MAX;
    for (start, end) in all_loop_spans {
        if *start <= header_byte_pos && header_byte_pos < *end {
            tightest_loop_size = tightest_loop_size.min(end - start);
        }
    }
    if tightest_loop_size < best_size {
        return None;
    }

    Some((best_start, best_end, invariants))
}

fn loop_precedes_nested_proof_assert(
    proof_assert_span: rustc_span::Span,
    loop_start: u32,
    loop_end: u32,
    all_loop_spans: &[(u32, u32)],
) -> bool {
    let pa_raw_start = proof_assert_span.lo().0;
    let pa_callsite_start = proof_assert_span.source_callsite().lo().0;
    let loop_before_assert = loop_end <= pa_raw_start || loop_end <= pa_callsite_start;
    if !loop_before_assert {
        return false;
    }

    all_loop_spans.iter().any(|(parent_start, parent_end)| {
        (*parent_start, *parent_end) != (loop_start, loop_end)
            && ((*parent_start <= pa_raw_start && pa_raw_start < *parent_end)
                || (*parent_start <= pa_callsite_start && pa_callsite_start < *parent_end))
    })
}

#[derive(Debug, Clone)]
struct PlainReborrowCarrierAlias {
    child_name: String,
    parent_name: String,
    sort: Option<ExprSort>,
    final_same_parent: bool,
}

fn derive_plain_reborrow_carrier_aliases<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    substitutions: &mut NameSubstitutions,
) -> Vec<PlainReborrowCarrierAlias> {
    let debug_names = debug_names_by_local(body);
    let mut local_to_borrow_name: HashMap<Local, String> = HashMap::new();
    let mut aliases = Vec::new();
    let analysis = crate::mir_analysis::not_final_places::NotFinalPlaces::new(tcx, body);
    let results = analysis.iterate_to_fixpoint(tcx, body, None);
    let mut cursor = results.into_results_cursor(body);

    for (index, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(index + 1);
        if body.local_decls.get(local).is_some_and(|decl| {
            matches!(
                decl.ty.kind(),
                TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            )
        }) {
            local_to_borrow_name.insert(local, name.clone());
        }
    }

    for (bb_idx, block) in body.basic_blocks.iter_enumerated() {
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            let StatementKind::Assign((dest, rvalue)) = &stmt.kind else {
                continue;
            };
            if !dest.projection.is_empty() {
                continue;
            }
            let Rvalue::Ref(_, BorrowKind::Mut { .. }, place) = rvalue else {
                continue;
            };
            if !is_plain_deref_reborrow(place) {
                continue;
            };
            let Some(parent_name) = local_to_borrow_name.get(&place.local).cloned() else {
                continue;
            };
            let child_name = format!("{parent_name}$rb{}", dest.local.as_u32());
            local_to_borrow_name.insert(dest.local, child_name.clone());
            let mut inserted_alias = false;

            let Some(names) = debug_names.get(&dest.local) else {
                continue;
            };
            let sort = crate::mir_analysis::translate::ty_to_expr_sort_enriched(
                tcx,
                body.local_decls[dest.local].ty,
            );
            let child_expr = PureExpr::Var(child_name.clone(), sort.clone());
            for name in names {
                if substitutions.contains_key(name) {
                    // fact-source: reborrow_carrier_rename
                    substitutions.insert(name.clone(), child_expr.clone());
                    substitutions.name_sorts.insert(name.clone(), sort.clone());
                    inserted_alias = true;
                }
            }
            if inserted_alias {
                let final_same_parent =
                    crate::mir_analysis::not_final_places::NotFinalPlaces::is_final_at(
                        &mut cursor,
                        place,
                        Location {
                            block: bb_idx,
                            statement_index: stmt_idx,
                        },
                    )
                    .is_some();
                aliases.push(PlainReborrowCarrierAlias {
                    child_name,
                    parent_name,
                    sort,
                    final_same_parent,
                });
            }
        }
    }

    aliases
}

fn debug_names_by_local(body: &Body<'_>) -> HashMap<Local, Vec<String>> {
    let mut names: HashMap<Local, Vec<String>> = HashMap::new();
    for debug in &body.var_debug_info {
        let VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        if !place.projection.is_empty() {
            continue;
        }
        let name = debug.name.to_string();
        if name == "_" {
            continue;
        }
        names.entry(place.local).or_default().push(name);
    }
    names
}

fn is_plain_deref_reborrow(place: &Place<'_>) -> bool {
    place.projection.len() == 1 && matches!(place.projection.first(), Some(ProjectionElem::Deref))
}

fn is_plain_reborrow_parent_alias(expr: &PureExpr, aliases: &[PlainReborrowCarrierAlias]) -> bool {
    let PureExpr::BinOp(left, trust_wp_core::formula::BinOp::Eq, right) = expr else {
        return false;
    };
    let Some(left_name) = bare_var_name(left) else {
        return false;
    };
    let Some(right_name) = bare_var_name(right) else {
        return false;
    };
    aliases.iter().any(|alias| {
        !alias.final_same_parent
            && ((left_name == alias.child_name && right_name == alias.parent_name)
                || (left_name == alias.parent_name && right_name == alias.child_name))
    })
}

fn extend_final_plain_reborrow_parent_aliases(
    assumptions: &mut Vec<PureExpr>,
    aliases: &[PlainReborrowCarrierAlias],
) {
    for alias in aliases.iter().filter(|alias| alias.final_same_parent) {
        let fact = PureExpr::BinOp(
            Arc::new(PureExpr::Var(alias.child_name.clone(), alias.sort.clone())),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::Var(alias.parent_name.clone(), alias.sort.clone())),
        );
        if !assumptions.contains(&fact) {
            assumptions.push(fact);
        }
    }
}

fn bare_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        _ => None,
    }
}

fn derive_projected_snapshot_deref_aliases<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    substitutions: &mut NameSubstitutions,
) -> usize {
    let mut added = 0usize;
    for (bb, block) in body.basic_blocks.iter_enumerated() {
        let terminator = block.terminator();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        if !is_snapshot_capture_call(tcx, &func) {
            continue;
        }

        let snapshot_names =
            snapshot_names_for_capture_result(body, substitutions, destination.local);
        if snapshot_names.is_empty() {
            continue;
        }

        // The captured reference is the sole inline `&expr`. For a direct
        // `Snapshot::capture(&expr)` it is the last argument of THIS call; for
        // the type-directed dispatch the matched `.capture()` is the identity
        // tail whose sole argument is the selector, so the `&expr` lives in the
        // preceding `snapshot_capture_select(&expr)` call — `ref_bb` is the
        // block that formed it (which the projection search below must scan).
        // (bug/869)
        let Some((ref_bb, captured_place)) = args
            .last()
            .and_then(|arg| resolve_dispatch_capture_place(tcx, body, bb, &arg.node))
        else {
            continue;
        };
        let alias =
            projected_mut_ref_snapshot_alias(tcx, body, ref_bb, &captured_place).or_else(|| {
                // Plain `snapshot!(*a)` of a `&mut T`: the snapshot's value is the
                // frozen current pointee `Deref(Var("a"))` (= `a_current`). Since
                // `Snapshot<T>` derefs to `T` identically, `*<snapshot>` must
                // resolve to that same frozen current — NOT a second `Deref`
                // (which would deref an integer). Reuse the snapshot's own
                // current-deref carrier value as the `*<snapshot>` alias. (#682)
                snapshot_names.iter().find_map(|name| {
                    substitutions.get(name).and_then(|value| match value {
                        PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(_, _)) => {
                            Some(value.clone())
                        }
                        _ => None,
                    })
                })
            });
        let Some(alias) = alias else {
            continue;
        };

        for snapshot_name in snapshot_names {
            let key = format!("*{snapshot_name}");
            if substitutions.contains_key(&key) {
                continue;
            }
            // fact-source: snapshot_deref_aliases
            substitutions.insert(key, alias.clone());
            added += 1;
        }
    }
    added
}

fn snapshot_names_for_capture_result(
    body: &Body<'_>,
    substitutions: &NameSubstitutions,
    result_local: Local,
) -> Vec<String> {
    let call_result_name = format!("$call_{}", result_local.as_u32());
    let mut names: Vec<String> = substitutions
        .iter()
        .filter_map(|(name, expr)| {
            if name.starts_with('*') || name.starts_with('^') {
                return None;
            }
            match expr {
                PureExpr::Var(var, _) if var == &call_result_name => Some(name.clone()),
                _ => None,
            }
        })
        .collect();
    for debug in &body.var_debug_info {
        let VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        if place.local != result_local || !place.projection.is_empty() {
            continue;
        }
        let name = debug.name.to_string();
        if name != "_" && !names.contains(&name) {
            names.push(name);
        }
    }
    names
}

fn is_snapshot_capture_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Operand::Constant(deref!(constant)) = func else {
        return false;
    };
    let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return false;
    };
    // Provenance: only the spec library's capture freezes its argument.
    if !crate::provenance::is_spec_library_item(tcx, *def_id) {
        return false;
    }
    let path = tcx.def_path_str(*def_id);
    path.ends_with("::capture") && path.contains("Snapshot")
}

fn snapshot_capture_argument_place<'tcx>(
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    operand: &Operand<'tcx>,
) -> Option<Place<'tcx>> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }

    for stmt in body.basic_blocks[bb].statements.iter().rev() {
        let rustc_middle::mir::StatementKind::Assign((dest, rvalue)) = &stmt.kind else {
            continue;
        };
        if dest.local != place.local || !dest.projection.is_empty() {
            continue;
        }
        let Rvalue::Ref(_, _, captured_place) = rvalue else {
            return None;
        };
        return Some(*captured_place);
    }
    None
}

/// Whether `func` calls the `snapshot!` dispatch's `snapshot_capture_select`. (bug/869)
fn is_dispatch_select_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Operand::Constant(deref!(constant)) = func else {
        return false;
    };
    let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return false;
    };
    tcx.def_path_str(*def_id)
        .ends_with("::snapshot_capture_select")
}

/// Resolve the captured `&expr` reborrow behind a snapshot capture, returning
/// the block that formed it and the borrowed place.
///
/// - A direct `Snapshot::capture(&expr)` forms `&expr` inline in `bb`, so the
///   last argument resolves there directly.
/// - The type-directed `snapshot!` dispatch's `.capture()` tail takes the ZST
///   selector as its argument; the `&expr` was formed one call earlier by
///   `snapshot_capture_select(&expr)`. Trace the selector local back to that
///   call and read its inline reborrow (in the select's own block). (bug/869)
fn resolve_dispatch_capture_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    operand: &Operand<'tcx>,
) -> Option<(rustc_middle::mir::BasicBlock, Place<'tcx>)> {
    if let Some(place) = snapshot_capture_argument_place(body, bb, operand) {
        return Some((bb, place));
    }
    let (Operand::Copy(sel) | Operand::Move(sel)) = operand else {
        return None;
    };
    if !sel.projection.is_empty() {
        return None;
    }
    for (sbb, block) in body.basic_blocks.iter_enumerated() {
        let Some(terminator) = &block.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        if destination.local != sel.local
            || !destination.projection.is_empty()
            || !is_dispatch_select_call(tcx, func)
        {
            continue;
        }
        return args
            .last()
            .and_then(|arg| snapshot_capture_argument_place(body, sbb, &arg.node))
            .map(|place| (sbb, place));
    }
    None
}

fn projected_mut_ref_snapshot_alias<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    captured_place: &Place<'tcx>,
) -> Option<PureExpr> {
    let (alias_local, alias_projection, captured_ty) =
        projected_mut_ref_snapshot_alias_input(tcx, body, bb, captured_place)?;
    if alias_projection.is_empty() {
        return None;
    }
    let TyKind::Ref(_, inner_ty, mutability) = captured_ty.kind() else {
        return None;
    };
    if !mutability.is_mut() {
        return None;
    }
    let inner_sort = crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, *inner_ty)?;
    let mut projection_segments = alias_projection
        .into_iter()
        .map(projected_snapshot_alias_projection_segment)
        .collect::<Option<Vec<_>>>()?;
    projection_segments.push("deref".to_string());

    Some(PureExpr::Var(
        format!(
            "__trust_wp_reborrow_{}_{}",
            alias_local.as_u32(),
            projection_segments.join("_"),
        ),
        Some(ExprSort::MutRef(Box::new(inner_sort))),
    ))
}

fn projected_mut_ref_snapshot_alias_input<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    captured_place: &Place<'tcx>,
) -> Option<(
    Local,
    Vec<ProjectionElem<Local, rustc_middle::ty::Ty<'tcx>>>,
    rustc_middle::ty::Ty<'tcx>,
)> {
    if let Some(source_place) = captured_snapshot_ref_source_place(body, bb, captured_place) {
        return Some((
            source_place.local,
            source_place.projection.iter().collect(),
            source_place.ty(body, tcx).ty,
        ));
    }
    Some((
        captured_place.local,
        captured_place.projection.iter().collect(),
        captured_place.ty(body, tcx).ty,
    ))
}

fn captured_snapshot_ref_source_place<'tcx>(
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    captured_place: &Place<'tcx>,
) -> Option<Place<'tcx>> {
    let mut projection = captured_place.projection.iter();
    if !matches!(projection.next(), Some(ProjectionElem::Deref)) || projection.next().is_some() {
        return None;
    }
    local_ref_source_place(body, bb, captured_place.local)
}

fn local_ref_source_place<'tcx>(
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    local: Local,
) -> Option<Place<'tcx>> {
    for stmt in body.basic_blocks[bb].statements.iter().rev() {
        let rustc_middle::mir::StatementKind::Assign((dest, rvalue)) = &stmt.kind else {
            continue;
        };
        if dest.local != local || !dest.projection.is_empty() {
            continue;
        }
        let Rvalue::Ref(_, _, source_place) = rvalue else {
            return None;
        };
        return Some(*source_place);
    }
    None
}

fn projected_snapshot_alias_projection_segment(
    proj: ProjectionElem<Local, rustc_middle::ty::Ty<'_>>,
) -> Option<String> {
    match proj {
        ProjectionElem::Deref => Some("deref".to_string()),
        ProjectionElem::Field(field, _) => Some(format!("field{}", field.as_u32())),
        ProjectionElem::Downcast(_, variant) => Some(format!("downcast{}", variant.as_u32())),
        ProjectionElem::Index(local) => Some(format!("index{}", local.as_u32())),
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => Some(format!("const{offset}_{min_length}_{}", u8::from(from_end))),
        ProjectionElem::Subslice { from, to, from_end } => {
            Some(format!("subslice{from}_{to}_{}", u8::from(from_end)))
        }
        ProjectionElem::OpaqueCast(_) => Some("opaque".to_string()),
        ProjectionElem::UnwrapUnsafeBinder(_) => Some("unwrap".to_string()),
        // A phantom deref reaches an indeterminate indirect place: no alias.
        ProjectionElem::PhantomDeref => None,
    }
}

/// Extract loop invariant-based continuation assumptions from ghost closures
/// that contain a loop preceding the proof_assert. (#2584)
fn extract_ghost_closure_loop_assumptions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    containing_ghost_block: Option<&GhostBlock>,
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    let Some(ghost_block) = containing_ghost_block else {
        return Vec::new();
    };

    let Some(body_with_facts) = super::try_get_body_with_context(tcx, assertion.containing_fn)
    else {
        return Vec::new();
    };
    let mir_body = get_mir_body(&body_with_facts);
    let ghost_closure_def_ids =
        ghost_closure_candidates_for_assertion(tcx, assertion, ghost_block, mir_body);

    let mut assumptions = Vec::new();
    for closure_def_id in ghost_closure_def_ids {
        let Some(local_def_id) = closure_def_id.as_local() else {
            continue;
        };
        let (flat_invariants, _, _, _, all_loop_spans) =
            collect_loop_contract_attrs(tcx, local_def_id);
        if flat_invariants.is_empty()
            || all_loop_spans.is_empty()
            || !proof_assert_is_after_all_loops(assertion.span, &all_loop_spans)
        {
            continue;
        }
        // Keep the first slice bounded to the single-loop ghost-closure case
        // required by #2584's `ghost/fmap_iter.rs` shape.
        if all_loop_spans.len() != 1 {
            continue;
        }

        let Ok(closure_body) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tcx.optimized_mir(closure_def_id)
        })) else {
            continue;
        };
        let loop_analysis = detect_loops(closure_body);
        if loop_analysis.loops.len() != 1 {
            continue;
        }
        // The assertion's own point in the closure's body: the invariants
        // are facts there only as the exit facts of any other loop are
        // (D-189). An assertion this body does not create states none.
        let Some(at) = proof_assert_location_in(closure_body, assertion) else {
            continue;
        };
        if loop_analysis.loops[0].body_blocks.contains(&at.block) {
            continue;
        }

        let arg_names = resolve_arg_names_or_warn(tcx, closure_def_id, None);
        let call_spec_ctx = CallSpecContext {
            tcx,
            user_specs,
            trait_specs: ctx.trait_specs,
            extern_specs: ctx.extern_specs,
        };
        let loop_body = extract_loop_body(
            closure_body,
            &arg_names,
            &loop_analysis.loops[0],
            Some(&loop_analysis.loops),
            Some(&call_spec_ctx),
        );

        let mut parsed_invariants = Vec::new();
        for inv_text in &flat_invariants {
            match parse_contract(inv_text) {
                Ok(expr) => parsed_invariants.push(expr),
                Err(e) => {
                    tracing::debug!(
                        "failed to parse ghost closure loop invariant '{}': {}",
                        inv_text,
                        e
                    );
                }
            }
        }
        if parsed_invariants.is_empty() {
            continue;
        }
        // An invariant names the bindings visible at its loop (D-237).
        let parsed_invariants = crate::mir_analysis::binding_identity::resolve_loop_clauses(
            closure_body,
            loop_analysis.loops[0].header,
            parsed_invariants,
        );

        // For proof_assert, only inject the user invariants — not the full
        // continuation bundle (produces, structural, bridge facts) which references
        // loop-internal iterator state variables not declared in the proof_assert
        // encoding scope. Specialize the invariants for the completed-iterator
        // case: at loop exit, the iterator's view is empty. (#2584)
        let capture_names = closure_capture_names(tcx, closure_def_id);
        let is_fmap_iter = loop_body.for_loop_state.as_ref().is_some_and(|st| {
            super::iterator_spec_rewrite::helpers::is_fmap_backed_iterator(&st.iter_state)
                || super::iterator_spec_rewrite::helpers::is_logical_fmap_iter(&st.iter_state)
        });
        let specialized_invariants = if is_fmap_iter {
            specialize_invariants_for_completed_fmap_iter(&parsed_invariants, &capture_names)
        } else {
            parsed_invariants.clone()
        };
        let scope = crate::mir_analysis::fact_scope::FactScope::new(closure_body);
        let Some(stale) = exit_fact_stale_names(
            &scope,
            closure_body,
            &loop_analysis.loops,
            &loop_analysis.loops[0],
            &loop_body,
            at,
        ) else {
            continue;
        };
        for assumption in specialized_invariants
            .into_iter()
            .filter(|expr| !expr.free_vars().iter().any(|name| stale.contains(name)))
            .map(|expr| rewrite_ghost_closure_capture_vars(&expr, &capture_names))
        {
            if !assumptions.contains(&assumption) {
                assumptions.push(assumption);
            }
        }
    }
    if assumptions.is_empty() {
        assumptions.extend(extract_ghost_block_function_loop_assumptions(
            tcx,
            assertion,
            ghost_block,
            mir_body,
            user_specs,
            ctx,
        ));
    }
    assumptions
}

#[allow(clippy::similar_names)] // has_hir_loops / has_mir_loops are domain-distinct
fn ghost_closure_candidates_for_assertion(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_block: &GhostBlock,
    mir_body: &Body<'_>,
) -> Vec<DefId> {
    let mut closure_def_ids = Vec::new();

    if let Some(mut current) = assertion.closure_def_id {
        while let Some(parent) = tcx.opt_parent(current) {
            current = parent;
            if !matches!(tcx.def_kind(parent), DefKind::Closure) {
                continue;
            }
            let Some(local_def_id) = parent.as_local() else {
                continue;
            };
            let (_, _, _, _, all_loop_spans) = collect_loop_contract_attrs(tcx, local_def_id);
            let has_hir_loops = !all_loop_spans.is_empty();
            let has_mir_loops = tcx.is_mir_available(parent)
                && std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    tcx.optimized_mir(parent)
                }))
                .ok()
                .map_or(false, |body| !detect_loops(body).loops.is_empty());
            if has_hir_loops || has_mir_loops {
                closure_def_ids.push(parent);
                break;
            }
        }
    }

    for closure_def_id in find_ghost_closure_def_ids_in_mir(mir_body, ghost_block.span) {
        if !closure_def_ids.contains(&closure_def_id) {
            closure_def_ids.push(closure_def_id);
        }
    }

    closure_def_ids
}

fn extract_ghost_block_function_loop_assumptions<'tcx>(
    tcx: TyCtxt<'tcx>,
    assertion: &ProofAssert,
    ghost_block: &GhostBlock,
    mir_body: &Body<'tcx>,
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    let Some(at) = assertion.location else {
        return Vec::new();
    };
    let (_, _, per_loop_invariants, _, all_loop_spans) =
        collect_loop_contract_attrs(tcx, assertion.containing_fn);
    // Keep the ghost-block span in the same expansion coordinate space as the
    // raw loop-attribute spans collected from HIR. Using source_callsite()
    // here can move the ghost block to source coordinates while the loop spans
    // remain in proc-macro expansion coordinates, which drops the live #2584
    // fallback match in ghost/fmap_iter.rs.
    let ghost_block_span = ghost_block.span;
    let loop_spans_in_block: Vec<(u32, u32)> = all_loop_spans
        .into_iter()
        .filter(|(start, end)| ghost_block_span.lo().0 <= *start && *end <= ghost_block_span.hi().0)
        .collect();
    if loop_spans_in_block.len() != 1 {
        return Vec::new();
    }
    let (loop_start, loop_end) = loop_spans_in_block[0];
    let invariant_texts = per_loop_invariants
        .into_iter()
        .find_map(|(start, end, invariants)| {
            (start == loop_start && end == loop_end).then_some(invariants)
        })
        .unwrap_or_default();
    let mut parsed_invariants = Vec::new();
    for inv_text in &invariant_texts {
        match parse_contract(inv_text) {
            Ok(expr) => parsed_invariants.push(expr),
            Err(e) => {
                tracing::debug!(
                    "failed to parse ghost block loop invariant '{}': {}",
                    inv_text,
                    e
                );
            }
        }
    }
    if parsed_invariants.is_empty() {
        return Vec::new();
    }

    let loop_analysis = detect_loops(mir_body);
    let matching_loops: Vec<_> = loop_analysis
        .loops
        .iter()
        .filter(|loop_info| {
            let header_pos = mir_body.basic_blocks[loop_info.header]
                .terminator()
                .source_info
                .span
                .lo()
                .0;
            loop_start <= header_pos
                && header_pos < loop_end
                && !loop_info.body_blocks.contains(&at.block)
        })
        .collect();
    if matching_loops.len() != 1 {
        return Vec::new();
    }
    // An invariant names the bindings visible at its loop (D-237).
    let parsed_invariants = crate::mir_analysis::binding_identity::resolve_loop_clauses(
        mir_body,
        matching_loops[0].header,
        parsed_invariants,
    );

    // For proof_assert in the fallback path (outer function, not ghost closure),
    // only inject user invariants — not the full continuation bundle which references
    // loop-internal iterator state variables not in the proof_assert scope. (#2584)
    // Always specialize: non-arg iterator views become fmap_new() at loop exit.
    let arg_names = resolve_arg_names_or_warn(tcx, assertion.containing_fn.to_def_id(), None);
    let call_spec_ctx = CallSpecContext {
        tcx,
        user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
    };
    let loop_body = extract_loop_body(
        mir_body,
        &arg_names,
        matching_loops[0],
        Some(&loop_analysis.loops),
        Some(&call_spec_ctx),
    );
    // The invariants are exit facts like any other loop's (D-189).
    let scope = crate::mir_analysis::fact_scope::FactScope::new(mir_body);
    let Some(stale) = exit_fact_stale_names(
        &scope,
        mir_body,
        &loop_analysis.loops,
        matching_loops[0],
        &loop_body,
        at,
    ) else {
        return Vec::new();
    };
    specialize_invariants_for_completed_fmap_iter(&parsed_invariants, &arg_names)
        .into_iter()
        .filter(|expr| !expr.free_vars().iter().any(|name| stale.contains(name)))
        .collect()
}

/// The point in `body` where `assertion`'s closure is created, or `None`
/// when `body` does not create it.
fn proof_assert_location_in(
    body: &Body<'_>,
    assertion: &ProofAssert,
) -> Option<rustc_middle::mir::Location> {
    let closure = assertion.closure_def_id?;
    body.basic_blocks
        .iter_enumerated()
        .find_map(|(block, data)| {
            data.statements
                .iter()
                .position(|statement| {
                    matches!(
                        &statement.kind,
                        rustc_middle::mir::StatementKind::Assign((
                            _,
                            rustc_middle::mir::Rvalue::Aggregate(
                                rustc_middle::mir::AggregateKind::Closure(def_id, _),
                                _,
                            ),
                        )) if *def_id == closure
                    )
                })
                .map(|statement_index| rustc_middle::mir::Location {
                    block,
                    statement_index,
                })
        })
}

/// Specialize loop invariants for the proof_assert post-loop context by
/// replacing non-capture iterator views with the empty FMap. (#2584)
///
/// At loop exit, the FMap iterator is exhausted — its `view()` is the empty FMap.
/// The proof_assert encoding scope doesn't declare the loop-local iterator
/// variable, so `View(Var("iter"))` or `LogicFnCall("view", [Var("iter")])`
/// would trigger a ay sort mismatch panic. This function replaces both forms
/// for non-capture variables (loop-local iterator references) with `fmap_new()`.
///
/// The contract parser produces `LogicFnCall { name: "view", .. }` for `view(x)`
/// syntax, while the macro preprocess produces `View(x)` for `x@` syntax.
/// Both must be handled.
fn specialize_invariants_for_completed_fmap_iter(
    invariants: &[PureExpr],
    capture_names: &[String],
) -> Vec<PureExpr> {
    let captures: HashSet<&str> = capture_names.iter().map(String::as_str).collect();
    let fmap_new = || PureExpr::LogicFnCall {
        name: "fmap_new".to_string(),
        args: vec![],
    };
    invariants
        .iter()
        .map(|inv| {
            inv.rewrite_bottom_up(|node| match &node {
                // Match `x@` syntax (View node)
                PureExpr::View(inner) => match inner.as_ref() {
                    PureExpr::Var(name, _) if !captures.contains(name.as_str()) => fmap_new(),
                    _ => node,
                },
                // Match `view(x)` syntax (LogicFnCall node from contract parser)
                PureExpr::LogicFnCall { name, args } if name == "view" && args.len() == 1 => {
                    match &args[0] {
                        PureExpr::Var(var_name, _) if !captures.contains(var_name.as_str()) => {
                            fmap_new()
                        }
                        _ => node,
                    }
                }
                _ => node,
            })
        })
        .collect()
}

fn proof_assert_is_after_all_loops(span: rustc_span::Span, loop_spans: &[(u32, u32)]) -> bool {
    if loop_spans.is_empty() {
        return false;
    }
    let callsite = span.source_callsite();
    let proof_assert_start = callsite.lo().0;
    loop_spans.iter().all(|(_, end)| *end <= proof_assert_start)
}

/// Build a substitution map for callee call-assumption rewriting that drops
/// POST-call deref remappings (`*x -> call_N`, the value read AFTER the call).
///
/// A callee's postcondition (e.g. `^a > *a`) references the dereferenced
/// argument as observed AT the call (pre-call). Rewriting that pre-call `*a`
/// with the post-call read corrupts the postcondition. Only `*<simple var>`
/// keys whose value is a fresh `call_*` post-state symbol are removed; every
/// other mapping (including identity `*x` carriers) is preserved. (#682)
/// Drop the conflating `Deref(Var(x)) == call_N` equalities for variables `x`
/// whose CURRENT pointee was frozen by a `snapshot!(*x)`. See the call site:
/// these equate the frozen pre-call current with the post-call read. (#682)
fn drop_frozen_current_post_call_equalities(
    facts: &mut Vec<PureExpr>,
    substitutions: &NameSubstitutions,
) {
    let frozen_roots: HashSet<String> = substitutions
        .values()
        .filter_map(|value| match value {
            PureExpr::Deref(inner) => match inner.as_ref() {
                PureExpr::Var(name, _) => Some(name.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    if frozen_roots.is_empty() {
        return;
    }
    facts.retain(|fact| {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = fact else {
            return true;
        };
        !(is_frozen_current_post_call_equality(lhs, rhs, &frozen_roots)
            || is_frozen_current_post_call_equality(rhs, lhs, &frozen_roots))
    });
}

fn is_frozen_current_post_call_equality(
    deref_side: &PureExpr,
    other_side: &PureExpr,
    frozen_roots: &HashSet<String>,
) -> bool {
    let PureExpr::Deref(inner) = deref_side else {
        return false;
    };
    let PureExpr::Var(name, _) = inner.as_ref() else {
        return false;
    };
    if !frozen_roots.contains(name) {
        return false;
    }
    matches!(other_side, PureExpr::Var(other, _) if other.starts_with("$call_"))
}

fn drop_post_call_deref_remappings(
    substitutions: &std::collections::HashMap<String, PureExpr>,
) -> std::collections::HashMap<String, PureExpr> {
    substitutions
        .iter()
        .filter(|(key, value)| {
            let is_deref_key = key.strip_prefix('*').is_some_and(is_simple_ident_local);
            let is_post_call_value =
                matches!(value, PureExpr::Var(name, _) if name.starts_with("$call_"));
            !(is_deref_key && is_post_call_value)
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

/// Build a substitution for callee PRECONDITION obligations that keeps the
/// dereferenced argument at its PRE-call value.
///
/// A callee's precondition `P(*x)` is evaluated against the value the caller
/// holds AT THE CALL — the pre-call current pointee `Deref(Var(x))`
/// (= `x_current`). The proof_assert substitution map, however, advances each
/// mutated reference root to its prophecy (`x -> Final(Var(x))`) to express the
/// post-call program state. Applying that to a surviving `Deref(Var(x))` in the
/// obligation rewrites it to `Deref(Final(Var(x)))` (= the POST-call pointee),
/// which is the wrong (and, in the proof_assert solve, unconstrained) value.
///
/// We therefore drop exactly the self-advancement entry `root -> Final(.. root
/// ..)` for any root the obligations actually dereference. Every other mapping
/// (including the post-call `*x -> call_N` remapping, already excluded upstream
/// for the call-assumption substitution) is preserved unchanged.
///
/// SOUND: removing an advancement mapping makes `*x` resolve to the pre-call
/// `x_current` — the exact value the callee observes — instead of a free
/// post-call symbol. The obligation is checked against the actual (more
/// constrained) argument value, so this can only make a VALID precondition
/// provable; it can never let a false precondition verify. (#682)
fn drop_self_advancement_for_dereffed_roots(
    substitutions: &std::collections::HashMap<String, PureExpr>,
    raw_obligations: &[PureExpr],
) -> std::collections::HashMap<String, PureExpr> {
    let mut dereffed_roots: HashSet<String> = HashSet::new();
    for obligation in raw_obligations {
        collect_dereffed_var_roots(obligation, &mut dereffed_roots);
    }
    if dereffed_roots.is_empty() {
        return substitutions.clone();
    }
    substitutions
        .iter()
        .filter(|(key, value)| {
            let advances_self = dereffed_roots.contains(key.as_str())
                && matches!(value, PureExpr::Final(_))
                && advancement_root_name(value).is_some_and(|root| root == key.as_str());
            !advances_self
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

/// Collect the names of variables that appear directly inside a `Deref(Var(_))`
/// anywhere in `expr` (the roots whose current pointee the expression reads).
fn collect_dereffed_var_roots(expr: &PureExpr, out: &mut HashSet<String>) {
    // `rewrite_bottom_up` visits every subterm; we only observe (returning each
    // node unchanged) and record any `Deref(Var(_))` root encountered.
    let _ = expr.rewrite_bottom_up(|node| {
        if let PureExpr::Deref(inner) = &node {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                out.insert(name.clone());
            }
        }
        node
    });
}

/// For a `Final`-carrier substitution value, return the variable name at its
/// leaf (`Final(Var(x))` → `x`, `Final(Deref(Var(x)))` → `x`).
fn advancement_root_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Final(inner) | PureExpr::Deref(inner) => advancement_root_name(inner),
        _ => None,
    }
}

/// True when `fact` contains a sort-invalid `Deref(Var(_, Int))` — a deref of a
/// scalar-sorted variable. These arise as Snapshot-deref-identity equality
/// artifacts and must not be asserted. (#682)
/// Repair the sort-invalid `Deref(Var(x, scalar))` subterm (a deref of a scalar)
/// by collapsing it to `Var(x, scalar)`. Arises when `*<snapshot>` of a value
/// snapshot is materialized as an equality fact: a `Snapshot<T>` / frozen scalar
/// derefs to itself identically, so the deref is a no-op on the value. Repairing
/// in place keeps the fact well-sorted AND preserves it as a solver assumption
/// (vs. dropping the whole fact, which starved the mut-borrow proof_assert solve
/// of atoms). (#682)
fn repair_scalar_var_deref(fact: PureExpr) -> PureExpr {
    fact.rewrite_bottom_up(|node| {
        if let PureExpr::Deref(inner) = &node {
            if matches!(
                inner.as_ref(),
                PureExpr::Var(_, Some(ExprSort::Int | ExprSort::Bool | ExprSort::Float(_)))
            ) {
                return inner.as_ref().clone();
            }
        }
        node
    })
}

fn is_simple_ident_local(name: &str) -> bool {
    // A renamed shadowed binding names a source binding too (D-237).
    crate::mir_analysis::binding_identity::is_binding_ident(name)
}

fn preserve_snapshot_substitution_value(expr: PureExpr) -> PureExpr {
    if transparent_adapter_inner(&expr).is_some() {
        preserve_transparent_adapter_view_witness(expr)
    } else {
        collapse_idempotent_views(expr)
    }
}

fn preserve_snapshot_fact_value(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| {
        if transparent_adapter_inner(&node).is_some() {
            preserve_transparent_adapter_view_witness(node)
        } else {
            node
        }
    })
}

/// Whether an effect fact of the body extraction reads memory a write may
/// have changed before the assertion (D-186): a store's write fact (under any
/// path guard, [`is_current_pointee_write_fact`]) about memory
/// `written_memory` names, or any read `*name` of memory
/// `memory_written_anywhere` names. Each such fact was stated at its own
/// program point, and the snapshot substitution reads its `*name` at the
/// assertion's.
fn reads_written_memory_at_another_state(
    fact: &PureExpr,
    written_memory: &HashSet<String>,
    memory_written_anywhere: &HashSet<String>,
) -> bool {
    if is_current_pointee_write_fact(fact, written_memory) {
        return true;
    }
    if memory_written_anywhere.is_empty() {
        return false;
    }
    let mut found = false;
    fact.rewrite_bottom_up(|node| {
        if let PureExpr::Deref(inner) = &node {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                found |= memory_written_anywhere.contains(name);
            }
        }
        node
    });
    found
}

/// Whether `fact` is a store's write fact `*name == v` or `name == v`
/// (either side) about memory `written_memory` names (D-185), under any path
/// guard `g ==> ..` and inside any conjunction (D-186): the side is the
/// memory AFTER the store, spelled as the entry value (`Deref(Var name)` is
/// `name_current`; a capture's name is its entry value), so the fact equates
/// the entry value with the written one.
fn is_current_pointee_write_fact(fact: &PureExpr, written_memory: &HashSet<String>) -> bool {
    match fact {
        PureExpr::BinOp(_, BinOp::Implies, conclusion) => {
            return is_current_pointee_write_fact(conclusion, written_memory);
        }
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            return is_current_pointee_write_fact(lhs, written_memory)
                || is_current_pointee_write_fact(rhs, written_memory);
        }
        _ => {}
    }
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = fact else {
        return false;
    };
    let names_written_memory = |side: &PureExpr| {
        let side = match side {
            PureExpr::Deref(inner) => inner.as_ref(),
            other => other,
        };
        matches!(side, PureExpr::Var(name, _) if written_memory.contains(name))
    };
    names_written_memory(lhs) || names_written_memory(rhs)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;

    use super::{preserve_snapshot_fact_value, preserve_snapshot_substitution_value};

    #[test]
    fn preserve_snapshot_substitution_value_keeps_copied_adapter_bridge() {
        let copied_intersection = PureExpr::LogicFnCall {
            name: "Copied".to_string(),
            args: vec![PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "xs".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "ys".to_string(),
                    None,
                )))],
            }],
        };

        let preserved = preserve_snapshot_substitution_value(copied_intersection);

        assert_eq!(
            preserved,
            PureExpr::View(Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "xs".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "ys".to_string(),
                    None,
                )))],
            })),
            "snapshot substitutions should keep a bridged view witness for copied adapters"
        );
    }

    #[test]
    fn preserve_snapshot_substitution_value_keeps_scalar_identity_collapsed() {
        let copied_int = PureExpr::LogicFnCall {
            name: "Copied".to_string(),
            args: vec![PureExpr::Int(5)],
        };

        let preserved = preserve_snapshot_substitution_value(copied_int);

        assert_eq!(preserved, PureExpr::Int(5));
    }

    #[test]
    fn preserve_snapshot_fact_value_keeps_copied_adapter_bridge() {
        let fact = PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "Copied".to_string(),
                args: vec![PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                        "xs".to_string(),
                        None,
                    )))),
                    method: "intersection".to_string(),
                    args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                        "ys".to_string(),
                        None,
                    )))],
                }],
            }),
        );

        let preserved = preserve_snapshot_fact_value(fact);

        assert_eq!(
            preserved,
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("result".to_string(), None)),
                trust_wp_core::formula::BinOp::Eq,
                Arc::new(PureExpr::View(Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                        "xs".to_string(),
                        None,
                    )))),
                    method: "intersection".to_string(),
                    args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                        "ys".to_string(),
                        None,
                    )))],
                }))),
            ),
            "snapshot facts should preserve the copied-adapter bridge for set relations"
        );
    }

    use trust_wp_core::formula::{BinOp, ExprSort};

    use super::{is_scalar_view_target, viewed_integer_comparison};

    fn int_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Int))
    }

    fn cmp(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }

    #[test]
    fn viewed_int_lt_var_var_wraps_both_sides() {
        let expr = cmp(int_var("i"), BinOp::Lt, int_var("n"));
        let viewed = viewed_integer_comparison(&expr).expect("scalar int Lt should view");
        assert_eq!(
            viewed,
            cmp(
                PureExpr::View(Arc::new(int_var("i"))),
                BinOp::Lt,
                PureExpr::View(Arc::new(int_var("n"))),
            )
        );
    }

    #[test]
    fn viewed_int_lt_var_literal_wraps_both_sides() {
        let expr = cmp(int_var("i"), BinOp::Le, PureExpr::Int(8));
        let viewed = viewed_integer_comparison(&expr).expect("int literal RHS should view");
        assert_eq!(
            viewed,
            cmp(
                PureExpr::View(Arc::new(int_var("i"))),
                BinOp::Le,
                PureExpr::View(Arc::new(PureExpr::Int(8))),
            )
        );
    }

    #[test]
    fn viewed_int_returns_none_for_non_comparison_ops() {
        let expr = cmp(int_var("i"), BinOp::Add, int_var("n"));
        assert!(viewed_integer_comparison(&expr).is_none());
    }

    #[test]
    fn viewed_int_returns_none_for_unsorted_var() {
        // Unsorted Var is rejected: we cannot guarantee it is a scalar int.
        let expr = cmp(
            PureExpr::Var("i".to_string(), None),
            BinOp::Lt,
            PureExpr::Var("n".to_string(), None),
        );
        assert!(viewed_integer_comparison(&expr).is_none());
    }

    #[test]
    fn viewed_int_returns_none_for_bool_var() {
        let expr = cmp(
            PureExpr::Var("b".to_string(), Some(ExprSort::Bool)),
            BinOp::Eq,
            PureExpr::Var("b2".to_string(), Some(ExprSort::Bool)),
        );
        assert!(viewed_integer_comparison(&expr).is_none());
    }

    #[test]
    fn viewed_int_idempotent_on_already_viewed() {
        // View(i) cmp View(n) — already in view form; both sides count as
        // scalar view targets so the function still emits a view form
        // (without double-wrapping, since `View(View(_))` is idempotent at the
        // encoder level and `view_or_self` preserves an existing View node).
        let expr = cmp(
            PureExpr::View(Arc::new(int_var("i"))),
            BinOp::Lt,
            PureExpr::View(Arc::new(int_var("n"))),
        );
        let viewed = viewed_integer_comparison(&expr).expect("view form is a valid target");
        assert_eq!(viewed, expr);
    }

    #[test]
    fn is_scalar_view_target_accepts_int_var_and_int_literal() {
        assert!(is_scalar_view_target(&int_var("i")));
        assert!(is_scalar_view_target(&PureExpr::Int(42)));
        assert!(is_scalar_view_target(&PureExpr::View(Arc::new(int_var(
            "i"
        )))));
    }

    #[test]
    fn is_scalar_view_target_rejects_other_shapes() {
        assert!(!is_scalar_view_target(&PureExpr::Var(
            "x".to_string(),
            None
        )));
        assert!(!is_scalar_view_target(&PureExpr::Var(
            "b".to_string(),
            Some(ExprSort::Bool)
        )));
        assert!(!is_scalar_view_target(&cmp(
            int_var("i"),
            BinOp::Lt,
            int_var("n")
        )));
    }
}
