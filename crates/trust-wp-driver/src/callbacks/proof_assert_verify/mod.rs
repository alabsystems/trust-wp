// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof assertion verification helpers.
//!
//! Contains `ProofAssertSetup`, `PreparedAssertion`, `build_proof_assert_setup`,
//! and `prepare_proof_assert`. The inline verification loop in `verification.rs`
//! calls these helpers per-function (Phase 4, #1572).

mod mapping_closure;
mod setup;

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

pub(super) use mapping_closure::{
    inline_bool_mapping_closure_calls, instantiate_mapping_closure_ground,
    instantiate_mapping_closure_ground_from_expr, retain_relevant_mapping_closure_foralls,
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;
pub(super) use setup::build_proof_assert_setup;
use tracing::debug;
use trust_wp_core::{
    closure::ClosureCaptureInfo,
    contract_parser::parse_contract_body,
    formula::{
        elaborate::{
            first_final_held_through_a_reference_parameter,
            first_final_of_a_value_not_named_as_a_borrow,
        },
        BinOp, PureExpr,
    },
    logic::LogicMode,
};
use trust_wp_driver::StdSpec;

pub(super) use super::proof_assert_snapshot_facts::{
    collect_deref_snapshot_aliases, derive_snapshot_deref_alias_substitutions,
    substitute_assertion_final_carriers, substitute_snapshot_facts,
};
use super::{
    super::contracts::FunctionContract,
    contract_rewrite::rewrite_logic_method_calls_expr,
    helpers::contains_mutating_call_effect,
    iterator_spec_rewrite::rewrite_iterator_spec_expr,
    logic_fn_scope::normalize_logic_fn_names,
    parsing::get_arg_names_from_def_id,
    proof_assert_extract::{
        apply_constructor_equality_substitutions,
        apply_constructor_equality_substitutions_to_facts, apply_type_and_field_rewrites,
        collapse_idempotent_views, constructor_equality_to_tester_selector_facts,
        get_arg_names_for_proof_assert_body, normalize_old_constructor_equality_facts,
        normalize_scalar_proof_assert_boundary, normalize_seq_final_fact_views,
        normalize_view_fn_calls, preserve_transparent_adapter_view_witness,
        reduce_concrete_constructor_method_calls, reduce_concrete_matches,
        simplify_proof_assert_expr, synthesize_constructor_equalities,
        synthesize_ground_equality_substitution_facts,
    },
    proof_assert_leading_calls::collect_leading_proof_assert_assumptions,
    proof_assert_snapshot::AssertionSnapshot,
    proof_assert_wiring::apply_closure_wiring,
    type_invariants::build_type_invariant_clauses,
};

/// Shared setup for preparing individual `proof_assert` checks.
pub(super) struct ProofAssertSetup<'a> {
    fn_preconditions: HashMap<LocalDefId, Vec<PureExpr>>,
    const_item_substitutions: HashMap<String, PureExpr>,
    contract_by_local: HashMap<LocalDefId, &'a FunctionContract>,
    logic_fn_path_map: HashMap<String, String>,
    logic_method_names: HashSet<String>,
    pub(super) user_specs: HashMap<DefId, StdSpec>,
}

/// Fully prepared proof assertion ready for solver dispatch.
pub(super) struct PreparedAssertion {
    pub(super) preconditions: Vec<PureExpr>,
    pub(super) ensures: Vec<PureExpr>,
    pub(super) return_expr: Option<PureExpr>,
    pub(super) mode_overrides: Option<Vec<LogicMode>>,
    pub(super) closure_capture_infos: Vec<ClosureCaptureInfo>,
    pub(super) has_mutating_call_effect: bool,
    pub(super) is_contractless: bool,
    /// Whether the containing function carries an explicit user-authored
    /// `#[requires(false)]`. Such a function is provably uncallable, so a
    /// vacuous `proof_assert!` inside it is vacuously discharged by Creusot
    /// semantics and must be accepted rather than counted as an error. Keyed to
    /// the PRECONDITION position only (does NOT credit `#[ensures(false)]`).
    pub(super) containing_requires_false: bool,
    pub(super) fn_path: String,
    pub(super) loc: String,
    pub(super) expr_text: String,
}

pub(super) fn rewrite_iterator_spec_proof_assert_clauses(
    preconditions: &mut [PureExpr],
    ensures: &mut [PureExpr],
) {
    for expr in preconditions {
        *expr = rewrite_iterator_spec_expr(expr);
    }
    for expr in ensures {
        *expr = rewrite_iterator_spec_expr(expr);
    }
}

pub(super) fn substitute_assertion_names(
    assertion: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
    names: &HashSet<String>,
) -> PureExpr {
    if substitutions.is_empty() || names.is_empty() {
        return assertion.clone();
    }

    let filter: HashSet<&str> = names.iter().map(String::as_str).collect();
    assertion.substitute_filtered(&filter, substitutions)
}

pub(super) fn preserve_transparent_adapter_views(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(preserve_transparent_adapter_view_witness)
}

fn is_stale_mutation_alias_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_self_final_alias(lhs, rhs) || is_self_final_alias(rhs, lhs)
}

/// Detect an assumed fact whose substituted form contains a literal-vs-literal
/// FALSE equality (e.g. `42 == 43`, or `guard ==> (42 == 43)`).
///
/// Such facts are substitution-corrupt: the cutoff-time name substitution map
/// keys on SOURCE names, so when a binding is SHADOWED (two `let x` bindings,
/// or an `if let Some(x)` pattern followed by a later `let (x, ..)`), a fact
/// recorded against the FIRST binding (`*x == 43`) gets rewritten with the
/// SECOND binding's value (`42`), manufacturing `42 == 43`. Asserting it (even
/// guarded) collapses the base premises to UNSAT on the guard's path and trips
/// the vacuity guard (ghost/ghost_map). Dropping an assumption is always
/// fail-closed: it can only lose provability, never soundness.
fn is_substitution_falsified_fact(expr: &PureExpr) -> bool {
    fn contains_positive_literal_false(expr: &PureExpr) -> bool {
        match expr {
            PureExpr::Bool(false) => true,
            PureExpr::BinOp(lhs, BinOp::Eq, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                (PureExpr::Int(a), PureExpr::Int(b)) => a != b,
                (PureExpr::Bool(a), PureExpr::Bool(b)) => a != b,
                _ => false,
            },
            PureExpr::BinOp(lhs, BinOp::Ne, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                (PureExpr::Int(a), PureExpr::Int(b)) => a == b,
                (PureExpr::Bool(a), PureExpr::Bool(b)) => a == b,
                _ => false,
            },
            // A conjunction is false when either side is; an implication is
            // corrupt when its CONSEQUENT is a literal false (the manufactured
            // `guard ==> (42 == 43)` shape reduces to `!guard`, a path-negation
            // fact the extraction never legitimately emits through this
            // channel).
            PureExpr::BinOp(lhs, BinOp::And, rhs) => {
                contains_positive_literal_false(lhs) || contains_positive_literal_false(rhs)
            }
            PureExpr::BinOp(_, BinOp::Implies, rhs) => contains_positive_literal_false(rhs),
            _ => false,
        }
    }
    contains_positive_literal_false(expr)
}

fn is_stale_closure_capture_env_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_stale_double_final_capture_alias(lhs, rhs) || is_stale_double_final_capture_alias(rhs, lhs)
}

fn is_stale_double_final_capture_alias(capture_candidate: &PureExpr, rhs: &PureExpr) -> bool {
    let PureExpr::Var(_, _) = capture_candidate else {
        return false;
    };
    let PureExpr::LogicFnCall { name, args } = rhs else {
        return false;
    };
    if name != "__trust_wp_tuple1" {
        return false;
    }
    args.iter().any(contains_nested_final)
}

fn contains_nested_final(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Final(inner) => {
            matches!(inner.as_ref(), PureExpr::Final(_)) || contains_nested_final(inner)
        }
        PureExpr::BinOp(lhs, _, rhs) => contains_nested_final(lhs) || contains_nested_final(rhs),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::View(inner) => contains_nested_final(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_nested_final(cond)
                || contains_nested_final(then_expr)
                || contains_nested_final(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            triggers.iter().flatten().any(contains_nested_final) || contains_nested_final(body)
        }
        PureExpr::Match { scrutinee, arms } => {
            contains_nested_final(scrutinee)
                || arms.iter().any(|arm| contains_nested_final(&arm.body))
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_nested_final(receiver) || args.iter().any(contains_nested_final)
        }
        PureExpr::Closure { body, .. } => contains_nested_final(body),
        PureExpr::Let { value, body, .. } => {
            contains_nested_final(value) || contains_nested_final(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_nested_final(assumption) || contains_nested_final(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_nested_final(obligation) || contains_nested_final(body)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

fn is_self_final_alias(pre: &PureExpr, post: &PureExpr) -> bool {
    let PureExpr::Var(pre_name, _) = pre else {
        return false;
    };
    let PureExpr::Final(inner) = post else {
        return false;
    };
    matches!(inner.as_ref(), PureExpr::Var(post_name, _) if post_name == pre_name)
}

fn derive_has_mutating_call_effect(
    snapshot_has_mutating_call_effect: bool,
    leading_has_mutating_call_effect: bool,
    call_effect_expr: Option<&PureExpr>,
) -> bool {
    snapshot_has_mutating_call_effect
        || leading_has_mutating_call_effect
        || call_effect_expr.is_some_and(contains_mutating_call_effect)
}

/// Source names of by-reference parameters whose ENTRY facts a loop has
/// invalidated by the time `pa` is reached (D-38).
///
/// `#[requires((*a)@ == 0)]` describes the pointee at entry, and the encoder
/// names the entry pointee and the current pointee with the SAME symbol
/// (`a_current`). A straight-line write is walked by the extraction, which
/// records the written value against that symbol; a write inside a loop body is
/// not walked at all, so left in place the entry fact survives to an assertion
/// after the loop and discharges `proof_assert!((*a)@ == 0)` against a pointee
/// the loop has already set to 7 (s53_pa_stale_param_pointee_after_loop.rs).
///
/// Reporting a name only removes premises from the assertion's context, so an
/// imprecise answer costs provability, never soundness. An assertion with no
/// recorded program point asks the question with none, and every parameter any
/// loop writes is reported.
fn loop_invalidated_param_names(
    tcx: TyCtxt<'_>,
    pa: &crate::proof_assert::ProofAssert,
) -> crate::mir_analysis::InvalidatedEntryNames {
    let Some(body_with_facts) = crate::callbacks::try_get_body_with_context(tcx, pa.containing_fn)
    else {
        return crate::mir_analysis::InvalidatedEntryNames::default();
    };
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    let at = pa.location.map(|location| location.block);
    let invalidated = crate::mir_analysis::params_invalidated_by_loops(body, at);
    if invalidated.is_empty() {
        return crate::mir_analysis::InvalidatedEntryNames::default();
    }
    let def_id = pa.containing_fn.to_def_id();
    let arg_names = get_arg_names_from_def_id(tcx, def_id).unwrap_or_default();
    crate::mir_analysis::name_invalidated_args(
        &invalidated,
        tcx.is_closure_like(def_id),
        &arg_names,
    )
}

/// The parameters whose own storage may be written before the assertion
/// ([`crate::mir_analysis::param_writes_before`], D-241): `whole` names those
/// a write may change as a whole (or that have no name of their own, a
/// closure's environment), `fields` those only some of whose first-level
/// fields are written, with each written field's index and name.
#[derive(Debug, Default)]
pub(super) struct WrittenParams {
    whole: crate::mir_analysis::InvalidatedEntryNames,
    fields: HashMap<String, Vec<(usize, Option<String>)>>,
    /// The parameters a store reaches, not only a `&mut` borrow.
    stored: HashSet<String>,
}

impl WrittenParams {
    /// Whether any part of the parameter `name` may be written.
    fn names(&self, name: &str) -> bool {
        self.whole.invalidates(std::iter::once(name)) || self.fields.contains_key(name)
    }

    /// Whether `fact` reads a part of a parameter that may be written: the
    /// parameter whole, or a written field. A read of an unwritten field
    /// (`p.a` after `set7(&mut p.b)`) is still the entry value.
    fn stale(&self, fact: &PureExpr) -> bool {
        if self
            .whole
            .invalidates(fact.free_vars().iter().map(String::as_str))
        {
            return true;
        }
        self.fields.iter().any(|(name, written)| {
            let reads_unwritten_field = |expr: &PureExpr| {
                use trust_wp_core::formula::internal::tuple_lowering::{
                    tuple_field_logic_fn_index, NAMED_FIELD_LOGIC_FN_PREFIX,
                };
                let PureExpr::LogicFnCall {
                    name: accessor,
                    args,
                } = expr
                else {
                    return false;
                };
                if !matches!(args.as_slice(), [PureExpr::Var(var, _)] if var == name) {
                    return false;
                }
                if let Some(index) = tuple_field_logic_fn_index(accessor) {
                    return written
                        .iter()
                        .all(|(written_index, _)| *written_index != index);
                }
                if let Some(field) = accessor.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
                    return written.iter().all(|(_, written_name)| {
                        written_name
                            .as_deref()
                            .is_some_and(|written_name| written_name != field)
                    });
                }
                false
            };
            let masked = fact.rewrite_bottom_up_prune(
                |expr| !reads_unwritten_field(expr),
                |expr| {
                    if reads_unwritten_field(&expr) {
                        PureExpr::Bool(true)
                    } else {
                        expr
                    }
                },
            );
            masked.free_vars().contains(name)
        })
    }

    /// Stop naming a SCALAR parameter whose binding at the assertion is its
    /// own prophecy (`x -> ^x`, what the walk records for a `&mut x` a call
    /// or a closure capture hands back) and that no store reaches before the
    /// assertion. There the current value is `^x`, a symbol of its own, and
    /// `x` in an entry fact, and in the callee's fact about the borrow's
    /// current value, is the entry value the fact is about. Past a store
    /// (`x = 5; inc(&mut x)`) the walk still names the borrowed place `x`,
    /// whose current value at the borrow is the stored one, not the entry
    /// value. A datatype parameter is not exempt: the encoder collapses `^p`
    /// of a datatype value onto `p`
    /// (s48_uncontracted_helper_param_field_direct.rs).
    fn keep_scalars_advanced_to_their_prophecy(
        &mut self,
        substitutions: &HashMap<String, PureExpr>,
    ) {
        fn own_prophecy(name: &str, value: &PureExpr, under_final: bool) -> bool {
            match value {
                PureExpr::Var(bound, sort) => {
                    under_final
                        && bound == name
                        && matches!(
                            sort,
                            Some(
                                trust_wp_core::formula::ExprSort::Int
                                    | trust_wp_core::formula::ExprSort::Bool
                                    | trust_wp_core::formula::ExprSort::Float(_)
                            )
                        )
                }
                PureExpr::Final(inner) => own_prophecy(name, inner, true),
                _ => false,
            }
        }
        let stored = &self.stored;
        let advanced = |name: &String| {
            !stored.contains(name)
                && substitutions
                    .get(name)
                    .is_some_and(|value| own_prophecy(name, value, false))
        };
        self.whole.params.retain(|name| !advanced(name));
        self.fields.retain(|name, _| !advanced(name));
    }

    /// Stop naming the parameters in `names`, whose entry value has a
    /// symbol of its own (D-241).
    fn forget(&mut self, names: &HashSet<String>) {
        self.whole.params.retain(|name| !names.contains(name));
        self.fields.retain(|name, _| !names.contains(name));
    }

    /// Drop the top-level conjuncts of `facts` that [`Self::stale`] names.
    /// Returns how many were dropped.
    fn drop_stale_facts(&self, facts: &mut Vec<PureExpr>) -> usize {
        fn split_conjuncts(expr: &PureExpr, out: &mut Vec<PureExpr>) {
            if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
                split_conjuncts(lhs, out);
                split_conjuncts(rhs, out);
            } else {
                out.push(expr.clone());
            }
        }
        if !facts.iter().any(|fact| self.stale(fact)) {
            return 0;
        }
        let mut dropped = 0;
        let mut kept = Vec::with_capacity(facts.len());
        for fact in facts.drain(..) {
            if !self.stale(&fact) {
                kept.push(fact);
                continue;
            }
            let mut conjuncts = Vec::new();
            split_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                if self.stale(&conjunct) {
                    dropped += 1;
                } else {
                    kept.push(conjunct);
                }
            }
        }
        *facts = kept;
        dropped
    }
}

/// [`WrittenParams`] at the assertion of `pa`.
fn written_params(tcx: TyCtxt<'_>, pa: &crate::proof_assert::ProofAssert) -> WrittenParams {
    let Some(body_with_facts) = crate::callbacks::try_get_body_with_context(tcx, pa.containing_fn)
    else {
        return WrittenParams::default();
    };
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    let writes = crate::mir_analysis::param_writes_before(body, pa.location);
    if writes.is_empty() {
        return WrittenParams::default();
    }
    let def_id = pa.containing_fn.to_def_id();
    let is_closure = tcx.is_closure_like(def_id);
    let first_param = if is_closure { 2 } else { 1 };
    let arg_names = get_arg_names_from_def_id(tcx, def_id).unwrap_or_default();
    let mut written = WrittenParams::default();
    for (local, write) in writes {
        let name = local
            .as_usize()
            .checked_sub(first_param)
            .and_then(|index| arg_names.get(index));
        let Some(name) = name else {
            written.whole.unnamed = true;
            continue;
        };
        if write.stored {
            written.stored.insert(name.clone());
        }
        if write.whole {
            written.whole.params.insert(name.clone());
            continue;
        }
        let field_names: Vec<Option<String>> = match body.local_decls[local].ty.kind() {
            rustc_middle::ty::TyKind::Adt(adt, _) if adt.is_struct() => adt
                .non_enum_variant()
                .fields
                .iter()
                .map(|field| Some(field.name.to_string()))
                .collect(),
            _ => Vec::new(),
        };
        written.fields.insert(
            name.clone(),
            write
                .fields
                .iter()
                .map(|&index| (index, field_names.get(index).cloned().flatten()))
                .collect(),
        );
    }
    written
}

/// The first name the assertion reads whose local a write through a holder
/// of its borrow may have changed before the assertion
/// ([`crate::mir_analysis::deref_store_staleness::first_name_written_through_a_holder`]).
fn name_read_after_a_holder_write(
    tcx: TyCtxt<'_>,
    pa: &crate::proof_assert::ProofAssert,
    assertion: &PureExpr,
) -> Option<String> {
    let location = pa.location?;
    let body_with_facts = crate::callbacks::try_get_body_with_context(tcx, pa.containing_fn)?;
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    let names = assertion.free_vars();
    crate::mir_analysis::deref_store_staleness::first_name_written_through_a_holder(
        tcx, body, location, &names,
    )
}

/// The first name the assertion reads at a state this lane cannot give its
/// current value (D-185), with why.
///
/// The encoders name the memory behind a reference by ONE symbol, the entry
/// pointee (`Deref(Var x)` is `x_current`), and a `#[requires]` speaks of it.
/// An assertion reads the memory as it is at the assertion's program point,
/// so a read of memory a write may have changed before that point is the
/// entry value unless the program-point substitution replaces it with the
/// value the walk recorded: `*x.m = 5; proof_assert!(*x.m == 0)` under
/// `#[requires(*x.m == 0)]` read the precondition back. Only a whole-pointee
/// read `*x` whose every preceding write is a store `*x = v` through `x`
/// itself has a recorded value (the `*x` substitution); a read through a held
/// borrow, a field, an alias, or after a call or drop handed the borrow has
/// none, and is refused. A read under `old(..)` or `^..` names the entry or
/// the final value and is not a current read.
fn name_read_at_an_unknown_current_state(
    tcx: TyCtxt<'_>,
    pa: &crate::proof_assert::ProofAssert,
    assertion: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
) -> Option<(String, &'static str)> {
    use crate::mir_analysis::deref_store_staleness::{
        names_read_through_written_memory, CurrentState,
    };
    let location = pa.location?;
    let body_with_facts = crate::callbacks::try_get_body_with_context(tcx, pa.containing_fn)?;
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    let current_reads = assertion.rewrite_bottom_up_prune(
        |expr| !matches!(expr, PureExpr::Old(_) | PureExpr::Final(_)),
        |expr| match expr {
            PureExpr::Old(_) | PureExpr::Final(_) => PureExpr::Bool(true),
            other => other,
        },
    );
    let read_names = current_reads.free_vars();
    if read_names.is_empty() {
        return None;
    }
    let states = names_read_through_written_memory(tcx, body, location);
    // A raw pointer's own value is its address, which no write through it
    // changes: only a dereference of it reads memory (`p1 != p2` compares
    // two addresses).
    let mut reads_its_memory: HashSet<String> = HashSet::new();
    let mut read_only_through_a_dereference: HashSet<String> = HashSet::new();
    for debug in &body.var_debug_info {
        let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        if place.projection.is_empty() && body.local_decls[place.local].ty.is_raw_ptr() {
            read_only_through_a_dereference.insert(debug.name.to_string());
        } else {
            reads_its_memory.insert(debug.name.to_string());
        }
    }
    // A name one binding of which reads memory by its own name is read so.
    read_only_through_a_dereference.retain(|name| !reads_its_memory.contains(name));
    let read_through_a_pointer = |name: &str| {
        let mut found = false;
        current_reads.rewrite_bottom_up_prune(
            |expr| !matches!(expr, PureExpr::Deref(_)),
            |expr| {
                if let PureExpr::Deref(inner) = &expr {
                    found |= inner.free_vars().contains(name);
                }
                expr
            },
        );
        found
    };
    let mut names: Vec<&String> = read_names
        .iter()
        .filter(|n| states.contains_key(*n))
        .filter(|n| !read_only_through_a_dereference.contains(*n) || read_through_a_pointer(n))
        .collect();
    names.sort();
    for name in names {
        match states[name] {
            CurrentState::Unwritten => {}
            CurrentState::Untracked => {
                return Some((
                    name.clone(),
                    "the memory it reads is not the value of ONE write the walk records: \
                     two writes (or a write and the entry value) join before the assertion, a \
                     back edge carries a write round, or a write goes through a held borrow, a \
                     field, an alias, or a call or drop handed the borrow",
                ));
            }
            CurrentState::DirectPlaceStores => {
                let rebound = substitutions.get(name).is_some_and(
                    |value| !matches!(value, PureExpr::Var(bound, _) if bound == name),
                );
                if !rebound {
                    return Some((name.clone(), "the stores to it recorded no value for it"));
                }
            }
            CurrentState::DirectPointeeStores => {
                let is_whole_pointee = |expr: &PureExpr| {
                    matches!(expr, PureExpr::Deref(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(var, _) if var == name))
                };
                let other_reads = current_reads.rewrite_bottom_up_prune(
                    |expr| !is_whole_pointee(expr),
                    |expr| {
                        if is_whole_pointee(&expr) {
                            PureExpr::Bool(true)
                        } else {
                            expr
                        }
                    },
                );
                let recorded = substitutions.contains_key(&format!("*{name}"));
                if !recorded || other_reads.free_vars().contains(name) {
                    return Some((
                        name.clone(),
                        "it is read other than as the whole pointee `*name` the stores \
                         through it record, or no stored value was recorded for it",
                    ));
                }
            }
        }
    }
    None
}

/// Source names of parameters the body may have RE-BOUND by the time the
/// assertion of `snapshot` is reached, whose entry facts this lane must not
/// read (D-140).
///
/// This lane equates a parameter's name with its binding at the assertion
/// (the substitution fact `x == v`), and a `#[requires]` over that name is a
/// fact about its ENTRY value. Once the body re-binds the parameter, the two
/// together make the entry fact a premise about `v`:
///
/// - a hand-off (a `Drop`, or a call whose drop glue may write) re-binds every
///   local its glue reaches to a fresh symbol, a by-value parameter, a
///   `&mut` parameter's pointee and a field alike, so `proof_assert!(x@ == 0)`
///   under `#[requires(x@ == 0)]` would be proved after `G::drop` stored 5
///   (proof_assert_entry_requires_pins_param_after_drop_glue.rs,
///   proof_assert_param_entry_requires_revived_by_drop_glue.rs). Which
///   hand-offs re-bind is asked of every one that may run before the
///   assertion, which names every parameter the walk re-binds and possibly
///   more;
/// - a plain write re-binds a BY-VALUE parameter to the value written
///   (`x = y`, `x = any()`), and the entry fact then constrains `y` or the
///   call's result (proof_assert_param_rebind_reads_entry_requires.rs). That
///   is read from the walk's own substitution, the map that emits `x == v`.
///   A binding the walk keeps naming by the parameter itself (the parameter,
///   its view, or the prophecy `^x` a `&mut x` call leaves, whose fact this
///   lane does not emit) is no re-binding. Not asked, and so not withdrawn:
///   a `&mut` parameter's pointee written by a plain store, a reference
///   parameter re-bound, a pattern parameter's binding and a store through a
///   `Box` parameter, whose entry facts are read beside the new binding
///   (proof_assert_mut_param_pointee_store_reads_entry_requires.rs,
///   proof_assert_ref_param_rebind_reads_entry_requires.rs,
///   proof_assert_pattern_or_box_param_write_reads_entry_requires.rs). For
///   memory behind a reference (a `&mut` parameter's pointee, a `Box`'s
///   contents) D-185 names the entry and the current value apart instead:
///   the entry facts stay, and the current value is no fact about them
///   ([`name_read_at_an_unknown_current_state`]).
///
/// Reporting a name only removes premises, so an over-report costs
/// provability, never soundness. An assertion with no recorded program point
/// asks the hand-off question with none, and every parameter any hand-off
/// re-binds is reported.
pub(super) fn rebound_param_names(
    tcx: TyCtxt<'_>,
    snapshot: &AssertionSnapshot,
) -> crate::mir_analysis::InvalidatedEntryNames {
    let pa = &snapshot.assertion;
    let Some(body_with_facts) = crate::callbacks::try_get_body_with_context(tcx, pa.containing_fn)
    else {
        return crate::mir_analysis::InvalidatedEntryNames::default();
    };
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    let def_id = pa.containing_fn.to_def_id();
    let is_closure = tcx.is_closure_like(def_id);
    let arg_names = get_arg_names_from_def_id(tcx, def_id).unwrap_or_default();
    let at = pa.location.map(|location| location.block);
    let mut names = crate::mir_analysis::name_invalidated_args(
        &crate::mir_analysis::params_rebound_by_handoffs(tcx, body, at),
        is_closure,
        &arg_names,
    );
    let first_param = if is_closure { 2 } else { 1 };
    for (index, name) in arg_names.iter().enumerate() {
        let local = rustc_middle::mir::Local::from_usize(first_param + index);
        if local.as_usize() > body.arg_count
            || matches!(
                body.local_decls[local].ty.kind(),
                rustc_middle::ty::TyKind::Ref(..) | rustc_middle::ty::TyKind::RawPtr(..)
            )
        {
            continue;
        }
        if snapshot
            .substitutions
            .get(name)
            .is_some_and(|value| !names_its_own_binding(name, value))
        {
            names.params.insert(name.clone());
        }
    }
    names
}

/// Whether the substitution value `value` of `name` still names `name`'s own
/// binding: the parameter itself, its view or deref, or its prophecy `^name`.
pub(super) fn names_its_own_binding(name: &str, value: &PureExpr) -> bool {
    match value {
        PureExpr::Var(bound, _) => bound == name,
        PureExpr::View(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            names_its_own_binding(name, inner)
        }
        _ => false,
    }
}

/// Drop the facts that name a parameter in `stale` (one a loop invalidated,
/// or one the body re-bound). A fact is judged by its top-level `&&`
/// conjuncts: `x@ == 1 && y@ == 2` with `x` stale keeps `y@ == 2`, which a
/// conjunction implies on its own; a conjunct under an `||`, an implication
/// or an `if` guards its branch and goes whole. Returns how many conjuncts
/// were dropped.
pub(super) fn drop_stale_param_facts(
    facts: &mut Vec<PureExpr>,
    stale: &crate::mir_analysis::InvalidatedEntryNames,
) -> usize {
    fn split_conjuncts(expr: &PureExpr, out: &mut Vec<PureExpr>) {
        if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
            split_conjuncts(lhs, out);
            split_conjuncts(rhs, out);
        } else {
            out.push(expr.clone());
        }
    }
    let is_stale = |fact: &PureExpr| stale.invalidates(fact.free_vars().iter().map(String::as_str));
    if stale.is_empty() || !facts.iter().any(is_stale) {
        return 0;
    }
    let mut dropped = 0;
    let mut kept = Vec::with_capacity(facts.len());
    for fact in facts.drain(..) {
        if !is_stale(&fact) {
            kept.push(fact);
            continue;
        }
        let mut conjuncts = Vec::new();
        split_conjuncts(&fact, &mut conjuncts);
        for conjunct in conjuncts {
            if is_stale(&conjunct) {
                dropped += 1;
            } else {
                kept.push(conjunct);
            }
        }
    }
    *facts = kept;
    dropped
}

/// Prepare a single `proof_assert` for verification.
///
/// Returns:
/// - `Ok(Some(..))` when preparation succeeds,
/// - `Ok(None)` when the assertion is trusted and intentionally skipped,
/// - `Err(())` when preparation fails and should count as an error.
pub(super) fn prepare_proof_assert(
    tcx: TyCtxt<'_>,
    snapshot: &AssertionSnapshot,
    setup: &ProofAssertSetup<'_>,
    ctx: &super::verification_context::ProofAssertContext<'_>,
    local_crate_name: &str,
) -> Result<Option<PreparedAssertion>, ()> {
    let pa = &snapshot.assertion;
    let fn_path_local = tcx.def_path_str(pa.containing_fn);
    let fn_path = format!("{local_crate_name}::{fn_path_local}");
    let loc = tcx.sess.source_map().span_to_diagnostic_string(pa.span);

    if pa.trusted {
        if ctx.verbose {
            eprintln!("trust-wp: proof_assert in {fn_path} trusted (skipped)");
        }
        return Ok(None);
    }

    let Some(expr_text) = pa.expr_text.as_deref() else {
        if ctx.verbose {
            eprintln!("trust-wp: proof_assert in {fn_path} has no expression text");
        }
        return Err(());
    };

    // Parse the assertion expression.
    // Use parse_contract_body to support multi-statement proof_assert! blocks
    // (Creusot pattern: `lemma_call(); assertion_expr`). Leading statements
    // are parsed and discarded; the trailing expression is the assertion.
    let mut assertion = match parse_contract_body(expr_text) {
        Ok(expr) => expr,
        Err(e) => {
            crate::result_protocol_state::record_parse_error();
            eprintln!("trust-wp: error: failed to parse proof_assert '{expr_text}': {e}");
            return Err(());
        }
    };

    // Creusot type-checks the assertion body as `bool` (`proof_assert! { 1 }`
    // is `error[E0308]: mismatched types`). A body that is structurally not a
    // boolean is a frontend refusal, never an obligation to hand to the solver.
    if assertion.is_definitely_non_boolean() {
        crate::result_protocol_state::record_parse_error();
        eprintln!(
            "trust-wp: frontend diagnostic: mismatched types in proof_assert \
             '{expr_text}' at {loc}: expected `bool`, found a non-boolean expression"
        );
        return Err(());
    }

    // The assertion names bindings by source name; a name the body binds
    // more than once means the binding visible at the assertion, and every
    // later reader keys on that binding's own name (D-237).
    assertion = match crate::mir_analysis::binding_identity::resolve_proof_assert_bindings(
        tcx, pa, &assertion,
    ) {
        Ok(resolved) => resolved,
        Err(name) => {
            eprintln!(
                "trust-wp: proof_assert in {fn_path} error: `{name}` is bound more than once in \
                 the body and the binding the assertion names cannot be told (fail-closed)"
            );
            return Err(());
        }
    };

    // Normalize `view(expr)` → View(expr) and `final_value(expr)` → Final(expr).
    // When proof_assert! is inside ghost!, the ghost macro's preprocess_view_syntax
    // transforms `expr@` to `view(expr)` at the token level, causing the contract
    // parser to produce LogicFnCall instead of View. (#2209)
    assertion = normalize_view_fn_calls(assertion);
    assertion = collapse_idempotent_views(assertion);

    // `^x[0]`, `^x.m`, `^(^x).m`, `^(if c { x } else { x }).m` written in the
    // assertion read the final value of a borrow the value holds, which its
    // holder decides; the encoder would read each as the place the outer
    // borrow is left with (D-129). Read here, before the driver substitutes
    // its own images of reborrowed places into the assertion.
    if let Some(why) = first_final_of_a_value_not_named_as_a_borrow(
        &assertion,
        &trust_wp_core::logic::final_reads::FinalReaders::default(),
    ) {
        eprintln!(
            "trust-wp: proof_assert in {fn_path} error: final value refused (fail-closed): {why}"
        );
        return Err(());
    }

    // `^*x`, `^x.m`, `^x[0]` of a reference PARAMETER `x` reads the final
    // value of a borrow `x`'s referent holds, which its holder decides after
    // the call; `*x` of `x: &mut &mut i32` is a name's dereference to the
    // text guard above. The parameter's type decides it, as it does for a
    // clause of the contract (D-183).
    {
        let def_id = pa.containing_fn.to_def_id();
        let names = get_arg_names_from_def_id(tcx, def_id).unwrap_or_default();
        let signature = crate::mir_analysis::contract_signature(tcx, def_id, &names);
        if let Some(why) = first_final_held_through_a_reference_parameter(
            &assertion,
            &|name| signature.reference(name),
            signature.final_readers(),
        ) {
            eprintln!(
                "trust-wp: proof_assert in {fn_path} error: final value refused (fail-closed): \
                 {why}"
            );
            return Err(());
        }
    }

    // A local whose borrow a tuple, struct, enum or array holds is written
    // by a store through the holder, and by a call or drop handed it, which
    // this lane does not carry to the local: the assertion would read it at
    // its value from before the write, as the result, postcondition and
    // call-precondition lanes did (D-127 item 5, D-129).
    if let Some(name) = name_read_after_a_holder_write(tcx, pa, &assertion) {
        eprintln!(
            "trust-wp: proof_assert in {fn_path} error: stale read refused (fail-closed): `{name}` \
             is read after a write through a value that holds a borrow of it, which this lane \
             does not apply to `{name}`"
        );
        return Err(());
    }

    // The assertion reads memory as it is at its program point; memory a
    // write may have changed is read at its entry value unless the walk
    // recorded the value the write left (D-185).
    if let Some((name, why)) =
        name_read_at_an_unknown_current_state(tcx, pa, &assertion, &snapshot.substitutions)
    {
        eprintln!(
            "trust-wp: proof_assert in {fn_path} error: stale read refused (fail-closed): `{name}` \
             is read at the assertion, but {why}; its current value is not known to this lane"
        );
        return Err(());
    }

    // Normalize module-qualified logic function names in the assertion.
    // The contract parser preserves paths like `x::transparent()`, but
    // logic functions are registered by short name (`transparent`). Without
    // normalization, the SMT encoder creates a free placeholder function
    // instead of finding the registered axiomatized function. (#746)
    // Resolve colliding logic-function names in the containing fn's scope.
    assertion = crate::logic::identity::resolve_logic_fn_paths_in_scope(
        tcx,
        pa.containing_fn.to_def_id(),
        &assertion,
        crate::logic::identity::ClausePosition::Body,
        &crate::logic::spec_calls::ClauseRef::written("proof_assert", expr_text),
    );
    assertion = crate::logic::ptr_casts::classify_pointer_casts(
        tcx,
        pa.containing_fn.to_def_id(),
        &assertion,
    );
    assertion = normalize_logic_fn_names(assertion, &setup.logic_fn_path_map);
    assertion = rewrite_logic_method_calls_expr(&assertion, &setup.logic_method_names);
    // Apply sound tautology simplifications before SMT encoding. This avoids
    // quantifier-unknown outcomes for formulas that are trivially true by
    // propositional/first-order identities (for example `forall<x> p ==> p`).
    assertion = simplify_proof_assert_expr(assertion);
    assertion = crate::assoc_const_paths::normalize_local_assoc_const_paths(
        tcx,
        pa.containing_fn.to_def_id(),
        &assertion,
    );

    if !snapshot.assoc_const_substitutions.is_empty() {
        assertion = assertion.substitute(&snapshot.assoc_const_substitutions);
    }

    // Substitute named const items (e.g., `TUP` -> `__trust_wp_tuple2(42, 24)`).
    // Includes tuple beta-reduction so `TUP.0` simplifies to `42`. (#1588)
    if !setup.const_item_substitutions.is_empty() {
        assertion = assertion.substitute(&setup.const_item_substitutions);
    }

    // The typeck root owner is the enclosing function item. It is consulted
    // ONLY for the closure capture layout it defines (the wiring below), never
    // for the assertion's environment: a closure is a function of its own, and
    // its assertion is a goal of the closure's VC, whose premises are the
    // closure's own `requires`, the same environment its contract lane proves
    // it in. The enclosing function's `requires` are facts about the parent's
    // parameters at the parent's entry; a closure parameter may shadow one, a
    // capture may be taken after the parent overwrote it, and an `FnMut`
    // capture changes between calls (closure_assertion_inherits_parent_*.rs).
    let owner_local = tcx
        .typeck_root_def_id(pa.containing_fn.to_def_id())
        .expect_local();

    let fn_precond_vec = setup
        .fn_preconditions
        .get(&pa.containing_fn)
        .cloned()
        .unwrap_or_default();
    let fn_precond_count = fn_precond_vec.len();
    // fact-source: entry_requires
    let mut preconditions = fn_precond_vec;
    // A loop that writes a by-reference parameter's pointee invalidates the
    // `#[requires]` facts about it; the encoder cannot tell the entry value
    // from the current one, so a stale fact would discharge assertions the
    // loop has already falsified (D-38).
    let loop_invalidated = loop_invalidated_param_names(tcx, pa);
    {
        // fact-source: entry_fact_withdrawal
        let dropped = drop_stale_param_facts(&mut preconditions, &loop_invalidated);
        if dropped > 0 {
            debug!(
                "trust-wp:   (proof_assert in {fn_path}: {dropped} entry fact(s) dropped — \
                 a loop writes the pointee of {loop_invalidated:?})"
            );
        }
    }
    // A by-value parameter whose every write before the assertion the walks
    // record has its entry value read by a symbol of its own in every value
    // they recorded (`ParamEntryVersions`), so its entry facts are stated of
    // that symbol below rather than withdrawn (D-241).
    let versioned: HashSet<String> = snapshot
        .entry_versions
        .versioned
        .iter()
        .filter(|name| !loop_invalidated.invalidates(std::iter::once(name.as_str())))
        .cloned()
        .collect();
    // A parameter the body re-binds is equated with its new binding by this
    // lane, so an entry fact over its name would describe the new value
    // (D-140). The loop-exit facts below are withdrawn for the same names.
    let rebound = rebound_param_names(tcx, snapshot);
    {
        let rebound_unversioned = crate::mir_analysis::InvalidatedEntryNames {
            params: rebound
                .params
                .iter()
                .filter(|name| !versioned.contains(*name))
                .cloned()
                .collect(),
            unnamed: rebound.unnamed,
        };
        // fact-source: entry_fact_withdrawal
        let dropped = drop_stale_param_facts(&mut preconditions, &rebound_unversioned);
        if dropped > 0 {
            debug!(
                "trust-wp:   (proof_assert in {fn_path}: {dropped} entry fact(s) dropped — \
                 the body re-binds {rebound_unversioned:?} before the assertion)"
            );
        }
    }
    // A write to a parameter's own storage the walks do not record as a
    // value of its own (a `&mut` borrow of it or of a field handed to a
    // call, a write in a loop, a reference parameter re-bound) leaves its
    // name standing for the entry value while the program has moved on; an
    // entry fact over it would describe the current value (D-241).
    let mut written = written_params(tcx, pa);
    written.keep_scalars_advanced_to_their_prophecy(&snapshot.substitutions);
    written.forget(&snapshot.entry_versions.exact);
    {
        // fact-source: entry_fact_withdrawal
        let dropped = written.drop_stale_facts(&mut preconditions);
        if dropped > 0 {
            debug!(
                "trust-wp:   (proof_assert in {fn_path}: {dropped} entry fact(s) dropped — \
                 the body writes {written:?} before the assertion)"
            );
        }
    }
    // The `#[requires]` facts end here; the lemma calls below speak of the
    // assertion's own state.
    let entry_fact_count = preconditions.len();
    let (leading_call_assumptions, leading_has_mutating_call_effect) =
        collect_leading_proof_assert_assumptions(
            tcx,
            pa,
            ctx.logic_fn_defs,
            &setup.user_specs,
            &setup.logic_method_names,
        );
    let has_mutating_call_effect = derive_has_mutating_call_effect(
        snapshot.has_mutating_call_effect,
        leading_has_mutating_call_effect,
        snapshot.call_effect_expr.as_ref(),
    );
    if ctx.verbose && !leading_call_assumptions.is_empty() {
        debug!(
            "trust-wp:   (proof_assert: {} leading call assumption(s) injected)",
            leading_call_assumptions.len()
        );
    }
    // The lemma calls are written beside the assertion and name its
    // bindings; one whose binding cannot be told is no fact (D-237).
    // fact-source: lemma_calls_in_the_assertion
    preconditions.extend(leading_call_assumptions.into_iter().filter_map(|fact| {
        crate::mir_analysis::binding_identity::resolve_proof_assert_bindings(tcx, pa, &fact).ok()
    }));

    let body_arg_names = get_arg_names_for_proof_assert_body(tcx, pa.containing_fn);
    let containing_contract = setup.contract_by_local.get(&pa.containing_fn);
    // Whether the containing function carries an explicit user-authored
    // `#[requires(false)]`. Keyed to the PRECONDITION position only via the raw
    // source clause text, so `#[ensures(false)]` is not credited here.
    let containing_requires_false = containing_contract
        .is_some_and(|contract| super::reporting::user_authored_requires_false(contract));
    let containing_def_id = containing_contract
        .map_or_else(|| pa.containing_fn.to_def_id(), |contract| contract.def_id);
    let contract_arg_names =
        get_arg_names_from_def_id(tcx, containing_def_id).unwrap_or_else(|| {
            let path = tcx.def_path_str(containing_def_id);
            debug!(
                "trust-wp: warning: no parameter names for `{path}` ({containing_def_id:?}), \
                 using positional fallback \u{2014} named contract parameters will not be substituted"
            );
            Vec::new()
        });
    // Rewrite type invariant methods + struct field access in assertion and
    // preconditions. A named-field pattern whose declared field positions
    // cannot be established is REFUSED (D-31) rather than read in source order.
    if let Err(why) = apply_type_and_field_rewrites(
        tcx,
        containing_def_id,
        &contract_arg_names,
        ctx.type_invariant_defs,
        ctx.verbose,
        &mut assertion,
        // fact-source: field_rewrites
        &mut preconditions,
    ) {
        eprintln!(
            "trust-wp: proof_assert in {fn_path} error: {why}; refusing instead of binding \
             the fields in the order they were written, which would bind one field as another"
        );
        return Err(());
    }
    // An entry fact of a versioned parameter speaks of its entry symbol
    // (D-241). The facts are the `entry_requires` ones, renamed in place.
    if !versioned.is_empty() {
        for fact in &mut preconditions[..entry_fact_count] {
            *fact = super::proof_assert_snapshot::rename_to_entry_values(fact, &versioned);
        }
    }
    if !snapshot.post_loop_assumptions.is_empty() {
        // fact-source: loop_fact_handoff
        let mut post_loop_assumptions = snapshot.post_loop_assumptions.clone();
        // A loop's invariants and exit condition hold of the names at the
        // loop's exit; a parameter re-bound since reads them as facts about
        // its new binding (D-140).
        // fact-source: entry_fact_withdrawal
        drop_stale_param_facts(&mut post_loop_assumptions, &rebound);
        for assumption in &mut post_loop_assumptions {
            *assumption = normalize_logic_fn_names(assumption.clone(), &setup.logic_fn_path_map);
            *assumption = rewrite_logic_method_calls_expr(assumption, &setup.logic_method_names);
        }
        let mut dummy_assertion = PureExpr::Bool(true);
        if let Err(why) = apply_type_and_field_rewrites(
            tcx,
            containing_def_id,
            &contract_arg_names,
            ctx.type_invariant_defs,
            ctx.verbose,
            &mut dummy_assertion,
            // fact-source: field_rewrites
            &mut post_loop_assumptions,
        ) {
            eprintln!(
                "trust-wp: proof_assert in {fn_path} error: {why} (in a post-loop \
                 assumption); refusing instead of binding the fields in the order they \
                 were written, which would bind one field as another"
            );
            return Err(());
        }
        // fact-source: loop_fact_handoff
        preconditions.extend(post_loop_assumptions);
    }

    // Inject type-invariant preconditions for the containing function's
    // parameters. Normal contract verification gets these through
    // `enrich_effective_clauses`; proof_assert needs them too, or inv(x) and
    // container element invariant assertions fail on under-constrained VCs.
    // (#2244)
    //
    // Scope the injection to only parameters whose names appear as free
    // variables in the rewritten assertion. Injecting invariants for all
    // parameters over-constrains the VC for local proof_assert obligations
    // that only reference a subset of the function's arguments. (#2339)
    let invariant_arg_names = if contract_arg_names.is_empty() {
        body_arg_names.clone()
    } else {
        contract_arg_names.clone()
    };
    let assertion_free_vars = assertion.free_vars();
    let mut type_invariant_relevance_vars = assertion_free_vars.clone();
    for obligation in &snapshot.call_obligations {
        type_invariant_relevance_vars.extend(obligation.free_vars());
    }
    // A parameter's type invariant is an entry fact like its `#[requires]`:
    // it goes with them for every parameter a withdrawal names, and is stated
    // of the entry symbol of a versioned one, whose value the assertion may
    // read through a copy (D-241).
    let entry_fact_withdrawn = |name: &String| {
        !versioned.contains(name)
            && ([&loop_invalidated, &rebound]
                .iter()
                .any(|stale| stale.invalidates(std::iter::once(name.as_str())))
                || written.names(name))
    };
    let entry_symbols_read: HashSet<String> = assertion_free_vars
        .iter()
        .filter_map(|name| snapshot.substitutions.get(name))
        .flat_map(PureExpr::free_vars)
        .collect();
    let relevant_invariant_arg_names: Vec<String> = invariant_arg_names
        .into_iter()
        .filter(|name| {
            type_invariant_relevance_vars.contains(name)
                || (versioned.contains(name)
                    && entry_symbols_read
                        .contains(&super::proof_assert_snapshot::param_entry_value_name(name)))
        })
        .filter(|name| !entry_fact_withdrawn(name))
        .collect();
    let (inv_requires, _) = build_type_invariant_clauses(
        tcx,
        containing_def_id,
        &relevant_invariant_arg_names,
        ctx.type_invariant_defs,
    );
    let inv_requires: Vec<PureExpr> = inv_requires
        .iter()
        .map(|fact| super::proof_assert_snapshot::rename_to_entry_values(fact, &versioned))
        .collect();
    if !inv_requires.is_empty() {
        if ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: {} type invariant precondition(s) injected)",
                inv_requires.len()
            );
        }
        // fact-source: parameter_type_invariants
        preconditions.extend(inv_requires);
    }

    if ctx.verbose {
        eprintln!("trust-wp: verifying proof_assert in {fn_path} ({fn_precond_count} contract preconditions)");
        debug!(
            "trust-wp: verifying proof_assert in {fn_path} ({fn_precond_count} contract preconditions)"
        );
        debug!("  assertion: {assertion}");
    }

    let mut local_substitutions = snapshot.substitutions.clone();
    // fact-source: assumed_fact_handoff
    let mut assumed_facts = snapshot.assumed_facts.clone();
    let before_assumed_facts = assumed_facts.len();
    assumed_facts.retain(|fact| {
        !(has_mutating_call_effect && is_stale_mutation_alias_fact(fact))
            && !is_stale_closure_capture_env_fact(fact)
            && !is_substitution_falsified_fact(fact)
    });
    let filtered_assumed_facts = before_assumed_facts - assumed_facts.len();
    if filtered_assumed_facts > 0 && ctx.verbose {
        debug!(
            "trust-wp:   (proof_assert: filtered {} stale assumed fact(s))",
            filtered_assumed_facts,
        );
    }
    let mut call_obligations = snapshot.call_obligations.clone();
    derive_assertion_final_alias_substitutions(
        &mut local_substitutions,
        &assumed_facts,
        &assertion_free_vars,
    );
    if !local_substitutions.is_empty() {
        assertion =
            substitute_assertion_names(&assertion, &local_substitutions, &assertion_free_vars);
        assertion = preserve_transparent_adapter_views(assertion);
        assertion = collapse_idempotent_views(assertion);
        // Applying a program-point substitution such as `*a -> call_N` (the
        // post-call deref read) introduces a fresh call-result var that is
        // bound to a reference's prophecy by an assumed fact (`call_N == ^a`).
        // The earlier final-alias pass ran over the ORIGINAL free vars (`a`,
        // `a_p`) and never saw `call_N`. Re-derive final aliases over the
        // now-present vars and rewrite, so the goal expresses the post-call
        // read directly as `^a` — matching the callee's postcondition carrier
        // (`^a > *a`) syntactically and closing the proof. (#682)
        let introduced_free_vars = assertion.free_vars();
        let mut final_alias_substitutions: HashMap<String, PureExpr> = HashMap::new();
        derive_assertion_final_alias_substitutions(
            &mut final_alias_substitutions,
            &assumed_facts,
            &introduced_free_vars,
        );
        if !final_alias_substitutions.is_empty() {
            assertion = substitute_assertion_names(
                &assertion,
                &final_alias_substitutions,
                &introduced_free_vars,
            );
            assertion = preserve_transparent_adapter_views(assertion);
            assertion = collapse_idempotent_views(assertion);
        }
        if ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: applied {} program-point substitution(s))",
                local_substitutions.len()
            );
            debug!("trust-wp:     assertion_after_sub: {assertion}");
        }
        let deref_aliases = collect_deref_snapshot_aliases(&assertion, &assumed_facts);
        if !deref_aliases.is_empty() {
            let deref_alias_names: HashSet<String> = deref_aliases.keys().cloned().collect();
            derive_snapshot_deref_alias_substitutions(&mut local_substitutions, &deref_aliases);
            assertion =
                substitute_assertion_names(&assertion, &local_substitutions, &deref_alias_names);
            assertion = preserve_transparent_adapter_views(assertion);
            assertion = collapse_idempotent_views(assertion);
            assumed_facts = substitute_snapshot_facts(&assumed_facts, &local_substitutions);
            call_obligations = substitute_snapshot_facts(&call_obligations, &local_substitutions);
            if ctx.verbose {
                debug!("trust-wp:     assertion_after_deref_alias: {assertion}");
            }
        }
        let precise_final_rewritten =
            substitute_precise_final_update_carriers(&assertion, &assumed_facts);
        let final_carrier_rewritten =
            substitute_assertion_final_carriers(&precise_final_rewritten, &assumed_facts);
        if final_carrier_rewritten != assertion {
            assertion = preserve_transparent_adapter_views(final_carrier_rewritten);
            assertion = collapse_idempotent_views(assertion);
            if ctx.verbose {
                debug!("trust-wp:     assertion_after_final_fact_alias: {assertion}");
            }
        }
        let rewritten_call_obligations: Vec<PureExpr> = call_obligations
            .iter()
            .map(|obligation| substitute_precise_final_update_carriers(obligation, &assumed_facts))
            .map(|obligation| substitute_assertion_final_carriers(&obligation, &assumed_facts))
            .map(collapse_idempotent_views)
            .collect();
        if rewritten_call_obligations != call_obligations {
            call_obligations = rewritten_call_obligations;
            if ctx.verbose {
                debug!(
                    "trust-wp:     call_obligations_after_final_fact_alias: {call_obligations:?}"
                );
            }
        }
        if !has_mutating_call_effect {
            // fact-source: stale_alias_withdrawal
            filter_consumed_final_update_facts(&mut assumed_facts, &assertion, &call_obligations);
        }
    }
    if !snapshot.mapping_closures.is_empty() {
        assertion = inline_bool_mapping_closure_calls(&assertion, &snapshot.mapping_closures);
        assertion = collapse_idempotent_views(assertion);
        if ctx.verbose {
            debug!("trust-wp:     assertion_after_bool_inline: {assertion}");
        }
    }
    // Direct ground instantiation: for each assumed fact matching
    // `mapping.get(arg)` where `mapping` has a MappingClosureInfo,
    // substitute `arg` into the closure body and add as a precondition.
    // This bypasses sort interop issues between mapping_get (Int) and
    // Bool-valued closure bodies like `(x + 1) == 42`. (#2245)
    let ground_instances =
        instantiate_mapping_closure_ground(&assumed_facts, &snapshot.mapping_closures);
    if !ground_instances.is_empty() {
        if ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: {} mapping closure ground instance(s))",
                ground_instances.len(),
            );
            for (i, gi) in ground_instances.iter().enumerate() {
                debug!("trust-wp:     ground_instance[{i}]: {gi:?}");
            }
        }
        // fact-source: mapping_closure_ground_instances
        preconditions.extend(ground_instances);
    }

    if ctx.verbose && (!assumed_facts.is_empty() || !call_obligations.is_empty()) {
        debug!(
            "trust-wp:   (proof_assert: {} assumed fact(s), {} call obligation(s))",
            assumed_facts.len(),
            call_obligations.len(),
        );
        for (i, fact) in assumed_facts.iter().enumerate() {
            debug!("trust-wp:     assumed_fact[{i}]: {fact}");
        }
    }
    // Second pass: ground-instantiate mapping closures from the assertion
    // expression (post-substitution). The first pass only scanned snapshot
    // assumed facts. The assertion itself may contain `mapping.index_logic(arg)`
    // terms that provide ground instances the solver needs. (#2245)
    if !snapshot.mapping_closures.is_empty() {
        let assertion_ground =
            instantiate_mapping_closure_ground_from_expr(&assertion, &snapshot.mapping_closures);
        if !assertion_ground.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} assertion-derived ground instance(s))",
                    assertion_ground.len(),
                );
                for (i, gi) in assertion_ground.iter().enumerate() {
                    debug!("trust-wp:     assertion_ground[{i}]: {gi:?}");
                }
            }
            // fact-source: mapping_closure_ground_instances
            preconditions.extend(assertion_ground);
        }
    }

    // Static match elimination: reduce match expressions with concrete
    // constructor scrutinees (e.g., `match *None() { Some(v) => ..., None => ... }`)
    // before SMT encoding. Match-style postconditions from specs like ok_or
    // produce these patterns as assumed facts, and the ay encoder cannot
    // statically evaluate them. (#2675)
    {
        let mut match_reduced_count = 0usize;
        for fact in &mut assumed_facts {
            // `reduce_concrete_matches` resolves matches on concrete constructor
            // scrutinees; `simplify_identity_matches` additionally collapses an
            // *identity* match on a SYMBOLIC scrutinee (e.g. the body binding
            // `y == match x { -1 => -1, 127 => 127, _ => x }` ⇒ `y == x`). Without
            // it, each such match lowers to a discriminant case-split that the
            // solver multiplies across independent body matches, exploding search
            // (4 sequential identity matches: timeout vs ~0s for one). SOUND: an
            // identity match equals its scrutinee on every input. (#negative_int_pats)
            let reduced = reduce_concrete_matches(fact.clone()).simplify_identity_matches();
            if reduced != *fact {
                match_reduced_count += 1;
                *fact = reduced;
            }
        }
        let reduced_assertion =
            reduce_concrete_matches(assertion.clone()).simplify_identity_matches();
        if reduced_assertion != assertion {
            match_reduced_count += 1;
            assertion = reduced_assertion;
        }
        if match_reduced_count > 0 && ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: {} concrete match(es) statically reduced)",
                match_reduced_count,
            );
        }
    }

    // Static evaluation of constructor method calls in assumed facts.
    // Implication-style postconditions from specs like ok_or produce assumed
    // facts like `None().is_some() ==> (call_3 == Ok(old(None()).unwrap()))`.
    // The antecedent `None().is_some()` is statically false, making the
    // implication vacuously true (useless). Similarly, `None().is_none()`
    // is statically true, so `None().is_none() ==> X` simplifies to `X`.
    //
    // Without this reduction, the solver must reason about `is_some`/`is_none`
    // on concrete constructors, which requires additional axiom instantiation
    // that may not trigger. This pass evaluates these calls at the expression
    // level before encoding. (#2675)
    {
        let mut ctor_method_reduced_count = 0usize;
        for fact in &mut assumed_facts {
            let reduced = reduce_concrete_constructor_method_calls(fact.clone());
            if reduced != *fact {
                ctor_method_reduced_count += 1;
                *fact = reduced;
            }
        }
        {
            let reduced = reduce_concrete_constructor_method_calls(assertion.clone());
            if reduced != assertion {
                ctor_method_reduced_count += 1;
                assertion = reduced;
            }
        }
        if ctor_method_reduced_count > 0 && ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: {} constructor method call(s) statically reduced)",
                ctor_method_reduced_count,
            );
        }
    }

    // Synthesize constructor equalities from tester+selector assumed fact
    // pairs (e.g., `x.is_err() ∧ x.unwrap_err() == v` → `x == Err(v)`).
    // These are direct consequences of ADT datatype theory axioms that
    // the solver cannot derive without explicit constructor-tester-selector
    // axiom instantiation. (#2675)
    {
        let synthesized = synthesize_constructor_equalities(&assumed_facts);
        if !synthesized.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} constructor equality/ies synthesized)",
                    synthesized.len(),
                );
            }
            // fact-source: constructor_facts
            assumed_facts.extend(synthesized);
        }
        let normalized_old_facts: Vec<PureExpr> = assumed_facts
            .iter()
            .flat_map(normalize_old_constructor_equality_facts)
            .collect();
        if !normalized_old_facts.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} old-wrapped constructor equality/ies normalized)",
                    normalized_old_facts.len(),
                );
            }
            // fact-source: constructor_facts
            assumed_facts.extend(normalized_old_facts);
        }
        let ctor_tester_selector_facts: Vec<PureExpr> = assumed_facts
            .iter()
            .flat_map(constructor_equality_to_tester_selector_facts)
            .collect();
        if !ctor_tester_selector_facts.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} constructor tester/selector fact(s) synthesized)",
                    ctor_tester_selector_facts.len(),
                );
            }
            // fact-source: constructor_facts
            assumed_facts.extend(ctor_tester_selector_facts);
        }
    }

    // Apply constructor equality substitutions: when assumed facts contain
    // `var == Constructor(...)`, substitute var in the assertion and re-run
    // concrete match reduction. This resolves match expressions on variables
    // that are known to be specific constructors. (#2675)
    {
        let reduced = apply_constructor_equality_substitutions(assertion.clone(), &assumed_facts);
        if reduced != assertion {
            if ctx.verbose {
                debug!("trust-wp:   (proof_assert: assertion reduced via constructor equality substitution)");
                debug!("trust-wp:     assertion_after_ctor_eq: {reduced}");
            }
            assertion = reduced;
        }

        let (reduced_facts, reduced_count) =
            apply_constructor_equality_substitutions_to_facts(&assumed_facts);
        if reduced_count > 0 {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} assumed fact(s) reduced via constructor equality substitution)",
                    reduced_count,
                );
            }
            assumed_facts = reduced_facts;
        }

        let mut equality_sources = preconditions.clone();
        equality_sources.extend(assumed_facts.iter().cloned());
        let ground_instances =
            synthesize_ground_equality_substitution_facts(&equality_sources, &assumed_facts);
        if !ground_instances.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} ground equality substitution fact(s) synthesized)",
                    ground_instances.len(),
                );
            }
            // fact-source: ground_equality_facts
            assumed_facts.extend(ground_instances);
        }
    }
    {
        let mut equality_sources = preconditions.clone();
        equality_sources.extend(assumed_facts.iter().cloned());
        let transitive_disequalities =
            synthesize_transitive_disequalities(&equality_sources, &equality_sources);
        if !transitive_disequalities.is_empty() {
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: {} transitive disequality fact(s) synthesized)",
                    transitive_disequalities.len(),
                );
            }
            // fact-source: transitive_disequalities
            assumed_facts.extend(transitive_disequalities);
        }
    }

    // fact-source: irrelevant_fact_withdrawal
    let filtered_mapping_foralls = retain_relevant_mapping_closure_foralls(
        &mut assumed_facts,
        &snapshot.mapping_closures,
        &assertion,
        &preconditions,
        &call_obligations,
    );
    if filtered_mapping_foralls > 0 && ctx.verbose {
        debug!(
            "trust-wp:   (proof_assert: filtered {} irrelevant mapping closure forall assumption(s))",
            filtered_mapping_foralls
        );
    }

    // fact-source: irrelevant_fact_withdrawal
    let filtered_len_facts = filter_len_only_irrelevant_facts(&assertion, &mut assumed_facts);
    if filtered_len_facts > 0 && ctx.verbose {
        debug!(
            "trust-wp:   (proof_assert: filtered {} non-length fact(s) from length-only assertion)",
            filtered_len_facts
        );
    }

    // Assertion slicing: filter assumed_facts to only those transitively
    // relevant to the assertion's free variables. Ghost-heavy tests (e.g.,
    // ghost_vec with 50+ accumulated postconditions) spend most solver time
    // on irrelevant preconditions. This performs cone-of-influence reduction
    // to keep only facts that share variables with the assertion (transitively).
    // Skip slicing when assumed_facts is small (threshold: 20) to avoid
    // overhead on simple assertions where all facts are likely relevant.
    if assumed_facts.len() > 20 {
        let mut relevant_vars: HashSet<String> = assertion.free_vars();
        // Pre-compute free vars for each assumed fact
        let fact_vars: Vec<HashSet<String>> = assumed_facts.iter().map(|f| f.free_vars()).collect();
        // Fixed-point expansion: keep adding facts whose vars overlap with
        // the relevant set until no new facts are added
        let mut relevant_indices: HashSet<usize> = HashSet::new();
        loop {
            let prev_count = relevant_indices.len();
            for (i, fv) in fact_vars.iter().enumerate() {
                if !relevant_indices.contains(&i) && !fv.is_disjoint(&relevant_vars) {
                    relevant_indices.insert(i);
                    relevant_vars.extend(fv.iter().cloned());
                }
            }
            if relevant_indices.len() == prev_count {
                break;
            }
        }
        let original_count = assumed_facts.len();
        if relevant_indices.len() < original_count {
            let sliced: Vec<PureExpr> = assumed_facts
                .into_iter()
                .enumerate()
                .filter(|(i, _)| relevant_indices.contains(i))
                .map(|(_, f)| f)
                .collect();
            if ctx.verbose {
                debug!(
                    "trust-wp:   (proof_assert: assertion slicing reduced {} → {} assumed facts)",
                    original_count,
                    sliced.len(),
                );
            }
            assumed_facts = sliced;
        }
    }

    // Filter out trivially-true assumed facts (Bool(true)) that result from
    // boolean constant folding in reduce_concrete_constructor_method_calls.
    // These add noise to the solver without providing information. (#2671)
    {
        let before = assumed_facts.len();
        assumed_facts.retain(|f| !matches!(f, PureExpr::Bool(true)));
        let filtered = before - assumed_facts.len();
        if filtered > 0 && ctx.verbose {
            debug!(
                "trust-wp:   (proof_assert: filtered {} trivially-true assumed fact(s))",
                filtered,
            );
        }
    }

    // Phase 8: Closure wiring, obligation filtering, and enrichment passes.
    //
    // Call postconditions are part of the proof_assert premises. Add them
    // before closure wiring so existential enrichment can see closure
    // postcondition facts synthesized from preceding calls.
    // fact-source: assumed_fact_handoff
    preconditions.extend(assumed_facts.iter().cloned());
    let wiring_ctx = super::proof_assert_wiring::ClosureWiringContext {
        tcx,
        containing_fn: pa.containing_fn,
        owner_local,
        user_specs: &setup.user_specs,
        const_item_substitutions: &setup.const_item_substitutions,
        logic_fn_defs: ctx.logic_fn_defs,
        verbose: ctx.verbose,
        body_arg_names: &body_arg_names,
        fn_path: &fn_path,
    };
    // fact-source: closure_wiring
    let wiring = apply_closure_wiring(
        &wiring_ctx,
        &mut preconditions,
        assertion,
        &call_obligations,
    );
    let mut ensures = wiring.ensures;
    if !snapshot.assoc_const_substitutions.is_empty() {
        preconditions = preconditions
            .into_iter()
            .map(|expr| expr.substitute(&snapshot.assoc_const_substitutions))
            .collect();
        ensures = ensures
            .into_iter()
            .map(|expr| expr.substitute(&snapshot.assoc_const_substitutions))
            .collect();
    }
    // fact-source: field_rewrites
    rewrite_iterator_spec_proof_assert_clauses(&mut preconditions, &mut ensures);
    preconditions = preconditions
        .into_iter()
        .map(normalize_seq_final_fact_views)
        .map(collapse_idempotent_views)
        .collect();
    ensures = ensures
        .into_iter()
        .map(normalize_seq_final_fact_views)
        .map(collapse_idempotent_views)
        .collect();
    // Proof assertions are an explicit proof-authority boundary. Keep even a
    // syntactic `true` or a goal already present in the premises: the strict
    // lane must solve and replay that exact authored obligation. Deleting it
    // here turns an authored assertion into an empty obligation set, which can
    // aggregate to `Verified` without any per-slice certificate.
    let mut return_expr = snapshot.return_expr.clone();
    if !snapshot.assoc_const_substitutions.is_empty() {
        return_expr = return_expr.map(|expr| expr.substitute(&snapshot.assoc_const_substitutions));
    }
    return_expr = return_expr.map(preserve_transparent_adapter_views);
    assumed_facts = assumed_facts
        .into_iter()
        .map(preserve_transparent_adapter_views)
        .collect();
    call_obligations = call_obligations
        .into_iter()
        .map(preserve_transparent_adapter_views)
        .collect();
    // fact-source: field_rewrites
    normalize_scalar_proof_assert_boundary(&mut preconditions, &mut ensures, &mut return_expr);
    preconditions = preconditions
        .into_iter()
        .map(preserve_transparent_adapter_views)
        .collect();
    ensures = ensures
        .into_iter()
        .map(preserve_transparent_adapter_views)
        .collect();
    return_expr = return_expr.map(preserve_transparent_adapter_views);

    Ok(Some(PreparedAssertion {
        preconditions,
        ensures,
        return_expr,
        mode_overrides: wiring.mode_overrides,
        closure_capture_infos: wiring.closure_capture_infos,
        has_mutating_call_effect,
        is_contractless: false,
        containing_requires_false,
        fn_path,
        loc,
        expr_text: expr_text.to_string(),
    }))
}

pub(super) fn filter_len_only_irrelevant_facts(
    assertion: &PureExpr,
    assumed_facts: &mut Vec<PureExpr>,
) -> usize {
    if assumed_facts.is_empty() || !is_len_only_assertion(assertion) {
        return 0;
    }

    let mut relevant_len_receivers = collect_len_receiver_names(assertion);
    if relevant_len_receivers.is_empty() {
        return 0;
    }
    let mut relevant_scalars = assertion.free_vars();
    for receiver in &relevant_len_receivers {
        relevant_scalars.remove(receiver);
    }

    let mut retained = vec![false; assumed_facts.len()];
    loop {
        let mut changed = false;
        for (idx, fact) in assumed_facts.iter().enumerate() {
            if retained[idx] || contains_non_len_method_or_quantifier(fact) {
                continue;
            }

            let fact_len_receivers = collect_len_receiver_names(fact);
            let keep = if fact_len_receivers.is_empty() {
                let vars = fact.free_vars();
                !vars.is_disjoint(&relevant_scalars)
            } else {
                !fact_len_receivers.is_disjoint(&relevant_len_receivers)
            };
            if !keep {
                continue;
            }

            retained[idx] = true;
            changed = true;
            relevant_len_receivers.extend(fact_len_receivers);
            let mut vars = fact.free_vars();
            for receiver in &relevant_len_receivers {
                vars.remove(receiver);
            }
            relevant_scalars.extend(vars);
        }
        if !changed {
            break;
        }
    }

    let before = assumed_facts.len();
    *assumed_facts = assumed_facts
        .iter()
        .cloned()
        .zip(retained)
        .filter_map(|(fact, keep)| keep.then_some(fact))
        .collect();
    before - assumed_facts.len()
}

fn is_len_only_assertion(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => true,
        PureExpr::BinOp(left, _, right) => {
            is_len_only_assertion(left) && is_len_only_assertion(right)
        }
        PureExpr::UnOp(_, operand)
        | PureExpr::Old(operand)
        | PureExpr::Deref(operand)
        | PureExpr::Final(operand)
        | PureExpr::View(operand) => is_len_only_assertion(operand),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            is_len_only_assertion(cond)
                && is_len_only_assertion(then_expr)
                && is_len_only_assertion(else_expr)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            matches!(method.as_str(), "len" | "len_logic")
                && args.is_empty()
                && is_len_receiver_expr(receiver)
        }
        _ => false,
    }
}

fn is_len_receiver_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, _) => true,
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => is_len_receiver_expr(inner),
        _ => false,
    }
}

fn len_receiver_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => len_receiver_name(inner),
        _ => None,
    }
}

fn collect_len_receiver_names(expr: &PureExpr) -> HashSet<String> {
    let mut receivers = HashSet::new();
    collect_len_receiver_names_into(expr, &mut receivers);
    receivers
}

fn collect_len_receiver_names_into(expr: &PureExpr, receivers: &mut HashSet<String>) {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if matches!(method.as_str(), "len" | "len_logic") && args.is_empty() {
                if let Some(name) = len_receiver_name(receiver) {
                    receivers.insert(name.to_string());
                }
            }
            collect_len_receiver_names_into(receiver, receivers);
            for arg in args {
                collect_len_receiver_names_into(arg, receivers);
            }
        }
        PureExpr::BinOp(left, _, right) => {
            collect_len_receiver_names_into(left, receivers);
            collect_len_receiver_names_into(right, receivers);
        }
        PureExpr::UnOp(_, operand)
        | PureExpr::Old(operand)
        | PureExpr::Deref(operand)
        | PureExpr::Final(operand)
        | PureExpr::View(operand) => collect_len_receiver_names_into(operand, receivers),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_len_receiver_names_into(cond, receivers);
            collect_len_receiver_names_into(then_expr, receivers);
            collect_len_receiver_names_into(else_expr, receivers);
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                collect_len_receiver_names_into(arg, receivers);
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_len_receiver_names_into(scrutinee, receivers);
            for arm in arms {
                collect_len_receiver_names_into(&arm.body, receivers);
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_len_receiver_names_into(value, receivers);
            collect_len_receiver_names_into(body, receivers);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_len_receiver_names_into(assumption, receivers);
            collect_len_receiver_names_into(body, receivers);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_len_receiver_names_into(obligation, receivers);
            collect_len_receiver_names_into(body, receivers);
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            collect_len_receiver_names_into(body, receivers);
            for trigger in triggers {
                for trigger_expr in trigger {
                    collect_len_receiver_names_into(trigger_expr, receivers);
                }
            }
        }
        PureExpr::Closure { body, .. } => collect_len_receiver_names_into(body, receivers),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        _ => {}
    }
}

fn contains_non_len_method_or_quantifier(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            !(matches!(method.as_str(), "len" | "len_logic") && args.is_empty())
                || contains_non_len_method_or_quantifier(receiver)
                || args.iter().any(contains_non_len_method_or_quantifier)
        }
        PureExpr::Forall { .. } | PureExpr::Exists { .. } | PureExpr::Closure { .. } => true,
        PureExpr::LogicFnCall { .. } | PureExpr::Match { .. } => true,
        PureExpr::BinOp(left, _, right) => {
            contains_non_len_method_or_quantifier(left)
                || contains_non_len_method_or_quantifier(right)
        }
        PureExpr::UnOp(_, operand)
        | PureExpr::Old(operand)
        | PureExpr::Deref(operand)
        | PureExpr::Final(operand)
        | PureExpr::View(operand) => contains_non_len_method_or_quantifier(operand),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_non_len_method_or_quantifier(cond)
                || contains_non_len_method_or_quantifier(then_expr)
                || contains_non_len_method_or_quantifier(else_expr)
        }
        PureExpr::Let { value, body, .. } => {
            contains_non_len_method_or_quantifier(value)
                || contains_non_len_method_or_quantifier(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_non_len_method_or_quantifier(assumption)
                || contains_non_len_method_or_quantifier(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_non_len_method_or_quantifier(obligation)
                || contains_non_len_method_or_quantifier(body)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        _ => false,
    }
}

fn synthesize_transitive_disequalities(
    sources: &[PureExpr],
    existing: &[PureExpr],
) -> Vec<PureExpr> {
    const MAX_SYNTHESIZED_DISEQUALITIES: usize = 128;

    let mut classes: Vec<Vec<PureExpr>> = Vec::new();
    let mut disequalities: Vec<(&PureExpr, &PureExpr)> = Vec::new();
    for fact in sources {
        if let Some((left, right)) = equality_operands(fact) {
            merge_expr_classes(&mut classes, left, right);
        } else if let Some((left, right)) = disequality_operands(fact) {
            disequalities.push((left, right));
        }
    }

    let mut synthesized = Vec::new();
    for (left, right) in disequalities {
        let left_members = expr_class_members(&classes, left);
        let right_members = expr_class_members(&classes, right);
        for left_member in &left_members {
            for right_member in &right_members {
                if left_member == right_member {
                    continue;
                }
                let fact = PureExpr::BinOp(
                    Arc::new(left_member.clone()),
                    BinOp::Ne,
                    Arc::new(right_member.clone()),
                );
                let reverse = PureExpr::BinOp(
                    Arc::new(right_member.clone()),
                    BinOp::Ne,
                    Arc::new(left_member.clone()),
                );
                if existing.contains(&fact)
                    || existing.contains(&reverse)
                    || synthesized.contains(&fact)
                    || synthesized.contains(&reverse)
                {
                    continue;
                }
                synthesized.push(fact);
                if synthesized.len() >= MAX_SYNTHESIZED_DISEQUALITIES {
                    return synthesized;
                }
            }
        }
    }
    synthesized
}

fn equality_operands(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    Some((left, right))
}

fn disequality_operands(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Ne, right) = expr else {
        return None;
    };
    Some((left, right))
}

fn merge_expr_classes(classes: &mut Vec<Vec<PureExpr>>, left: &PureExpr, right: &PureExpr) {
    if left == right {
        return;
    }
    match (
        expr_class_index(classes, left),
        expr_class_index(classes, right),
    ) {
        (Some(left_idx), Some(right_idx)) if left_idx == right_idx => {}
        (Some(left_idx), Some(right_idx)) => {
            let (keep_idx, remove_idx) = if left_idx < right_idx {
                (left_idx, right_idx)
            } else {
                (right_idx, left_idx)
            };
            let removed = classes.remove(remove_idx);
            for expr in removed {
                if !classes[keep_idx].contains(&expr) {
                    classes[keep_idx].push(expr);
                }
            }
        }
        (Some(idx), None) => {
            if !classes[idx].contains(right) {
                classes[idx].push(right.clone());
            }
        }
        (None, Some(idx)) => {
            if !classes[idx].contains(left) {
                classes[idx].push(left.clone());
            }
        }
        (None, None) => classes.push(vec![left.clone(), right.clone()]),
    }
}

fn derive_assertion_final_alias_substitutions(
    substitutions: &mut HashMap<String, PureExpr>,
    facts: &[PureExpr],
    assertion_free_vars: &HashSet<String>,
) {
    if assertion_free_vars.is_empty() {
        return;
    }
    for fact in facts {
        let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
            continue;
        };
        derive_assertion_final_alias_substitution_from_side(
            substitutions,
            left,
            right,
            assertion_free_vars,
        );
        derive_assertion_final_alias_substitution_from_side(
            substitutions,
            right,
            left,
            assertion_free_vars,
        );
    }
}

fn derive_assertion_final_alias_substitution_from_side(
    substitutions: &mut HashMap<String, PureExpr>,
    alias_side: &PureExpr,
    final_side: &PureExpr,
    assertion_free_vars: &HashSet<String>,
) {
    let PureExpr::Var(name, _) = alias_side else {
        return;
    };
    if !assertion_free_vars.contains(name) || substitutions.contains_key(name) {
        return;
    }
    if is_bare_final_carrier(final_side) {
        // fact-source: final_alias_substitutions
        substitutions.insert(name.clone(), final_side.clone());
    }
}

fn is_bare_final_carrier(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(_, _))
    )
}

fn expr_class_index(classes: &[Vec<PureExpr>], expr: &PureExpr) -> Option<usize> {
    classes
        .iter()
        .position(|class| class.iter().any(|member| member == expr))
}

fn expr_class_members(classes: &[Vec<PureExpr>], expr: &PureExpr) -> Vec<PureExpr> {
    expr_class_index(classes, expr)
        .map(|idx| classes[idx].clone())
        .unwrap_or_else(|| vec![expr.clone()])
}

pub(super) fn substitute_precise_final_update_carriers(
    expr: &PureExpr,
    facts: &[PureExpr],
) -> PureExpr {
    let aliases = collect_precise_final_update_aliases(facts);
    if aliases.is_empty() {
        return expr.clone();
    }
    rewrite_precise_final_update_expr(expr, &aliases, 0)
}

fn collect_precise_final_update_aliases(facts: &[PureExpr]) -> HashMap<PureExpr, PureExpr> {
    let mut aliases = HashMap::new();
    for fact in facts {
        let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
            continue;
        };
        collect_precise_final_update_alias_from_side(left, right, &mut aliases);
        collect_precise_final_update_alias_from_side(right, left, &mut aliases);
    }
    aliases
}

fn collect_precise_final_update_alias_from_side(
    final_side: &PureExpr,
    other_side: &PureExpr,
    aliases: &mut HashMap<PureExpr, PureExpr>,
) {
    let Some((name, depth)) = final_base_and_depth(final_side) else {
        return;
    };
    if depth == 0 {
        return;
    }
    if matches!(
        final_base_and_depth(other_side),
        Some((other_name, other_depth)) if other_name == name && other_depth < depth
    ) {
        return;
    }
    if final_update_alias_is_plain_var(other_side) {
        return;
    }
    aliases
        .entry(final_side.clone())
        .or_insert_with(|| other_side.clone());
}

fn final_update_alias_is_plain_var(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(_, _))
}

fn rewrite_precise_final_update_expr(
    expr: &PureExpr,
    aliases: &HashMap<PureExpr, PureExpr>,
    depth: usize,
) -> PureExpr {
    if depth > 16 {
        return expr.clone();
    }
    if let Some(alias) = aliases.get(expr) {
        return rewrite_precise_final_update_expr(alias, aliases, depth + 1);
    }
    match expr {
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(rewrite_precise_final_update_expr(left, aliases, depth)),
            *op,
            Arc::new(rewrite_precise_final_update_expr(right, aliases, depth)),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(rewrite_precise_final_update_expr(inner, aliases, depth)),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(rewrite_precise_final_update_expr(cond, aliases, depth)),
            Arc::new(rewrite_precise_final_update_expr(then_expr, aliases, depth)),
            Arc::new(rewrite_precise_final_update_expr(else_expr, aliases, depth)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(rewrite_precise_final_update_expr(
            inner, aliases, depth,
        ))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(rewrite_precise_final_update_expr(
            inner, aliases, depth,
        ))),
        PureExpr::Final(inner) => {
            let rewritten = PureExpr::Final(Arc::new(rewrite_precise_final_update_expr(
                inner, aliases, depth,
            )));
            aliases.get(&rewritten).map_or(rewritten, |alias| {
                rewrite_precise_final_update_expr(alias, aliases, depth + 1)
            })
        }
        PureExpr::View(inner) => PureExpr::View(Arc::new(rewrite_precise_final_update_expr(
            inner, aliases, depth,
        ))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(rewrite_precise_final_update_expr(receiver, aliases, depth)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_precise_final_update_expr(arg, aliases, depth))
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let bound_names = HashSet::from([var.as_str()]);
            let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
            PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(rewrite_precise_final_update_expr(
                    body,
                    &scoped_aliases,
                    depth,
                )),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|part| {
                                rewrite_precise_final_update_expr(part, &scoped_aliases, depth)
                            })
                            .collect()
                    })
                    .collect(),
            }
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => {
            let bound_names = HashSet::from([var.as_str()]);
            let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
            PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(rewrite_precise_final_update_expr(
                    body,
                    &scoped_aliases,
                    depth,
                )),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|part| {
                                rewrite_precise_final_update_expr(part, &scoped_aliases, depth)
                            })
                            .collect()
                    })
                    .collect(),
            }
        }
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(rewrite_precise_final_update_expr(scrutinee, aliases, depth)),
            arms: arms
                .iter()
                .map(|arm| {
                    let bound_names: HashSet<&str> =
                        arm.pattern.bound_names().into_iter().collect();
                    let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
                    trust_wp_core::formula::MatchArm {
                        pattern: arm.pattern.clone(),
                        body: rewrite_precise_final_update_expr(&arm.body, &scoped_aliases, depth),
                    }
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_precise_final_update_expr(arg, aliases, depth))
                .collect(),
        },
        PureExpr::Let { var, value, body } => {
            let bound_names = HashSet::from([var.as_str()]);
            let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
            PureExpr::Let {
                var: var.clone(),
                value: Arc::new(rewrite_precise_final_update_expr(value, aliases, depth)),
                body: Arc::new(rewrite_precise_final_update_expr(
                    body,
                    &scoped_aliases,
                    depth,
                )),
            }
        }
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(rewrite_precise_final_update_expr(
                assumption, aliases, depth,
            )),
            body: Arc::new(rewrite_precise_final_update_expr(body, aliases, depth)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(rewrite_precise_final_update_expr(
                obligation, aliases, depth,
            )),
            body: Arc::new(rewrite_precise_final_update_expr(body, aliases, depth)),
        },
        PureExpr::Closure { params, body } => {
            let bound_names: HashSet<&str> = params.iter().map(|(name, _)| name.as_str()).collect();
            let scoped_aliases = precise_aliases_without_bound_names(aliases, &bound_names);
            PureExpr::Closure {
                params: params.clone(),
                body: Arc::new(rewrite_precise_final_update_expr(
                    body,
                    &scoped_aliases,
                    depth,
                )),
            }
        }
        _ => expr.clone(),
    }
}

fn precise_aliases_without_bound_names(
    aliases: &HashMap<PureExpr, PureExpr>,
    bound_names: &HashSet<&str>,
) -> HashMap<PureExpr, PureExpr> {
    if bound_names.is_empty() {
        return aliases.clone();
    }
    aliases
        .iter()
        .filter(|(from, to)| {
            !expr_references_any_name(from, bound_names)
                && !expr_references_any_name(to, bound_names)
        })
        .map(|(from, to)| (from.clone(), to.clone()))
        .collect()
}

fn expr_references_any_name(expr: &PureExpr, names: &HashSet<&str>) -> bool {
    expr.free_vars()
        .iter()
        .any(|name| names.contains(name.as_str()))
}

fn filter_consumed_final_update_facts(
    facts: &mut Vec<PureExpr>,
    assertion: &PureExpr,
    call_obligations: &[PureExpr],
) {
    let mut referenced_final_roots = HashSet::new();
    collect_final_root_names(assertion, &mut referenced_final_roots);
    for obligation in call_obligations {
        collect_final_root_names(obligation, &mut referenced_final_roots);
    }
    facts.retain(|fact| {
        non_alias_final_update_fact_base(fact).is_none_or(|name| {
            referenced_final_roots.contains(&name) || is_concrete_final_update_fact(fact)
        })
    });
}

fn is_concrete_final_update_fact(fact: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return false;
    };
    is_concrete_final_update_side(left, right) || is_concrete_final_update_side(right, left)
}

fn is_concrete_final_update_side(final_side: &PureExpr, other_side: &PureExpr) -> bool {
    if final_base_and_depth(final_side).is_none_or(|(_, depth)| depth == 0) {
        return false;
    }
    matches!(
        other_side,
        PureExpr::MethodCall { .. } | PureExpr::LogicFnCall { .. } | PureExpr::View(_)
    )
}

fn collect_final_root_names(expr: &PureExpr, roots: &mut HashSet<String>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::Final(inner) = node {
            if let Some((name, _)) = final_base_and_depth(inner) {
                roots.insert(name);
            }
        }
    });
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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, PureExpr};

    use super::{derive_has_mutating_call_effect, drop_stale_param_facts, names_its_own_binding};

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn eq(lhs: PureExpr, value: i64) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(PureExpr::Int(value)))
    }

    fn stale(names: &[&str]) -> crate::mir_analysis::InvalidatedEntryNames {
        crate::mir_analysis::InvalidatedEntryNames {
            params: names.iter().map(|name| (*name).to_string()).collect(),
            unnamed: false,
        }
    }

    /// `#[requires(x@ == 1 && y@ == 2)]` with `x` re-bound keeps `y@ == 2`,
    /// which the conjunction implies alone
    /// (proof_assert_param_rebind_keeps_other_entry_facts_control.rs).
    #[test]
    fn a_stale_conjunct_is_dropped_and_its_sibling_kept() {
        let mut facts = vec![PureExpr::BinOp(
            Arc::new(eq(var("x"), 1)),
            BinOp::And,
            Arc::new(eq(var("y"), 2)),
        )];
        assert_eq!(drop_stale_param_facts(&mut facts, &stale(&["x"])), 1);
        assert_eq!(facts, vec![eq(var("y"), 2)]);
    }

    /// A disjunct guards its branch: `x@ == 1 || y@ == 2` is not `y@ == 2`.
    #[test]
    fn a_disjunction_naming_a_stale_parameter_goes_whole() {
        let mut facts = vec![
            PureExpr::BinOp(
                Arc::new(eq(var("x"), 1)),
                BinOp::Or,
                Arc::new(eq(var("y"), 2)),
            ),
            eq(var("z"), 3),
        ];
        assert_eq!(drop_stale_param_facts(&mut facts, &stale(&["x"])), 1);
        assert_eq!(facts, vec![eq(var("z"), 3)]);
    }

    /// An argument with no name of its own (a closure's environment) makes
    /// every fact stale.
    #[test]
    fn an_unnamed_stale_argument_drops_every_fact() {
        let mut facts = vec![eq(var("y"), 2), eq(var("z"), 3)];
        let mut names = stale(&[]);
        names.unnamed = true;
        assert_eq!(drop_stale_param_facts(&mut facts, &names), 2);
        assert!(facts.is_empty());
    }

    /// `x -> y`, `x -> 7` and `x -> call_N` re-bind `x`; `x -> x`, its view
    /// and the prophecy `^x` a `&mut x` call leaves do not.
    #[test]
    fn only_a_value_other_than_the_parameter_itself_re_binds_it() {
        assert!(names_its_own_binding("x", &var("x")));
        assert!(names_its_own_binding(
            "x",
            &PureExpr::View(Arc::new(var("x")))
        ));
        assert!(names_its_own_binding(
            "x",
            &PureExpr::Final(Arc::new(var("x")))
        ));
        assert!(!names_its_own_binding("x", &var("y")));
        assert!(!names_its_own_binding("x", &PureExpr::Int(7)));
        assert!(!names_its_own_binding("x", &var("$call_4")));
    }

    #[test]
    fn wrapped_postcondition_mut_recovers_mutating_provenance() {
        let wrapped_mutating_effect = PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                method: "postcondition_mut".to_string(),
                args: vec![
                    PureExpr::Var("arg".to_string(), None),
                    PureExpr::Var("state".to_string(), None),
                    PureExpr::Var("result".to_string(), None),
                ],
            }),
            body: Arc::new(PureExpr::Bool(true)),
        };
        let wrapped_non_mutating_effect = PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
                method: "postcondition".to_string(),
                args: vec![
                    PureExpr::Var("arg".to_string(), None),
                    PureExpr::Var("result".to_string(), None),
                ],
            }),
            body: Arc::new(PureExpr::Bool(true)),
        };

        assert!(
            derive_has_mutating_call_effect(false, false, Some(&wrapped_mutating_effect)),
            "wrapped postcondition_mut call effect should recover mutating provenance"
        );
        assert!(
            !derive_has_mutating_call_effect(false, false, Some(&wrapped_non_mutating_effect)),
            "non-mutating wrapped call effect should not be treated as mutating"
        );
    }
}
