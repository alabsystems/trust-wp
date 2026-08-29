// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

pub(super) use ay_dpll::api::Sort;
pub(super) use ntest::timeout;
pub(super) use trust_wp_core::formula::{BinOp, ExprSort, NamedBindingValue};

pub(super) use super::{
    encoder_setup::{
        collect_loop_sort_plan, encode_and_assert_condition, encode_and_assert_requires,
        is_base_vacuous, propagate_bool_and_predeclare, resolve_sat_result_lightweight,
        resolve_sat_result_lightweight_timed, setup_loop_encoder, solve_scoped_loop_obligation,
        solve_scoped_loop_obligation_with_base_recheck,
    },
    expr_helpers::{
        collect_expr_var_names, collect_final_var_names, expr_has_chain_projection,
        expr_references_any_var, strip_scalar_views,
    },
    initialization::loop_entry_may_execute,
    invariant_transforms::{
        inject_forall_triggers, normalize_fmap_get_biconditional, relax_single_var_multitriggers,
    },
    prime_substitutions::{build_prime_substitutions, sort_to_expr_sort},
    *,
};
pub(super) use crate::{tests::helpers::*, UnknownReason};

mod alias_substitution;
mod body_break;
mod core_verification;
mod encoder_helpers;
mod entry_and_initialization;
mod fixtures;
mod fmap_iter;
mod logic_fn_filter;
mod logic_selection;
mod loop_invariant_patterns;
mod postcondition_regressions;
mod postcondition_slicing;
mod seq_iter;
mod sorts_and_borrow;
mod trigger_injection;
mod type_invariant_maintenance;
mod unchanged_mut_refs;
mod variant_edge_cases;
mod walker_helpers;
mod while_loop_patterns;

use self::{
    body_break::{i_effect, i_ge_zero, i_le_n, i_lt_n, i_var, modified_i, n_ge, n_var},
    fixtures::{
        effects, postcondition_inputs, verify_initialization, verify_initialization_outcome,
        verify_postcondition, verify_postcondition_outcome, verify_preservation_with_config,
        verify_variant_decrease, verify_variant_nonneg,
    },
};

#[test]
fn loop_phase_timeout_preserves_critical_phase_floor_after_early_spend() {
    let timeout = loop_phase_timeout(
        Some(std::time::Duration::from_secs(20)),
        std::time::Duration::from_secs(11),
        2,
        LOOP_CRITICAL_PHASE_MIN_TIMEOUT,
    );

    assert_eq!(timeout, Some(std::time::Duration::from_secs(8)));
}

#[test]
fn loop_phase_timeout_keeps_short_total_budgets_bounded() {
    let timeout = loop_phase_timeout(
        Some(std::time::Duration::from_secs(5)),
        std::time::Duration::from_secs(1),
        2,
        LOOP_CRITICAL_PHASE_MIN_TIMEOUT,
    );

    assert_eq!(timeout, Some(std::time::Duration::from_secs(5)));
}

/// Per-sub-check panic isolation (#2273): when preservation triggers a ay sort
/// mismatch panic, the initialization result is preserved (not replaced with
/// Unknown). Before #2273, the outer `catch_ay_sort_panics_loop` wrapper
/// discarded all sub-results on any single panic.
#[test]
#[timeout(30000)]
fn preservation_panic_preserves_init_result() {
    // Invariant: `flag` (Bool variable) — trivially verifiable for init when
    // flag is asserted as an init_extra_fact.
    let invariants = vec![PureExpr::Var("flag".to_string(), None)];
    let init_extra_facts = vec![PureExpr::Var("flag".to_string(), None)];

    // Body effect: map `flag` to Int(42) — a Bool→Int sort mismatch that will
    // cause a ay panic when preservation encodes `flag_next = 42`.
    let mut body_effect = HashMap::new();
    body_effect.insert("flag".to_string(), PureExpr::Int(42));
    let empty_effect = HashMap::new();
    let pre_loop_assignments = HashMap::new();
    let loop_condition = PureExpr::Bool(true);

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&loop_condition),
        condition_is_body_break: false,
        modified_vars: &["flag"],
        body_effect: &body_effect,
        deref_body_effect: &empty_effect,
        double_deref_body_effect: &empty_effect,
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &init_extra_facts,
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("encoding should not hard-error");

    // Init should still be Verified — the body effect sort mismatch only
    // affects preservation, not initialization.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should be Verified even when preservation panics; got {:?}",
        result.initialization
    );

    // Preservation: the Bool→Int sort mismatch formerly triggered a ay panic
    // caught by the per-sub-check wrapper (→ Unknown). A later Bool→Int
    // coercion encoded `ite(flag_next, 1, 0) == 42` — which is UNSAT, so the
    // "Verified" it produced was VACUOUS (contradictory premises), a false
    // pass. The bool-vs-out-of-range-int-literal guard now encodes the
    // unencodable equality as a polarity-neutral fresh Bool: `flag_next` is
    // left unconstrained and preservation honestly FAILS with a
    // counterexample (or stays Unknown on the panic path). It must NOT be
    // Verified — that would require the vacuous premise collapse.
    assert!(
        matches!(
            result.preservation,
            VerificationResult::Failed(_) | VerificationResult::Unknown(_)
        ),
        "preservation should be Failed (unconstrained honest cex) or Unknown (panic); got {:?}",
        result.preservation
    );
}
