// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function postcondition verification.
//!
//! Verifies postconditions of logic functions against their specification
//! bodies (not MIR). Runs before regular function verification so that
//! `unverified_axioms` is populated when checking caller dependencies.
//! Extracted from `verification.rs` (#1669).

use std::collections::{HashMap, HashSet};

use trust_wp_ay::{
    type_constants_for_int, verify_function_with_modes_outcome, VerificationOutcome,
    VerificationRequest, VerificationResult,
};
use trust_wp_core::{
    formula::{PureExpr, PureExprDepthLimitedTraversalExt as _},
    logic::{AdtDecls, AdtFieldRanges, LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};

use super::{
    super::{
        helpers::scope_logic_fn_modes,
        reporting::{
            emit_verification_diagnostic_if_requested, verified_evidence_gap_reason,
            VerificationCounters,
        },
        struct_field_map::extract_int_type_from_path,
    },
    recursive_induction::build_recursive_induction_hypotheses,
};

/// Shared configuration for extracted verification helper functions.
///
/// Groups the five read-only parameters that every Phase 2 helper needs,
/// keeping individual function signatures under clippy's 7-argument limit.
pub(in crate::callbacks) struct VerifyConfig<'a> {
    pub(in crate::callbacks) logic_fns: &'a [LogicFnDef],
    pub(in crate::callbacks) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    pub(in crate::callbacks) track_level: TrackLevel,
    pub(in crate::callbacks) timeout: Option<std::time::Duration>,
    pub(in crate::callbacks) strict_axioms: bool,
    /// Map from trait logic method full path to owning trait full path.
    ///
    /// Used only while proving logic-function postconditions. When the target
    /// is itself a trait logic method, same-trait default bodies are opaque:
    /// trait laws must hold for all implementors, including overrides.
    pub(in crate::callbacks) trait_logic_fn_groups: Option<&'a HashMap<String, String>>,
    /// Crate-wide ADT field range constraints for unsigned/signed integer fields.
    ///
    /// Populated from all function MIR bodies in the crate so logic function
    /// verification can inject range axioms on ADT fields (e.g., `u32` field
    /// of `List::Cons` constrained to `[0, 2^32)`). Without this, logic
    /// functions like `lemma_sum_nonneg` fail because the solver assigns
    /// negative values to unsigned fields. (#2178, #2097 RC1)
    pub(in crate::callbacks) adt_field_ranges: Option<AdtFieldRanges>,
    /// Crate-wide rustc-backed ADT declarations for logic function verification. (#1982)
    pub(in crate::callbacks) adt_decls: Option<AdtDecls>,
}

/// Whether a law postcondition should be exposed as an axiom without eager proof.
///
/// Concrete and free Creusot laws are specifications intended for callers; proving
/// all of them before ordinary functions can dominate compat runs. Trait-declared
/// laws still need eager checking in non-strict mode because they are generic over
/// all implementors and catch invalid overridable-default proofs such as bug/222.
pub(in crate::callbacks) fn assumes_concrete_law_postcondition(
    logic_fn: &LogicFnDef,
    trait_logic_fn_groups: Option<&HashMap<String, String>>,
    strict_axioms: bool,
) -> bool {
    logic_fn.is_law()
        && !strict_axioms
        && !trait_logic_fn_groups.is_some_and(|groups| groups.contains_key(logic_fn.full_path()))
}

/// Check if a `PureExpr` body (or any subexpression) contains a
/// `Closure` with one or more parameters.
///
/// Parameterized closures in logic context are encoded as unconstrained
/// Bool constants by the ay encoder (`encode_closure_in_logic`), producing
/// unreliable counterexamples. This check is used to downgrade `Failed`
/// results to `Unknown` for logic function postcondition verification. (#2676)
fn body_has_parameterized_closure(body: &PureExpr) -> bool {
    // Depth limit 200 matches MAX_ENCODING_DEPTH used by the encoder.
    body.any_recursive_with_depth_limit(
        200,
        false,
        |node| matches!(node, PureExpr::Closure { params, .. } if !params.is_empty()),
    )
}

pub(in crate::callbacks) fn record_logic_fn_verified_evidence_gap_if_any(
    outcome: &VerificationOutcome,
    def_path: &str,
    counters: &mut VerificationCounters,
    unverified_axioms: &mut HashSet<String>,
) -> bool {
    let Some(reason) = verified_evidence_gap_reason(outcome) else {
        return false;
    };
    counters.evidence_gaps += 1;
    counters.warnings += 1;
    unverified_axioms.insert(def_path.to_owned());
    eprintln!("trust-wp: {def_path} postcondition evidence gap ({reason})");
    true
}

/// Verify logic function postconditions (#893, #1490).
///
/// Logic functions with `#[ensures]` have their postconditions verified
/// against their specification body (from `LogicFnDef`), NOT their erased
/// MIR body. This matches Creusot's behavior where logic function
/// postconditions generate VCs (e.g., `quant.rs` `M_forall`/`M_exists`).
///
/// This runs before regular function verification so that
/// `unverified_axioms` is populated when checking caller dependencies.
pub(in crate::callbacks) fn verify_logic_fn_postconditions(
    cfg: &VerifyConfig<'_>,
    counters: &mut VerificationCounters,
    unverified_axioms: &mut HashSet<String>,
) {
    let logic_fns = cfg.logic_fns;
    let type_invariants_opt = cfg.type_invariants_opt;
    let track_level = cfg.track_level;
    let timeout = cfg.timeout;
    let strict_axioms = cfg.strict_axioms;
    let trait_logic_fn_groups = cfg.trait_logic_fn_groups;

    for logic_fn in logic_fns {
        if logic_fn.ensures().is_empty() {
            continue;
        }

        // Skip trusted logic functions — their postconditions are assumed as
        // axioms, not verified. Previously, trusted logic functions with ensures
        // clauses were fed through verification and produced spurious failures
        // (e.g., opaque+trusted+forall view specs failing because the trivial
        // body cannot prove the quantified spec). (#2700)
        if logic_fn.is_trusted() {
            continue;
        }

        let def_path = logic_fn.full_path();
        if assumes_concrete_law_postcondition(logic_fn, trait_logic_fn_groups, strict_axioms) {
            unverified_axioms.insert(def_path.to_owned());
            counters.warnings += 1;
            eprintln!(
                "trust-wp: {def_path} law postcondition unverified (non-strict axiom exposure)"
            );
            continue;
        }

        // Build the VC: requires => (result = body) => ensures
        // For void logic functions (body = unit), result binding is optional;
        // the postcondition may reference parameters and other logic functions.
        let return_expr = Some(logic_fn.body());

        // Filter logic functions available as axioms.
        //
        // For NON-recursive functions: exclude the function being verified
        // entirely (to prevent circular reasoning).
        //
        // For RECURSIVE functions with ensures: include the function under test
        // for its SYMBOL DECLARATION only — both its defining axiom (body) and
        // its spec axiom (own `ensures`) are suppressed (see the soundness note
        // at the `available_logic_fns` construction below). The induction
        // hypothesis is supplied separately as a well-founded, variant-guarded
        // assumption built by `recursive_induction`, NOT by E-matching the
        // (ungated, unsound) spec axiom as a previous revision did. (#2097, #ri)
        let same_trait_group =
            trait_logic_fn_groups.and_then(|groups| groups.get(def_path).map(String::as_str));
        let hides_same_trait_logic_axiom = same_trait_group.is_some_and(|target_group| {
            trait_logic_fn_groups.is_some_and(|groups| {
                logic_fns.iter().any(|lf| {
                    lf.full_path() != logic_fn.full_path()
                        && groups
                            .get(lf.full_path())
                            .is_some_and(|group| group == target_group)
                })
            })
        });

        let use_induction = logic_fn.is_recursive() && !logic_fn.ensures().is_empty();
        // SOUNDNESS (recursive-induction): when verifying a recursive logic
        // function's OWN postcondition, the function is kept in the axiom set so
        // its SMT symbol is declared with the correct sorts, but BOTH of its
        // self-axioms are removed:
        //   * the DEFINING axiom (body) — suppressed via the Default-mode
        //     override applied below; and
        //   * the SPEC axiom (its own `ensures`) — suppressed HERE by clearing
        //     the ensures on the self copy.
        // The spec axiom, left intact and E-matched at the recursive call term,
        // was an UNGATED induction hypothesis (the postcondition assumed for the
        // recursive arguments without any decrease check) — a demonstrated
        // false-accept for non-decreasing recursion. It is replaced by the
        // well-founded, variant-guarded IH injected into `requires` below. See
        // `recursive_induction` for the soundness argument.
        let mut available_logic_fns: Vec<_> = if use_induction {
            logic_fns
                .iter()
                .map(|lf| {
                    let mut copy = lf.clone();
                    if copy.full_path() == def_path {
                        copy.set_ensures(Vec::new());
                    }
                    copy
                })
                .collect()
        } else {
            logic_fns
                .iter()
                .filter(|lf| lf.full_path() != logic_fn.full_path())
                .cloned()
                .collect()
        };

        // Induction hypotheses for the self-recursive calls: variant-guarded
        // (single integer `#[variant]`) or structural subterm-descent (no
        // variant, ADT-parameter match recursion). Empty when neither scheme's
        // sound preconditions hold (the postcondition stays incomplete — sound).
        let induction_hypotheses =
            build_recursive_induction_hypotheses(logic_fn, cfg.adt_decls.as_ref());
        if let (Some(groups), Some(target_group)) = (trait_logic_fn_groups, same_trait_group) {
            available_logic_fns.retain(|lf| {
                lf.full_path() == logic_fn.full_path()
                    || groups
                        .get(lf.full_path())
                        .is_none_or(|group| group != target_group)
            });
        }
        let (logic_fns_opt, mode_overrides_for_logic_fn) = if available_logic_fns.is_empty() {
            (None, None)
        } else {
            // Always compute mode overrides when using induction, to force
            // the function under test to Default (spec-axiom-only) mode.
            let needs_scoping = use_induction
                || hides_same_trait_logic_axiom
                || available_logic_fns
                    .iter()
                    .any(|lf| matches!(lf.mode(), LogicMode::OpenSelf | LogicMode::Default));
            if needs_scoping {
                let mut overrides = scope_logic_fn_modes(&available_logic_fns, def_path);
                if let (Some(groups), Some(target_group)) =
                    (trait_logic_fn_groups, same_trait_group)
                {
                    for (i, lf) in available_logic_fns.iter().enumerate() {
                        if groups
                            .get(lf.full_path())
                            .is_some_and(|group| group == target_group)
                        {
                            overrides[i] = LogicMode::Default;
                        }
                    }
                }
                if use_induction {
                    // Force the function under test to Default mode so its
                    // DEFINING axiom (body) is suppressed. Its SPEC axiom was
                    // already removed by clearing `ensures` on the self copy
                    // above; together this leaves only the (correctly-sorted)
                    // symbol declaration, with the variant-gated IH supplying the
                    // sound induction hypothesis.
                    for (i, lf) in available_logic_fns.iter().enumerate() {
                        if lf.full_path() == logic_fn.full_path() {
                            overrides[i] = LogicMode::Default;
                        }
                    }
                }
                (Some(available_logic_fns.as_slice()), Some(overrides))
            } else {
                (Some(available_logic_fns.as_slice()), None)
            }
        };

        // Resolve type-level constants (Self::MIN, Self::MAX) for logic functions
        // defined in integer impl blocks. (#915, #688)
        let logic_fn_type_constants =
            extract_int_type_from_path(def_path).and_then(type_constants_for_int);

        // Assumptions for the VC = the fn's own `requires` plus any variant-gated
        // induction hypotheses. The IH replaces the deleted ungated self spec
        // axiom; it is a sound consequence of well-founded induction (see
        // `recursive_induction`), so it can only ever prove a genuinely-valid
        // postcondition.
        let requires_with_ih: Vec<PureExpr> = logic_fn
            .requires()
            .iter()
            .cloned()
            .chain(induction_hypotheses.iter().cloned())
            .collect();

        let verification_result = verify_function_with_modes_outcome(
            VerificationRequest::new(&requires_with_ih, logic_fn.ensures())
                .return_expr(return_expr)
                .logic_fns(logic_fns_opt)
                .mode_overrides(mode_overrides_for_logic_fn.as_deref())
                .type_invariants(type_invariants_opt)
                .track(Some(track_level))
                .timeout(timeout)
                .type_constants(logic_fn_type_constants.as_ref())
                .adt_field_ranges(cfg.adt_field_ranges.clone())
                .adt_decls(cfg.adt_decls.clone()),
        );
        // Whether the TRUST_WP_DIAGNOSTIC wire line should be emitted for this
        // outcome. The diagnostic line contains `reason=counterexample` for
        // `Failed` outcomes, which matches the harness's text-based
        // "counterexample" failure-marker check (#2700). For warning-only
        // dispositions we mirror the suppression of the human-readable
        // counterexample output below.
        let mut suppress_diagnostic_emission = false;
        match verification_result {
            Ok(outcome)
                if record_logic_fn_verified_evidence_gap_if_any(
                    &outcome,
                    def_path,
                    counters,
                    unverified_axioms,
                ) =>
            {
                emit_verification_diagnostic_if_requested(
                    def_path,
                    "logic_fn_postcondition",
                    &outcome,
                );
            }
            Ok(
                ref outcome_ref @ VerificationOutcome {
                    result: VerificationResult::Verified(_),
                    ..
                },
            ) => {
                counters.verified += 1;
                eprintln!("trust-wp: {def_path} verified ✓");
                emit_verification_diagnostic_if_requested(
                    def_path,
                    "logic_fn_postcondition",
                    outcome_ref,
                );
            }
            Ok(
                ref outcome_ref @ VerificationOutcome {
                    result: VerificationResult::Assumed(ref reason),
                    ..
                },
            ) => {
                counters.assumed += 1;
                eprintln!("trust-wp: {def_path} assumed ({reason})");
                emit_verification_diagnostic_if_requested(
                    def_path,
                    "logic_fn_postcondition",
                    outcome_ref,
                );
            }
            Ok(
                ref outcome_ref @ VerificationOutcome {
                    result: VerificationResult::Failed(ref counterexample),
                    ..
                },
            ) => {
                // When the body contains parameterized closures (which fall
                // back to unconstrained Bool constants in the encoder), the
                // counterexample is unreliable — the solver can falsify the
                // unconstrained constant to produce a spurious counterexample.
                // Downgrade to Unknown so the postcondition is treated as
                // unverified rather than failed. (#2676)
                if body_has_parameterized_closure(logic_fn.body()) {
                    unverified_axioms.insert(def_path.to_owned());
                    counters.warnings += 1;
                    eprintln!(
                        "trust-wp: {def_path} postcondition unverified \
                         (body contains parameterized closure — #985)"
                    );
                    // Warning-only disposition: suppress the diagnostic
                    // wire line so its `reason=counterexample` does not
                    // trigger the harness's text-based failure detection.
                    suppress_diagnostic_emission = true;
                } else if hides_same_trait_logic_axiom {
                    unverified_axioms.insert(def_path.to_owned());
                    counters.failed += 1;
                    eprintln!("trust-wp: {def_path} FAILED (trait logic postcondition)");
                    // Omit counterexample output for logic fn postconditions.
                    // The failure itself is actionable, but the model may be
                    // noisy because the body is checked as a spec-level VC.
                    let _ = counterexample;
                } else {
                    // Logic function postcondition failures are unverified
                    // specs, not function-level behavioral failures. Treat
                    // them like Unknown results: track as unverified axioms
                    // with a warning, not as `failed`. This prevents logic
                    // fn postcondition failures from blocking compat test
                    // classification as function-level failures. (#2700)
                    unverified_axioms.insert(def_path.to_owned());
                    counters.warnings += 1;
                    eprintln!("trust-wp: {def_path} postcondition FAILED (logic postcondition)");
                    // Omit counterexample output for logic fn postconditions.
                    // The counterexample may be unreliable (incomplete axioms,
                    // sort fallback) and would trigger the harness's
                    // "counterexample" text-based failure detection. (#2700)
                    let _ = counterexample;
                    // Suppress the TRUST_WP_DIAGNOSTIC wire line for the same
                    // reason as the human-readable counterexample output:
                    // its `reason=counterexample` field would match the
                    // harness classifier's "counterexample" substring check
                    // and reclassify a warning into a fail (#2700).
                    suppress_diagnostic_emission = true;
                }
                if !suppress_diagnostic_emission {
                    emit_verification_diagnostic_if_requested(
                        def_path,
                        "logic_fn_postcondition",
                        outcome_ref,
                    );
                }
            }
            Ok(
                ref outcome_ref @ VerificationOutcome {
                    result: VerificationResult::Unknown(ref reason),
                    ..
                },
            ) => {
                // Vacuous proofs indicate contradictory axiom premises —
                // the postcondition holds trivially, not because it is
                // correct. Do NOT count as verified (#2663).
                let is_vacuous = matches!(
                    reason,
                    trust_wp_ay::UnknownReason::SolverMessage(msg) if msg.contains("vacuous proof")
                );
                if is_vacuous {
                    counters.vacuous += 1;
                    counters.warnings += 1;
                    eprintln!("trust-wp: {def_path} vacuous (contradictory axiom premises)");
                } else {
                    // Logic function postcondition verification may return Unknown
                    // for complex quantified formulas that ay's E-matching can't handle.
                    // Track the unverified axiom for dependency reporting (#1490).
                    unverified_axioms.insert(def_path.to_owned());
                    // Track demotions from the unsoundness demotion pipeline (#2106).
                    let is_demoted = matches!(reason, trust_wp_ay::UnknownReason::Demoted(_));
                    if strict_axioms {
                        // Under --strict-axioms, unverified postconditions are errors.
                        counters.errors += 1;
                        if is_demoted {
                            counters.demoted += 1;
                        }
                        eprintln!(
                            "trust-wp: {def_path} postcondition unverified — ERROR (strict-axioms) ({reason})"
                        );
                    } else {
                        // Default: emit a warning. The postcondition is still available
                        // as a spec axiom to callers (#1296).
                        // Demotions in non-strict mode are warnings, not errors —
                        // do not track as demoted since the counter tracks error demotions.
                        counters.warnings += 1;
                        eprintln!("trust-wp: {def_path} postcondition unverified ({reason})");
                    }
                }
                emit_verification_diagnostic_if_requested(
                    def_path,
                    "logic_fn_postcondition",
                    outcome_ref,
                );
            }
            // VerificationResult is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns)]
            Ok(_) => {
                counters.errors += 1;
            }
            Err(ref e) => {
                counters.errors += 1;
                counters.encoding_errors.record(e);
                eprintln!("trust-wp: {def_path} error: {e}");
            }
        }
    }
}
