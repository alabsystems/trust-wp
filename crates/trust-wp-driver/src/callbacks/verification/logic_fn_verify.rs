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

mod assertions;
mod callee_preconditions;
mod parameter_sorts;
mod stale_credits;

use assertions::{assertion_goal, AssertionGoal};
use callee_preconditions::{
    callee_precondition_goal, integer_params, owed_requires, own_premises, CalleePreconditionGoal,
};
pub(in crate::callbacks) use callee_preconditions::{
    BodyCallees, LogicBodyCallees, ProgramFnsWithRequires, RecordedBody, ResolvedCallee,
};
use stale_credits::LogicCreditKind;
pub(in crate::callbacks) use stale_credits::LogicCredits;

use super::{
    super::{
        function_credit::{grant_function_credit, CreditKind, FunctionCredit, OwnAssertions},
        helpers::scope_logic_fn_modes,
        reporting::{
            emit_verification_diagnostic_if_requested, verified_evidence_gap_reason,
            VerificationCounters,
        },
        struct_field_map::extract_int_type_from_path,
    },
    prep::neutralized,
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
    /// Full paths of bodyless trait logic methods whose postcondition each
    /// implementation owes (`logic_impl_discharge`). Such a declaration's
    /// `body` is a transport placeholder, so checking its `ensures` against
    /// it proves nothing about any code.
    pub(in crate::callbacks) impl_owed_postconditions: Option<&'a HashSet<String>>,
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
    /// The crate's program functions with a precondition: a logic body that
    /// may call one is refused (`callee_preconditions`).
    pub(in crate::callbacks) program_fns_with_requires: Option<&'a ProgramFnsWithRequires>,
    /// What rustc resolved each logic body's calls to (`prep::logic_body_callees`):
    /// the callee-precondition walk owes what those definitions require.
    pub(in crate::callbacks) logic_body_callees: &'a LogicBodyCallees,
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

/// Whether Creusot emits a `vc_` goal for this function: it has a written
/// `requires`, an `ensures` or a `variant`.
fn has_user_contract(logic_fn: &LogicFnDef) -> bool {
    !logic_fn.ensures().is_empty()
        || !owed_requires(logic_fn).is_empty()
        || !logic_fn.variants().is_empty()
}

/// Report a logic function's own-assertion verdict and count it once as the
/// function's failure or error when it is not a proof.
///
/// The assertion line is spelled exactly as the in-function pass spells its
/// own (`proof_assert in <path> <verdict>`): the goal-coverage gate credits a
/// `verified ✓` of that form and reads any other spelling as a negative.
fn report_logic_fn_assertions(
    def_path: &str,
    outcome: &Result<VerificationOutcome, trust_wp_ay::EncodingError>,
    counters: &mut VerificationCounters,
    creditable: bool,
) -> OwnAssertions {
    let own = match outcome {
        Ok(
            proved @ VerificationOutcome {
                result: VerificationResult::Verified(_),
                ..
            },
        ) if verified_evidence_gap_reason(proved).is_none() => OwnAssertions::AllProved,
        Ok(VerificationOutcome {
            result: VerificationResult::Failed(_),
            ..
        }) => OwnAssertions::Refuted,
        _ => OwnAssertions::Unproved,
    };
    let verdict = match own {
        OwnAssertions::AllProved if creditable => {
            counters.logic_assertions_verified += 1;
            eprintln!("trust-wp: proof_assert in {def_path} verified \u{2713}");
            String::new()
        }
        // A function whose postcondition no lane here proves (a trait logic
        // method declaration, owed by each implementation) earns no credit from
        // its proved assertions and they are not counted: counting them would
        // make a run whose other obligations went unproved read as having
        // verified something (logic_law_unproved_credited_by_its_assertion.rs).
        OwnAssertions::AllProved => {
            eprintln!(
                "trust-wp: proof_assert in {def_path} proved, not credited: the function's postcondition is not proved"
            );
            String::new()
        }
        OwnAssertions::Refuted => {
            counters.failed += 1;
            eprintln!("trust-wp: proof_assert in {def_path} FAILED \u{2717}");
            format!("trust-wp: {def_path} FAILED \u{2717} (proof_assert)")
        }
        OwnAssertions::Unproved => {
            counters.errors += 1;
            eprintln!("trust-wp: proof_assert in {def_path} unknown");
            format!("trust-wp: {def_path} unknown (proof_assert not proved)")
        }
    };
    if !verdict.is_empty() {
        eprintln!("{verdict}");
    }
    if let Ok(outcome) = outcome {
        emit_verification_diagnostic_if_requested(def_path, "logic_fn_proof_assert", outcome);
    } else if let Err(e) = outcome {
        counters.encoding_errors.record(e);
        eprintln!("trust-wp: {def_path} error: {e}");
    }
    own
}

/// What the preconditions a logic function owes its callees came to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CalleePreconditions {
    /// Proved, or the body owes none.
    Proved,
    Refuted,
    /// Not refuted, but no proof: unknown, an evidence gap, an encoding error
    /// or a call the body walk refused to place.
    Unproved,
}

/// Report the callee-precondition verdict of a logic function and count it
/// once as the function's failure or error when it is not a proof. A proof
/// prints nothing of its own: it is one of the things the function's credit
/// line stands on, never a credit by itself.
fn report_logic_fn_callee_preconditions(
    def_path: &str,
    outcome: &Result<VerificationOutcome, trust_wp_ay::EncodingError>,
    counters: &mut VerificationCounters,
) -> CalleePreconditions {
    let verdict = match outcome {
        Ok(
            proved @ VerificationOutcome {
                result: VerificationResult::Verified(_),
                ..
            },
        ) if verified_evidence_gap_reason(proved).is_none() => CalleePreconditions::Proved,
        Ok(VerificationOutcome {
            result: VerificationResult::Failed(_),
            ..
        }) => CalleePreconditions::Refuted,
        _ => CalleePreconditions::Unproved,
    };
    match verdict {
        CalleePreconditions::Proved => {}
        CalleePreconditions::Refuted => {
            counters.failed += 1;
            eprintln!("trust-wp: {def_path} FAILED \u{2717} (logic callee precondition)");
        }
        CalleePreconditions::Unproved => {
            counters.errors += 1;
            eprintln!("trust-wp: {def_path} unknown (logic callee precondition not proved)");
        }
    }
    match outcome {
        Ok(outcome) => emit_verification_diagnostic_if_requested(
            def_path,
            "logic_fn_callee_precondition",
            outcome,
        ),
        Err(e) => {
            counters.encoding_errors.record(e);
            eprintln!("trust-wp: {def_path} error: {e}");
        }
    }
    verdict
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
///
/// Returns the credits it granted, each with the axioms its proof
/// environment had already neutralized: a credit whose goal reaches an axiom
/// lost after that is withdrawn by [`LogicCredits::withdraw_stale`].
pub(in crate::callbacks) fn verify_logic_fn_postconditions(
    cfg: &VerifyConfig<'_>,
    counters: &mut VerificationCounters,
    unverified_axioms: &mut HashSet<String>,
) -> LogicCredits {
    let logic_fns = cfg.logic_fns;
    let type_invariants_opt = cfg.type_invariants_opt;
    let track_level = cfg.track_level;
    let timeout = cfg.timeout;
    let strict_axioms = cfg.strict_axioms;
    let trait_logic_fn_groups = cfg.trait_logic_fn_groups;

    let mut credits = LogicCredits::default();
    for (index, logic_fn) in logic_fns.iter().enumerate() {
        let typed = if !logic_fn.is_trusted() && has_user_contract(logic_fn) {
            match parameter_sorts::annotate(logic_fn) {
                Ok(typed) => Some(typed),
                Err(why) => {
                    counters.errors += 1;
                    unverified_axioms.insert(logic_fn.full_path().to_string());
                    eprintln!(
                        "trust-wp: {} error: {why}; logic obligations refused",
                        logic_fn.full_path()
                    );
                    continue;
                }
            }
        } else {
            None
        };
        let logic_fn = typed.as_ref().unwrap_or(logic_fn);
        // A logic function's own assertions and its callees' preconditions
        // are goals only when it has a contract: Creusot's `translate_logic`
        // emits no `vc_` otherwise.
        let owes_body_goals = !logic_fn.is_trusted() && has_user_contract(logic_fn);
        let assertion_goal = if owes_body_goals {
            assertion_goal(logic_fn.body())
        } else {
            AssertionGoal::None
        };
        let callee_goal = if owes_body_goals {
            callee_precondition_goal(
                logic_fn.body(),
                logic_fns,
                cfg.program_fns_with_requires,
                cfg.logic_body_callees.resolution(logic_fn.full_path()),
                &integer_params(logic_fn),
            )
        } else {
            CalleePreconditionGoal::None
        };
        let owes_body_goal =
            assertion_goal != AssertionGoal::None || callee_goal != CalleePreconditionGoal::None;
        if logic_fn.ensures().is_empty() && !owes_body_goal {
            continue;
        }

        // Skip trusted logic functions — their postconditions are assumed as
        // axioms, not verified. Previously, trusted logic functions with ensures
        // clauses were fed through verification and produced spurious failures
        // (e.g., opaque+trusted+forall view specs failing because the trivial
        // body cannot prove the quantified spec). (#2700)
        //
        // This arm deliberately does NOT record into `unverified_axioms`, and it
        // is the one arm where leaving the clause live is the intended answer:
        // `#[trusted]` is the user's explicit request to take the `ensures` on
        // faith, and the request is paid for in the open — the contract loop
        // classifies the same item `Trusted`, counts it, prints
        // `trusted (skipped)`, and a non-zero `trusted` is a reported soundness
        // gap. Recording here would strip the clause instead, so `#[trusted]`
        // would mean "delete my spec", which no opt-in can be asking for. Every
        // other non-proof arm below records, because nobody asked for those.
        if logic_fn.is_trusted() {
            continue;
        }

        // A law is proved like any other logic function: a concrete impl's law
        // is exactly the goal Creusot discharges for it, and a law left
        // unproved is recorded below, never credited.
        let def_path = logic_fn.full_path();
        // The ensures lane does not run for a function with no `ensures`, or
        // for a bodyless trait logic method whose postcondition each
        // implementation owes (D-110); its body goals are still owed.
        let mut ensures_lane_runs = !logic_fn.ensures().is_empty();
        if ensures_lane_runs
            && cfg
                .impl_owed_postconditions
                .is_some_and(|owed| owed.contains(def_path))
        {
            eprintln!(
                "trust-wp: {def_path} is a trait logic method declaration (postcondition owed by \
                 each implementation)"
            );
            ensures_lane_runs = false;
        }
        if !ensures_lane_runs && !owes_body_goal {
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
        // A function with no `ensures` is credited on its body goals alone, so
        // its body must also be one the encoder reads (the callee-precondition
        // request below binds it). A recursive body calls the function itself,
        // so its symbol is declared the way the induction scheme declares it:
        // both self-axioms suppressed.
        let credited_on_body_goals = logic_fn.ensures().is_empty();
        let declares_self = use_induction || (credited_on_body_goals && logic_fn.is_recursive());
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
        //
        // A function whose own obligation this pass has already lost is read
        // here as every downstream consumer reads it, neutralized: its spec
        // axiom was never proved, and a proof that leans on it proves nothing
        // (logic_fn_callee_unproved_ensures_credits_caller.rs). What is lost
        // later is answered by `LogicCredits::withdraw_stale` against this
        // snapshot.
        let excluded = unverified_axioms.clone();
        let environment = |lf: &LogicFnDef| {
            if lf.full_path() != def_path && excluded.contains(lf.full_path()) {
                neutralized(lf)
            } else {
                lf.clone()
            }
        };
        let mut available_logic_fns: Vec<_> = if declares_self {
            logic_fns
                .iter()
                .map(|lf| {
                    let mut copy = environment(lf);
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
                .map(environment)
                .collect()
        };

        // Induction hypotheses for the self-recursive calls: variant-guarded
        // (single integer `#[variant]`) or structural subterm-descent (no
        // variant, ADT-parameter match recursion). Empty when neither scheme's
        // sound preconditions hold (the postcondition stays incomplete — sound).
        let induction_hypotheses =
            build_recursive_induction_hypotheses(logic_fn, cfg.adt_decls.as_ref());
        if let (Some(groups), Some(target_group)) = (trait_logic_fn_groups, same_trait_group) {
            // SOUNDNESS (bug/222): a trait law must hold for EVERY implementor,
            // so no body that defines a same-trait method may be visible:
            // neither the trait's own (overridable) default body nor an impl
            // override such as `<() as A>::mktrue`. Logic calls resolve by
            // method NAME (`Self::mktrue()` -> `mktrue`), so an impl override
            // is not in `groups` (only trait-declared methods are) yet would
            // silently define the generic `Self::mktrue` with one impl's body.
            // Hide every logic fn whose name collides with a same-trait method
            // name. This only removes premises (completeness cost at worst).
            let same_trait_names: HashSet<&str> = logic_fns
                .iter()
                .filter(|lf| {
                    lf.full_path() != logic_fn.full_path()
                        && groups
                            .get(lf.full_path())
                            .is_some_and(|group| group == target_group)
                })
                .map(LogicFnDef::name)
                .collect();
            available_logic_fns.retain(|lf| {
                lf.full_path() == logic_fn.full_path()
                    || (groups
                        .get(lf.full_path())
                        .is_none_or(|group| group != target_group)
                        && !same_trait_names.contains(lf.name()))
            });
        }
        let (logic_fns_opt, mode_overrides_for_logic_fn) = if available_logic_fns.is_empty() {
            (None, None)
        } else {
            // Always compute mode overrides when using induction, to force
            // the function under test to Default (spec-axiom-only) mode.
            let needs_scoping = declares_self
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
                if declares_self {
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

        // The assertions are proved under the function's own `requires`, in
        // the same logic-function environment the ensures lane uses below,
        // and before it: the ensures lane's credit stands only beside them.
        let own_assertions = match &assertion_goal {
            AssertionGoal::None => OwnAssertions::AllProved,
            AssertionGoal::Refused(why) => {
                unverified_axioms.insert(def_path.to_owned());
                counters.errors += 1;
                eprintln!(
                    "trust-wp: {def_path} error: {why} in a logic function body; \
                     refused instead of leaving the assertion unexamined"
                );
                OwnAssertions::Unproved
            }
            AssertionGoal::Goal(goal) => {
                let requires = own_premises(logic_fn);
                let goals = [goal.clone()];
                let outcome = verify_function_with_modes_outcome(
                    VerificationRequest::new(&requires, &goals)
                        .return_expr(None)
                        .logic_fns(logic_fns_opt)
                        .mode_overrides(mode_overrides_for_logic_fn.as_deref())
                        .type_invariants(type_invariants_opt)
                        .track(Some(track_level))
                        .timeout(timeout)
                        .type_constants(logic_fn_type_constants.as_ref())
                        .adt_field_ranges(cfg.adt_field_ranges.clone())
                        .adt_decls(cfg.adt_decls.clone()),
                );
                // Every obligation of a function with no `ensures` is a body goal
                // examined here, so its assertions count wherever the function
                // itself can be credited.
                let creditable = ensures_lane_runs || credited_on_body_goals;
                let own = report_logic_fn_assertions(def_path, &outcome, counters, creditable);
                if own != OwnAssertions::AllProved {
                    unverified_axioms.insert(def_path.to_owned());
                } else if creditable {
                    credits.record(index, LogicCreditKind::Assertions, &excluded);
                }
                own
            }
        };
        // The callees' preconditions are proved in the same environment and
        // under the same premises as the ensures lane below: the function's
        // own `requires` and, for a recursive one, the variant-guarded
        // induction hypothesis, which assumes only the `ensures` of a smaller
        // call and so is as sound here as there (`recursive_induction`).
        //
        // A function with no `ensures` is credited on its body goals alone, so
        // its body must also be one the encoder reads: the request binds the
        // body as the ensures lane binds it, and a construct the encoder
        // refuses there (a method it does not know) is refused here too. Its
        // goal is `true` when no call owes anything.
        let callee_goal = match callee_goal {
            CalleePreconditionGoal::None if credited_on_body_goals => {
                CalleePreconditionGoal::Goal(PureExpr::Bool(true))
            }
            other => other,
        };
        let callee_preconditions = match &callee_goal {
            CalleePreconditionGoal::None => CalleePreconditions::Proved,
            CalleePreconditionGoal::Refused(why) => {
                counters.errors += 1;
                eprintln!(
                    "trust-wp: {def_path} error: {why} in a logic function body; \
                     refused instead of leaving a callee precondition unexamined"
                );
                CalleePreconditions::Unproved
            }
            CalleePreconditionGoal::Goal(goal) => {
                let mut premises = own_premises(logic_fn);
                premises.extend(induction_hypotheses.iter().cloned());
                let goals = [goal.clone()];
                let outcome = verify_function_with_modes_outcome(
                    VerificationRequest::new(&premises, &goals)
                        .return_expr(credited_on_body_goals.then(|| logic_fn.body()))
                        .logic_fns(logic_fns_opt)
                        .mode_overrides(mode_overrides_for_logic_fn.as_deref())
                        .type_invariants(type_invariants_opt)
                        .track(Some(track_level))
                        .timeout(timeout)
                        .type_constants(logic_fn_type_constants.as_ref())
                        .adt_field_ranges(cfg.adt_field_ranges.clone())
                        .adt_decls(cfg.adt_decls.clone()),
                );
                report_logic_fn_callee_preconditions(def_path, &outcome, counters)
            }
        };
        if callee_preconditions != CalleePreconditions::Proved {
            unverified_axioms.insert(def_path.to_owned());
        }
        let body_goals_proved = own_assertions == OwnAssertions::AllProved
            && callee_preconditions == CalleePreconditions::Proved;
        if !ensures_lane_runs {
            // A function with no `ensures` owes exactly its body goals, all
            // of which were examined above; a trait logic method declaration
            // also owes a postcondition its implementations discharge, and is
            // never credited here.
            if credited_on_body_goals && body_goals_proved {
                grant_function_credit(
                    counters,
                    FunctionCredit::new(
                        CreditKind::Verified { native_only: false },
                        format!("trust-wp: {def_path} verified \u{2713}"),
                    ),
                );
                credits.record(index, LogicCreditKind::Function, &excluded);
            }
            continue;
        }

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
                // Its own body-goal verdicts are already out and counted.
                if body_goals_proved {
                    grant_function_credit(
                        counters,
                        FunctionCredit::new(
                            CreditKind::Verified { native_only: false },
                            format!("trust-wp: {def_path} verified ✓"),
                        ),
                    );
                    credits.record(index, LogicCreditKind::Function, &excluded);
                }
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
                // `Assumed` is a verdict reached without a proof: the clause
                // was DECLARED, never proved, so it is paid for like every
                // other unproved clause. Recording is the only thing that
                // neutralizes it; `counters.assumed` only denies the crate a
                // clean exit, and a denied exit still leaves every caller in
                // the crate collecting `verified` credit from an `ensures`
                // nobody discharged.
                unverified_axioms.insert(def_path.to_owned());
                counters.assumed += 1;
                eprintln!(
                    "trust-wp: {def_path} assumed ({reason}) \
                     — postcondition withheld from callers"
                );
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
                } else if logic_fn
                    .ensures()
                    .iter()
                    .any(|clause| matches!(clause, PureExpr::Bool(false)))
                {
                    // A literal `#[ensures(false)]` that the solver refutes is a
                    // genuine failure, never an unreliable model: `false` holds in
                    // no model, and a Verified/vacuous outcome is handled above,
                    // so reaching `Failed` means the requires are satisfiable.
                    // Creusot rejects it (bug/1204 `vc_wrong`: `[@expl:wrong
                    // ensures] false`). Counting it as failed only removes an
                    // accept path.
                    unverified_axioms.insert(def_path.to_owned());
                    counters.failed += 1;
                    // Counted failure with a validated model: the standard
                    // `FAILED \u{2717}` mark, so this verdict is recognisable
                    // as one (the harness credits a refutation only through
                    // that spelling plus its validated DIAGNOSTIC record).
                    eprintln!("trust-wp: {def_path} FAILED \u{2717} (logic postcondition `false`)");
                    let _ = counterexample;
                } else if hides_same_trait_logic_axiom {
                    unverified_axioms.insert(def_path.to_owned());
                    counters.failed += 1;
                    eprintln!("trust-wp: {def_path} FAILED \u{2717} (trait logic postcondition)");
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
                // A WITHHELD refutation (this run refuted the postcondition but
                // had no validated model, so the verdict fell back to Unknown)
                // must keep the disposition the `Failed` arm above would have
                // given it. Otherwise the gate that removed a false
                // `counterexample` claim would also remove the REJECTION:
                // `should_fail/bug/1204`'s `#[ensures(false)]` on `wrong` went
                // from `failed` to a warning, and the crate compiled clean —
                // a false accept manufactured by an honesty fix. The verdict is
                // reported as an error, never as `failed`: there is no
                // counterexample to stand behind, but there is also no proof.
                let withheld_refutation =
                    crate::callbacks::reporting::is_withheld_refutation(&outcome_ref.result);
                let inconsistent_postcondition = logic_fn
                    .ensures()
                    .iter()
                    .any(|clause| matches!(clause, PureExpr::Bool(false)));
                if is_vacuous {
                    // A vacuous proof says the premises were CONTRADICTORY, not
                    // that the postcondition holds — so the `ensures` was not
                    // proved and must not stay available to any caller. The
                    // recorded path is what neutralizes it (forced opaque, both
                    // spec and defining axiom removed); without it, callers in
                    // this same crate collect `verified` credit against a clause
                    // no model supports. The crate-level disposition is left a
                    // warning: `counters.vacuous` already denies a clean exit.
                    unverified_axioms.insert(def_path.to_owned());
                    counters.vacuous += 1;
                    counters.warnings += 1;
                    eprintln!("trust-wp: {def_path} vacuous (contradictory axiom premises)");
                } else if withheld_refutation
                    && (inconsistent_postcondition || hides_same_trait_logic_axiom)
                {
                    // Same two cases the `Failed` arm counts as a hard failure:
                    // a literal `#[ensures(false)]` (publishing it as a spec
                    // axiom would make anything provable downstream) and a
                    // trait-law postcondition that only "held" by assuming the
                    // same trait's default body.
                    unverified_axioms.insert(def_path.to_owned());
                    counters.errors += 1;
                    let kind = if inconsistent_postcondition {
                        "logic postcondition `false`"
                    } else {
                        "trait logic postcondition"
                    };
                    eprintln!(
                        "trust-wp: {def_path} postcondition unverified — ERROR ({kind}: {reason})"
                    );
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
                        // Default: emit a warning. The postcondition is NOT
                        // available as a spec axiom either way — the insert
                        // above neutralizes it; only the crate-level
                        // disposition differs from strict mode.
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
            // A variant this driver does not know is not a proof, so the
            // postcondition is recorded unproved rather than left live, and it
            // is NAMED: a counted error with no line attached to a def path
            // cannot be diagnosed by whoever meets it.
            #[allow(unreachable_patterns)]
            Ok(_) => {
                unverified_axioms.insert(def_path.to_owned());
                counters.errors += 1;
                eprintln!(
                    "trust-wp: {def_path} postcondition unverified \
                     — ERROR (unrecognised verification result)"
                );
            }
            Err(ref e) => {
                // An encoding refusal means the postcondition was never put to
                // the solver, so the `ensures` is unproved and must be
                // neutralized like any other unproved one. Recording it is what
                // does that; the counted error already denies the crate a clean
                // exit, and refusing the whole crate here would stop every other
                // function being checked for no soundness gain.
                unverified_axioms.insert(def_path.to_owned());
                counters.errors += 1;
                counters.encoding_errors.record(e);
                eprintln!("trust-wp: {def_path} error: {e}");
            }
        }
    }
    credits
}
