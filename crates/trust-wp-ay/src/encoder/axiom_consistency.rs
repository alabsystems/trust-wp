// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Encoder-axiom consistency guard: the vacuity shield for axioms.
//!
//! WHY. The base vacuity recheck asks whether `requires ∧ program facts` is
//! satisfiable, and it does so with the encoder's quantified axiom scope
//! POPPED (`solver_tail`: "the axioms are not needed for the base recheck"),
//! and the fresh `PreconditionsOnly` escalation rebuilds without them too. An
//! encoder-emitted axiom family that is inconsistent ON ITS OWN therefore
//! makes every query that carries it vacuously UNSAT, with a genuine, strictly
//! checked certificate, while every vacuity check reports a satisfiable base.
//! That is exactly how the Bool-getter-over-Int-slot tuple axiom
//! `∀x0 x1. ite(get_1(tuple2(x0,x1)), 1, 0) = x1` (every Int is 0 or 1) was
//! credited on `s34_field_nested_struct`.
//!
//! WHAT. Before an UNSAT becomes proof authority, the axiom set asserted in the
//! live query is tested for refutability on its own:
//!
//! * The axiom set is every active assertion that is a top-level universal,
//!   CLOSED (mentions no program constant, only function symbols and its own
//!   binders), and was NOT emitted on the goal side (negated-postcondition
//!   phase, an active negated-goal label, or [`AYEncoder::with_goal_assertions`])
//!   nor in the precondition phase. Requires, program facts and the goal are
//!   therefore never part of it.
//! * ay's E-matching cannot refute a trigger-guarded universal with no ground
//!   terms (it answers `unknown` on the tuple axiom alone; z3's MBQI says
//!   `unsat`). So the check asserts INSTANCES: each Int binder (up to three per
//!   axiom) is instantiated over `{0, 1, 2, -1}` and each Bool binder over
//!   `{true, false}`; any other binder stays universally quantified. Every
//!   instance is a logical consequence of its axiom (SMT sorts are non-empty),
//!   so an UNSAT instance set is a refutation of the axiom set.
//! * The instances are solved on a FRESH solver (a native replay of the live
//!   stack filtered to exactly those assertions). UNSAT → the axioms are
//!   inconsistent and no UNSAT that carries them may be credited.
//!
//! Refusal only. The guard can remove credit, never add it: a `NotRefuted`
//! verdict leaves the caller's decision exactly as it was.
//!
//! RESIDUAL RISK (deliberate). A SAT, `unknown` or timed-out instance check does
//! NOT block credit. Axioms are normally consistent and a stalled check must not
//! destroy coverage; the price is that an inconsistent family whose refutation
//! needs instances outside the small pools (or binders of other sorts that ay
//! cannot eliminate) is not caught here. Axioms that mention a nullary constant
//! (including a nullary datatype constructor) are not closed and are also out
//! of scope. The second layer, the axiom-preserving base refutation check in
//! `solver_tail` (`live_stack_refuted_by_fresh_replay`), covers the family
//! jointly with the base's ground terms on the function-obligation lane.

use std::{
    collections::{HashMap, HashSet},
    time::{Duration, Instant},
};

use ay_dpll::api::{NativeReplayMetadata, Solver, Sort, Term, TermKind};

use super::{type_resolve::catch_solver_panic_with_reason, AYEncoder, AssertionPhase};

/// ay-style reason code recorded on the strict-replay observation when the
/// guard withholds authority.
pub(crate) const ENCODER_AXIOMS_INCONSISTENT_REASON: &str = "encoder_axioms_inconsistent";

/// Node budget for the closedness walk of one assertion.
const AXIOM_WALK_BUDGET: usize = 50_000;
/// Binders instantiated per axiom; the rest stay quantified.
const MAX_INSTANTIATED_BINDERS: usize = 3;
/// Upper bound on instances asserted by one check.
const MAX_INSTANCES: usize = 2048;
/// Wall-clock cap for the fresh instance solve.
const AXIOM_CHECK_TIMEOUT_CAP: Duration = Duration::from_millis(1000);
/// Floor so a tiny caller budget still runs the (usually ground) check.
const AXIOM_CHECK_TIMEOUT_FLOOR: Duration = Duration::from_millis(50);
const INT_POOL: [i64; 4] = [0, 1, 2, -1];

/// Outcome of the encoder-axiom consistency check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AxiomConsistency {
    /// The live query carries no closed encoder axiom.
    NoCandidates,
    /// Not refuted (SAT, unknown, timeout, nothing instantiable). Credit is
    /// NOT blocked; the string is an evidence note.
    NotRefuted(String),
    /// The axiom set alone is UNSAT: no UNSAT carrying it is a proof.
    Refuted(String),
    /// The check could not restore the live solver; fail closed.
    CheckCorrupted(String),
}

impl AxiomConsistency {
    /// Whether an UNSAT carrying this axiom set must be refused credit.
    pub(crate) fn refuses_credit(&self) -> bool {
        matches!(self, Self::Refuted(_) | Self::CheckCorrupted(_))
    }
}

fn guard_trace_enabled() -> bool {
    std::env::var_os("TRUST_WP_AXIOM_GUARD_TRACE").is_some()
}

impl AYEncoder {
    /// Record which side of the query an asserted term belongs to.
    pub(in crate::encoder) fn note_assertion_provenance(&mut self, term: Term) {
        let phase = self.assertion_pipeline.current_phase();
        if self.goal_assertion_depth > 0
            || phase == AssertionPhase::NegatedPostcondition
            || self
                .assertion_pipeline
                .negated_goal_label_prefix()
                .is_some()
        {
            self.goal_side_assertion_terms.insert(term);
        } else if phase == AssertionPhase::Precondition {
            self.precondition_assertion_terms.insert(term);
        }
    }

    /// Run `f` with every assertion it makes classified as goal-side, so the
    /// encoder-axiom consistency guard never mistakes a (negated) goal or a
    /// goal-guard for an axiom.
    pub(crate) fn with_goal_assertions<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.goal_assertion_depth = self.goal_assertion_depth.saturating_add(1);
        let result = f(self);
        self.goal_assertion_depth = self.goal_assertion_depth.saturating_sub(1);
        result
    }

    /// Every `Var` term reachable from `root` by name, plus the names bound by
    /// quantifiers inside `root`. `None` when the walk budget runs out.
    fn axiom_walk(&self, root: Term) -> Option<(HashMap<String, Term>, HashSet<String>)> {
        let mut vars: HashMap<String, Term> = HashMap::new();
        let mut bound: HashSet<String> = HashSet::new();
        let mut seen: HashSet<Term> = HashSet::new();
        let mut stack = vec![root];
        let mut budget = AXIOM_WALK_BUDGET;
        while let Some(term) = stack.pop() {
            budget = budget.checked_sub(1)?;
            if !seen.insert(term) {
                continue;
            }
            match self.solver.term_kind(term) {
                TermKind::Var { name } => {
                    vars.entry(name).or_insert(term);
                }
                TermKind::Forall | TermKind::Exists => {
                    if let Some(binders) = self.solver.quantifier_bound_vars(term) {
                        bound.extend(binders.into_iter().map(|(name, _)| name));
                    }
                }
                _ => {}
            }
            stack.extend(self.solver.term_children(term));
        }
        Some((vars, bound))
    }

    /// The closed, encoder-emitted universals active in the live query.
    pub(crate) fn encoder_axiom_candidates(&self) -> Vec<Term> {
        let mut seen: HashSet<Term> = HashSet::new();
        self.solver
            .assertions()
            .into_iter()
            .filter(|&term| {
                seen.insert(term)
                    && matches!(self.solver.term_kind(term), TermKind::Forall)
                    && !self.goal_side_assertion_terms.contains(&term)
                    && !self.precondition_assertion_terms.contains(&term)
                    && self
                        .axiom_walk(term)
                        .is_some_and(|(vars, bound)| vars.keys().all(|name| bound.contains(name)))
            })
            .collect()
    }

    /// Push the small-pool instances of one closed universal onto `out`.
    fn instantiate_encoder_axiom(&mut self, axiom: Term, out: &mut Vec<Term>) -> Option<()> {
        let binders = self.solver.quantifier_bound_vars(axiom)?;
        let children = self.solver.term_children(axiom);
        let body = *children.first()?;
        let (body_vars, _) = self.axiom_walk(body)?;

        let mut from: Vec<Term> = Vec::new();
        let mut pools: Vec<Vec<Term>> = Vec::new();
        let mut remaining: Vec<Term> = Vec::new();
        for (name, sort) in &binders {
            let Some(&var_term) = body_vars.get(name) else {
                // A binder that does not occur in the body can be dropped.
                continue;
            };
            if self.solver.term_sort(var_term) != *sort {
                return None;
            }
            let pool = if from.len() < MAX_INSTANTIATED_BINDERS {
                match sort {
                    Sort::Int => Some(
                        INT_POOL
                            .iter()
                            .map(|&value| self.solver.int_const(value))
                            .collect::<Vec<_>>(),
                    ),
                    Sort::Bool => Some(vec![
                        self.solver.bool_const(true),
                        self.solver.bool_const(false),
                    ]),
                    _ => None,
                }
            } else {
                None
            };
            match pool {
                Some(pool) => {
                    from.push(var_term);
                    pools.push(pool);
                }
                None => remaining.push(var_term),
            }
        }
        if from.is_empty() {
            return Some(());
        }

        let mut index = vec![0usize; pools.len()];
        loop {
            if out.len() >= MAX_INSTANCES {
                return Some(());
            }
            let to: Vec<Term> = index.iter().zip(&pools).map(|(&i, pool)| pool[i]).collect();
            let instance = self.solver.substitute(body, &from, &to);
            let instance = if remaining.is_empty() {
                instance
            } else {
                self.solver.try_forall(&remaining, instance).ok()?
            };
            out.push(instance);

            let mut digit = 0;
            loop {
                if digit == index.len() {
                    return Some(());
                }
                index[digit] += 1;
                if index[digit] < pools[digit].len() {
                    break;
                }
                index[digit] = 0;
                digit += 1;
            }
        }
    }

    fn axiom_check_timeout(&self) -> Duration {
        self.solver
            .timeout()
            .map_or(AXIOM_CHECK_TIMEOUT_CAP, |caller| {
                (caller / 4).min(AXIOM_CHECK_TIMEOUT_CAP)
            })
            .max(AXIOM_CHECK_TIMEOUT_FLOOR)
    }

    /// Is the encoder-axiom set of the live query refutable on its own?
    /// Cached per exact axiom set.
    pub(crate) fn check_encoder_axiom_consistency(&mut self) -> AxiomConsistency {
        let mut candidates = self.encoder_axiom_candidates();
        if candidates.is_empty() {
            return AxiomConsistency::NoCandidates;
        }
        candidates.sort_by_key(|term| term.id());
        if let Some(cached) = self.axiom_consistency_cache.get(&candidates) {
            return cached.clone();
        }
        let started = Instant::now();
        let verdict = self.run_encoder_axiom_consistency_check(&candidates);
        if guard_trace_enabled() {
            eprintln!(
                "[TRUST_WP_AXIOM_GUARD] axioms={} elapsed_ms={} verdict={verdict:?}",
                candidates.len(),
                started.elapsed().as_millis()
            );
        }
        tracing::debug!(
            axioms = candidates.len(),
            elapsed_ms = started.elapsed().as_millis() as u64,
            ?verdict,
            "encoder-axiom consistency check"
        );
        self.axiom_consistency_cache
            .insert(candidates, verdict.clone());
        verdict
    }

    fn run_encoder_axiom_consistency_check(&mut self, candidates: &[Term]) -> AxiomConsistency {
        let mut instances: Vec<Term> = Vec::new();
        if let Err(err) = catch_solver_panic_with_reason("axiom_consistency_instantiate", || {
            for &axiom in candidates {
                if self
                    .instantiate_encoder_axiom(axiom, &mut instances)
                    .is_none()
                {
                    continue;
                }
            }
        }) {
            return AxiomConsistency::NotRefuted(format!(
                "instantiation panicked: {}",
                err.into_reason()
            ));
        }
        instances.retain({
            let mut seen: HashSet<Term> = HashSet::new();
            move |term| seen.insert(*term)
        });
        if instances.is_empty() {
            return AxiomConsistency::NotRefuted(format!(
                "{} closed encoder axioms, none with an instantiable binder",
                candidates.len()
            ));
        }

        // Materialize the instances in a scratch scope of the live solver only
        // long enough to export them; the export's term closure is what lets a
        // fresh solver rebuild them. The scope is popped before anything else
        // runs, so the live assertion stack is unchanged.
        let live: HashSet<Term> = self.solver.assertions().into_iter().collect();
        let exported = catch_solver_panic_with_reason("axiom_consistency_export", || {
            if let Err(err) = self.solver.try_push() {
                return Err((false, format!("push failed: {err}")));
            }
            let mut assert_error = None;
            for &instance in &instances {
                if live.contains(&instance) {
                    continue;
                }
                if let Err(err) = self.solver.try_assert_term(instance) {
                    assert_error = Some(format!("assert failed: {err}"));
                    break;
                }
            }
            let artifact = assert_error.is_none().then(|| {
                self.solver
                    .export_native_replay_artifact(NativeReplayMetadata::default(), None)
            });
            if let Err(err) = self.solver.try_pop() {
                return Err((true, format!("pop failed: {err}")));
            }
            match (artifact, assert_error) {
                (Some(artifact), _) => Ok(artifact),
                (None, Some(err)) => Err((false, err)),
                (None, None) => Err((false, "no artifact".to_string())),
            }
        });
        let mut artifact = match exported {
            Ok(Ok(artifact)) => artifact,
            Ok(Err((false, note))) => {
                return AxiomConsistency::NotRefuted(format!("instance export declined: {note}"))
            }
            Ok(Err((true, note))) => {
                self.assertion_pipeline
                    .record_solver_panic(format!("axiom consistency check: {note}"));
                return AxiomConsistency::CheckCorrupted(note);
            }
            Err(err) => {
                // A panic may have left the scratch scope pushed. Fail closed:
                // the encoder is marked panicked and the credit is refused.
                let note = err.into_reason();
                self.assertion_pipeline
                    .record_solver_panic(format!("axiom consistency check: {note}"));
                return AxiomConsistency::CheckCorrupted(note);
            }
        };

        let instance_ids: HashSet<_> = instances.iter().map(|term| term.id()).collect();
        artifact
            .assertions
            .retain(|assertion| instance_ids.contains(&assertion.term));
        artifact.created_unix_ms = 0;
        artifact.timeout_ms = Some(self.axiom_check_timeout().as_millis());
        let asserted = artifact.assertions.len();
        match catch_solver_panic_with_reason("axiom_consistency_replay", || {
            Solver::replay_native_replay_artifact(&artifact)
        }) {
            Ok(Ok(details)) if details.result.is_unsat() => AxiomConsistency::Refuted(format!(
                "{} closed encoder axioms; {asserted} small-pool instances are UNSAT on a fresh solver",
                candidates.len()
            )),
            Ok(Ok(details)) => AxiomConsistency::NotRefuted(format!(
                "{} closed encoder axioms; {asserted} instances not refuted (result {:?})",
                candidates.len(),
                details.result
            )),
            Ok(Err(err)) => AxiomConsistency::NotRefuted(format!("instance replay error: {err}")),
            Err(err) => AxiomConsistency::NotRefuted(format!(
                "instance replay panicked: {}",
                err.into_reason()
            )),
        }
    }

    /// Refuse proof authority for an UNSAT whose encoder axioms are refuted on
    /// their own. `None` in, `None` out; a non-refuted check passes the summary
    /// through unchanged.
    pub(crate) fn refuse_unsat_credit_on_inconsistent_encoder_axioms(
        &mut self,
        summary: Option<crate::verify::ProofCertificateSummary>,
    ) -> Option<crate::verify::ProofCertificateSummary> {
        let summary = summary?;
        let verdict = self.check_encoder_axiom_consistency();
        crate::verify::authority_trace(|| format!("encoder-axiom consistency: {verdict:?}"));
        if verdict.refuses_credit() {
            tracing::debug!(
                ?verdict,
                "[TRUST_WP_DEBUG] UNSAT credit refused: vacuous (encoder axioms inconsistent)"
            );
            return None;
        }
        Some(summary)
    }

    /// Solve the live assertion stack, exactly as it stands, on a fresh
    /// non-proof solver. `Some(true)` only for UNSAT; used to refute a base
    /// that keeps its axiom scope (vacuity with axioms). Refusal-only: callers
    /// must never treat `Some(false)`/`None` as a non-vacuity witness.
    pub(crate) fn live_stack_refuted_by_fresh_replay(&self, timeout: Duration) -> Option<bool> {
        let mut artifact = self
            .solver
            .export_native_replay_artifact(NativeReplayMetadata::default(), None);
        artifact.created_unix_ms = 0;
        artifact.timeout_ms = Some(timeout.as_millis());
        let started = Instant::now();
        let details = catch_solver_panic_with_reason("axiom_base_refutation_replay", || {
            Solver::replay_native_replay_artifact(&artifact)
        })
        .ok()?
        .ok()?;
        if guard_trace_enabled() {
            eprintln!(
                "[TRUST_WP_AXIOM_GUARD] base-with-axioms asserts={} elapsed_ms={} result={:?}",
                artifact.assertions.len(),
                started.elapsed().as_millis(),
                details.result
            );
        }
        Some(details.result.is_unsat())
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use ay_dpll::api::{SolveResult, Sort};

    use super::*;

    fn test_summary() -> crate::verify::ProofCertificateSummary {
        crate::verify::ProofCertificateSummary {
            strict_verified: true,
            restricted_rule_subset: false,
            trust_count: 0,
            trust_fallback_count: 0,
            hole_count: 0,
            theory_lemma_count: 0,
            resolution_count: 1,
            farkas_certificate_count: 0,
            lrat_present: false,
            alethe_text: None,
        }
    }

    fn strict_encoder() -> AYEncoder {
        let mut encoder = AYEncoder::new_pure();
        encoder.begin_strict_replay_obligation();
        encoder.begin_strict_replay_obligation_slice();
        encoder
    }

    /// `x > 0` as a precondition, `x < 0` as the negated goal: a genuine proof.
    fn assert_true_contract(encoder: &mut AYEncoder) {
        let x = encoder.solver_mut().declare_const("x", Sort::Int);
        let zero = encoder.solver_mut().int_const(0);
        encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
            let pos = encoder.solver_mut().gt(x, zero);
            encoder.assert_term(pos);
        });
        encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
            let neg = encoder.solver_mut().lt(x, zero);
            encoder.assert_term(neg);
        });
    }

    /// Fault injection: `∀y:Int. y = 0 ∧ y = 1`, unsatisfiable on its own.
    fn contradictory_axiom(encoder: &mut AYEncoder) -> Term {
        let solver = encoder.solver_mut();
        let y = solver.fresh_var("axiom_y", Sort::Int);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);
        let is_zero = solver.eq(y, zero);
        let is_one = solver.eq(y, one);
        let body = solver.and(is_zero, is_one);
        solver.forall(&[y], body)
    }

    /// The s34 shape: a Bool getter bridged onto an Int payload,
    /// `∀t k:Int. ite(get(tuple(t, k)), 1 = k, 0 = k)` (every Int is 0 or 1).
    fn bool_getter_over_int_payload_axiom(encoder: &mut AYEncoder) -> Term {
        let solver = encoder.solver_mut();
        let tuple = solver.declare_fun("axiom_tuple2", &[Sort::Int, Sort::Int], Sort::Int);
        let get_1 = solver.declare_fun("axiom_get_1", &[Sort::Int], Sort::Bool);
        let t = solver.fresh_var("axiom_t", Sort::Int);
        let k = solver.fresh_var("axiom_k", Sort::Int);
        let packed = solver.apply(&tuple, &[t, k]);
        let flag = solver.apply(&get_1, &[packed]);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);
        let then_branch = solver.eq(one, k);
        let else_branch = solver.eq(zero, k);
        let body = solver.ite(flag, then_branch, else_branch);
        solver.forall(&[t, k], body)
    }

    /// A consistent sibling: `∀k:Int. ite(get(k), f(k) = 1, f(k) = 0)`.
    fn consistent_axiom(encoder: &mut AYEncoder) -> Term {
        let solver = encoder.solver_mut();
        let get = solver.declare_fun("axiom_ok_get", &[Sort::Int], Sort::Bool);
        let f = solver.declare_fun("axiom_ok_f", &[Sort::Int], Sort::Int);
        let k = solver.fresh_var("axiom_ok_k", Sort::Int);
        let flag = solver.apply(&get, &[k]);
        let value = solver.apply(&f, &[k]);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);
        let then_branch = solver.eq(value, one);
        let else_branch = solver.eq(value, zero);
        let body = solver.ite(flag, then_branch, else_branch);
        solver.forall(&[k], body)
    }

    fn assert_axiom(encoder: &mut AYEncoder, axiom: Term) {
        encoder.with_assertion_phase(AssertionPhase::EncodingAxiom, |encoder| {
            encoder.assert_term(axiom);
        });
    }

    #[test]
    fn contradictory_axiom_is_refuted() {
        let mut encoder = strict_encoder();
        let axiom = contradictory_axiom(&mut encoder);
        assert_axiom(&mut encoder, axiom);
        assert_eq!(encoder.encoder_axiom_candidates(), vec![axiom]);
        assert!(matches!(
            encoder.check_encoder_axiom_consistency(),
            AxiomConsistency::Refuted(_)
        ));
    }

    #[test]
    fn bool_getter_over_int_payload_axiom_is_refuted() {
        let mut encoder = strict_encoder();
        let axiom = bool_getter_over_int_payload_axiom(&mut encoder);
        assert_axiom(&mut encoder, axiom);
        let verdict = encoder.check_encoder_axiom_consistency();
        assert!(verdict.refuses_credit(), "{verdict:?}");
    }

    #[test]
    fn consistent_axiom_is_not_refuted() {
        let mut encoder = strict_encoder();
        let axiom = consistent_axiom(&mut encoder);
        assert_axiom(&mut encoder, axiom);
        let verdict = encoder.check_encoder_axiom_consistency();
        assert!(
            matches!(verdict, AxiomConsistency::NotRefuted(_)),
            "{verdict:?}"
        );
        // Cached per exact axiom set: the second call is the same verdict.
        assert_eq!(encoder.check_encoder_axiom_consistency(), verdict);
    }

    #[test]
    fn goal_side_and_precondition_universals_are_never_axioms() {
        let mut encoder = strict_encoder();
        let in_goal_phase = contradictory_axiom(&mut encoder);
        encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
            encoder.assert_term(in_goal_phase);
        });
        let in_goal_region = bool_getter_over_int_payload_axiom(&mut encoder);
        encoder.with_goal_assertions(|encoder| encoder.assert_term(in_goal_region));
        let labelled = consistent_axiom(&mut encoder);
        encoder.with_negated_goal_label_prefix("__test_goal".to_string(), |encoder| {
            encoder.assert_term(labelled);
        });
        assert!(encoder.encoder_axiom_candidates().is_empty());
        assert_eq!(
            encoder.check_encoder_axiom_consistency(),
            AxiomConsistency::NoCandidates
        );

        let mut encoder = strict_encoder();
        let in_requires = contradictory_axiom(&mut encoder);
        encoder.with_assertion_phase(AssertionPhase::Precondition, |encoder| {
            encoder.assert_term(in_requires);
        });
        assert!(encoder.encoder_axiom_candidates().is_empty());
    }

    #[test]
    fn open_universal_over_program_constant_is_not_an_axiom() {
        let mut encoder = strict_encoder();
        let solver = encoder.solver_mut();
        let n = solver.declare_const("n", Sort::Int);
        let y = solver.fresh_var("open_y", Sort::Int);
        let body = solver.eq(y, n);
        let open = solver.forall(&[y], body);
        assert_axiom(&mut encoder, open);
        assert!(encoder.encoder_axiom_candidates().is_empty());
    }

    /// The deterministic end-to-end pin: the same true contract is credited
    /// with a consistent axiom scope and is NOT credited once an inconsistent
    /// axiom is injected, and the refusal names the guard.
    #[test]
    fn injected_inconsistent_axiom_gets_no_verified_credit() {
        let mut control = strict_encoder();
        assert_true_contract(&mut control);
        let ok = consistent_axiom(&mut control);
        assert_axiom(&mut control, ok);
        assert_eq!(control.check_sat(), SolveResult::unsat());
        let control_summary = control.authorize_current_stack_unsat_with_strict_proof();

        let mut poisoned = strict_encoder();
        assert_true_contract(&mut poisoned);
        let bad = contradictory_axiom(&mut poisoned);
        assert_axiom(&mut poisoned, bad);
        assert_eq!(poisoned.check_sat(), SolveResult::unsat());
        assert!(
            poisoned
                .authorize_current_stack_unsat_with_strict_proof()
                .is_none(),
            "an UNSAT carrying an inconsistent encoder axiom must not be credited"
        );
        let observation = poisoned
            .capture_provenance(Duration::ZERO)
            .strict_proof_replay
            .expect("strict replay observation");
        assert!(!observation.authority_accepted);
        // Teeth: ay certifies this stack shape (the control is credited), so
        // the only thing withholding the poisoned stack's authority is the guard.
        assert!(
            control_summary.is_some_and(|summary| summary.is_fully_verified()),
            "control contract with consistent axioms must keep its strict credit"
        );
        assert_eq!(
            observation.unknown_reason.as_deref(),
            Some(ENCODER_AXIOMS_INCONSISTENT_REASON),
            "{observation:?}"
        );
        // The live stack is unchanged by the check's scratch scope.
        assert_eq!(poisoned.check_sat(), SolveResult::unsat());
        assert!(!poisoned.assertion_pipeline.is_panicked());
    }

    #[test]
    fn retained_artifact_credit_is_refused_too() {
        let mut encoder = strict_encoder();
        let bad = contradictory_axiom(&mut encoder);
        assert_axiom(&mut encoder, bad);
        let summary = test_summary();
        assert!(encoder
            .refuse_unsat_credit_on_inconsistent_encoder_axioms(Some(summary))
            .is_none());

        let mut encoder = strict_encoder();
        let ok = consistent_axiom(&mut encoder);
        assert_axiom(&mut encoder, ok);
        let summary = test_summary();
        assert!(encoder
            .refuse_unsat_credit_on_inconsistent_encoder_axioms(Some(summary))
            .is_some());
    }
}
