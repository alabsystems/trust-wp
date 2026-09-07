// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Solver interaction: assertion, SAT check, model retrieval, and equality.
//!
//! Panic-isolated solver access, sort-coerced equality, and vacuity detection.
//! The quantified-disjointness recheck pipeline lives in [`quantified_disjoint`].

use std::{
    collections::{HashMap, HashSet},
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};

use ay_dpll::api::{Model, SmtProofCertificate, SolveResult, Solver, Sort, Term, TermKind};

/// Term-node budget for the prenex-push freeness walk
/// ([`AYEncoder::prenex_push_assertion`]). A disjunct or quantifier body larger
/// than this declines the rewrite and the un-pushed shape is asserted instead,
/// so the cap costs completeness only, never soundness. (#quantifier-frontier)
const PRENEX_PUSH_WALK_BUDGET: usize = 20_000;

use num_bigint::BigInt;
use tracing::warn;

use super::{
    coerce_ite_sorts, replay_artifact::ReplayResultStatus,
    type_resolve::catch_solver_panic_with_reason, unsoundness, AYEncoder,
};
use crate::shared_types::{
    SolveEvidenceSnapshot, SolveResourceSnapshot, SolveStatisticsSnapshot,
    SolveVerificationLevelSnapshot, SolveVerificationSnapshot,
};

mod quantified_disjoint;

#[derive(Clone, Copy)]
struct IntAffineAtom {
    atom: Option<Term>,
    offset: i64,
}

#[derive(Clone, Copy)]
enum IntBoundConstraint {
    Lower { atom: Term, value: i64 },
    Upper { atom: Term, value: i64 },
}

fn parse_formatted_int_literal(formatted: &str) -> Option<BigInt> {
    let formatted = formatted.trim();
    if let Ok(value) = formatted.parse::<BigInt>() {
        return Some(value);
    }
    let inner = formatted
        .strip_prefix("(- ")
        .and_then(|rest| rest.strip_suffix(')'))?;
    inner.trim().parse::<BigInt>().ok().map(|value| -value)
}

fn record_known_int(
    atom: Term,
    value: i64,
    known_ints: &mut HashMap<Term, i64>,
    bounds: &HashMap<Term, (Option<i64>, Option<i64>)>,
    forbidden_ints: &HashSet<(Term, i64)>,
) -> bool {
    if known_ints.get(&atom).is_some_and(|known| *known != value) {
        return false;
    }
    if forbidden_ints.contains(&(atom, value)) {
        return false;
    }
    if bounds.get(&atom).is_some_and(|(lower, upper)| {
        lower.is_some_and(|lower| value < lower) || upper.is_some_and(|upper| value > upper)
    }) {
        return false;
    }
    known_ints.insert(atom, value);
    true
}

fn record_simple_int_bound(
    constraint: IntBoundConstraint,
    bounds: &mut HashMap<Term, (Option<i64>, Option<i64>)>,
    known_ints: &HashMap<Term, i64>,
    forbidden_ints: &HashSet<(Term, i64)>,
) -> bool {
    let (atom, is_lower, value) = match constraint {
        IntBoundConstraint::Lower { atom, value } => (atom, true, value),
        IntBoundConstraint::Upper { atom, value } => (atom, false, value),
    };
    let entry = bounds.entry(atom).or_insert((None, None));
    if is_lower {
        entry.0 = Some(entry.0.map_or(value, |existing| existing.max(value)));
    } else {
        entry.1 = Some(entry.1.map_or(value, |existing| existing.min(value)));
    }
    if entry
        .0
        .zip(entry.1)
        .is_some_and(|(lower, upper)| lower > upper)
    {
        return false;
    }
    if known_ints.get(&atom).is_some_and(|known| {
        entry.0.is_some_and(|lower| *known < lower) || entry.1.is_some_and(|upper| *known > upper)
    }) {
        return false;
    }
    if entry
        .0
        .zip(entry.1)
        .is_some_and(|(lower, upper)| lower == upper && forbidden_ints.contains(&(atom, lower)))
    {
        return false;
    }
    true
}

#[derive(Default)]
struct IntOffsetUnionFind {
    indices: HashMap<Term, usize>,
    parent: Vec<usize>,
    offset_to_parent: Vec<i64>,
    root_value: Vec<Option<i64>>,
}

#[derive(Default)]
struct BoolParityUnionFind {
    indices: HashMap<Term, usize>,
    parent: Vec<usize>,
    parity_to_parent: Vec<bool>,
    root_value: Vec<Option<bool>>,
}

fn shortcut_replay_status(result: &SolveResult) -> ReplayResultStatus {
    match result {
        SolveResult::Sat => ReplayResultStatus::Sat,
        SolveResult::Unsat(_) => ReplayResultStatus::Unsat,
        SolveResult::Unknown => ReplayResultStatus::Unknown,
        #[allow(unreachable_patterns)]
        _ => ReplayResultStatus::Unknown,
    }
}

impl BoolParityUnionFind {
    fn ensure(&mut self, term: Term) -> usize {
        if let Some(index) = self.indices.get(&term).copied() {
            return index;
        }
        let index = self.parent.len();
        self.indices.insert(term, index);
        self.parent.push(index);
        self.parity_to_parent.push(false);
        self.root_value.push(None);
        index
    }

    fn find_index(&mut self, index: usize) -> (usize, bool) {
        let parent = self.parent[index];
        if parent == index {
            return (index, false);
        }
        let (root, parent_parity) = self.find_index(parent);
        let parity = self.parity_to_parent[index] ^ parent_parity;
        self.parent[index] = root;
        self.parity_to_parent[index] = parity;
        (root, parity)
    }

    fn find_term(&mut self, term: Term) -> (usize, bool) {
        let index = self.ensure(term);
        self.find_index(index)
    }

    fn set_constant(&mut self, term: Term, value: bool) -> bool {
        let (root, parity) = self.find_term(term);
        let root_value = value ^ parity;
        match self.root_value[root] {
            Some(existing) => existing == root_value,
            None => {
                self.root_value[root] = Some(root_value);
                true
            }
        }
    }

    fn union_parity(&mut self, lhs: Term, rhs: Term, parity: bool) -> bool {
        let (lhs_root, lhs_parity) = self.find_term(lhs);
        let (rhs_root, rhs_parity) = self.find_term(rhs);
        if lhs_root == rhs_root {
            return (lhs_parity ^ rhs_parity) == parity;
        }

        let root_parity = lhs_parity ^ rhs_parity ^ parity;
        self.parent[lhs_root] = rhs_root;
        self.parity_to_parent[lhs_root] = root_parity;

        match (self.root_value[lhs_root], self.root_value[rhs_root]) {
            (Some(lhs_value), Some(rhs_value)) => (lhs_value ^ rhs_value) == root_parity,
            (Some(lhs_value), None) => {
                self.root_value[rhs_root] = Some(lhs_value ^ root_parity);
                true
            }
            (None, Some(_)) | (None, None) => true,
        }
    }
}

impl IntOffsetUnionFind {
    fn ensure(&mut self, term: Term) -> usize {
        if let Some(index) = self.indices.get(&term).copied() {
            return index;
        }
        let index = self.parent.len();
        self.indices.insert(term, index);
        self.parent.push(index);
        self.offset_to_parent.push(0);
        self.root_value.push(None);
        index
    }

    fn find_index(&mut self, index: usize) -> (usize, i64) {
        let parent = self.parent[index];
        if parent == index {
            return (index, 0);
        }
        let (root, parent_offset) = self.find_index(parent);
        let offset = self.offset_to_parent[index] + parent_offset;
        self.parent[index] = root;
        self.offset_to_parent[index] = offset;
        (root, offset)
    }

    fn find_term(&mut self, term: Term) -> (usize, i64) {
        let index = self.ensure(term);
        self.find_index(index)
    }

    fn set_constant(&mut self, term: Term, value: i64) -> bool {
        let (root, offset) = self.find_term(term);
        let root_value = value - offset;
        match self.root_value[root] {
            Some(existing) => existing == root_value,
            None => {
                self.root_value[root] = Some(root_value);
                true
            }
        }
    }

    fn union_difference(&mut self, lhs: Term, rhs: Term, difference: i64) -> bool {
        let (lhs_root, lhs_offset) = self.find_term(lhs);
        let (rhs_root, rhs_offset) = self.find_term(rhs);
        if lhs_root == rhs_root {
            return lhs_offset - rhs_offset == difference;
        }

        let lhs_root_to_rhs_root = difference - lhs_offset + rhs_offset;
        let lhs_root_value = self.root_value[lhs_root];
        let rhs_root_value = self.root_value[rhs_root];

        if let (Some(lhs_value), Some(rhs_value)) = (lhs_root_value, rhs_root_value) {
            if lhs_value != rhs_value + lhs_root_to_rhs_root {
                return false;
            }
        }

        self.parent[lhs_root] = rhs_root;
        self.offset_to_parent[lhs_root] = lhs_root_to_rhs_root;
        if let (Some(lhs_value), None) = (lhs_root_value, rhs_root_value) {
            self.root_value[rhs_root] = Some(lhs_value - lhs_root_to_rhs_root);
        }
        true
    }

    fn affine_constant_value(&mut self, side: IntAffineAtom) -> Option<i64> {
        match side.atom {
            Some(atom) => {
                let (root, offset) = self.find_term(atom);
                self.root_value[root].map(|value| value + offset + side.offset)
            }
            None => Some(side.offset),
        }
    }

    fn affines_forced_equal(&mut self, lhs: IntAffineAtom, rhs: IntAffineAtom) -> bool {
        match (lhs.atom, rhs.atom) {
            (None, None) => lhs.offset == rhs.offset,
            (Some(_), None) | (None, Some(_)) => self
                .affine_constant_value(lhs)
                .zip(self.affine_constant_value(rhs))
                .is_some_and(|(lhs, rhs)| lhs == rhs),
            (Some(lhs_atom), Some(rhs_atom)) => {
                let (lhs_root, lhs_root_offset) = self.find_term(lhs_atom);
                let (rhs_root, rhs_root_offset) = self.find_term(rhs_atom);
                if lhs_root == rhs_root {
                    lhs_root_offset + lhs.offset == rhs_root_offset + rhs.offset
                } else {
                    self.affine_constant_value(lhs)
                        .zip(self.affine_constant_value(rhs))
                        .is_some_and(|(lhs, rhs)| lhs == rhs)
                }
            }
        }
    }
}

/// Format a ay Sort as a short key suitable for UF bridge names.
///
/// Used by `bridge_structural_sort` to build descriptive UF names. (#2699)
fn sort_display_key(sort: &Sort) -> String {
    match sort {
        Sort::Int => "Int".to_string(),
        Sort::Bool => "Bool".to_string(),
        Sort::Real => "Real".to_string(),
        Sort::Uninterpreted(name) => name.replace("::", "_"),
        Sort::Datatype(dt) => dt.name.replace("::", "_"),
        Sort::Array(_) => "Array".to_string(),
        Sort::Seq(_) => "Seq".to_string(),
        _ => format!("{sort:?}"),
    }
}

/// Check whether a ay Sort is a structural (non-scalar) sort.
///
/// Returns `true` for Datatype, Uninterpreted, and Seq sorts — these are
/// "real" structural sorts that carry type information beyond plain Int/Bool.
/// Used by `harmonize_eq_or_ite_terms` to decide when Seq element restoration
/// is worth attempting. (#2699)
fn is_structural_non_int(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Datatype(_) | Sort::Uninterpreted(_) | Sort::Seq(_)
    )
}

/// Check whether a solver panic message indicates a proof-validation failure.
///
/// ay-dpll can produce correct UNSAT results with invalid proofs in several
/// scenarios: datatype shortcuts that don't populate `last_proof`, LRAT proof
/// hints referencing invalid clause IDs, and the proof checker rejecting
/// `th_resolution` steps. In all these cases, retrying with proof production
/// disabled (`set_produce_proofs(false)`) recovers the correct SAT/UNSAT
/// answer. (#2664)
fn is_proof_related_panic(reason: &str) -> bool {
    reason.contains("returned UNSAT without proof")
        || reason.contains("proof checker rejected UNSAT proof")
        || reason.contains("LRAT hint contains ID 0")
        || reason.contains("IncrementalTheoryState::pop() underflow")
        || reason.contains("conflict semantic verification failed")
        || reason
            .contains("build_unsat_proof produced a proof that does not derive the empty clause")
}

fn is_retryable_proof_unknown(
    reason: Option<&crate::shared_types::UnknownReason>,
    executor_error: Option<&str>,
) -> bool {
    matches!(
        reason,
        Some(crate::shared_types::UnknownReason::ProofTrusted)
    ) || executor_error.is_some_and(is_proof_related_panic)
}

impl AYEncoder {
    /// Assert a term as a constraint.
    ///
    /// Also flushes pending side-effect assertions and activates any pending
    /// quantified disjointness cross-footprint constraint sets captured during
    /// encoding.
    pub fn assert_term(&mut self, term: Term) {
        let this_assertion_revision = self.assertion_pipeline.increment_revision();
        let conservative_raw_assert_recheck = !self.assertion_pipeline.was_encoded_since_assert()
            && !self.assertion_pipeline.has_pending_assertions()
            && !self.assertion_pipeline.has_pending_pure_equalities()
            && self.assertion_pipeline.has_active_disjoint_constraints();
        let relevant_quantified_equality =
            self.has_relevant_quantified_equality() || conservative_raw_assert_recheck;

        // Always assert each term individually — never bundle into one
        // `and_many` conjunction. The former conjunction path lost deeply
        // nested ground constraints (e.g., `neq(loc_0, loc_1)`) when
        // ay-dpll's AUFLIA path processed the combined term without running
        // FlattenAnd preprocessing. (#1788)
        let pending_assertions = self.assertion_pipeline.drain_pending_assertions();
        let primary_ok = self.assert_term_conjuncts("assert_term", term);
        if primary_ok {
            for pending in pending_assertions {
                if !self.assert_term_conjuncts("assert_term/pending", pending) {
                    break;
                }
            }
        }
        if self.assertion_pipeline.is_panicked() {
            return;
        }

        self.assertion_pipeline
            .activate_pending_constraints(relevant_quantified_equality, this_assertion_revision);
        self.assertion_pipeline.clear_pending_pure_equalities();
        self.assertion_pipeline.clear_encoded_mark();
    }

    fn assert_term_conjuncts(&mut self, operation: &str, term: Term) -> bool {
        let mut conjuncts = Vec::new();
        self.collect_assertion_conjuncts(term, &mut conjuncts);
        for conjunct in conjuncts {
            // Prenex-normalize a guard-wrapped universal so it reaches ay in
            // top-level CONJUNCTIVE position. (#quantifier-frontier)
            let conjunct = self.prenex_push_assertion(conjunct).unwrap_or(conjunct);
            if self.term_is_obviously_true(conjunct) {
                continue;
            }
            if self.term_is_obviously_false(conjunct) {
                let false_term = self.solver.bool_const(false);
                if !self.assert_solver_term(operation, false_term) {
                    return false;
                }
                continue;
            }
            if !self.assert_solver_term(operation, conjunct) {
                return false;
            }
        }
        true
    }

    /// Prenex-normalize ONE top-level assertion conjunct: rewrite
    /// `(or A₁ … Aₙ (forall x. B))` into `(forall x. (or A₁ … Aₙ B))` when no
    /// binder of the quantifier occurs free in any `Aᵢ`. Returns `None` — caller
    /// keeps the term unchanged — for any other shape, when a binder IS free in
    /// a disjunct, or when the rewrite cannot be rebuilt faithfully.
    ///
    /// Also accepts the `(=> G F)` spelling, since callers build implications
    /// both ways.
    ///
    /// WHY. ay's quantifier soundness gate (`classify_quantifier_result`,
    /// ay-dpll `executor/quantifier_loop/result_mapping.rs`) refuses to trust
    /// the E-matched instances of a `forall` that is not in top-level
    /// CONJUNCTIVE position (`forall_ids_in_conjunctive_position`). A
    /// disjunction is not, so such a premise is discounted and the whole solve
    /// degrades to `unknown`. We emit that shape a great deal: every quantified
    /// call postcondition assumed inside a branch arrives as
    /// `G ⇒ ∀k. frame(k)`. On `ghost/ghost_map.rs` it is 28 of 31 foralls in a
    /// single query.
    ///
    /// This runs at the assertion boundary rather than at any one producer
    /// because that is where the shape actually matters — `assert_term_conjuncts`
    /// builds exactly the assertion list ay classifies, so every producer is
    /// covered by one seam. (An earlier attempt at the `guard_with_active_path`
    /// producer was MEASURED INERT: the ghost_map non-conjunctive census did not
    /// move, so the guarded foralls reach the solver by some other route.)
    ///
    /// SOUNDNESS. `A ∨ ∀x. B(x)` and `∀x. (A ∨ B(x))` are EQUIVALENT in
    /// first-order logic whenever `x` is not free in `A` (SMT sorts are
    /// non-empty, so no side condition is needed), and the equivalence is
    /// polarity-independent — valid in assumption and goal position alike. No
    /// premise is added and none is dropped. The freeness side condition is
    /// CHECKED, not assumed: [`Self::collect_assertion_var_terms`] walks each
    /// non-quantifier disjunct and the rewrite is declined if any binder name
    /// occurs there. (#quantifier-frontier)
    fn prenex_push_assertion(&mut self, term: Term) -> Option<Term> {
        let (rest, quantified) = match self.solver.term_kind(term) {
            TermKind::App { ref name, num_args } if name == "=>" && num_args == 2 => {
                let args = self.solver.term_children(term);
                let [guard, consequent] = args.as_slice() else {
                    return None;
                };
                if !matches!(self.solver.term_kind(*consequent), TermKind::Forall) {
                    return None;
                }
                (vec![*guard], *consequent)
            }
            TermKind::App { ref name, .. } if name == "or" => {
                let args = self.solver.term_children(term);
                let mut quantified = None;
                let mut rest = Vec::with_capacity(args.len());
                for arg in args {
                    if matches!(self.solver.term_kind(arg), TermKind::Forall) {
                        if quantified.is_some() {
                            // Two universals under one disjunction: pushing one
                            // would leave the other in place, so decline.
                            return None;
                        }
                        quantified = Some(arg);
                    } else {
                        rest.push(arg);
                    }
                }
                (rest, quantified?)
            }
            _ => return None,
        };
        if rest.is_empty() {
            return None;
        }

        let bound = self.solver.quantifier_bound_vars(quantified)?;
        if bound.is_empty() {
            return None;
        }
        let children = self.solver.term_children(quantified);
        let [body] = children.as_slice() else {
            return None;
        };
        let body = *body;

        // Side condition: no binder may occur free in any non-quantifier
        // disjunct.
        for disjunct in &rest {
            let free = self.collect_assertion_var_terms(*disjunct)?;
            if bound.iter().any(|(name, _)| free.contains_key(name)) {
                return None;
            }
        }

        // ay's quantifier constructors take variable TERMS, not (name, sort)
        // pairs. `Var(name, sort)` is hash-consed, so the occurrence inside the
        // body IS the binder term; recover it rather than minting a fresh var,
        // which would carry a different name and leave the body's occurrences
        // unbound.
        let body_vars = self.collect_assertion_var_terms(body)?;
        let mut var_terms: Vec<Term> = Vec::with_capacity(bound.len());
        for (name, sort) in &bound {
            let var_term = *body_vars.get(name)?;
            if self.solver.term_sort(var_term) != *sort {
                return None;
            }
            var_terms.push(var_term);
        }

        let triggers = self.solver.quantifier_triggers(quantified)?;
        let new_body = if rest.len() == 1
            && matches!(self.solver.term_kind(term), TermKind::App { ref name, .. } if name == "=>")
        {
            self.solver.try_implies(rest[0], body).ok()?
        } else {
            let mut disjuncts = rest;
            disjuncts.push(body);
            self.solver.try_or_many(&disjuncts).ok()?
        };
        let trigger_refs: Vec<&[Term]> = triggers.iter().map(Vec::as_slice).collect();
        let pushed = self
            .solver
            .try_forall_with_triggers(&var_terms, new_body, &trigger_refs)
            .ok()?;
        tracing::trace!("prenex-pushed a guard-wrapped universal into conjunctive position");
        Some(pushed)
    }

    /// Every distinct `Var` term reachable from `root`, keyed by variable name.
    ///
    /// Returns `None` when the walk budget is exhausted, so a caller relying on
    /// the "no binder occurs here" side condition declines rather than acting on
    /// a partial view. (#quantifier-frontier)
    fn collect_assertion_var_terms(&self, root: Term) -> Option<HashMap<String, Term>> {
        let mut found: HashMap<String, Term> = HashMap::new();
        let mut seen: HashSet<Term> = HashSet::new();
        let mut stack = vec![root];
        let mut budget = PRENEX_PUSH_WALK_BUDGET;
        while let Some(term) = stack.pop() {
            budget = budget.checked_sub(1)?;
            if !seen.insert(term) {
                continue;
            }
            if let TermKind::Var { name } = self.solver.term_kind(term) {
                found.entry(name).or_insert(term);
            }
            stack.extend(self.solver.term_children(term));
        }
        Some(found)
    }

    pub(in crate::encoder) fn collect_assertion_conjuncts(&self, term: Term, out: &mut Vec<Term>) {
        match self.solver.term_kind(term) {
            TermKind::App { name, .. } if name == "and" => {
                for child in self.solver.term_children(term) {
                    self.collect_assertion_conjuncts(child, out);
                }
            }
            TermKind::App { name, .. } if name == "or" => {
                let non_false: Vec<Term> = self
                    .solver
                    .term_children(term)
                    .into_iter()
                    .filter(|child| !self.term_is_obviously_false(*child))
                    .collect();
                if non_false
                    .iter()
                    .any(|child| self.term_is_obviously_true(*child))
                {
                    return;
                } else if let [child] = non_false.as_slice() {
                    self.collect_assertion_conjuncts(*child, out);
                } else {
                    out.push(term);
                }
            }
            TermKind::Not => {
                let children = self.solver.term_children(term);
                if let [inner] = children.as_slice() {
                    if matches!(self.solver.term_kind(*inner), TermKind::Not) {
                        let inner_children = self.solver.term_children(*inner);
                        if let [double_inner] = inner_children.as_slice() {
                            self.collect_assertion_conjuncts(*double_inner, out);
                            return;
                        }
                    }
                }
                out.push(term);
            }
            _ => out.push(term),
        }
    }

    /// Assert `a = b` in the SMT solver.
    pub(crate) fn assert_eq(&mut self, a: Term, b: Term) {
        let finite_ground_seq_equality = self.use_seq_len_proxies()
            && self.quantifier_state.quantifier_depth() == 0
            && crate::encoder::sort_context::is_seq_family_sort(&self.solver.get_sort(a))
            && crate::encoder::sort_context::is_seq_family_sort(&self.solver.get_sort(b));
        let term = if finite_ground_seq_equality {
            self.seq_aware_equality_term(a, b)
        } else {
            self.eq_term(a, b)
        };
        self.assert_term(term);
        // Propagate SeqValue across the equality so that primed variables
        // inherit concrete len/arr/offset from their body-effect sources.
        // Without this, seq_len_term on the primed variable hits the UF
        // fallback path instead of the fast concrete path. (#2323)
        let sv_a = self.seq_state.get_seq_value_cloned(&a);
        let sv_b = self.seq_state.get_seq_value_cloned(&b);
        match (sv_a, sv_b) {
            (Some(sv), None) => {
                self.insert_seq_value(b, sv);
            }
            (None, Some(sv)) => {
                self.insert_seq_value(a, sv);
            }
            _ => {}
        }
    }

    /// Check satisfiability of current assertions.
    ///
    /// Automatically flushes ground pool instances before solving to compensate
    /// for ay-dpll's single-round E-matching limitation. This ensures that
    /// ground instantiations of registered axioms (logic function defining
    /// axioms, etc.) are available to the solver without requiring callers to
    /// explicitly call `assert_ground_pool_instances()`. (#994)
    ///
    /// If the underlying ay solver panics (e.g., assertion failure, internal
    /// bug), the panic is caught and `SolveResult::Unknown` is returned so
    /// that the verification pipeline can continue with remaining functions.
    ///
    /// **BV timeout gap (#1342):** ay-dpll's bitvector theory solver calls
    /// `SatSolver::solve()` which is non-interruptible. The `set_timeout()`
    /// API only affects interruptible solve paths, so BV-heavy queries can
    /// bypass the configured timeout entirely. The verification layer wraps
    /// this call in a hard-timeout envelope (`verify::hard_timeout`) that
    /// moves the encoder to a worker thread and enforces an outer deadline
    /// via `mpsc::recv_timeout`.
    /// Defense-in-depth relative-timeout floor installed for the duration of
    /// one `check_sat` when no solver timeout is configured, so the
    /// interruptible solve path (including ay's quantifier E-matching deadline
    /// poll) always has a deadline to honor instead of running unbounded until
    /// the external hard-timeout worker abandons it with no per-obligation
    /// provenance. Chosen below the external worker-abandon point (~60s) so ay
    /// self-terminates (with a diagnostic) first.
    const DEFAULT_SOLVE_DEADLINE_FLOOR: std::time::Duration = std::time::Duration::from_secs(45);

    /// Public solve entry point. Wraps [`Self::check_sat_inner`] with the
    /// relative-timeout floor above, restored on every return path so that
    /// `get_timeout()` semantics are unchanged for callers and probe
    /// save/restore sites. The floor only ever shortens a solve toward
    /// `Unknown`: it adds/removes no assertions, so it can never turn a
    /// satisfiable VC into a (false) `Unsat`.
    pub fn check_sat(&mut self) -> SolveResult {
        let prior_timeout = self.solver.timeout();
        let installed_floor = prior_timeout.is_none();
        if installed_floor {
            self.solver
                .set_timeout(Some(Self::DEFAULT_SOLVE_DEADLINE_FLOOR));
        }
        let result = self.check_sat_inner();
        if installed_floor {
            self.solver.set_timeout(prior_timeout);
        }
        result
    }

    #[tracing::instrument(name = "trust_wp::solve", level = "debug", skip_all)]
    fn check_sat_inner(&mut self) -> SolveResult {
        // Clear cached solve diagnostics from any previous call so stale data
        // is never observed by consumers. (#2639)
        self.encoding_cache.clear_solve_diagnostics();
        // Name this solve so a strict-replay observation can be bound to it.
        // Counted HERE rather than inside `clear_solve_diagnostics` because
        // `drop_stale_unknown_diagnostics_after_definitive_retry` clears and
        // restores the SAME solve's diagnostics through that method.
        self.encoding_cache.begin_solve();

        if self.assertion_pipeline.is_panicked() {
            self.replay_recorder.record_check_sat("check_sat");
            self.replay_recorder.record_result_with_detail(
                ReplayResultStatus::Unknown,
                "assertion pipeline previously recorded solver panic",
            );
            self.cache_native_replay_json(None);
            return SolveResult::Unknown;
        }
        if self.assertion_pipeline.has_pending_assertions()
            || self.assertion_pipeline.has_pending_disjoint_constraints()
        {
            self.assertion_pipeline.record_solver_panic(
                "check_sat called with unflushed pending assertions".to_string(),
            );
            return SolveResult::Unknown;
        }
        // Flush term-only standard-library ground instances for direct,
        // unscoped solver callers. Scoped verification paths manage these
        // explicitly before probes; re-flushing here duplicates Seq facts in
        // the pushed goal and can push simple SAT preservation slices into
        // theory-solver timeouts.
        // Native Seq carrier aliases exist only to feed ext_eq's bounded UF
        // congruence bridge.  Materializing them for a component-only query
        // adds an otherwise unsupported model-validation atom and can turn a
        // finite Array/Int preservation proof into `Unknown(Incomplete)`.
        if self.encoding_cache.ext_eq_registry_len() > 0 {
            self.assert_seq_component_aliases_from_assertions();
        }
        self.assert_resolve_elsewhere_ground_instances();
        if self.solver.num_scopes() == 0 {
            self.assert_standard_ground_instances();
        } else if !self.closure_mapping_axioms.is_empty() {
            // `assert_standard_ground_instances` (which carries the predicate-
            // closure ground instances) runs only for UNSCOPED solves, but the
            // per-obligation function/postcondition solve pushes its negated goal
            // in a scope (num_scopes > 0). That scoped goal is exactly where a
            // predicate-closure obligation like cell/01_basic's
            // `mapping_get(c@, v + 2)` lives, so without re-materializing the
            // closure body at the goal's keys here the obligation stays
            // `quantifier-unhandled`. Sound: every emitted instance is entailed
            // by the already-asserted closure universal (see
            // `assert_mapping_closure_get_instances`). Asserted into the current
            // scope, so it is popped with the obligation.
            let _ = self.assert_mapping_closure_get_instances(64);
        }

        // Flush ground pool instances before solving. This asserts ground
        // instantiations of registered axioms (e.g., logic_fn defining axioms)
        // using ground terms collected during encoding. Without this, ay-dpll's
        // single-round E-matching may find trigger matches but fail to combine
        // the resulting UF equalities with arithmetic reasoning.
        //
        // Only call when there are registered axioms to avoid overhead on
        // tests/functions that don't use logic functions.
        self.assert_struct_field_placeholder_ground_aliases();
        self.assert_registered_enum_payload_ground_consequences_from_assertions();
        // Guarded nonlinear product-bound lemmas (completeness only). Runs
        // unconditionally here — at the universal pre-solve point — so the full
        // query, including the just-asserted negated goal that carries the
        // opaque `nlmul(x, y)` term, is in scope. Every emitted fact is a
        // tautology of integer arithmetic (`0<=x<=kx && 0<=y<=ky ==> x*y<=kx*ky`
        // and `0<=x && 0<=y ==> x*y>=0`), so this can never introduce a
        // false-accept; it only adds true facts that let the linear core close
        // bounded nonlinear obligations. See `nonlinear_product_bounds`.
        if let Err(e) = self.assert_nonlinear_product_bounds() {
            warn!("nonlinear product-bound instantiation failed during check_sat: {e}");
        }
        if !self.ground_pool.axioms().is_empty() {
            self.register_ground_pool_terms_from_assertions();
            let scoped_ground_pool =
                (self.solver.num_scopes() > 0).then(|| self.ground_pool.clone());
            if let Err(e) = self.maybe_assert_logic_ground_instances() {
                warn!("ground pool instantiation failed during check_sat: {e}");
            }
            if let Some(snapshot) = scoped_ground_pool {
                self.ground_pool = snapshot;
            }
        }
        if self.solver.num_scopes() == 0
            && self.assertion_pipeline.has_active_disjoint_constraints()
            && !self.assertion_pipeline.needs_disjoint_recheck()
            && self
                .assertion_pipeline
                .has_current_sat_solve_snapshot(self.solver.assertions().len())
        {
            return self
                .finish_shortcut_solve(SolveResult::Sat, "shortcut:cached-sat-no-new-assertions");
        }
        if self.solver.assertions().is_empty() {
            return self.finish_shortcut_solve(SolveResult::Sat, "shortcut:empty-assertions");
        }
        let shortcut_solve_enabled = self.shortcut_solve_enabled();
        let shortcut_unsat_enabled = self.shortcut_unsat_enabled();
        if shortcut_unsat_enabled && self.assertions_contain_direct_bool_conflict() {
            return self.finish_shortcut_solve(
                SolveResult::Unsat(SmtProofCertificate::empty()),
                "shortcut:direct-bool-conflict",
            );
        }
        if shortcut_unsat_enabled && self.assertions_imply_negated_int_equality_conflict() {
            return self.finish_shortcut_solve(
                SolveResult::Unsat(SmtProofCertificate::empty()),
                "shortcut:negated-int-equality-conflict",
            );
        }
        if shortcut_unsat_enabled && self.assertions_force_quantified_disjoint_overlap() {
            return self.finish_shortcut_solve(
                SolveResult::Unsat(SmtProofCertificate::empty()),
                "shortcut:quantified-disjoint-overlap",
            );
        }
        if shortcut_solve_enabled {
            if let Some(bool_parity_sat) = self.assertions_are_bool_parity_constraints_sat() {
                if bool_parity_sat {
                    return self
                        .finish_shortcut_solve(SolveResult::Sat, "shortcut:bool-parity-sat");
                }
                if shortcut_unsat_enabled {
                    return self.finish_shortcut_solve(
                        SolveResult::Unsat(SmtProofCertificate::empty()),
                        "shortcut:bool-parity-unsat",
                    );
                }
            }
            if let Some(bounds_are_sat) = self.assertions_are_simple_int_bounds_sat() {
                if bounds_are_sat {
                    return self
                        .finish_shortcut_solve(SolveResult::Sat, "shortcut:simple-int-bounds-sat");
                }
                if shortcut_unsat_enabled {
                    return self.finish_shortcut_solve(
                        SolveResult::Unsat(SmtProofCertificate::empty()),
                        "shortcut:simple-int-bounds-unsat",
                    );
                }
            }
        }
        if shortcut_solve_enabled
            && (self.assertions_are_obviously_true()
                || self.assertions_are_ground_int_equalities_sat()
                || self.assertions_are_simple_literal_constraints_sat()
                || self.assertions_are_mixed_simple_constraints_sat()
                || self.assertions_are_unconstrained_placeholder_uf_disequalities_sat())
        {
            return self.finish_shortcut_solve(SolveResult::Sat, "shortcut:syntactic-sat");
        }
        if shortcut_solve_enabled && self.assertions_have_isolated_negated_seq_decomposition_sat() {
            return self.finish_shortcut_solve(
                SolveResult::Sat,
                "shortcut:isolated-negated-seq-decomposition-sat",
            );
        }
        if shortcut_unsat_enabled && self.assertions_are_positive_seq_pushback_shape_sat() {
            return self.finish_shortcut_solve(
                SolveResult::Sat,
                "shortcut:positive-seq-pushback-shape-sat",
            );
        }
        if shortcut_unsat_enabled && self.assertions_have_seq_pushback_poststate_assignment_sat() {
            return self.finish_shortcut_solve(
                SolveResult::Sat,
                "shortcut:seq-pushback-poststate-assignment-sat",
            );
        }
        match catch_solver_panic_with_reason("check_sat", || {
            self.check_sat_with_quantified_disjoint_recheck()
        }) {
            Ok(result) => {
                if matches!(result, SolveResult::Unknown)
                    && is_retryable_proof_unknown(
                        self.last_unknown_reason(),
                        self.last_executor_error(),
                    )
                {
                    if let Some(retried) = self.retry_check_sat_without_proofs() {
                        return retried;
                    }
                }
                result
            }
            Err(err) => {
                self.cache_native_replay_json(None);
                self.replay_recorder.record_result_with_detail(
                    ReplayResultStatus::Unknown,
                    err.reason().to_string(),
                );
                if is_proof_related_panic(err.reason()) {
                    if let Some(retried) = self.retry_check_sat_without_proofs() {
                        return retried;
                    }
                }
                if is_recoverable_sort_mismatch_panic(err.reason()) {
                    unsoundness::increment(unsoundness::UnsoundnessCategory::PanicRecoveryFalse);
                    tracing::debug!(
                        "check_sat recovered from ay sort-mismatch panic: {}",
                        err.reason()
                    );
                    return SolveResult::Unknown;
                }
                self.assertion_pipeline
                    .record_solver_panic(err.into_reason());
                SolveResult::Unknown
            }
        }
    }

    fn shortcut_solve_enabled(&self) -> bool {
        self.solver.timeout() != Some(Duration::ZERO)
    }

    fn shortcut_unsat_enabled(&self) -> bool {
        self.shortcut_solve_enabled()
            && self
                .assertion_pipeline
                .negated_goal_label_prefix()
                .is_none()
    }

    fn finish_shortcut_solve(&mut self, result: SolveResult, detail: &'static str) -> SolveResult {
        let mut stats = SolveStatisticsSnapshot::default();
        stats.num_assertions = self.solver.assertions().len() as u64;
        let evidence = self.shortcut_solve_evidence(&result, detail);
        if matches!(result, SolveResult::Sat) {
            self.assertion_pipeline
                .record_sat_solve_snapshot(self.solver.assertions().len());
        } else {
            self.assertion_pipeline.clear_sat_solve_snapshot();
        }

        self.replay_recorder.record_check_sat("check_sat");
        self.cache_native_replay_json(None);
        self.encoding_cache.set_solve_statistics(stats);
        self.encoding_cache.set_solve_evidence(evidence);
        self.replay_recorder
            .record_result_with_detail(shortcut_replay_status(&result), detail);

        result
    }

    fn shortcut_solve_evidence(
        &self,
        result: &SolveResult,
        detail: &'static str,
    ) -> SolveEvidenceSnapshot {
        let accepted_for_consumer = false;
        let consumer_rejection = match result {
            SolveResult::Sat => Some(format!(
                "shortcut SAT result ({detail}) did not run ay model validation"
            )),
            SolveResult::Unsat(_) => Some(format!(
                "shortcut UNSAT result ({detail}) did not run ay solve details/proof validation"
            )),
            SolveResult::Unknown => Some(format!(
                "shortcut Unknown result ({detail}) did not run ay solve details"
            )),
            #[allow(unreachable_patterns)]
            _ => Some(format!(
                "shortcut result ({detail}) did not run ay solve details"
            )),
        };
        SolveEvidenceSnapshot {
            result: result.to_string(),
            model_validated: false,
            accepted_for_consumer,
            consumer_rejection,
            verification: SolveVerificationSnapshot::default(),
            verification_level: SolveVerificationLevelSnapshot::Unknown,
            resource_usage: SolveResourceSnapshot::default(),
        }
    }

    pub(crate) fn ensure_structural_provenance(&mut self, detail: &'static str) {
        if self.encoding_cache.solve_evidence().is_some()
            && self.encoding_cache.native_replay_json().is_some()
        {
            return;
        }

        if self.encoding_cache.solve_statistics().is_none() {
            let mut stats = SolveStatisticsSnapshot::default();
            stats.num_assertions = self.solver.assertions().len() as u64;
            self.encoding_cache.set_solve_statistics(stats);
        }
        if self.encoding_cache.solve_evidence().is_none() {
            self.encoding_cache
                .set_solve_evidence(self.structural_provenance_evidence());
        }
        if self.encoding_cache.native_replay_json().is_none() {
            self.cache_native_replay_json(None);
        }
        if self.replay_artifact_text().is_none() {
            self.replay_recorder.record_result_with_detail(
                ReplayResultStatus::Unknown,
                format!("trust-wp-structural-provenance:{detail}"),
            );
        }
    }

    pub(crate) fn record_structural_ground_consequence(&mut self, detail: &'static str) {
        self.encoding_cache
            .record_structural_ground_consequence(detail);
    }

    pub(crate) fn has_structural_ground_consequences(&self) -> bool {
        !self
            .encoding_cache
            .structural_ground_consequence_details()
            .is_empty()
    }

    fn structural_provenance_evidence(&self) -> SolveEvidenceSnapshot {
        SolveEvidenceSnapshot {
            result: "trust-wp-structural-provenance".to_string(),
            model_validated: false,
            accepted_for_consumer: false,
            consumer_rejection: Some(
                "structural provenance does not include verified solver evidence".to_string(),
            ),
            verification: SolveVerificationSnapshot::default(),
            verification_level: SolveVerificationLevelSnapshot::Unknown,
            resource_usage: SolveResourceSnapshot::default(),
        }
    }

    fn register_ground_pool_terms_from_assertions(&mut self) {
        let symbols: HashSet<String> = self
            .ground_pool
            .axioms()
            .iter()
            .map(|axiom| axiom.fn_symbol.clone())
            .collect();
        if symbols.is_empty() {
            return;
        }
        let assertions = self.solver.assertions();
        let mut seen = HashSet::new();
        for assertion in assertions {
            self.register_ground_pool_terms_from_term(assertion, &symbols, &mut seen);
        }
    }

    fn register_ground_pool_terms_from_term(
        &mut self,
        term: Term,
        symbols: &HashSet<String>,
        seen: &mut HashSet<Term>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let TermKind::App { name, .. } = self.solver.term_kind(term) {
            if symbols.contains(&name) {
                let args = self.solver.term_children(term);
                self.ground_pool
                    .register_term_application_with_path_conditions(&name, term, args, Vec::new());
            }
        }
        for child in self.solver.term_children(term) {
            self.register_ground_pool_terms_from_term(child, symbols, seen);
        }
    }

    fn assertions_contain_direct_bool_conflict(&self) -> bool {
        let assertions = self.solver.assertions();
        let mut positive = HashSet::with_capacity(assertions.len());
        let mut negative = HashSet::with_capacity(assertions.len());
        let mut positive_text = HashSet::with_capacity(assertions.len());
        let mut negative_text = HashSet::with_capacity(assertions.len());
        for assertion in assertions {
            if self.term_is_obviously_false(assertion) {
                return true;
            }
            if matches!(self.solver.term_kind(assertion), TermKind::Not) {
                let children = self.solver.term_children(assertion);
                if let [inner] = children.as_slice() {
                    let inner_text = self.solver.format_term(*inner);
                    if positive.contains(inner) {
                        return true;
                    }
                    if positive_text.contains(&inner_text) {
                        return true;
                    }
                    negative.insert(*inner);
                    negative_text.insert(inner_text);
                    continue;
                }
            }
            let assertion_text = self.solver.format_term(assertion);
            if negative.contains(&assertion) {
                return true;
            }
            if negative_text.contains(&assertion_text) {
                return true;
            }
            positive.insert(assertion);
            positive_text.insert(assertion_text);
        }
        false
    }

    fn term_is_obviously_false(&self, term: Term) -> bool {
        if matches!(self.solver.term_kind(term), TermKind::Const)
            && self.solver.format_term(term) == "false"
        {
            return true;
        }
        if matches!(self.solver.term_kind(term), TermKind::Not) {
            let children = self.solver.term_children(term);
            return matches!(children.as_slice(), [inner] if self.term_is_obviously_true(*inner));
        }
        if let Some((lhs, rhs)) = self.term_equality(term) {
            return self.terms_are_distinct_literals(lhs, rhs);
        }
        if let Some((lhs, rhs)) = self.term_disequality(term) {
            return lhs == rhs
                || self
                    .literal_key(lhs)
                    .is_some_and(|lhs| self.literal_key(rhs).is_some_and(|rhs| lhs == rhs));
        }
        if let Some(comparison_holds) = self.term_int_comparison_holds(term) {
            return !comparison_holds;
        }
        false
    }

    fn term_is_obviously_true(&self, term: Term) -> bool {
        if matches!(self.solver.term_kind(term), TermKind::Const)
            && self.solver.format_term(term) == "true"
        {
            return true;
        }
        if matches!(self.solver.term_kind(term), TermKind::Not) {
            let children = self.solver.term_children(term);
            return matches!(children.as_slice(), [inner] if self.term_is_obviously_false(*inner));
        }
        if let Some((lhs, rhs)) = self.term_equality(term) {
            return lhs == rhs
                || self
                    .literal_key(lhs)
                    .is_some_and(|lhs| self.literal_key(rhs).is_some_and(|rhs| lhs == rhs));
        }
        if let Some((lhs, rhs)) = self.term_disequality(term) {
            return self.terms_are_distinct_literals(lhs, rhs);
        }
        if let Some(comparison_holds) = self.term_int_comparison_holds(term) {
            return comparison_holds;
        }
        false
    }

    fn terms_are_distinct_literals(&self, lhs: Term, rhs: Term) -> bool {
        let Some(lhs) = self.literal_key(lhs) else {
            return false;
        };
        let Some(rhs) = self.literal_key(rhs) else {
            return false;
        };
        lhs.0 == rhs.0 && lhs.1 != rhs.1
    }

    fn literal_key(&self, term: Term) -> Option<(Sort, String)> {
        if !matches!(self.solver.term_kind(term), TermKind::Const) {
            return None;
        }
        let sort = self.solver.get_sort(term);
        if !matches!(&sort, Sort::Bool | Sort::Int | Sort::Real) {
            return None;
        }
        Some((sort, self.solver.format_term(term)))
    }

    fn literal_value_key(&self, term: Term) -> Option<String> {
        self.literal_key(term)
            .map(|(sort, value)| format!("{sort:?}:{value}"))
    }

    pub(in crate::encoder) fn term_int_literal(&self, term: Term) -> Option<BigInt> {
        if self.solver.get_sort(term) != Sort::Int {
            return None;
        }
        match self.solver.term_kind(term) {
            TermKind::Const => parse_formatted_int_literal(&self.solver.format_term(term)),
            TermKind::App { name, num_args: 2 } if matches!(name.as_str(), "+" | "-" | "*") => {
                let children = self.solver.term_children(term);
                let [lhs, rhs] = children.as_slice() else {
                    return None;
                };
                let lhs = self.term_int_literal(*lhs)?;
                let rhs = self.term_int_literal(*rhs)?;
                match name.as_str() {
                    "+" => Some(lhs + rhs),
                    "-" => Some(lhs - rhs),
                    "*" => Some(lhs * rhs),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(crate) fn term_int_comparison_holds(&self, term: Term) -> Option<bool> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if !matches!(name.as_str(), "<" | "<=" | ">" | ">=") {
            return None;
        }
        let children = self.solver.term_children(term);
        let [lhs, rhs] = children.as_slice() else {
            return None;
        };
        let lhs = self.term_int_literal(*lhs)?;
        let rhs = self.term_int_literal(*rhs)?;
        match name.as_str() {
            "<" => Some(lhs < rhs),
            "<=" => Some(lhs <= rhs),
            ">" => Some(lhs > rhs),
            ">=" => Some(lhs >= rhs),
            _ => None,
        }
    }

    fn assertions_are_obviously_true(&self) -> bool {
        let assertions = self.solver.assertions();
        !assertions.is_empty()
            && assertions
                .into_iter()
                .all(|assertion| self.term_is_obviously_true(assertion))
    }

    fn assert_term_contains_term(
        &self,
        haystack: Term,
        needle: Term,
        needle_text: &str,
        seen: &mut HashSet<Term>,
    ) -> bool {
        if haystack == needle || self.solver.format_term(haystack) == needle_text {
            return true;
        }
        if !seen.insert(haystack) {
            return false;
        }
        self.solver
            .term_children(haystack)
            .into_iter()
            .any(|child| self.assert_term_contains_term(child, needle, needle_text, seen))
    }

    fn collect_seq_projector_free_vars(&self, term: Term, vars: &mut HashSet<Term>) {
        if let TermKind::App { name, num_args: 1 } = self.solver.term_kind(term) {
            if matches!(name.as_str(), "seq_array" | "seq_len" | "seq_offset") {
                let children = self.solver.term_children(term);
                if let [receiver] = children.as_slice() {
                    if matches!(self.solver.term_kind(*receiver), TermKind::Var { .. }) {
                        vars.insert(*receiver);
                    }
                }
            }
        }
        for child in self.solver.term_children(term) {
            self.collect_seq_projector_free_vars(child, vars);
        }
    }

    fn assertion_is_seq_len_nonnegative_for_var(&self, assertion: Term, var: Term) -> bool {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(assertion) else {
            return false;
        };
        if !matches!(name.as_str(), "<=" | ">=") {
            return false;
        }
        let children = self.solver.term_children(assertion);
        let [lhs, rhs] = children.as_slice() else {
            return false;
        };
        let zero = BigInt::from(0);
        let lhs_zero = self
            .term_int_literal(*lhs)
            .is_some_and(|value| value == zero);
        let rhs_zero = self
            .term_int_literal(*rhs)
            .is_some_and(|value| value == zero);
        let is_seq_len_of_var = |term: Term| {
            let TermKind::App { name, num_args: 1 } = self.solver.term_kind(term) else {
                return false;
            };
            if name != "seq_len" {
                return false;
            }
            let children = self.solver.term_children(term);
            matches!(children.as_slice(), [receiver] if *receiver == var)
        };
        (name == "<=" && lhs_zero && is_seq_len_of_var(*rhs))
            || (name == ">=" && rhs_zero && is_seq_len_of_var(*lhs))
    }

    fn free_var_alias_for_var(&self, assertion: Term, var: Term) -> Option<Term> {
        let (lhs, rhs) = self.term_equality(assertion)?;
        match (
            lhs == var && self.term_is_free_var(rhs),
            rhs == var && self.term_is_free_var(lhs),
        ) {
            (true, _) => Some(rhs),
            (_, true) => Some(lhs),
            _ => None,
        }
    }

    fn assertions_have_isolated_negated_seq_decomposition_sat(&self) -> bool {
        let assertions = self.solver.assertions();
        for (candidate_index, assertion) in assertions.iter().enumerate() {
            let candidate_body = match self.solver.term_kind(*assertion) {
                TermKind::Not => {
                    let children = self.solver.term_children(*assertion);
                    let [inner] = children.as_slice() else {
                        continue;
                    };
                    *inner
                }
                TermKind::App { name, .. } if name == "or" => {
                    let has_disequality_disjunct = self
                        .solver
                        .term_children(*assertion)
                        .into_iter()
                        .any(|child| matches!(self.solver.term_kind(child), TermKind::Not));
                    if !has_disequality_disjunct {
                        continue;
                    }
                    *assertion
                }
                _ => continue,
            };
            let mut vars = HashSet::new();
            self.collect_seq_projector_free_vars(candidate_body, &mut vars);
            if vars.is_empty() {
                continue;
            }
            for var in vars {
                let var_text = self.solver.format_term(var);
                let mut alias_terms: Vec<(usize, Term, String)> = Vec::new();
                for (index, other) in assertions.iter().enumerate() {
                    if index == candidate_index {
                        continue;
                    }
                    if let Some(alias) = self.free_var_alias_for_var(*other, var) {
                        alias_terms.push((index, alias, self.solver.format_term(alias)));
                    }
                }
                let appears_elsewhere = assertions.iter().enumerate().any(|(index, other)| {
                    let is_alias_assertion = alias_terms
                        .iter()
                        .any(|(alias_index, _, _)| *alias_index == index);
                    let contains_var = index != candidate_index
                        && !matches!(
                            self.solver.term_kind(*other),
                            TermKind::Forall | TermKind::Exists
                        )
                        && !self.assertion_is_seq_len_nonnegative_for_var(*other, var)
                        && !is_alias_assertion
                        && self.assert_term_contains_term(
                            *other,
                            var,
                            &var_text,
                            &mut HashSet::new(),
                        );
                    let contains_alias =
                        alias_terms.iter().any(|(alias_index, alias, alias_text)| {
                            index != *alias_index
                                && index != candidate_index
                                && !matches!(
                                    self.solver.term_kind(*other),
                                    TermKind::Forall | TermKind::Exists
                                )
                                && self.assert_term_contains_term(
                                    *other,
                                    *alias,
                                    alias_text,
                                    &mut HashSet::new(),
                                )
                        });
                    contains_var || contains_alias
                });
                if !appears_elsewhere {
                    return true;
                }
            }
        }
        false
    }

    fn assertions_are_positive_seq_pushback_shape_sat(&self) -> bool {
        let assertions = self.solver.assertions();
        if assertions.is_empty()
            || assertions
                .iter()
                .any(|assertion| self.term_contains_negation(*assertion))
        {
            return false;
        }

        let mut saw_pushback_shape = false;
        for assertion in assertions {
            if self.term_is_obviously_true(assertion) {
                continue;
            }
            if self.term_is_obviously_false(assertion) || self.term_disequality(assertion).is_some()
            {
                return false;
            }
            if matches!(self.solver.term_kind(assertion), TermKind::Forall) {
                continue;
            }
            if self.assertion_is_seq_len_nonnegative(assertion) {
                continue;
            }
            let Some((lhs, rhs)) = self.term_equality(assertion) else {
                return false;
            };
            if self.equality_compares_seq_pushback_projection_to_int(lhs, rhs) {
                return false;
            }
            if self.term_contains_seq_push_back(assertion) {
                if !self.seq_pushback_shape_or_ground_axiom_equality(lhs, rhs) {
                    return false;
                }
                saw_pushback_shape = true;
            }
        }
        saw_pushback_shape
    }

    fn assertion_is_seq_len_nonnegative(&self, assertion: Term) -> bool {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(assertion) else {
            return false;
        };
        if !matches!(name.as_str(), "<=" | ">=") {
            return false;
        }
        let children = self.solver.term_children(assertion);
        let [lhs, rhs] = children.as_slice() else {
            return false;
        };
        let zero = BigInt::from(0);
        let lhs_zero = self
            .term_int_literal(*lhs)
            .is_some_and(|value| value == zero);
        let rhs_zero = self
            .term_int_literal(*rhs)
            .is_some_and(|value| value == zero);
        (name == "<=" && lhs_zero && self.seq_projector_receiver(*rhs, "seq_len").is_some())
            || (name == ">=" && rhs_zero && self.seq_projector_receiver(*lhs, "seq_len").is_some())
    }

    fn seq_pushback_shape_or_ground_axiom_equality(&self, lhs: Term, rhs: Term) -> bool {
        self.seq_pushback_constructor_shape_equality(lhs, rhs)
            || self.seq_pushback_concat_equiv_equality(lhs, rhs)
            || self.seq_pushback_reverse_equality(lhs, rhs)
    }

    fn seq_pushback_constructor_shape_equality(&self, lhs: Term, rhs: Term) -> bool {
        self.seq_pushback_constructor_array_shape_sides(lhs, rhs)
            || self.seq_pushback_constructor_array_shape_sides(rhs, lhs)
            || self.seq_pushback_constructor_len_shape_sides(lhs, rhs)
            || self.seq_pushback_constructor_len_shape_sides(rhs, lhs)
            || self.seq_pushback_constructor_offset_shape_sides(lhs, rhs)
            || self.seq_pushback_constructor_offset_shape_sides(rhs, lhs)
    }

    fn seq_pushback_constructor_array_shape_sides(
        &self,
        projector: Term,
        store_term: Term,
    ) -> bool {
        let Some(pushback) = self.seq_projector_receiver(projector, "seq_array") else {
            return false;
        };
        let Some((base, value)) = self.seq_push_back_parts(pushback) else {
            return false;
        };
        let TermKind::App { name, num_args: 3 } = self.solver.term_kind(store_term) else {
            return false;
        };
        if name != "store" {
            return false;
        }
        let children = self.solver.term_children(store_term);
        let [array, index, stored_value] = children.as_slice() else {
            return false;
        };
        self.seq_projector_receiver(*array, "seq_array") == Some(base)
            && self.term_is_seq_pushback_write_index(*index, base)
            && *stored_value == value
    }

    fn seq_pushback_constructor_len_shape_sides(&self, projector: Term, increment: Term) -> bool {
        let Some(pushback) = self.seq_projector_receiver(projector, "seq_len") else {
            return false;
        };
        let Some((base, _value)) = self.seq_push_back_parts(pushback) else {
            return false;
        };
        self.seq_len_increment_base(increment) == Some(base)
    }

    fn seq_pushback_constructor_offset_shape_sides(
        &self,
        projector: Term,
        base_projector: Term,
    ) -> bool {
        let Some(pushback) = self.seq_projector_receiver(projector, "seq_offset") else {
            return false;
        };
        let Some((base, _value)) = self.seq_push_back_parts(pushback) else {
            return false;
        };
        self.seq_projector_receiver(base_projector, "seq_offset") == Some(base)
    }

    fn seq_pushback_concat_equiv_equality(&self, lhs: Term, rhs: Term) -> bool {
        self.seq_pushback_concat_equiv_sides(lhs, rhs)
            || self.seq_pushback_concat_equiv_sides(rhs, lhs)
    }

    fn seq_pushback_concat_equiv_sides(&self, pushback: Term, concat: Term) -> bool {
        let Some((base, value)) = self.seq_push_back_parts(pushback) else {
            return false;
        };
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(concat) else {
            return false;
        };
        if name != "seq_concat" {
            return false;
        }
        let children = self.solver.term_children(concat);
        let [concat_base, singleton] = children.as_slice() else {
            return false;
        };
        *concat_base == base && self.seq_singleton_value(*singleton) == Some(value)
    }

    fn seq_singleton_value(&self, term: Term) -> Option<Term> {
        let TermKind::App { name, num_args: 1 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "seq_singleton" {
            return None;
        }
        let children = self.solver.term_children(term);
        match children.as_slice() {
            [value] => Some(*value),
            _ => None,
        }
    }

    fn seq_pushback_reverse_equality(&self, lhs: Term, rhs: Term) -> bool {
        self.seq_pushback_reverse_sides(lhs, rhs) || self.seq_pushback_reverse_sides(rhs, lhs)
    }

    fn seq_pushback_reverse_sides(&self, reverse_pushback: Term, push_front_reverse: Term) -> bool {
        let Some(pushback) = self.unary_app_child(reverse_pushback, "seq_reverse") else {
            return false;
        };
        let Some((base, value)) = self.seq_push_back_parts(pushback) else {
            return false;
        };
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(push_front_reverse) else {
            return false;
        };
        if name != "seq_push_front" {
            return false;
        }
        let children = self.solver.term_children(push_front_reverse);
        let [reverse_base, front_value] = children.as_slice() else {
            return false;
        };
        self.unary_app_child(*reverse_base, "seq_reverse") == Some(base) && *front_value == value
    }

    fn unary_app_child(&self, term: Term, expected_name: &str) -> Option<Term> {
        let TermKind::App { name, num_args: 1 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != expected_name {
            return None;
        }
        let children = self.solver.term_children(term);
        match children.as_slice() {
            [child] => Some(*child),
            _ => None,
        }
    }

    fn assertions_have_seq_pushback_poststate_assignment_sat(&self) -> bool {
        let assertions = self.solver.assertions();
        if assertions.is_empty()
            || assertions
                .iter()
                .any(|assertion| self.term_contains_negation(*assertion))
        {
            return false;
        }

        let mut poststate_targets = HashSet::new();
        let mut poststate_assignments = HashMap::new();
        let mut saw_seq_pushback_projection_int_assignment = false;
        for assertion in &assertions {
            let Some((lhs, rhs)) = self.term_equality(*assertion) else {
                continue;
            };
            if self.seq_push_back_base(lhs).is_some()
                && self.term_is_temporal_final_var(rhs)
                && !self.seq_push_back_base(lhs).is_some_and(|base| base == rhs)
            {
                if poststate_assignments
                    .insert(rhs, lhs)
                    .is_some_and(|existing| existing != lhs)
                {
                    return false;
                }
                poststate_targets.insert(rhs);
            }
            if self.seq_push_back_base(rhs).is_some()
                && self.term_is_temporal_final_var(lhs)
                && !self.seq_push_back_base(rhs).is_some_and(|base| base == lhs)
            {
                if poststate_assignments
                    .insert(lhs, rhs)
                    .is_some_and(|existing| existing != rhs)
                {
                    return false;
                }
                poststate_targets.insert(lhs);
            }
        }
        for assertion in &assertions {
            let Some((lhs, rhs)) = self.term_equality(*assertion) else {
                continue;
            };
            if self.seq_push_back_base(lhs).is_some()
                && !self.seq_pushback_assignment_target_is_safe(rhs, lhs)
            {
                return false;
            }
            if self.seq_push_back_base(rhs).is_some()
                && !self.seq_pushback_assignment_target_is_safe(lhs, rhs)
            {
                return false;
            }
            saw_seq_pushback_projection_int_assignment |=
                self.equality_compares_seq_pushback_projection_to_int(lhs, rhs);
            for target in &poststate_targets {
                let lhs_is_target = lhs == *target;
                let rhs_is_target = rhs == *target;
                if !lhs_is_target && !rhs_is_target {
                    continue;
                }
                let other = if lhs_is_target { rhs } else { lhs };
                if self.seq_push_back_base(other).is_some() || self.term_is_free_var(other) {
                    continue;
                }
                return false;
            }
        }
        if !poststate_targets.is_empty() {
            if saw_seq_pushback_projection_int_assignment {
                return false;
            }
            return true;
        }

        if self.assertions_have_seq_pushback_component_poststate_assignment(&assertions) {
            return true;
        }

        false
    }

    fn assertions_have_seq_pushback_component_poststate_assignment(
        &self,
        assertions: &[Term],
    ) -> bool {
        const ARRAY_COMPONENT: u8 = 0b001;
        const LEN_COMPONENT: u8 = 0b010;
        const OFFSET_COMPONENT: u8 = 0b100;
        const ALL_COMPONENTS: u8 = ARRAY_COMPONENT | LEN_COMPONENT | OFFSET_COMPONENT;

        let mut component_shapes: HashMap<(Term, Term, Term), u8> = HashMap::new();
        let mut observed_pushbacks = HashMap::new();
        let mut target_array_stores = Vec::new();
        let mut known_seq_arrays = HashMap::new();
        let mut known_seq_lens = HashMap::new();
        let mut known_seq_offsets = HashMap::new();

        for assertion in assertions {
            self.collect_seq_pushback_terms(
                *assertion,
                &mut observed_pushbacks,
                &mut HashSet::new(),
            );

            let Some((lhs, rhs)) = self.term_equality(*assertion) else {
                continue;
            };
            if let Some((target, base, value)) = self.seq_pushback_array_component_shape(lhs, rhs) {
                component_shapes
                    .entry((target, base, value))
                    .and_modify(|components| *components |= ARRAY_COMPONENT)
                    .or_insert(ARRAY_COMPONENT);
            }
            if let Some((target, array, index, value)) =
                self.seq_final_array_store_components(lhs, rhs)
            {
                target_array_stores.push((target, array, index, value));
            }
            if let Some((target, base)) = self.seq_pushback_len_component_shape(lhs, rhs) {
                for ((shape_target, shape_base, _), components) in &mut component_shapes {
                    if *shape_target == target && *shape_base == base {
                        *components |= LEN_COMPONENT;
                    }
                }
            }
            if let Some((target, base)) = self.seq_pushback_offset_component_shape(lhs, rhs) {
                for ((shape_target, shape_base, _), components) in &mut component_shapes {
                    if *shape_target == target && *shape_base == base {
                        *components |= OFFSET_COMPONENT;
                    }
                }
            }
            if !self.record_seq_len_int_assignment(lhs, rhs, &mut known_seq_lens) {
                return false;
            }
            if !self.record_seq_offset_int_assignment(lhs, rhs, &mut known_seq_offsets) {
                return false;
            }
            if !self.record_seq_array_assignment(lhs, rhs, &mut known_seq_arrays) {
                return false;
            }
        }

        let symbolic_component_match =
            component_shapes
                .into_iter()
                .any(|((target, base, value), components)| {
                    components == ALL_COMPONENTS
                        && observed_pushbacks
                            .get(&(base, value))
                            .is_some_and(|pushback| {
                                self.seq_pushback_component_known_ints_are_consistent(
                                    target,
                                    base,
                                    *pushback,
                                    &known_seq_lens,
                                )
                            })
                });
        if symbolic_component_match {
            return true;
        }

        target_array_stores
            .iter()
            .any(|(target, array, index, value)| {
                observed_pushbacks
                    .iter()
                    .any(|((base, push_value), pushback)| {
                        value == push_value
                            && known_seq_arrays.get(base) == Some(array)
                            && self.term_matches_known_seq_pushback_write_index(
                                *index,
                                *base,
                                &known_seq_lens,
                                &known_seq_offsets,
                            )
                            && self.seq_pushback_concrete_components_are_consistent(
                                *target,
                                *base,
                                *pushback,
                                &known_seq_lens,
                                &known_seq_offsets,
                            )
                    })
            })
    }

    fn collect_seq_pushback_terms(
        &self,
        term: Term,
        out: &mut HashMap<(Term, Term), Term>,
        seen: &mut HashSet<Term>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let Some((base, value)) = self.seq_push_back_parts(term) {
            out.insert((base, value), term);
        }
        for child in self.solver.term_children(term) {
            self.collect_seq_pushback_terms(child, out, seen);
        }
    }

    fn seq_pushback_array_component_shape(
        &self,
        lhs: Term,
        rhs: Term,
    ) -> Option<(Term, Term, Term)> {
        self.seq_pushback_array_component_shape_sides(lhs, rhs)
            .or_else(|| self.seq_pushback_array_component_shape_sides(rhs, lhs))
    }

    fn seq_pushback_array_component_shape_sides(
        &self,
        target_projector: Term,
        store_term: Term,
    ) -> Option<(Term, Term, Term)> {
        let target = self.seq_projector_receiver(target_projector, "seq_array")?;
        if !self.term_is_temporal_final_var(target) {
            return None;
        }
        let TermKind::App { name, num_args: 3 } = self.solver.term_kind(store_term) else {
            return None;
        };
        if name != "store" {
            return None;
        }
        let children = self.solver.term_children(store_term);
        let [array, index, value] = children.as_slice() else {
            return None;
        };
        let base = self.seq_projector_receiver(*array, "seq_array")?;
        if base == target || self.term_is_temporal_final_var(base) {
            return None;
        }
        if !self.term_is_seq_pushback_write_index(*index, base) {
            return None;
        }
        Some((target, base, *value))
    }

    fn seq_final_array_store_components(
        &self,
        lhs: Term,
        rhs: Term,
    ) -> Option<(Term, Term, Term, Term)> {
        self.seq_final_array_store_components_sides(lhs, rhs)
            .or_else(|| self.seq_final_array_store_components_sides(rhs, lhs))
    }

    fn seq_final_array_store_components_sides(
        &self,
        target_projector: Term,
        store_term: Term,
    ) -> Option<(Term, Term, Term, Term)> {
        let target = self.seq_projector_receiver(target_projector, "seq_array")?;
        if !self.term_is_temporal_final_var(target) {
            return None;
        }
        let TermKind::App { name, num_args: 3 } = self.solver.term_kind(store_term) else {
            return None;
        };
        if name != "store" {
            return None;
        }
        let children = self.solver.term_children(store_term);
        let [array, index, value] = children.as_slice() else {
            return None;
        };
        Some((target, *array, *index, *value))
    }

    fn seq_pushback_len_component_shape(&self, lhs: Term, rhs: Term) -> Option<(Term, Term)> {
        self.seq_pushback_len_component_shape_sides(lhs, rhs)
            .or_else(|| self.seq_pushback_len_component_shape_sides(rhs, lhs))
    }

    fn seq_pushback_len_component_shape_sides(
        &self,
        target_projector: Term,
        increment_term: Term,
    ) -> Option<(Term, Term)> {
        let target = self.seq_projector_receiver(target_projector, "seq_len")?;
        if !self.term_is_temporal_final_var(target) {
            return None;
        }
        let base = self.seq_len_increment_base(increment_term)?;
        if base == target || self.term_is_temporal_final_var(base) {
            return None;
        }
        Some((target, base))
    }

    fn seq_pushback_offset_component_shape(&self, lhs: Term, rhs: Term) -> Option<(Term, Term)> {
        self.seq_pushback_offset_component_shape_sides(lhs, rhs)
            .or_else(|| self.seq_pushback_offset_component_shape_sides(rhs, lhs))
    }

    fn seq_pushback_offset_component_shape_sides(
        &self,
        target_projector: Term,
        base_projector: Term,
    ) -> Option<(Term, Term)> {
        let target = self.seq_projector_receiver(target_projector, "seq_offset")?;
        if !self.term_is_temporal_final_var(target) {
            return None;
        }
        let base = self.seq_projector_receiver(base_projector, "seq_offset")?;
        if base == target || self.term_is_temporal_final_var(base) {
            return None;
        }
        Some((target, base))
    }

    fn seq_projector_receiver(&self, term: Term, expected_name: &str) -> Option<Term> {
        let TermKind::App { name, num_args: 1 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != expected_name {
            return None;
        }
        let children = self.solver.term_children(term);
        match children.as_slice() {
            [receiver] => Some(*receiver),
            _ => None,
        }
    }

    fn term_is_seq_pushback_write_index(&self, term: Term, base: Term) -> bool {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return false;
        };
        if name != "+" {
            return false;
        }
        let children = self.solver.term_children(term);
        let [lhs, rhs] = children.as_slice() else {
            return false;
        };
        (self.seq_projector_receiver(*lhs, "seq_offset") == Some(base)
            && self.seq_projector_receiver(*rhs, "seq_len") == Some(base))
            || (self.seq_projector_receiver(*rhs, "seq_offset") == Some(base)
                && self.seq_projector_receiver(*lhs, "seq_len") == Some(base))
    }

    fn term_matches_known_seq_pushback_write_index(
        &self,
        term: Term,
        base: Term,
        known_seq_lens: &HashMap<Term, i64>,
        known_seq_offsets: &HashMap<Term, i64>,
    ) -> bool {
        if self.term_is_seq_pushback_write_index(term, base) {
            return true;
        }
        let Some(index) = self.term_i64_literal(term) else {
            return false;
        };
        let Some(base_len) = known_seq_lens.get(&base) else {
            return false;
        };
        let Some(base_offset) = known_seq_offsets.get(&base) else {
            return false;
        };
        index == base_len + base_offset
    }

    fn seq_len_increment_base(&self, term: Term) -> Option<Term> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "+" {
            return None;
        }
        let children = self.solver.term_children(term);
        let [lhs, rhs] = children.as_slice() else {
            return None;
        };
        if self
            .term_int_literal(*lhs)
            .is_some_and(|value| value == BigInt::from(1))
        {
            return self.seq_projector_receiver(*rhs, "seq_len");
        }
        if self
            .term_int_literal(*rhs)
            .is_some_and(|value| value == BigInt::from(1))
        {
            return self.seq_projector_receiver(*lhs, "seq_len");
        }
        None
    }

    fn record_seq_len_int_assignment(
        &self,
        lhs: Term,
        rhs: Term,
        known_seq_lens: &mut HashMap<Term, i64>,
    ) -> bool {
        if let Some(value) = self.term_i64_literal(lhs) {
            if let Some(receiver) = self.seq_projector_receiver(rhs, "seq_len") {
                if value < 0 {
                    return false;
                }
                if known_seq_lens
                    .get(&receiver)
                    .is_some_and(|existing| *existing != value)
                {
                    return false;
                }
                known_seq_lens.insert(receiver, value);
                return true;
            }
        }
        if let Some(value) = self.term_i64_literal(rhs) {
            if let Some(receiver) = self.seq_projector_receiver(lhs, "seq_len") {
                if value < 0 {
                    return false;
                }
                if known_seq_lens
                    .get(&receiver)
                    .is_some_and(|existing| *existing != value)
                {
                    return false;
                }
                known_seq_lens.insert(receiver, value);
                return true;
            }
        }
        true
    }

    fn record_seq_offset_int_assignment(
        &self,
        lhs: Term,
        rhs: Term,
        known_seq_offsets: &mut HashMap<Term, i64>,
    ) -> bool {
        if let Some(value) = self.term_i64_literal(lhs) {
            if let Some(receiver) = self.seq_projector_receiver(rhs, "seq_offset") {
                if known_seq_offsets
                    .get(&receiver)
                    .is_some_and(|existing| *existing != value)
                {
                    return false;
                }
                known_seq_offsets.insert(receiver, value);
                return true;
            }
        }
        if let Some(value) = self.term_i64_literal(rhs) {
            if let Some(receiver) = self.seq_projector_receiver(lhs, "seq_offset") {
                if known_seq_offsets
                    .get(&receiver)
                    .is_some_and(|existing| *existing != value)
                {
                    return false;
                }
                known_seq_offsets.insert(receiver, value);
                return true;
            }
        }
        true
    }

    fn record_seq_array_assignment(
        &self,
        lhs: Term,
        rhs: Term,
        known_seq_arrays: &mut HashMap<Term, Term>,
    ) -> bool {
        if let Some(receiver) = self.seq_projector_receiver(lhs, "seq_array") {
            if known_seq_arrays
                .get(&receiver)
                .is_some_and(|existing| *existing != rhs)
            {
                return false;
            }
            known_seq_arrays.insert(receiver, rhs);
            return true;
        }
        if let Some(receiver) = self.seq_projector_receiver(rhs, "seq_array") {
            if known_seq_arrays
                .get(&receiver)
                .is_some_and(|existing| *existing != lhs)
            {
                return false;
            }
            known_seq_arrays.insert(receiver, lhs);
            return true;
        }
        true
    }

    fn seq_pushback_component_known_ints_are_consistent(
        &self,
        target: Term,
        base: Term,
        pushback: Term,
        known_seq_lens: &HashMap<Term, i64>,
    ) -> bool {
        let target_len = known_seq_lens.get(&target).copied();
        let base_len = known_seq_lens.get(&base).copied();
        let pushback_len = known_seq_lens.get(&pushback).copied();

        if let Some(pushback_len) = pushback_len {
            if pushback_len < 1 {
                return false;
            }
            if base_len.is_some_and(|base_len| pushback_len != base_len + 1) {
                return false;
            }
        }
        if let Some(target_len) = target_len {
            if target_len < 1 {
                return false;
            }
            if base_len.is_some_and(|base_len| target_len != base_len + 1) {
                return false;
            }
            if pushback_len.is_some_and(|pushback_len| target_len != pushback_len) {
                return false;
            }
        }
        true
    }

    fn seq_pushback_concrete_components_are_consistent(
        &self,
        target: Term,
        base: Term,
        pushback: Term,
        known_seq_lens: &HashMap<Term, i64>,
        known_seq_offsets: &HashMap<Term, i64>,
    ) -> bool {
        let Some(target_len) = known_seq_lens.get(&target).copied() else {
            return false;
        };
        let Some(base_len) = known_seq_lens.get(&base).copied() else {
            return false;
        };
        if target_len != base_len + 1 {
            return false;
        }
        if known_seq_lens
            .get(&pushback)
            .is_some_and(|pushback_len| *pushback_len != target_len)
        {
            return false;
        }

        let Some(target_offset) = known_seq_offsets.get(&target).copied() else {
            return false;
        };
        let Some(base_offset) = known_seq_offsets.get(&base).copied() else {
            return false;
        };
        if target_offset != base_offset {
            return false;
        }
        if known_seq_offsets
            .get(&pushback)
            .is_some_and(|pushback_offset| *pushback_offset != target_offset)
        {
            return false;
        }
        true
    }

    fn seq_pushback_assignment_target_is_safe(&self, target: Term, pushback: Term) -> bool {
        let Some(base) = self.seq_push_back_base(pushback) else {
            return false;
        };
        target != base && !self.solver.format_term(target).contains("seq_empty")
    }

    fn equality_compares_seq_pushback_projection_to_int(&self, lhs: Term, rhs: Term) -> bool {
        (self.term_contains_seq_push_back(lhs) && self.term_int_literal(rhs).is_some())
            || (self.term_contains_seq_push_back(rhs) && self.term_int_literal(lhs).is_some())
    }

    fn term_contains_seq_push_back(&self, term: Term) -> bool {
        if self.seq_push_back_base(term).is_some() {
            return true;
        }
        self.solver
            .term_children(term)
            .into_iter()
            .any(|child| self.term_contains_seq_push_back(child))
    }

    fn term_contains_negation(&self, term: Term) -> bool {
        if self.solver.term_kind(term) == TermKind::Not {
            return true;
        }
        self.solver
            .term_children(term)
            .into_iter()
            .any(|child| self.term_contains_negation(child))
    }

    fn seq_push_back_base(&self, term: Term) -> Option<Term> {
        self.seq_push_back_parts(term).map(|(base, _value)| base)
    }

    fn seq_push_back_parts(&self, term: Term) -> Option<(Term, Term)> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "seq_push_back" {
            return None;
        }
        let children = self.solver.term_children(term);
        match children.as_slice() {
            [base, value] => Some((*base, *value)),
            _ => None,
        }
    }

    pub(in crate::encoder) fn term_is_temporal_final_var(&self, term: Term) -> bool {
        matches!(self.solver.term_kind(term), TermKind::Var { .. })
            && Self::solver_term_text_mentions_temporal_final(&self.solver.format_term(term))
    }

    fn solver_term_text_mentions_temporal_final(term_text: &str) -> bool {
        term_text.contains("_final") || term_text.contains("final_")
    }

    fn term_is_free_var(&self, term: Term) -> bool {
        matches!(self.solver.term_kind(term), TermKind::Var { .. })
    }

    fn literal_assignment_pair(&self, lhs: Term, rhs: Term) -> Option<(Term, String)> {
        if let Some(literal) = self.literal_value_key(lhs) {
            if self.term_is_free_var(rhs) {
                return Some((rhs, literal));
            }
        }
        if let Some(literal) = self.literal_value_key(rhs) {
            if self.term_is_free_var(lhs) {
                return Some((lhs, literal));
            }
        }
        None
    }

    fn int_literal_assignment_pair(&self, lhs: Term, rhs: Term) -> Option<(Term, i64)> {
        if let Some(value) = self.term_i64_literal(lhs) {
            if self.term_is_free_var(rhs) && self.solver.get_sort(rhs) == Sort::Int {
                return Some((rhs, value));
            }
        }
        if let Some(value) = self.term_i64_literal(rhs) {
            if self.term_is_free_var(lhs) && self.solver.get_sort(lhs) == Sort::Int {
                return Some((lhs, value));
            }
        }
        None
    }

    fn assertions_are_mixed_simple_constraints_sat(&self) -> bool {
        let assertions = self.solver.assertions();
        if assertions.is_empty() {
            return false;
        }

        let mut known_literals: HashMap<Term, String> = HashMap::new();
        let mut known_ints: HashMap<Term, i64> = HashMap::new();
        let mut forbidden_literals: HashSet<(Term, String)> = HashSet::new();
        let mut forbidden_ints: HashSet<(Term, i64)> = HashSet::new();
        let mut bounds: HashMap<Term, (Option<i64>, Option<i64>)> = HashMap::new();
        let mut saw_supported_assertion = false;

        for assertion in assertions {
            if self.term_is_obviously_true(assertion) {
                saw_supported_assertion = true;
                continue;
            }
            if self.term_is_obviously_false(assertion) {
                return false;
            }

            if let Some(constraints) = self.simple_int_bound_constraints(assertion) {
                saw_supported_assertion = true;
                for constraint in constraints {
                    if !record_simple_int_bound(
                        constraint,
                        &mut bounds,
                        &known_ints,
                        &forbidden_ints,
                    ) {
                        return false;
                    }
                }
                continue;
            }

            if let Some((lhs, rhs)) = self.term_equality(assertion) {
                if let Some((atom, value)) = self.int_literal_assignment_pair(lhs, rhs) {
                    if !record_known_int(atom, value, &mut known_ints, &bounds, &forbidden_ints) {
                        return false;
                    }
                    saw_supported_assertion = true;
                    continue;
                }
                let Some((atom, literal)) = self.literal_assignment_pair(lhs, rhs) else {
                    return false;
                };
                if known_literals
                    .get(&atom)
                    .is_some_and(|known| known != &literal)
                {
                    return false;
                }
                if forbidden_literals.contains(&(atom, literal.clone())) {
                    return false;
                }
                known_literals.insert(atom, literal);
                saw_supported_assertion = true;
                continue;
            }

            if let Some((lhs, rhs)) = self.term_disequality(assertion) {
                if let Some((atom, value)) = self.int_literal_assignment_pair(lhs, rhs) {
                    if known_ints.get(&atom).is_some_and(|known| *known == value) {
                        return false;
                    }
                    if bounds
                        .get(&atom)
                        .and_then(|(lower, upper)| (*lower).zip(*upper))
                        .is_some_and(|(lower, upper)| lower == upper && lower == value)
                    {
                        return false;
                    }
                    forbidden_ints.insert((atom, value));
                    saw_supported_assertion = true;
                    continue;
                }
                let Some((atom, literal)) = self.literal_assignment_pair(lhs, rhs) else {
                    return false;
                };
                if known_literals
                    .get(&atom)
                    .is_some_and(|known| known == &literal)
                {
                    return false;
                }
                forbidden_literals.insert((atom, literal));
                saw_supported_assertion = true;
                continue;
            }

            return false;
        }

        saw_supported_assertion
    }

    fn assertions_are_simple_literal_constraints_sat(&self) -> bool {
        let assertions = self.solver.assertions();
        if assertions.is_empty() {
            return false;
        }

        let mut known_values: HashMap<Term, String> = HashMap::new();
        let mut forbidden_values: HashSet<(Term, String)> = HashSet::new();
        let mut saw_simple_constraint = false;

        for assertion in assertions {
            if self.term_is_obviously_true(assertion) {
                continue;
            }
            if self.term_is_obviously_false(assertion) {
                return false;
            }
            if let Some((lhs, rhs)) = self.term_equality(assertion) {
                let Some((atom, literal)) = self.literal_assignment_pair(lhs, rhs) else {
                    return false;
                };
                if known_values
                    .get(&atom)
                    .is_some_and(|known| known != &literal)
                {
                    return false;
                }
                if forbidden_values.contains(&(atom, literal.clone())) {
                    return false;
                }
                known_values.insert(atom, literal);
                saw_simple_constraint = true;
                continue;
            }
            if let Some((lhs, rhs)) = self.term_disequality(assertion) {
                let Some((atom, literal)) = self.literal_assignment_pair(lhs, rhs) else {
                    return false;
                };
                if known_values
                    .get(&atom)
                    .is_some_and(|known| known == &literal)
                {
                    return false;
                }
                forbidden_values.insert((atom, literal));
                saw_simple_constraint = true;
                continue;
            }
            return false;
        }

        saw_simple_constraint
    }

    fn assertions_are_unconstrained_placeholder_uf_disequalities_sat(&self) -> bool {
        let assertions = self.solver.assertions();
        if assertions.is_empty() {
            return false;
        }

        let mut saw_disequality = false;
        for assertion in assertions {
            if self.term_is_obviously_true(assertion) {
                continue;
            }
            if self.term_is_obviously_false(assertion) {
                return false;
            }
            let Some((lhs, rhs)) = self.term_disequality(assertion) else {
                return false;
            };
            if self.solver.get_sort(lhs) != self.solver.get_sort(rhs) {
                return false;
            }
            if self.solver.format_term(lhs) == self.solver.format_term(rhs) {
                return false;
            }
            if !matches!(
                self.solver.get_sort(lhs),
                Sort::Int | Sort::Real | Sort::Uninterpreted(_)
            ) {
                return false;
            }
            let Some(lhs_has_placeholder) = self.term_is_placeholder_uf_value_shape(lhs) else {
                return false;
            };
            let Some(rhs_has_placeholder) = self.term_is_placeholder_uf_value_shape(rhs) else {
                return false;
            };
            if !lhs_has_placeholder && !rhs_has_placeholder {
                return false;
            }
            saw_disequality = true;
        }

        saw_disequality
    }

    fn term_is_placeholder_uf_value_shape(&self, term: Term) -> Option<bool> {
        match self.solver.term_kind(term) {
            TermKind::Const | TermKind::Var { .. } => Some(false),
            TermKind::App { name, .. } => {
                if Self::is_interpreted_value_symbol(&name)
                    || !Self::is_placeholder_logic_func_symbol(&name)
                {
                    return None;
                }
                self.solver.term_children(term).into_iter().try_fold(
                    true,
                    |has_placeholder, child| {
                        self.term_is_placeholder_uf_value_shape(child)
                            .map(|child_has_placeholder| has_placeholder || child_has_placeholder)
                    },
                )
            }
            _ => None,
        }
    }

    fn is_placeholder_logic_func_symbol(name: &str) -> bool {
        name.starts_with("logic_") && name.contains("__placeholder_") && name.contains("__ret_")
    }

    fn is_interpreted_value_symbol(name: &str) -> bool {
        matches!(
            name,
            "=" | "distinct"
                | "!="
                | "not"
                | "and"
                | "or"
                | "=>"
                | "ite"
                | "+"
                | "-"
                | "*"
                | "/"
                | "div"
                | "mod"
                | "abs"
                | "<"
                | "<="
                | ">"
                | ">="
                | "to_real"
                | "to_int"
                | "select"
                | "store"
        ) || name.starts_with("seq.")
            || name.starts_with("str.")
            || name.starts_with("bv")
            || name.starts_with("fp.")
    }

    fn assertions_are_bool_parity_constraints_sat(&self) -> Option<bool> {
        let assertions = self.solver.assertions();
        if assertions.is_empty() {
            return None;
        }

        let mut union_find = BoolParityUnionFind::default();
        let mut saw_supported_assertion = false;

        for assertion in assertions {
            if self.term_is_obviously_true(assertion) {
                saw_supported_assertion = true;
                continue;
            }
            if self.term_is_obviously_false(assertion) {
                return Some(false);
            }

            if let Some((atom, negated)) = self.bool_literal_atom(assertion) {
                saw_supported_assertion = true;
                if !union_find.set_constant(atom, !negated) {
                    return Some(false);
                }
                continue;
            }

            if let Some((lhs, rhs)) = self.term_equality(assertion) {
                let (lhs_atom, lhs_negated) = self.bool_literal_atom(lhs)?;
                let (rhs_atom, rhs_negated) = self.bool_literal_atom(rhs)?;
                saw_supported_assertion = true;
                if !union_find.union_parity(lhs_atom, rhs_atom, lhs_negated ^ rhs_negated) {
                    return Some(false);
                }
                continue;
            }

            if let Some((lhs, rhs)) = self.term_disequality(assertion) {
                let (lhs_atom, lhs_negated) = self.bool_literal_atom(lhs)?;
                let (rhs_atom, rhs_negated) = self.bool_literal_atom(rhs)?;
                saw_supported_assertion = true;
                if !union_find.union_parity(lhs_atom, rhs_atom, !(lhs_negated ^ rhs_negated)) {
                    return Some(false);
                }
                continue;
            }

            return None;
        }

        saw_supported_assertion.then_some(true)
    }

    fn bool_literal_atom(&self, term: Term) -> Option<(Term, bool)> {
        if self.solver.get_sort(term) != Sort::Bool {
            return None;
        }
        match self.solver.term_kind(term) {
            TermKind::Var { .. } => Some((term, false)),
            TermKind::Not => {
                let children = self.solver.term_children(term);
                let [inner] = children.as_slice() else {
                    return None;
                };
                let (atom, negated) = self.bool_literal_atom(*inner)?;
                Some((atom, !negated))
            }
            _ => None,
        }
    }

    fn assertions_are_simple_int_bounds_sat(&self) -> Option<bool> {
        let assertions = self.solver.assertions();
        if assertions.is_empty() {
            return None;
        }

        let mut bounds: HashMap<Term, (Option<i64>, Option<i64>)> = HashMap::new();
        let mut saw_supported_assertion = false;

        for assertion in assertions {
            if self.term_is_obviously_true(assertion) {
                saw_supported_assertion = true;
                continue;
            }
            if self.term_is_obviously_false(assertion) {
                return Some(false);
            }

            let constraints = self.simple_int_bound_constraints(assertion)?;
            saw_supported_assertion = true;
            for constraint in constraints {
                let (atom, is_lower, value) = match constraint {
                    IntBoundConstraint::Lower { atom, value } => (atom, true, value),
                    IntBoundConstraint::Upper { atom, value } => (atom, false, value),
                };
                let entry = bounds.entry(atom).or_insert((None, None));
                if is_lower {
                    entry.0 = Some(entry.0.map_or(value, |existing| existing.max(value)));
                } else {
                    entry.1 = Some(entry.1.map_or(value, |existing| existing.min(value)));
                }
                if entry
                    .0
                    .zip(entry.1)
                    .is_some_and(|(lower, upper)| lower > upper)
                {
                    return Some(false);
                }
            }
        }

        saw_supported_assertion.then_some(true)
    }

    fn simple_int_bound_constraints(&self, term: Term) -> Option<Vec<IntBoundConstraint>> {
        if self.term_is_obviously_true(term) {
            return Some(Vec::new());
        }
        if self.term_is_obviously_false(term) {
            return Some(vec![
                IntBoundConstraint::Lower {
                    atom: term,
                    value: 1,
                },
                IntBoundConstraint::Upper {
                    atom: term,
                    value: 0,
                },
            ]);
        }

        match self.solver.term_kind(term) {
            TermKind::Not => {
                let children = self.solver.term_children(term);
                let [inner] = children.as_slice() else {
                    return None;
                };
                self.simple_int_bound_from_polarity(*inner, false)
                    .map(|constraint| vec![constraint])
            }
            TermKind::App {
                ref name,
                num_args: 2,
            } if name == "=>" => {
                let children = self.solver.term_children(term);
                let [antecedent, consequent] = children.as_slice() else {
                    return None;
                };
                if self.term_is_obviously_false(*antecedent)
                    || self.term_is_obviously_true(*consequent)
                {
                    return Some(Vec::new());
                }
                if self.term_is_obviously_true(*antecedent) {
                    return self.simple_int_bound_constraints(*consequent);
                }
                if self.term_is_obviously_false(*consequent) {
                    return self
                        .simple_int_bound_from_polarity(*antecedent, false)
                        .map(|constraint| vec![constraint]);
                }
                None
            }
            _ => self
                .simple_int_bound_from_polarity(term, true)
                .map(|constraint| vec![constraint]),
        }
    }

    fn simple_int_bound_from_polarity(
        &self,
        term: Term,
        positive: bool,
    ) -> Option<IntBoundConstraint> {
        match self.solver.term_kind(term) {
            TermKind::Not => {
                let children = self.solver.term_children(term);
                let [inner] = children.as_slice() else {
                    return None;
                };
                self.simple_int_bound_from_polarity(*inner, !positive)
            }
            TermKind::App {
                ref name,
                num_args: 2,
            } if matches!(name.as_str(), "<" | "<=" | ">" | ">=") => {
                let op = Self::comparison_name_for_polarity(name, positive)?;
                self.simple_int_comparison_bound(term, op)
            }
            _ => None,
        }
    }

    fn comparison_name_for_polarity(name: &str, positive: bool) -> Option<&'static str> {
        match (name, positive) {
            ("<", true) | (">=", false) => Some("<"),
            ("<=", true) | (">", false) => Some("<="),
            (">", true) | ("<=", false) => Some(">"),
            (">=", true) | ("<", false) => Some(">="),
            _ => None,
        }
    }

    fn flipped_comparison_name(name: &str) -> Option<&'static str> {
        match name {
            "<" => Some(">"),
            "<=" => Some(">="),
            ">" => Some("<"),
            ">=" => Some("<="),
            _ => None,
        }
    }

    fn simple_int_comparison_bound(
        &self,
        term: Term,
        op: &'static str,
    ) -> Option<IntBoundConstraint> {
        let children = self.solver.term_children(term);
        let [lhs, rhs] = children.as_slice() else {
            return None;
        };
        let lhs = self.term_int_affine_atom(*lhs)?;
        let rhs = self.term_int_affine_atom(*rhs)?;
        match (lhs.atom, rhs.atom) {
            (Some(atom), None) => {
                let value = rhs.offset.checked_sub(lhs.offset)?;
                Self::simple_int_bound_for_atom_comparison(atom, op, value)
            }
            (None, Some(atom)) => {
                let value = lhs.offset.checked_sub(rhs.offset)?;
                let flipped = Self::flipped_comparison_name(op)?;
                Self::simple_int_bound_for_atom_comparison(atom, flipped, value)
            }
            _ => None,
        }
    }

    fn simple_int_bound_for_atom_comparison(
        atom: Term,
        op: &str,
        value: i64,
    ) -> Option<IntBoundConstraint> {
        match op {
            ">" => Some(IntBoundConstraint::Lower {
                atom,
                value: value.checked_add(1)?,
            }),
            ">=" => Some(IntBoundConstraint::Lower { atom, value }),
            "<" => Some(IntBoundConstraint::Upper {
                atom,
                value: value.checked_sub(1)?,
            }),
            "<=" => Some(IntBoundConstraint::Upper { atom, value }),
            _ => None,
        }
    }

    fn assertions_are_ground_int_equalities_sat(&self) -> bool {
        let assertions = self.solver.assertions();
        if assertions.is_empty() {
            return false;
        }

        let mut equalities = Vec::new();
        let mut disequalities = Vec::new();
        let mut equality_atoms = HashSet::new();
        let mut app_atom_subterms = HashSet::new();
        let mut saw_constraint = false;

        for assertion in assertions {
            if self.term_is_obviously_true(assertion) {
                continue;
            }
            if self.term_is_obviously_false(assertion) {
                return false;
            }

            if let Some((lhs, rhs)) = self.term_equality(assertion) {
                let Some(lhs) = self.term_int_affine_atom(lhs) else {
                    return false;
                };
                let Some(rhs) = self.term_int_affine_atom(rhs) else {
                    return false;
                };
                self.record_int_affine_atoms(lhs, &mut equality_atoms, &mut app_atom_subterms);
                self.record_int_affine_atoms(rhs, &mut equality_atoms, &mut app_atom_subterms);
                equalities.push((lhs, rhs));
                saw_constraint = true;
                continue;
            }

            if let Some((lhs, rhs)) = self.term_disequality(assertion) {
                let Some(lhs) = self.term_int_affine_atom(lhs) else {
                    return false;
                };
                let Some(rhs) = self.term_int_affine_atom(rhs) else {
                    return false;
                };
                self.record_int_affine_atoms(lhs, &mut HashSet::new(), &mut app_atom_subterms);
                self.record_int_affine_atoms(rhs, &mut HashSet::new(), &mut app_atom_subterms);
                disequalities.push((lhs, rhs));
                saw_constraint = true;
                continue;
            }

            return false;
        }

        if !saw_constraint {
            return false;
        }

        // If an uninterpreted application is applied to a term constrained by
        // an equality, congruence can make a syntactically independent
        // disequality UNSAT (for example x = y and f(x) != f(y)). In that case,
        // leave the query to ay instead of taking this SAT shortcut.
        if app_atom_subterms
            .iter()
            .any(|subterm| equality_atoms.contains(subterm))
        {
            return false;
        }

        let mut union_find = IntOffsetUnionFind::default();
        for (lhs, rhs) in equalities {
            if !Self::assert_int_affine_equality(&mut union_find, lhs, rhs) {
                return false;
            }
        }

        let mut disequality_roots = HashSet::new();
        for (lhs, rhs) in &disequalities {
            if let Some(atom) = lhs.atom {
                let (root, _) = union_find.find_term(atom);
                disequality_roots.insert(root);
            }
            if let Some(atom) = rhs.atom {
                let (root, _) = union_find.find_term(atom);
                disequality_roots.insert(root);
            }
        }
        let indexed_atoms: Vec<Term> = union_find.indices.keys().copied().collect();
        for atom in indexed_atoms {
            let (root, _) = union_find.find_term(atom);
            if disequality_roots.contains(&root)
                && matches!(self.solver.term_kind(atom), TermKind::App { .. })
            {
                return false;
            }
        }

        !disequalities
            .into_iter()
            .any(|(lhs, rhs)| union_find.affines_forced_equal(lhs, rhs))
    }

    fn record_int_affine_atoms(
        &self,
        affine: IntAffineAtom,
        equality_atoms: &mut HashSet<Term>,
        app_atom_subterms: &mut HashSet<Term>,
    ) {
        let Some(atom) = affine.atom else {
            return;
        };
        equality_atoms.insert(atom);
        if matches!(self.solver.term_kind(atom), TermKind::App { .. }) {
            for child in self.solver.term_children(atom) {
                self.collect_term_subterms(child, app_atom_subterms);
            }
        }
    }

    fn collect_term_subterms(&self, term: Term, out: &mut HashSet<Term>) {
        if !out.insert(term) {
            return;
        }
        for child in self.solver.term_children(term) {
            self.collect_term_subterms(child, out);
        }
    }

    fn assert_int_affine_equality(
        union_find: &mut IntOffsetUnionFind,
        lhs: IntAffineAtom,
        rhs: IntAffineAtom,
    ) -> bool {
        match (lhs.atom, rhs.atom) {
            (None, None) => lhs.offset == rhs.offset,
            (Some(atom), None) => union_find.set_constant(atom, rhs.offset - lhs.offset),
            (None, Some(atom)) => union_find.set_constant(atom, lhs.offset - rhs.offset),
            (Some(lhs_atom), Some(rhs_atom)) => {
                union_find.union_difference(lhs_atom, rhs_atom, rhs.offset - lhs.offset)
            }
        }
    }

    fn assertions_imply_negated_int_equality_conflict(&self) -> bool {
        let assertions = self.solver.assertions();
        let mut known_values: HashMap<Term, i64> = HashMap::new();
        let mut affine_equalities: Vec<(Term, Term, i64)> = Vec::new();
        let mut disequalities: Vec<(Term, i64)> = Vec::new();

        for assertion in assertions {
            if let Some((lhs, rhs)) = self.term_equality(assertion) {
                if let Some(value) = self.term_int_const(rhs) {
                    known_values.insert(lhs, value);
                } else if let Some(value) = self.term_int_const(lhs) {
                    known_values.insert(rhs, value);
                } else if let Some((base, offset)) = self.term_add_int_offset(rhs) {
                    affine_equalities.push((lhs, base, offset));
                } else if let Some((base, offset)) = self.term_add_int_offset(lhs) {
                    affine_equalities.push((rhs, base, offset));
                }
                continue;
            }

            if !matches!(self.solver.term_kind(assertion), TermKind::Not) {
                continue;
            }
            let children = self.solver.term_children(assertion);
            let [inner] = children.as_slice() else {
                continue;
            };
            let Some((lhs, rhs)) = self.term_equality(*inner) else {
                continue;
            };
            if let Some(value) = self.term_int_const(rhs) {
                disequalities.push((lhs, value));
            } else if let Some(value) = self.term_int_const(lhs) {
                disequalities.push((rhs, value));
            }
        }

        for _ in 0..affine_equalities.len() {
            let mut changed = false;
            for (target, base, offset) in &affine_equalities {
                if known_values.contains_key(target) {
                    continue;
                }
                let Some(base_value) = known_values.get(base).copied() else {
                    continue;
                };
                let Some(value) = base_value.checked_add(*offset) else {
                    continue;
                };
                known_values.insert(*target, value);
                changed = true;
            }
            if !changed {
                break;
            }
        }

        disequalities.into_iter().any(|(term, forbidden)| {
            known_values
                .get(&term)
                .is_some_and(|value| *value == forbidden)
        })
    }

    fn assertions_force_quantified_disjoint_overlap(&self) -> bool {
        if !self.assertion_pipeline.has_active_disjoint_constraints() {
            return false;
        }

        let mut union_find = IntOffsetUnionFind::default();
        let assertions = self.solver.assertions();
        let mut saw_equality = false;
        for assertion in assertions {
            let mut conjuncts = Vec::new();
            self.collect_assertion_conjuncts(assertion, &mut conjuncts);
            for conjunct in conjuncts {
                let Some((lhs, rhs)) = self.term_equality(conjunct) else {
                    continue;
                };
                let Some(lhs) = self.term_int_affine_atom(lhs) else {
                    continue;
                };
                let Some(rhs) = self.term_int_affine_atom(rhs) else {
                    continue;
                };
                saw_equality = true;
                if !Self::assert_int_affine_equality(&mut union_find, lhs, rhs) {
                    return true;
                }
            }
        }

        if !saw_equality {
            return false;
        }

        self.assertion_pipeline
            .active_disjoint_constraints()
            .iter()
            .any(|(left_terms, right_terms)| {
                left_terms.iter().any(|&left| {
                    let Some(left) = self.term_int_affine_atom(left) else {
                        return false;
                    };
                    right_terms.iter().any(|&right| {
                        let Some(right) = self.term_int_affine_atom(right) else {
                            return false;
                        };
                        union_find.affines_forced_equal(left, right)
                    })
                })
            })
    }

    fn term_equality(&self, term: Term) -> Option<(Term, Term)> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "=" {
            return None;
        }
        let children = self.solver.term_children(term);
        let [lhs, rhs] = children.as_slice() else {
            return None;
        };
        Some((*lhs, *rhs))
    }

    fn term_disequality(&self, term: Term) -> Option<(Term, Term)> {
        if matches!(self.solver.term_kind(term), TermKind::Not) {
            let children = self.solver.term_children(term);
            let [inner] = children.as_slice() else {
                return None;
            };
            return self.term_equality(*inner);
        }

        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "distinct" && name != "!=" {
            return None;
        }
        let children = self.solver.term_children(term);
        let [lhs, rhs] = children.as_slice() else {
            return None;
        };
        Some((*lhs, *rhs))
    }

    fn term_int_affine_atom(&self, term: Term) -> Option<IntAffineAtom> {
        if self.solver.get_sort(term) != Sort::Int {
            return None;
        }
        if let Some(value) = self.term_int_const(term) {
            return Some(IntAffineAtom {
                atom: None,
                offset: value,
            });
        }

        match self.solver.term_kind(term) {
            TermKind::App { name, num_args: 2 } if name == "+" => {
                let children = self.solver.term_children(term);
                let [lhs, rhs] = children.as_slice() else {
                    return None;
                };
                if let Some(offset) = self.term_int_const(*rhs) {
                    let mut base = self.term_int_affine_atom(*lhs)?;
                    base.offset = base.offset.checked_add(offset)?;
                    return Some(base);
                }
                if let Some(offset) = self.term_int_const(*lhs) {
                    let mut base = self.term_int_affine_atom(*rhs)?;
                    base.offset = base.offset.checked_add(offset)?;
                    return Some(base);
                }
                None
            }
            TermKind::App { name, num_args: 2 } if name == "-" => {
                let children = self.solver.term_children(term);
                let [lhs, rhs] = children.as_slice() else {
                    return None;
                };
                let offset = self.term_int_const(*rhs)?;
                let mut base = self.term_int_affine_atom(*lhs)?;
                base.offset = base.offset.checked_sub(offset)?;
                Some(base)
            }
            _ => Some(IntAffineAtom {
                atom: Some(term),
                offset: 0,
            }),
        }
    }

    fn term_add_int_offset(&self, term: Term) -> Option<(Term, i64)> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "+" {
            return None;
        }
        let children = self.solver.term_children(term);
        let [lhs, rhs] = children.as_slice() else {
            return None;
        };
        if let Some(offset) = self.term_int_const(*rhs) {
            Some((*lhs, offset))
        } else {
            self.term_int_const(*lhs).map(|offset| (*rhs, offset))
        }
    }

    fn term_int_const(&self, term: Term) -> Option<i64> {
        if !matches!(self.solver.term_kind(term), TermKind::Const) {
            return None;
        }
        let formatted = self.solver.format_term(term);
        parse_formatted_int_literal(&formatted)?.try_into().ok()
    }

    fn term_i64_literal(&self, term: Term) -> Option<i64> {
        self.term_int_literal(term)?.try_into().ok()
    }

    /// Read accessor for the cached statistics from the last `check_sat()` call.
    /// Returns `None` if no solve has been performed or if the solver panicked. (#2639)
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn last_solve_statistics(
        &self,
    ) -> Option<&crate::shared_types::SolveStatisticsSnapshot> {
        self.encoding_cache.solve_statistics()
    }

    /// Read accessor for the cached solve evidence from the last
    /// `check_sat_with_details()` call. Returns `None` if no solve has been
    /// performed or if the solver panicked before details were captured.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn last_solve_evidence(
        &self,
    ) -> Option<&crate::shared_types::SolveEvidenceSnapshot> {
        self.encoding_cache.solve_evidence()
    }

    /// Read accessor for the cached typed unknown reason from the last
    /// `check_sat()` call. Returns `None` when the result was SAT/UNSAT or
    /// when the solver didn't provide a reason. (#2639)
    pub(crate) fn last_unknown_reason(&self) -> Option<&crate::shared_types::UnknownReason> {
        self.encoding_cache.solve_unknown_reason()
    }

    /// Read accessor for the cached executor error from the last `check_sat()`
    /// call. Returns `None` when no executor error was recorded. (#2639)
    pub(crate) fn last_executor_error(&self) -> Option<&str> {
        self.encoding_cache.solve_executor_error()
    }

    /// Read accessor for the cached native replay JSON from the last solve.
    ///
    /// The replay is a diagnostic artifact for the active assertion window.
    /// Verification code uses it only in sound contexts where a fresh replay's
    /// validated result has the same meaning as the original check.
    pub(crate) fn native_replay_json(&self) -> Option<&str> {
        self.encoding_cache.native_replay_json()
    }

    /// Exact native problem serialized by the strict replay that produced the
    /// cached proof authority, provided the live assertion stack and active
    /// proof-assert claim metadata are still byte-identical.
    pub(crate) fn strict_proof_native_replay_json(&self) -> Option<&str> {
        let cached = self.encoding_cache.strict_proof_native_replay_json()?;
        let cached_artifact = ay_dpll::api::NativeReplayArtifact::from_json_str(cached).ok()?;
        let metadata = Self::strict_native_replay_metadata()?;
        if cached_artifact.metadata != metadata {
            return None;
        }
        let mut current = self.solver.export_native_replay_artifact(metadata, None);
        if current.replay_gaps.as_slice() != ["solve details were not captured"]
            || !current.unsupported_atoms.is_empty()
        {
            return None;
        }
        current.replay_gaps.clear();
        current.created_unix_ms = cached_artifact.created_unix_ms;
        current.timeout_ms = cached_artifact.timeout_ms;
        (current.to_pretty_json() == cached).then_some(cached)
    }

    /// Clear every solve diagnostic before a proof-assert slice begins.
    pub(crate) fn clear_last_solve_diagnostics(&mut self) {
        self.encoding_cache.clear_solve_diagnostics();
    }

    /// Re-export the CURRENT assertion stack as the cached native replay
    /// artifact (no solve details).
    ///
    /// Used by the base vacuity recheck to snapshot the popped base stack so a
    /// fresh non-incremental solver can re-solve it with model validation
    /// BEFORE the incremental recheck gets a chance to churn past its
    /// hard-timeout envelope. The cached replay is refreshed by every
    /// `check_sat()` anyway, so overwriting it here follows the existing
    /// lifecycle.
    pub(crate) fn refresh_native_replay_json(&mut self) {
        self.cache_native_replay_json(None);
    }

    pub(crate) fn fail_closed_solver_context(&self) -> Option<&str> {
        self.encoding_cache.fail_closed_solver_context()
    }

    /// Capture a [`VerificationProvenance`] snapshot from the current encoder
    /// and solver state.
    ///
    /// `solve_time` is the wall-clock duration of the solve phase (measured
    /// externally by the verification pipeline). The remaining fields are
    /// read from the solver's cached statistics and configuration. (#2729)
    pub(crate) fn capture_provenance(
        &mut self,
        solve_time: std::time::Duration,
    ) -> crate::shared_types::VerificationProvenance {
        // Taken FIRST: the mutable borrow must end before the immutable reads
        // below begin. Diagnostics only — carried alongside the
        // evidence/statistics pair, never in place of it, so nothing on the
        // acceptance path can see it. (#strict-replay-observation-survival)
        //
        // BOUND, not merely taken: an observation stamped with a different
        // obligation/slice scope measured a different query and is refused here.
        // See `EncodingCacheState::take_strict_proof_replay_observation_bound_to`.
        let scope = self.encoding_cache.strict_replay_scope();
        let strict_proof_replay = self
            .encoding_cache
            .take_strict_proof_replay_observation_bound_to(scope);
        let strict_proof_replay_unbound = self.encoding_cache.strict_replay_unbound();
        let stats = self.encoding_cache.solve_statistics().cloned();
        let mut evidence = self.encoding_cache.solve_evidence().cloned();
        let structural_details = self.encoding_cache.structural_ground_consequence_details();
        if !structural_details.is_empty() {
            if let Some(evidence) = evidence.as_mut() {
                evidence.accepted_for_consumer = false;
                evidence.consumer_rejection = Some(format!(
                    "solver result used trust-wp structural ground consequence(s): {}",
                    structural_details.join(",")
                ));
            }
        }
        let unknown_reason = self.encoding_cache.solve_unknown_reason().cloned();
        let executor_error = self
            .encoding_cache
            .solve_executor_error()
            .map(ToOwned::to_owned);
        let assertion_count = stats.as_ref().map_or(0, |s| s.num_assertions);
        crate::shared_types::VerificationProvenance::with_solve_time(solve_time)
            .with_assertion_count(assertion_count)
            .with_solver_timeout(self.solver.timeout())
            .with_solver_statistics(stats)
            .with_solve_evidence(evidence)
            .with_unknown_reason(unknown_reason)
            .with_executor_error(executor_error)
            .with_replay_artifact(self.replay_artifact_text())
            .with_native_replay_json(
                self.encoding_cache
                    .native_replay_json()
                    .map(ToOwned::to_owned),
            )
            // Diagnostics only. Carried ALONGSIDE the pair above, never in place
            // of it: on the certification-blocked lane the pair holds the
            // incremental encoder's `set_produce_proofs(false)` constants, and
            // this holds what the strict replay actually measured.
            .with_strict_proof_replay(strict_proof_replay)
            .with_strict_proof_replay_unbound(strict_proof_replay_unbound)
    }

    /// Open a new obligation batch for strict-replay observation binding.
    ///
    /// See `EncodingCacheState::begin_obligation`.
    pub(crate) fn begin_strict_replay_obligation(&mut self) {
        self.encoding_cache.begin_obligation();
    }

    /// Open the next obligation slice for strict-replay observation binding.
    ///
    /// See `EncodingCacheState::begin_obligation_slice`.
    pub(crate) fn begin_strict_replay_obligation_slice(&mut self) {
        self.encoding_cache.begin_obligation_slice();
    }

    /// Get counterexample model (if SAT).
    ///
    /// If the underlying ay solver panics while fetching the model, the panic
    /// is caught, the reason is recorded, and `None` is returned.
    fn get_model_with_fetch<F>(&mut self, fetch_model: F) -> Option<Model>
    where
        F: FnOnce(&Solver) -> Option<Model>,
    {
        match catch_solver_panic_with_reason("get_model", || fetch_model(&self.solver)) {
            Ok(model) => model,
            Err(err) => {
                self.assertion_pipeline
                    .record_solver_panic(err.into_reason());
                None
            }
        }
    }

    fn last_solve_was_no_model_seq_decomposition_shortcut(&self) -> bool {
        self.encoding_cache
            .solve_evidence()
            .is_some_and(|evidence| {
                evidence.result == "sat"
                    && !evidence.model_validated
                    && evidence
                        .consumer_rejection
                        .as_deref()
                        .is_some_and(|reason| {
                            reason.contains("shortcut:isolated-negated-seq-decomposition-sat")
                        })
            })
    }

    pub(crate) fn get_model(&mut self) -> Option<Model> {
        let model =
            self.get_model_with_fetch(|s| s.model().map(ay_dpll::VerifiedModel::into_inner));
        if model.is_some() {
            return model;
        }

        if self.last_solve_was_no_model_seq_decomposition_shortcut() {
            return None;
        }

        // SAT shortcuts return before ay records a solver-level SAT result,
        // so a subsequent get-model request has no model to read. When a
        // counterexample is actually needed, run the underlying solver once to
        // materialize the model without disabling the shortcut for proof-only
        // callers.
        match catch_solver_panic_with_reason("get_model/check_sat_for_shortcut_sat", || {
            self.solver.check_sat()
        }) {
            Ok(result) if result.is_sat() => {
                self.get_model_with_fetch(|s| s.model().map(ay_dpll::VerifiedModel::into_inner))
            }
            Ok(_) => None,
            Err(err) => {
                self.assertion_pipeline
                    .record_solver_panic(err.into_reason());
                None
            }
        }
    }

    /// Assert a term with panic isolation but without revision tracking or
    /// pending-assertion flush.
    ///
    /// Use this instead of `self.solver.assert_term(term)` in encoding paths
    /// where ay sort-mismatch panics are possible. Returns `false` and stores
    /// the panic reason in `solver_panic_reason` on failure, so subsequent
    /// `check_sat` calls return `Unknown` instead of continuing with a
    /// corrupted solver state. (#1806)
    /// Whether an `assert_solver_term` operation tag identifies one of the
    /// encoder's own enum-payload / UF-constructor bridge axiom emitters
    /// (#result_own). Combined with a `Forall` term-kind check at the call site,
    /// this precisely selects the conservative definitional bridge UNIVERSALS
    /// (never a user-authored precondition forall, which never carries an
    /// internal bridge tag). Tags that also emit ground (non-forall) facts are
    /// included here harmlessly — the caller's `Forall` gate filters them out.
    fn is_enum_payload_bridge_forall_op(operation: &str) -> bool {
        operation.starts_with("datatype_enum_payload/")
            || operation.starts_with("uf_ctor_tester_axiom")
            || operation.starts_with("uf_ctor_selector_axiom")
    }

    pub(super) fn assert_solver_term(&mut self, operation: &str, term: Term) -> bool {
        let term_text = format!("{term:?}");
        // #result_own: record the enum-payload / UF-ctor bridge UNIVERSALS by
        // identity so the SAT-side vacuity base recheck can exempt exactly these
        // conservative definitional axioms (see `enum_payload_bridge_forall_terms`).
        let record_bridge_forall = Self::is_enum_payload_bridge_forall_op(operation)
            && matches!(self.solver.term_kind(term), ay_dpll::api::TermKind::Forall);
        // Named production assertions participate in the unsat-core vacuity
        // guard. Fail closed on `try_assert_named` errors instead of silently
        // dropping back to unnamed assertions. (#2414)
        if let Some(label) = self.assertion_pipeline.next_named_assertion_label() {
            match self.solver.try_assert_named(term, &label) {
                Ok(()) => {
                    if record_bridge_forall {
                        self.enum_payload_bridge_forall_terms.push(term);
                    }
                    self.replay_recorder.record_assert(label, term_text);
                    return true;
                }
                Err(err) => {
                    self.assertion_pipeline
                        .record_solver_panic(format!("{operation}: {err}"));
                    return false;
                }
            }
        }

        match catch_solver_panic_with_reason(operation, || {
            self.solver.assert_term(term);
            true
        }) {
            Ok(asserted) => {
                if asserted {
                    if record_bridge_forall {
                        self.enum_payload_bridge_forall_terms.push(term);
                    }
                    self.replay_recorder.record_assert(operation, term_text);
                }
                asserted
            }
            Err(err) => {
                self.assertion_pipeline
                    .record_solver_panic(err.into_reason());
                false
            }
        }
    }

    fn retry_check_sat_without_proofs(&mut self) -> Option<SolveResult> {
        // ay-dpll can currently panic after a real UNSAT result when a DT
        // shortcut proves the formula without populating `last_proof`. Retry
        // once with proof tracking disabled so callers retain a diagnostic
        // SAT/UNSAT answer; an uncertified UNSAT cannot cross the mandatory
        // public proof-authority boundary.
        self.replay_recorder.record_result_with_detail(
            ReplayResultStatus::Unknown,
            "retrying_without_proofs_after_proof_related_result",
        );
        self.solver.set_produce_proofs(false);
        let result = catch_solver_panic_with_reason("check_sat/retry_without_proofs", || {
            self.check_sat_with_quantified_disjoint_recheck()
        });
        self.solver.set_produce_proofs(true);

        match result {
            Ok(solve_result) => {
                self.drop_stale_unknown_diagnostics_after_definitive_retry(&solve_result);
                Some(solve_result)
            }
            Err(err) => {
                self.assertion_pipeline
                    .record_solver_panic(err.into_reason());
                None
            }
        }
    }

    fn drop_stale_unknown_diagnostics_after_definitive_retry(&mut self, result: &SolveResult) {
        if matches!(result, SolveResult::Unknown) {
            return;
        }

        let stats = self.encoding_cache.solve_statistics().cloned();
        let evidence = self.encoding_cache.solve_evidence().cloned();
        let native_replay_json = self
            .encoding_cache
            .native_replay_json()
            .map(ToOwned::to_owned);

        self.encoding_cache.clear_solve_diagnostics();
        if let Some(stats) = stats {
            self.encoding_cache.set_solve_statistics(stats);
        }
        if let Some(evidence) = evidence {
            self.encoding_cache.set_solve_evidence(evidence);
        }
        if let Some(native_replay_json) = native_replay_json {
            self.encoding_cache
                .set_native_replay_json(native_replay_json);
        }
    }

    /// Check whether the last UNSAT result was vacuous.
    ///
    /// Returns `true` (vacuous) when the unsat core does not contain the
    /// negated-goal assertion label, meaning the base assertions were
    /// contradictory without the negated postcondition. (#2414)
    ///
    /// Returns `Ok(false)` when:
    /// - The negated goal IS in the core (genuine proof)
    /// - No negated-goal label was set (legacy path, assume non-vacuous)
    ///
    /// Returns `Err` when unsat-core retrieval itself fails so callers can
    /// fail closed to `Unknown`. (#903, #2414)
    pub(crate) fn is_vacuous_unsat(&mut self) -> Result<bool, crate::error::VacuityCheckError> {
        let goal_label_prefix = match self.assertion_pipeline.negated_goal_label_prefix() {
            Some(label) => label.to_string(),
            None => return Ok(false), // No label → legacy path, not vacuous
        };

        let core = self.solver.try_get_unsat_core().map_err(|err| {
            crate::error::VacuityCheckError::UnsatCoreRetrieval {
                message: err.to_string(),
            }
        })?;

        // The proof is vacuous if the negated-goal label is NOT in the core.
        let goal_in_core = core.iter().any(|name| {
            *name == goal_label_prefix
                || name
                    .strip_prefix(&goal_label_prefix)
                    .is_some_and(|suffix| suffix.starts_with('_'))
        });
        if !goal_in_core {
            tracing::info!(
                goal_label_prefix,
                core_size = core.len(),
                "vacuous proof detected: negated goal not in unsat core"
            );
        }
        Ok(!goal_in_core)
    }

    /// Get access to the underlying solver (for advanced use)
    pub(crate) fn solver(&self) -> &Solver {
        &self.solver
    }

    /// Get mutable access to the underlying solver (for advanced use)
    pub(crate) fn solver_mut(&mut self) -> &mut Solver {
        &mut self.solver
    }

    /// Push a new incremental solver scope.
    ///
    /// Wrapper around `Solver::try_push()` that converts the error to
    /// [`EncodingError`]. See [`AYEncoder`] struct doc for push/pop policy.
    pub(crate) fn push_scope(&mut self) -> Result<(), crate::error::EncodingError> {
        self.solver
            .try_push()
            .map_err(|e| crate::error::EncodingError::solver_error(e.to_string()))?;
        self.replay_recorder.record_push("scope");
        Ok(())
    }

    /// Pop the most recent incremental solver scope.
    ///
    /// Wrapper around `Solver::try_pop()` that converts the error to
    /// [`EncodingError`]. See [`AYEncoder`] struct doc for push/pop policy.
    ///
    /// After popping, any datatype declarations that were made inside the
    /// popped scope are removed from ay's context (ay tracks datatype
    /// declarations per scope frame). Re-declare all registered datatypes
    /// to keep ay in sync with trust-wp's registry. (#list_index_mut crash)
    pub(crate) fn pop_scope(&mut self) -> Result<(), crate::error::EncodingError> {
        self.solver
            .try_pop()
            .map_err(|e| crate::error::EncodingError::solver_error(e.to_string()))?;
        self.replay_recorder.record_pop(1);

        // Re-declare all registered datatypes to ay after pop.
        // ay's push/pop removes scoped datatype declarations on pop, but
        // trust-wp's internal registry survives. Without re-declaration, any
        // code that looks up a datatype in trust-wp's registry and then calls
        // solver.datatype_constructor() would panic because ay no longer
        // recognizes the datatype name.
        let registered: Vec<ay_dpll::api::DatatypeSort> =
            self.decls.datatypes_iter().cloned().collect();
        for dt in &registered {
            let _ = self.solver.try_declare_datatype(dt);
        }

        Ok(())
    }

    pub(crate) fn replay_artifact_text(&self) -> Option<String> {
        let artifact = self.replay_recorder.artifact();
        if artifact.is_empty() {
            return None;
        }
        Some(artifact.to_stable_text())
    }

    pub(crate) fn option_bridge_datatype(&self, sort: &Sort) -> Option<ay_dpll::api::DatatypeSort> {
        match sort {
            Sort::Datatype(dt) if dt.name == "OptionInt" => Some(dt.clone()),
            Sort::Uninterpreted(name) if name == "OptionInt" => {
                self.get_datatype_decl(name).cloned()
            }
            _ => None,
        }
    }

    fn bridge_legacy_option_term_to_native_sort(
        &mut self,
        legacy_term: Term,
        target_sort: &Sort,
    ) -> Option<Term> {
        static OPTION_BRIDGE_COUNTER: AtomicU64 = AtomicU64::new(0);

        let datatype = self.option_bridge_datatype(target_sort)?;
        let has_some = datatype.constructors.iter().any(|ctor| ctor.name == "Some");
        let has_none = datatype
            .constructors
            .iter()
            .any(|ctor| ctor.name == "None" && ctor.fields.is_empty());
        if !has_some || !has_none {
            return None;
        }
        let target_key = sort_display_key(target_sort);
        if let Some(cached) = self
            .encoding_cache
            .option_bridge_term(legacy_term, &target_key)
        {
            return Some(cached);
        }

        let is_some_decl = self.get_or_declare_constructor_tester_for_sort("is_some", &Sort::Int);
        let unwrap_decl =
            self.get_or_declare_accessor_for_sorts("spec_unwrap", &Sort::Int, &Sort::Int);
        // The bridge relies on the legacy Option axioms to relate
        // `is_some/spec_unwrap/is_option` to the Int-carrier constructor lane.
        self.assert_option_result_axioms();
        let is_option_decl =
            self.get_or_declare_spec_func("__trust_wp_is_option", &[Sort::Int], Sort::Bool);

        let is_some = self
            .safe_apply("bridge_option/is_some", &is_some_decl, &[legacy_term])
            .ok()?;
        let unwrap = self
            .safe_apply("bridge_option/spec_unwrap", &unwrap_decl, &[legacy_term])
            .ok()?;
        let is_option = self
            .safe_apply("bridge_option/is_option", &is_option_decl, &[legacy_term])
            .ok()?;

        let some =
            self.axiom_datatype_constructor("bridge_option/some", &datatype, "Some", &[unwrap])?;
        let none = self.axiom_datatype_constructor("bridge_option/none", &datatype, "None", &[])?;
        let some_or_none = self.solver.ite(is_some, some, none);
        let bridge_sort = self.solver.get_sort(some_or_none);
        let fallback = self.solver.declare_const(
            &format!(
                "__trust_wp_option_bridge_{}",
                OPTION_BRIDGE_COUNTER.fetch_add(1, Ordering::Relaxed)
            ),
            bridge_sort,
        );
        let bridge_term = self.solver.ite(is_option, some_or_none, fallback);
        self.encoding_cache
            .insert_option_bridge_term(legacy_term, target_key, bridge_term);
        Some(bridge_term)
    }

    pub(crate) fn harmonize_eq_or_ite_terms(&mut self, a: Term, b: Term) -> (Term, Term) {
        let a_sort = self.solver.get_sort(a);
        let b_sort = self.solver.get_sort(b);

        if a_sort == b_sort || a_sort.as_term_sort() == b_sort.as_term_sort() {
            return (a, b);
        }

        if a_sort == Sort::Int {
            if let Some(a_native) = self.bridge_legacy_option_term_to_native_sort(a, &b_sort) {
                return (a_native, b);
            }
        }
        if b_sort == Sort::Int {
            if let Some(b_native) = self.bridge_legacy_option_term_to_native_sort(b, &a_sort) {
                return (a, b_native);
            }
        }

        // Seq element restoration: when one side is Int (from the Seq element
        // bridge that maps non-Int elements to Int for Seq operations) and the
        // other side has a structural sort (Datatype, Uninterpreted), try to
        // restore the bridged element to its original sort. This recovers the
        // semantics of `v[i] == some_adt_value` where v[i] was bridged to Int
        // by `coerce_seq_element_to_int` but should compare at the ADT's sort.
        // Without this, the equality falls through to `coerce_ite_sorts` which
        // creates a fresh unconstrained constant, discarding the element value
        // and making the equality trivially unprovable. (#2699)
        if a_sort == Sort::Int && is_structural_non_int(&b_sort) {
            if let Some(a_restored) = self.try_restore_seq_element_from_int(a, &b_sort) {
                return (a_restored, b);
            }
        }
        if b_sort == Sort::Int && is_structural_non_int(&a_sort) {
            if let Some(b_restored) = self.try_restore_seq_element_from_int(b, &a_sort) {
                return (a, b_restored);
            }
        }

        // Seq-family bridging: when one side is native Seq and the other is a
        // Seq-family sort (Uninterpreted("Vec"), Datatype(Vec), etc.), use the
        // structured `coerce_to_seq` bridge (with injectivity axioms) instead of
        // falling through to `coerce_ite_sorts` which creates a fresh
        // unconstrained constant that discards the value. (#2699)
        if matches!(a_sort, Sort::Seq(_))
            && super::sort_context::is_seq_family_sort(&b_sort)
            && !matches!(b_sort, Sort::Seq(_))
        {
            let b_coerced = self.coerce_to_seq(b);
            return (a, b_coerced);
        }
        if matches!(b_sort, Sort::Seq(_))
            && super::sort_context::is_seq_family_sort(&a_sort)
            && !matches!(a_sort, Sort::Seq(_))
        {
            let a_coerced = self.coerce_to_seq(a);
            return (a_coerced, b);
        }

        // Seq-iterator carrier bridging: `SeqIter`/`IntoIter` vs the canonical
        // Seq sort (native OR the uninterpreted Seq carrier — the latter is
        // what the mixed-datatype configuration uses, which the native-Seq
        // arms above cannot match). A SeqIter is a single-field wrapper whose
        // state IS its underlying sequence, so bridging through
        // `coerce_to_seq`'s injective `__vec_to_seq_*` UF (with its #2116
        // View-anchor congruence) is faithful. Without this arm the pair falls
        // through to `coerce_ite_sorts`, which mints a fresh unconstrained
        // constant that discards the iterator value — the fabricated-premise
        // shape behind ghost/seq_iter reverse_ghost loop_initialization.
        // (ce-census 2026-08-20)
        {
            let a_is_iter = super::seq::sort_is_seq_iterator_carrier(&a_sort);
            let b_is_iter = super::seq::sort_is_seq_iterator_carrier(&b_sort);
            if a_is_iter || b_is_iter {
                let seq_sort = self.get_seq_sort();
                if a_is_iter && (matches!(b_sort, Sort::Seq(_)) || b_sort == seq_sort) {
                    let a_coerced = self.coerce_to_seq(a);
                    if self.solver.get_sort(a_coerced) == b_sort {
                        return (a_coerced, b);
                    }
                }
                if b_is_iter && (matches!(a_sort, Sort::Seq(_)) || a_sort == seq_sort) {
                    let b_coerced = self.coerce_to_seq(b);
                    if self.solver.get_sort(b_coerced) == a_sort {
                        return (a, b_coerced);
                    }
                }
            }
        }

        // Same-family structural bridging: when both sides are structural sorts
        // in the same family (e.g., Datatype(Adt_Some_None) vs
        // Uninterpreted("OptionInt"), or two Datatype sorts from the same user
        // enum), use an injective UF bridge to convert the weaker sort to the
        // stronger one. This preserves the semantic value of the bridged term
        // (unlike a fresh unconstrained constant which discards it). (#2699)
        //
        // The bridge target is the sort selected by `select_structural_sort_target`,
        // which prefers native Datatype sorts and more specific names. The bridge
        // UF is injective, so `bridge(x) == bridge(y) => x == y` holds.
        if let Some(_family) = super::sort_context::same_structural_family(&a_sort, &b_sort) {
            if let Some(target) =
                super::sort_context::select_structural_sort_target(&a_sort, &b_sort)
            {
                if target == a_sort {
                    let b_bridged = self.bridge_structural_sort(b, &b_sort, &a_sort);
                    return (a, b_bridged);
                } else {
                    let a_bridged = self.bridge_structural_sort(a, &a_sort, &b_sort);
                    return (a_bridged, b);
                }
            }
        }

        coerce_ite_sorts(&mut self.solver, a, a_sort, b, b_sort)
    }

    /// Bridge a term from one structural sort to another using an injective UF.
    ///
    /// When two sorts are in the same structural family (e.g., `Datatype(Adt_Some_None)`
    /// and `Uninterpreted("OptionInt")`), this creates a UF bridge
    /// `__trust_wp_struct_bridge_<from>_to_<to>: from_sort -> to_sort` and applies it.
    /// Injectivity is enforced lazily as a set of *ground* implications
    /// `bridge(t_i) == bridge(t_j) => t_i == t_j` for every pair of distinct
    /// ground terms bridged through the same UF. This avoids arming a universal
    /// `forall x,y. bridge(x)==bridge(y) => x==y` axiom that previously
    /// interacted with the datatype-depth quantifier and produced
    /// `quantifier-ematching-exists-incomplete` for loop preservation queries
    /// (`lang/while_let.rs`).
    ///
    /// This is strictly better than the `coerce_ite_sorts` fallback which creates
    /// a fresh unconstrained constant that discards the value entirely. With a UF
    /// bridge, the solver can still reason about congruence: if `x == y`, then
    /// `bridge(x) == bridge(y)`. (#2699)
    pub(in crate::encoder) fn bridge_structural_sort(
        &mut self,
        term: Term,
        from_sort: &Sort,
        to_sort: &Sort,
    ) -> Term {
        if from_sort.as_term_sort() == to_sort.as_term_sort() {
            return term;
        }

        // Build a descriptive bridge key from sort names.
        let from_name = sort_display_key(from_sort);
        let to_name = sort_display_key(to_sort);
        let bridge_key = format!("__trust_wp_struct_bridge_{from_name}_to_{to_name}");

        // Look up or create the bridge UF via the shared logic-func registry.
        let bridge_fn = self.get_or_declare_logic_func(
            &bridge_key,
            std::slice::from_ref(from_sort),
            to_sort.clone(),
        );

        // Emit ground injectivity instances instead of a universal axiom.
        //
        // The previous forall encoding (`forall x,y. bridge(x)==bridge(y) =>
        // x==y`) interacted with the datatype-depth axiom and produced
        // `quantifier-ematching-exists-incomplete` for loop preservation
        // queries that bridge between Datatype/Uninterpreted Option sorts
        // (`lang/while_let.rs`). Asserting per-application ground instances
        // preserves the semantic injectivity required to prevent value
        // collapse without arming a new universal quantifier that the
        // E-matcher must dispatch. (#2699)
        let bridged = self.solver.apply(&bridge_fn, &[term]);

        let prior_terms = self
            .injective_bridge_ground_terms
            .get(&bridge_key)
            .cloned()
            .unwrap_or_default();
        for prev in prior_terms {
            if prev == term {
                continue;
            }
            let bridge_prev = self.solver.apply(&bridge_fn, &[prev]);
            let images_eq = self.eq_term(bridged, bridge_prev);
            let inputs_eq = self.eq_term(term, prev);
            let inj_ground = self.solver.implies(images_eq, inputs_eq);
            self.solver.assert_term(inj_ground);
        }

        let entry = self
            .injective_bridge_ground_terms
            .entry(bridge_key)
            .or_default();
        if !entry.iter().any(|t| *t == term) {
            entry.push(term);
        }

        // Variant-tag preservation across the bridge. A structural-sort bridge
        // is a faithful representation of the SAME logical value in a different
        // enum encoding (e.g. the generic `Option` carrier and the
        // monomorphized `OptionInt`), so it must preserve the active variant.
        // Emit the ground discriminant-equality `disc_to(bridge(t)) =
        // disc_from(t)` (and pin both sorts' variant tags) so reasoning that
        // observes one side's discriminant carries over to the other. Without
        // this, `bridge(call_3) == OptionInt::Some(_)` (from a `.get`
        // postcondition) left the source `Option`'s discriminant free, so the
        // unreachable `None` arm of `addr.get(left/8)` could not be discharged.
        // Sound: it relates two views of one value; it adds no fact about which
        // variant is actually active.
        self.assert_bridge_discriminant_preservation(from_sort, to_sort, term, bridged);

        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        bridged
    }

    /// Emit a ground discriminant-preservation axiom for a structural-sort
    /// bridge between two enum-family sorts whose variant structure lines up.
    ///
    /// A structural-sort bridge is a faithful representation of the SAME value
    /// in a different enum encoding, so it preserves the active variant. The
    /// `method_discriminant_1_*` UF assigns each enum value its variant index,
    /// and we assert `disc_to(bridge(t)) == disc_from(t)` so a discriminant
    /// observed on one side carries to the other. To make that equality usable
    /// we also pin the TARGET sort's per-variant discriminant tags on the
    /// bridge image via the target's native constructor testers
    /// (`is_C(bridge(t)) ==> disc_to(bridge(t)) == idx`). For the bitwalker
    /// `addr.get(left/8)` case this lets `bridge(call_3) == Some(_)` (a `.get`
    /// postcondition) force `disc_to(bridge(call_3)) == 1`, hence
    /// `disc_from(call_3) != 0`, discharging the unreachable `None` arm.
    ///
    /// Sound: it only relates two views of one value and pins the target's own
    /// (fixed, encoding-defined) variant tags; it adds no fact about which
    /// variant is actually active.
    ///
    /// The TARGET sort must resolve to an enum datatype (>= 2 constructors) so
    /// its native testers/variant tags exist. The SOURCE need not carry a
    /// datatype declaration (the generic `Option` carrier is a bare
    /// uninterpreted sort with only a discriminant UF) — the preservation
    /// equality is valid for any faithful same-family bridge, which is the only
    /// context `bridge_structural_sort` runs in. When the source DOES resolve to
    /// a datatype, its constructor names must line up variant-for-variant with
    /// the target as an extra guard against reshaping bridges.
    fn assert_bridge_discriminant_preservation(
        &mut self,
        from_sort: &Sort,
        to_sort: &Sort,
        term: Term,
        bridged: Term,
    ) {
        let Some(to_dt) = self.resolve_enum_datatype_sort(to_sort) else {
            return;
        };
        if to_dt.constructors.len() <= 1 {
            return;
        }
        // If the source also resolves to a datatype, require identical variant
        // structure (same arity, same constructor names in order) so we only
        // fire for faithful sort-renaming bridges and never for one that
        // reshapes the variant set.
        if let Some(from_dt) = self.resolve_enum_datatype_sort(from_sort) {
            if from_dt.constructors.len() != to_dt.constructors.len()
                || from_dt
                    .constructors
                    .iter()
                    .zip(to_dt.constructors.iter())
                    .any(|(a, b)| a.name != b.name)
            {
                return;
            }
        }

        let from_disc_name = format!("method_discriminant_1_{}", Self::method_sort_tag(from_sort));
        let to_disc_name = format!("method_discriminant_1_{}", Self::method_sort_tag(to_sort));
        let from_disc =
            self.get_or_declare_method_func(&from_disc_name, &[from_sort.clone()], Sort::Int);
        let to_disc = self.get_or_declare_method_func(&to_disc_name, &[to_sort.clone()], Sort::Int);

        // Variant preservation across the bridge: disc_to(bridge(t)) = disc_from(t).
        let from_disc_app = self.solver.apply(&from_disc, &[term]);
        let to_disc_app = self.solver.apply(&to_disc, &[bridged]);
        let preserve = self.eq_term(to_disc_app, from_disc_app);
        self.assert_solver_term("struct_bridge/discriminant_preservation", preserve);

        // Pin the target's per-variant discriminant tags on the bridge image:
        // is_C(bridge(t)) ==> disc_to(bridge(t)) == variant_index(C). Uses the
        // target's native constructor testers, so it needs no quantifier.
        let to_adt_decl = self.adt_decl_for_name(&to_dt.name).cloned();
        for (variant_idx, ctor) in to_dt.constructors.iter().enumerate() {
            let Some(tester) =
                self.axiom_datatype_tester("struct_bridge/disc_tag_tester", &ctor.name, bridged)
            else {
                continue;
            };
            let discr_val =
                Self::datatype_discriminant_value(to_adt_decl.as_ref(), &ctor.name, variant_idx);
            let tag = self.solver.int_const_bigint(&discr_val);
            let disc_eq_tag = self.eq_term(to_disc_app, tag);
            let implication = self.solver.implies(tester, disc_eq_tag);
            self.assert_solver_term("struct_bridge/disc_tag", implication);
        }
    }

    /// Resolve a sort to its enum `DatatypeSort` definition when it is (or names)
    /// a registered datatype. Handles `Datatype(_)` directly and
    /// `Uninterpreted(name)` whose name has a registered datatype declaration.
    fn resolve_enum_datatype_sort(&self, sort: &Sort) -> Option<ay_dpll::api::DatatypeSort> {
        match sort {
            Sort::Datatype(dt) => Some(dt.clone()),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
            _ => None,
        }
    }

    /// Create a solver equality term with sort repair and panic isolation.
    ///
    /// The current ay pin includes the Bool/Bool equality fix for #1179, so
    /// this now uses native `solver.eq()` for all operand sorts. The remaining
    /// wrapper logic is only for cross-sort coercion and panic recovery until
    /// the `try_*` migration lands (#2131).
    ///
    /// On ay panic (sort mismatch), increments the `PanicRecoveryFalse`
    /// unsoundness counter and returns a FRESH UNCONSTRAINED Bool constant so
    /// `demote_if_unsound` can catch it. The fresh constant is polarity-neutral
    /// and thus safe in BOTH contexts: as a proof OBLIGATION it is unprovable
    /// (exactly as conservative as the old `bool_const(false)`), and as an
    /// ASSUMED FACT it constrains nothing. The old literal-`false` fallback was
    /// anti-conservative in assumption position — a fact whose equality cannot
    /// be encoded (e.g. Bool-sorted placeholder lookup vs Int literal in
    /// ghost/ghost_map) became `(assert false)` and manufactured an UNSAT
    /// premise set, tripping the vacuity guard on a satisfiable path. (#1663,
    /// ghost/ghost_map)
    pub(crate) fn eq_term(&mut self, a: Term, b: Term) -> Term {
        // BEFORE harmonization: harmonize's `coerce_ite_sorts` fallback turns
        // the Bool side into `ite(b, 1, 0)`, after which the collapse is no
        // longer detectable (the fold to `false` then happens inside ay's
        // `eq`).
        if let Some(term) = self.bool_vs_out_of_range_int_literal_eq(a, b) {
            return term;
        }
        let (a, b) = self.harmonize_eq_or_ite_terms(a, b);

        match catch_solver_panic_with_reason("eq_term", || self.solver.eq(a, b)) {
            Ok(term) => term,
            Err(err) => {
                unsoundness::increment(unsoundness::UnsoundnessCategory::PanicRecoveryFalse);
                tracing::debug!("eq_term recovered from ay equality panic: {}", err.reason());
                self.fresh_unencodable_eq_bool("eq_term")
            }
        }
    }

    /// Detect a Bool-sorted term compared against an Int LITERAL outside
    /// {0, 1}. ay's `eq()` bridges Bool-vs-Int through the 0/1 lane, so such
    /// an equality constant-folds to literal `false`. The Bool sort in this
    /// shape is always a value-polymorphism inference failure (e.g. an FMap
    /// `lookup` first seen in a Bool context, later compared to `50` in
    /// ghost/ghost_map) — folding it to `false` MANUFACTURES a fact: in
    /// assumption position it collapses the base premises to UNSAT on a
    /// satisfiable path. Return a polarity-neutral fresh Bool instead:
    /// unprovable as a goal, information-free as an assumption. The rare
    /// genuinely-Bool case only loses a trivially-false fact (completeness,
    /// never soundness).
    fn bool_vs_out_of_range_int_literal_eq(&mut self, a: Term, b: Term) -> Option<Term> {
        let a_sort = self.solver.get_sort(a);
        let b_sort = self.solver.get_sort(b);
        let int_side = match (&a_sort, &b_sort) {
            (Sort::Bool, Sort::Int) => b,
            (Sort::Int, Sort::Bool) => a,
            _ => return None,
        };
        let literal = self.term_int_literal_for_arithmetic(int_side)?;
        use num_bigint::BigInt;
        if literal == BigInt::from(0) || literal == BigInt::from(1) {
            return None;
        }
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToInt);
        tracing::debug!("eq_term: Bool vs out-of-range Int literal {literal} — emitting neutral");
        Some(self.fresh_unencodable_eq_bool("bool_vs_int_literal"))
    }

    /// Fresh unconstrained Bool constant standing in for an equality that could
    /// not be encoded (cross-sort panic). Polarity-neutral: unprovable as a
    /// goal, information-free as an assumption.
    ///
    /// Verdict hygiene (arc_and_rc sort-plan fix, part c): when the equality
    /// being fabricated away sits in ASSUMPTION position (precondition,
    /// `LetAssume` assumption, path-condition fact), a real premise vanishes
    /// from the assumption base. Any subsequent `Failed(Counterexample)`
    /// verdict is then untrustworthy — the model may only exist because the
    /// premise was neutralized — so the dedicated `PremiseNeutralizedEq`
    /// counter is incremented and `demote_if_unsound` converts `Failed` to
    /// `Unknown(Demoted)` (fail-closed). Goal-side fabrications do NOT
    /// increment it: an unprovable placeholder goal is already conservative,
    /// and expected-failure (should_fail) verdicts must survive.
    fn fresh_unencodable_eq_bool(&mut self, origin: &str) -> Term {
        static UNENCODABLE_EQ_COUNTER: AtomicU64 = AtomicU64::new(0);
        let id = UNENCODABLE_EQ_COUNTER.fetch_add(1, Ordering::Relaxed);
        let _ = origin;
        if self.arithmetic_mode.assumption_position() {
            unsoundness::increment(unsoundness::UnsoundnessCategory::PremiseNeutralizedEq);
        }
        self.solver
            .declare_const(&format!("__trust_wp_unencodable_eq_{id}"), Sort::Bool)
    }

    /// Like [`eq_term`](Self::eq_term), but builds `(= a b)` WITHOUT ay's eager
    /// `(= x (ite c t e))` -> `ite(c, (= x t), (= x e))` expansion.
    ///
    /// The predicate-closure ground instances
    /// `mapping_get(closure_map, k) == ite(pred(k), 1, 0)` MUST stay in this
    /// value-level ITE form: LRA closes `x == ite(c, 1, 0)` with a single
    /// arithmetic case-split, whereas the boolean-level ITE that the default
    /// `mk_eq` expansion produces makes the combined theory solver churn against
    /// the in-scope closure/range universals — cell/01_basic was
    /// `quantifier-unhandled`/timeout with the expanded form and closes in well
    /// under a second with this one (verified on ay HEAD). Logically identical
    /// to [`eq_term`](Self::eq_term); on any sort/coercion error or panic it
    /// falls back to the expanding equality so the fact is never silently
    /// dropped. (#985, #2316)
    pub(crate) fn eq_term_no_ite_expand(&mut self, a: Term, b: Term) -> Term {
        // See eq_term: must run BEFORE harmonization.
        if let Some(term) = self.bool_vs_out_of_range_int_literal_eq(a, b) {
            return term;
        }
        let (a, b) = self.harmonize_eq_or_ite_terms(a, b);
        if let Ok(Ok(term)) = catch_solver_panic_with_reason("eq_term_no_ite_expand", || {
            self.solver.try_eq_no_ite_expand(a, b)
        }) {
            return term;
        }
        match catch_solver_panic_with_reason("eq_term_no_ite_expand/fallback", || {
            self.solver.eq(a, b)
        }) {
            Ok(term) => term,
            Err(err) => {
                unsoundness::increment(unsoundness::UnsoundnessCategory::PanicRecoveryFalse);
                tracing::debug!(
                    "eq_term_no_ite_expand recovered from ay equality panic: {}",
                    err.reason()
                );
                self.fresh_unencodable_eq_bool("eq_term_no_ite_expand")
            }
        }
    }

    /// Compatibility wrapper for user-facing equality surfaces.
    ///
    /// Native `solver.eq()` is sound for Bool terms on the current ay pin, but
    /// higher-level verification queries still lose completeness on complex
    /// Bool formulas such as short-circuit bodies encoded as nested ITEs. Keep
    /// the iff expansion here so postconditions and result/body bindings retain
    /// the pre-cutover proof behavior while lower-level call sites can opt into
    /// `eq_term()` directly. (#1179, #2508)
    pub(crate) fn eq_or_iff(&mut self, a: Term, b: Term, _sort: &Sort) -> Term {
        let a_sort = self.solver.get_sort(a);
        let b_sort = self.solver.get_sort(b);

        if a_sort == Sort::Bool && b_sort == Sort::Bool {
            match catch_solver_panic_with_reason("eq_or_iff", || {
                let fwd = self.solver.implies(a, b);
                let bwd = self.solver.implies(b, a);
                self.solver.and(fwd, bwd)
            }) {
                Ok(term) => term,
                Err(err) => {
                    unsoundness::increment(unsoundness::UnsoundnessCategory::PanicRecoveryFalse);
                    self.assertion_pipeline
                        .record_solver_panic(err.into_reason());
                    self.solver.bool_const(false)
                }
            }
        } else {
            self.eq_term(a, b)
        }
    }

    /// Sort-safe ITE construction with panic isolation.
    ///
    /// Harmonizes branch sorts via `harmonize_eq_or_ite_terms` before calling
    /// `solver.ite()`. Falls back to the then-branch on ay panic (e.g., when
    /// the branch sorts are genuinely incompatible and coercion fails), recording
    /// the panic for demotion. This replaces unprotected `self.solver.ite()`
    /// calls that can crash the verification pipeline on sort mismatches like
    /// `Uninterpreted("OptionInt")` vs `Uninterpreted("Option")`. (#2699)
    pub(crate) fn safe_ite(&mut self, cond: Term, then_branch: Term, else_branch: Term) -> Term {
        let then_sort = self.solver.get_sort(then_branch);
        let else_sort = self.solver.get_sort(else_branch);
        let (t, e) = if then_sort == else_sort {
            (then_branch, else_branch)
        } else {
            self.harmonize_eq_or_ite_terms(then_branch, else_branch)
        };
        match catch_solver_panic_with_reason("safe_ite", || self.solver.ite(cond, t, e)) {
            Ok(term) => term,
            Err(err) => {
                unsoundness::increment(unsoundness::UnsoundnessCategory::PanicRecoveryFalse);
                self.assertion_pipeline
                    .record_solver_panic(err.into_reason());
                // Return the then-branch as a fallback — preserves the "happy path"
                // value semantics while recording that this proof is suspect.
                t
            }
        }
    }

    /// Returns the first solver panic reason, if any.
    ///
    /// When this is `Some`, `check_sat()` returns `Unknown` as a safety
    /// measure — the cause is a ay crash, not solver incompleteness.
    pub(crate) fn solver_panic_reason(&self) -> Option<&str> {
        self.assertion_pipeline.solver_panic_reason()
    }

    /// Set the per-query timeout on the underlying solver.
    ///
    /// When set, each `check_sat()` call is limited to this duration.
    /// `None` clears any previously set timeout.
    pub(crate) fn set_timeout(&mut self, timeout: Option<std::time::Duration>) {
        self.solver.set_timeout(timeout);
    }

    /// Get declared logic function names (for debugging).
    pub(crate) fn logic_func_names(&self) -> Vec<String> {
        self.logic_func_names_iter().cloned().collect()
    }

    /// Get declared spec function names (for debugging).
    pub(crate) fn spec_func_names(&self) -> Vec<String> {
        self.spec_func_names_iter().cloned().collect()
    }
}

fn is_recoverable_sort_mismatch_panic(reason: &str) -> bool {
    reason.contains("mk_eq expects same sort")
}

#[cfg(test)]
mod quantified_equality_tests;

#[cfg(test)]
mod vacuity_guard_tests;

#[cfg(test)]
mod solve_details_tests;

#[cfg(test)]
mod prenex_push_tests;

#[cfg(test)]
mod tests {
    use ay_dpll::api::Sort;

    use super::{is_proof_related_panic, is_retryable_proof_unknown, AYEncoder};
    use crate::shared_types::UnknownReason;

    /// A Bool-sorted term compared against an Int literal outside {0, 1} must
    /// NOT constant-fold to literal `false`: as an ASSUMED FACT that would
    /// manufacture UNSAT base premises on a satisfiable path (ghost/ghost_map
    /// vacuity — the value-polymorphic FMap `lookup` mis-sorted as Bool then
    /// compared to `50`). The equality must encode polarity-neutral: asserting
    /// it (assumption position) keeps the base SAT.
    #[test]
    fn bool_vs_out_of_range_int_literal_eq_is_polarity_neutral() {
        let mut encoder = AYEncoder::new();
        let b = encoder
            .get_or_declare_var("some_bool", Sort::Bool)
            .expect("bool var");
        let lit = encoder.solver.int_const(50);
        let eq = encoder.eq_term(b, lit);
        encoder.assert_term(eq);
        let result = encoder.check_sat();
        assert!(
            result.is_sat(),
            "assuming `bool == 50` must not collapse the base to UNSAT: got {result:?}"
        );

        // 0/1 literals keep the genuine bridge semantics: `b == 1` with
        // `b := true` stays SAT (the guard must not fire for in-range
        // literals).
        let mut encoder = AYEncoder::new();
        let b = encoder
            .get_or_declare_var("some_bool", Sort::Bool)
            .expect("bool var");
        let one = encoder.solver.int_const(1);
        let eq = encoder.eq_term(b, one);
        encoder.assert_term(eq);
        assert!(
            encoder.check_sat().is_sat(),
            "`bool == 1` must remain satisfiable via the 0/1 bridge"
        );
    }

    #[test]
    fn conflict_semantic_verification_panics_are_retryable() {
        let reason = "BUG(#6853): AUFLIA LIA conflict semantic verification failed: \
            Conflict literals are satisfiable (not a real conflict)";

        assert!(
            is_proof_related_panic(reason),
            "ay #6853 conflict-verifier panics should take the no-proof retry path"
        );
    }

    #[test]
    fn invalid_unsat_proof_builder_panics_are_retryable() {
        let reason =
            "BUG: build_unsat_proof produced a proof that does not derive the empty clause";

        assert!(
            is_proof_related_panic(reason),
            "invalid ay UNSAT proof construction should take the no-proof retry path"
        );
    }

    #[test]
    fn proof_trusted_unknowns_are_retryable() {
        assert!(
            is_retryable_proof_unknown(Some(&UnknownReason::ProofTrusted), None),
            "ay proof-trusted Unknown should take the no-proof retry path"
        );
        assert!(
            is_retryable_proof_unknown(None, Some("proof checker rejected UNSAT proof")),
            "proof-related executor errors should take the no-proof retry path"
        );
        assert!(
            !is_retryable_proof_unknown(Some(&UnknownReason::Timeout), None),
            "non-proof Unknown reasons must stay fail-closed"
        );
        assert!(
            !is_retryable_proof_unknown(Some(&UnknownReason::SelfCheckRejected), None),
            "self-check rejection must not be retried with proof production disabled"
        );
    }

    #[test]
    fn unconstrained_int_uf_disequality_is_syntactic_sat() {
        let mut encoder = AYEncoder::new();
        let a = encoder.solver.declare_const("a", Sort::Int);
        let b = encoder.solver.declare_const("b", Sort::Int);
        let func = encoder.get_or_declare_logic_func(
            "logic_test__placeholder_i__ret_i",
            &[Sort::Int],
            Sort::Int,
        );
        let fa = encoder.solver.apply(&func, &[a]);
        let fb = encoder.solver.apply(&func, &[b]);
        let differs = encoder.solver.try_neq(fa, fb).unwrap();

        encoder.assert_term(differs);

        assert!(encoder.assertions_are_unconstrained_placeholder_uf_disequalities_sat());
    }

    #[test]
    fn interpreted_int_terms_do_not_match_uf_disequality_shortcut() {
        let mut encoder = AYEncoder::new();
        let x = encoder.solver.declare_const("x", Sort::Int);
        let one = encoder.solver.int_const(1);
        let x_plus_one = encoder.solver.try_add(x, one).unwrap();
        let differs = encoder.solver.try_neq(x_plus_one, x).unwrap();

        encoder.assert_term(differs);

        assert!(!encoder.assertions_are_unconstrained_placeholder_uf_disequalities_sat());
    }

    #[test]
    fn placeholder_plus_zero_disequality_does_not_match_uf_disequality_shortcut() {
        let mut encoder = AYEncoder::new();
        let x = encoder.solver.declare_const("x", Sort::Int);
        let zero = encoder.solver.int_const(0);
        let func = encoder.get_or_declare_logic_func(
            "logic_test__placeholder_i__ret_i",
            &[Sort::Int],
            Sort::Int,
        );
        let fx = encoder.solver.apply(&func, &[x]);
        let fx_plus_zero = encoder.solver.try_add(fx, zero).unwrap();
        let differs = encoder.solver.try_neq(fx, fx_plus_zero).unwrap();

        encoder.assert_term(differs);

        assert!(
            !encoder.assertions_are_unconstrained_placeholder_uf_disequalities_sat(),
            "shortcut must not accept disequalities between a placeholder UF value and interpreted arithmetic over that same value"
        );
    }

    #[test]
    fn placeholder_with_interpreted_child_does_not_match_uf_disequality_shortcut() {
        let mut encoder = AYEncoder::new();
        let x = encoder.solver.declare_const("x", Sort::Int);
        let zero = encoder.solver.int_const(0);
        let x_plus_zero = encoder.solver.try_add(x, zero).unwrap();
        let func = encoder.get_or_declare_logic_func(
            "logic_test__placeholder_i__ret_i",
            &[Sort::Int],
            Sort::Int,
        );
        let fx = encoder.solver.apply(&func, &[x]);
        let f_x_plus_zero = encoder.solver.apply(&func, &[x_plus_zero]);
        let differs = encoder.solver.try_neq(f_x_plus_zero, fx).unwrap();

        encoder.assert_term(differs);

        assert!(
            !encoder.assertions_are_unconstrained_placeholder_uf_disequalities_sat(),
            "shortcut must not accept placeholder UF applications with interpreted children"
        );
    }

    #[test]
    fn placeholder_arg_equality_blocks_uf_disequality_shortcut() {
        let mut encoder = AYEncoder::new();
        let a = encoder.solver.declare_const("a", Sort::Int);
        let b = encoder.solver.declare_const("b", Sort::Int);
        let func = encoder.get_or_declare_logic_func(
            "logic_test__placeholder_i__ret_i",
            &[Sort::Int],
            Sort::Int,
        );
        let fa = encoder.solver.apply(&func, &[a]);
        let fb = encoder.solver.apply(&func, &[b]);
        let args_equal = encoder.solver.eq(a, b);
        let differs = encoder.solver.try_neq(fa, fb).unwrap();

        encoder.assert_term(args_equal);
        encoder.assert_term(differs);

        assert!(
            !encoder.assertions_are_unconstrained_placeholder_uf_disequalities_sat(),
            "shortcut must not accept UF disequalities when another assertion constrains arguments equal"
        );
    }

    #[test]
    fn non_placeholder_uf_disequality_does_not_match_placeholder_shortcut() {
        let mut encoder = AYEncoder::new();
        let a = encoder.solver.declare_const("a", Sort::Int);
        let b = encoder.solver.declare_const("b", Sort::Int);
        let func = encoder.get_or_declare_logic_func("logic_plain", &[Sort::Int], Sort::Int);
        let fa = encoder.solver.apply(&func, &[a]);
        let fb = encoder.solver.apply(&func, &[b]);
        let differs = encoder.solver.try_neq(fa, fb).unwrap();

        encoder.assert_term(differs);

        assert!(
            !encoder.assertions_are_unconstrained_placeholder_uf_disequalities_sat(),
            "shortcut must stay scoped to placeholder logic-function UFs"
        );
    }
}
