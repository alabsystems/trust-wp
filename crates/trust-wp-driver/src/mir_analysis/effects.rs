// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Explicit call-effect context for extraction.
//!
//! An explicit struct that extraction code writes into and callers read
//! from, so call-site assumptions and obligations stay scoped to the
//! extraction (and the branch) that produced them rather than leaking
//! through a process-wide side channel any caller could observe or forget
//! to clear.

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};
use trust_wp_driver::StdSpec;

/// The kind of spec clause that was dropped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DroppedClauseKind {
    /// A `requires(...)` precondition clause.
    Precondition,
    /// An `ensures(...)` postcondition clause.
    Postcondition,
}

/// A spec clause that was dropped during call-site extraction.
///
/// Records provenance so the verification pipeline can generate
/// actionable diagnostics and fail-closed obligations.
#[derive(Debug, Clone)]
pub(crate) struct DroppedClause {
    /// Whether this was a precondition or postcondition.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) kind: DroppedClauseKind,
    /// The original clause text (e.g., `"x > 0"`).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) clause: String,
    /// Why it was dropped (parse error message, unresolved names, etc.).
    /// Written for diagnostic provenance; not yet displayed in user-facing output.
    #[expect(dead_code, reason = "diagnostic provenance: stored for future display")]
    pub(crate) reason: String,
}

/// Extracted closure body info from a `Mapping::from_closure(closure)` call.
///
/// Recorded in `CallEffects` during MIR extraction so the encoder can emit
/// a quantified axiom connecting the Mapping value to the closure's semantics.
#[derive(Debug, Clone)]
pub(crate) struct MappingClosureInfo {
    /// The result variable representing the Mapping value.
    pub(crate) result_var: PureExpr,
    /// The closure body expression (return value of the closure).
    pub(crate) body_expr: PureExpr,
    /// Formal parameter names of the closure.
    pub(crate) param_names: Vec<String>,
}

impl MappingClosureInfo {
    /// Convert to a `forall` axiom: `forall k. mapping.get(k) == body`.
    ///
    /// The closure's first parameter becomes the quantified variable. The body
    /// already references this parameter by name, so no substitution is needed.
    /// A trigger on `mapping.get(k)` guides SMT instantiation.
    ///
    /// Uses `ExprSort::Int` for the quantifier variable to match the Mapping
    /// encoding in the SMT layer (`mapping_get` takes `Sort::Int` keys).
    /// The body expression is rewritten to use `ExprSort::Int` for the
    /// parameter variable as well, ensuring sort consistency. (#2245)
    ///
    /// Returns `None` if `param_names` is empty (no quantified variable).
    pub(crate) fn to_forall_axiom(&self) -> Option<PureExpr> {
        let param = self.param_names.first()?;
        // Normalize the closure body's parameter sort to Int. The extraction
        // may produce Datatype(N) for creusot_std::Int, but Mapping.get()
        // operates on SMT Int keys.
        let normalized_body = normalize_var_sort_to_int(&self.body_expr, param);
        let k_var = PureExpr::Var(param.clone(), Some(ExprSort::Int));
        let get_call = PureExpr::MethodCall {
            receiver: Arc::new(self.result_var.clone()),
            method: "get".to_string(),
            args: vec![k_var],
        };
        let body = PureExpr::Forall {
            var: param.clone(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(get_call.clone()),
                BinOp::Eq,
                Arc::new(normalized_body),
            )),
            triggers: vec![vec![get_call]],
        };
        Some(body)
    }
}

/// Extracted per-element closure ensures for a `map_inv(iter, closure)` call.
///
/// Recorded in `CallEffects` during MIR extraction so the function VC can
/// assume two sound facts about the produced `MapInv` value (#2170 "Slice 3"):
///
/// 1. **Length preservation**: `result@.len() == iter@.len()`. `map_inv`
///    applies the closure to each produced element without dropping or adding
///    any, so the produced sequence has the same length as the inner
///    iterator's. This is always true.
///
/// 2. **Per-element closure ensures**: for each closure `#[ensures(P)]` whose
///    `result := result@.index_logic(i)` substitution leaves no free closure
///    formal parameter, `forall i. 0 <= i < result@.len() ==> P[result := result@[i]]`.
///    Element `i` of the `MapInv` view is exactly the closure's output on the
///    `i`-th produced element, so its `#[ensures]` clause holds. Clauses whose
///    substitution would leave a dangling closure formal (the element or
///    snapshot binders) are dropped here — emitting them would assert a fact
///    with free variables, which is unsound. (See `to_view_axioms`.)
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct MapInvClosureInfo {
    /// The result variable representing the `MapInv` value. It names ONE
    /// `map_inv` call site (`$call_<dest>_mapinv_bb<N>`), never the shared
    /// destination local, so a collect receiver identifies its source call.
    pub(crate) result_var: PureExpr,
    /// The block whose terminator is this `map_inv` call (the collect facts
    /// require it to dominate the collect call and be acyclic).
    pub(crate) call_block: rustc_middle::mir::BasicBlock,
    /// The produced-sequence length of the inner iterator, in `Int` space, if
    /// the handler could determine it soundly (e.g., `end - start` for a
    /// `Range`). When present, the length fact
    /// `produced_len_guard ==> result@.len() == produced_len` is emitted.
    /// `None` ⇒ no length fact (only the per-element ensures, which is
    /// independent of the length model).
    pub(crate) produced_len: Option<PureExpr>,
    /// Soundness guard for `produced_len`. The length equality is only asserted
    /// under this guard (e.g., `start <= end` for a `Range`, since a reversed
    /// range produces zero elements while `end - start` would be negative). A
    /// `None` guard means the length holds unconditionally.
    pub(crate) produced_len_guard: Option<PureExpr>,
    /// The closure's parsed `#[ensures]` expressions (each mentions `result`).
    pub(crate) ensures_exprs: Vec<PureExpr>,
    /// The closure's formal parameter names (the element and snapshot binders).
    ///
    /// Used as the soundness gate: a clause is only emitted per-element when it
    /// does not reference any of these names (after the `result` substitution),
    /// because those binders have no meaning at the call site.
    pub(crate) closure_param_names: Vec<String>,
}

impl MapInvClosureInfo {
    /// Build the sound view axioms for this `map_inv` call.
    ///
    /// Always emits the length-preservation fact. Emits a per-element
    /// `forall` clause for each closure `#[ensures]` clause that, after
    /// substituting `result := result@.index_logic(i)`, references none of the
    /// closure's formal parameters (the element / snapshot binders). Clauses
    /// that would leave a dangling formal are skipped — never asserted — so a
    /// false per-element fact can never reach the solver.
    ///
    /// `collected_var` is the result of `Iterator::collect::<MapInv<..>,
    /// Vec<_>>(result_var)` at ONE call site. Creusot's `collect` contract
    /// gives `Vec::from_iter_post(prod, res) == (prod == res@)` for the
    /// produced sequence `prod`, and `MapInv::produces` makes `prod` the
    /// per-element closure outputs with the inner iterator's produced length.
    /// The caller must pass a symbol that names only that call site's result
    /// and must scope the facts to the path through that call (a return slot
    /// `call_0` written on two branches is shared).
    pub(crate) fn to_view_axioms(&self, collected_var: &PureExpr) -> Vec<PureExpr> {
        let mut axioms = Vec::new();

        // Root every fact at the COLLECTED Vec, never at the `MapInv` value:
        // the `MapInv` iterator's own view is not the produced sequence, and the
        // generic collect spec does not bridge the two.
        // `collected@` is the produced sequence (Vec::from_iter_post); indexing
        // it gives the i-th closure output, and a further `@` that element's
        // own view.
        let result_view = PureExpr::View(Arc::new(collected_var.clone()));

        // The collected value's length is `collected@.len()` — a single view.
        // Viewing once more would be one level too deep. (#2170)
        let collected_len = PureExpr::MethodCall {
            receiver: Arc::new(result_view.clone()),
            method: "len".to_string(),
            args: vec![],
        };

        // Fact 1: produced length — collected@.len() == produced_len, guarded.
        // `map_inv` applies the closure once per produced element without
        // dropping or adding any, so the produced length equals the inner
        // iterator's produced length. The handler supplies that length (and an
        // optional guard) only when it can determine it soundly.
        if let Some(produced_len) = &self.produced_len {
            let len_eq = PureExpr::BinOp(
                Arc::new(collected_len.clone()),
                BinOp::Eq,
                Arc::new(produced_len.clone()),
            );
            let len_fact = match &self.produced_len_guard {
                Some(guard) => {
                    PureExpr::BinOp(Arc::new(guard.clone()), BinOp::Implies, Arc::new(len_eq))
                }
                None => len_eq,
            };
            axioms.push(len_fact);
        }

        // Fact 2: per-element closure ensures.
        // The quantified variable; `result@.index_logic(i)` is the i-th produced
        // element = the closure output on the i-th source element.
        let i_name = "__trust_wp_map_inv_i";
        let i_var = PureExpr::Var(i_name.to_string(), Some(ExprSort::Int));
        let elem = PureExpr::MethodCall {
            receiver: Arc::new(result_view),
            method: "index_logic".to_string(),
            args: vec![i_var.clone()],
        };

        let mut result_sub = HashMap::new();
        result_sub.insert("result".to_string(), elem.clone());

        for ensures in &self.ensures_exprs {
            // The clause must mention `result`; a clause that does not is a
            // global fact about captures, harmless but not per-element — skip
            // those to keep the axiom set tight and the trigger meaningful.
            if !ensures.free_vars().contains("result") {
                continue;
            }
            let substituted = ensures.substitute(&result_sub);

            // SOUNDNESS GATE: after substituting `result`, the clause must not
            // reference any closure formal parameter. Those binders (the
            // produced element and the snapshot) have no call-site meaning, so
            // emitting them would assert a fact with dangling free variables.
            // When in doubt, emit nothing (completeness loss is acceptable; a
            // false fact is catastrophic).
            let free = substituted.free_vars();
            if self
                .closure_param_names
                .iter()
                .any(|p| free.contains(p.as_str()))
            {
                continue;
            }

            // 0 <= i < collected@.len()
            let lo = PureExpr::BinOp(
                Arc::new(PureExpr::Int(0)),
                BinOp::Le,
                Arc::new(i_var.clone()),
            );
            let hi = PureExpr::BinOp(
                Arc::new(i_var.clone()),
                BinOp::Lt,
                Arc::new(collected_len.clone()),
            );
            let range = PureExpr::BinOp(Arc::new(lo), BinOp::And, Arc::new(hi));
            let body = PureExpr::BinOp(Arc::new(range), BinOp::Implies, Arc::new(substituted));

            axioms.push(PureExpr::Forall {
                var: i_name.to_string(),
                var_sort: Some(ExprSort::Int),
                body: Arc::new(body),
                triggers: vec![vec![elem.clone()]],
            });
        }

        axioms
    }
}

/// Rewrite all `Var(name, _)` occurrences to `Var(name, Some(Int))`.
///
/// Closure body extraction may produce `Var("x", Some(Datatype(N)))` for
/// `creusot_std::Int` parameters, but the Mapping encoding uses SMT `Int`.
/// This normalizes the sort so the forall body matches the `mapping_get`
/// key sort. Uses `PureExpr::substitute` with a sort-corrected replacement.
fn normalize_var_sort_to_int(expr: &PureExpr, var_name: &str) -> PureExpr {
    let replacement = PureExpr::Var(var_name.to_string(), Some(ExprSort::Int));
    let mut subs = HashMap::new();
    subs.insert(var_name.to_string(), replacement);
    expr.substitute(&subs)
}

/// Accumulated call-site effects from specification application.
///
/// During MIR extraction, applying a callee's spec at its call site
/// produces three kinds of side effects:
///
/// - **Assumptions**: postcondition-derived facts the solver can assume
///   (e.g., `result == x + 1` becomes `call_dest == arg0 + 1`).
/// - **Obligations**: precondition-derived facts the solver must prove
///   at the call site (e.g., `requires(x > 0)` becomes `arg0 > 0`).
/// - **Dropped spec clauses**: clauses that could not be parsed or
///   substituted. Each generates a synthetic `false` obligation to
///   enforce fail-closed semantics.
/// - **Mapping closures**: closure body info from `Mapping::from_closure`
///   calls, for downstream axiom emission. (#2316)
#[derive(Debug, Clone, Default)]
pub(crate) struct CallEffects {
    /// Postcondition-derived assumptions from spec application.
    pub(crate) assumptions: Vec<PureExpr>,
    /// Precondition-derived obligations from spec application.
    pub(crate) obligations: Vec<PureExpr>,
    /// Provenance bit: this extraction observed a mutating call effect.
    pub(crate) has_mutating_call_effect: bool,
    /// Number of spec clauses dropped due to parse/substitution failures.
    /// Derived from `dropped_clauses.len()` for backward compatibility.
    pub(crate) dropped_spec_clauses: usize,
    /// Structured provenance for each dropped clause.
    pub(crate) dropped_clauses: Vec<DroppedClause>,
    /// Closure body info from `Mapping::from_closure` calls (#2316).
    pub(crate) mapping_closures: Vec<MappingClosureInfo>,
    /// Per-element closure ensures from `map_inv(iter, closure)` calls (#2170).
    pub(crate) map_inv_closures: Vec<MapInvClosureInfo>,
    /// Every extraction of a `map_inv(..).collect::<Vec<_>>()` call site:
    /// `(site symbol, facts)`, with an EMPTY fact list recorded whenever that
    /// extraction could not state facts. Identical entries are deduplicated.
    /// Only a site with exactly one distinct, non-empty entry contributes
    /// function-level assumptions (see `map_inv_collect_assumptions`).
    pub(crate) map_inv_collect_sites: Vec<(String, Vec<PureExpr>)>,
    /// Extraction-only map from mut-ref result temps to the receiver they
    /// mutate. Used to commit writes like `*call_16 = 2` back into the
    /// receiver state during successor extraction.
    pub(crate) mut_ref_result_receivers: HashMap<String, PureExpr>,
    /// Facts that hold on every path that RETURNS from the function
    /// (surviving-path facts): when a switch arm can never
    /// return (a spinning `-> !` callee), the function only returns through
    /// the other arms. These are NOT assumptions: an assumption premises every
    /// goal, including call-precondition and panic-unreachability obligations
    /// that must hold on the diverging arm itself or before it. They may only
    /// premise the function's own postconditions (`facts ==> ensures`), and an
    /// arm's facts are guarded by that arm's condition.
    pub(crate) returning_path_facts: Vec<PureExpr>,
    /// How many of `obligations` are a literal `false` a USER wrote: a
    /// callee's own `#[requires(false)]`, substituted at this call site.
    ///
    /// The verdict gate asks whether the goal set carries a `false` trust-wp
    /// injected because it could not model something, and it answers by
    /// COUNTING falses, bare or behind the path guards a branch arm's
    /// obligations are wrapped in (`trust_wp_ay::is_fail_closed_marker`) — a
    /// scan cannot tell an injected marker from a written clause, because both
    /// are spelled `PureExpr::Bool(false)`. So
    /// the one kind that IS a clause a program can violate is counted where it
    /// is written and subtracted before the question is asked (D-27). The
    /// subtraction is the only direction that is safe: an injection lane this
    /// crate forgets to name still lands in the total and still arms the gate.
    pub(crate) user_written_false_obligations: usize,
}

/// The conjunction of `obligations` (ignoring literal `true`), or `None`.
pub(crate) fn conjoin_obligations(obligations: &[PureExpr]) -> Option<PureExpr> {
    obligations
        .iter()
        .filter(|ob| !matches!(ob, PureExpr::Bool(true)))
        .cloned()
        .reduce(|acc, ob| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(ob)))
}

/// Rewrite every assumption `a` to `guard ==> a` (a literal `true` stays).
/// SOUND: the guarded premise is implied by the unguarded one.
pub(crate) fn guard_assumptions(assumptions: &mut [PureExpr], guard: Option<&PureExpr>) {
    let Some(guard) = guard else {
        return;
    };
    let guard_free = guard.free_vars();
    for assumption in assumptions.iter_mut() {
        if matches!(assumption, PureExpr::Bool(true)) {
            continue;
        }
        let post = std::mem::replace(assumption, PureExpr::Bool(true));
        *assumption = guard_under_leading_foralls(guard, &guard_free, post);
    }
}

/// `guard ==> post`, with the implication moved under the universal binders
/// `post` starts with: `guard ==> forall x. p` is `forall x. guard ==> p`
/// whenever `x` is not free in `guard`. ay instantiates a quantifier it meets
/// at the top of an assumption and answers `unknown` for one under an
/// implication, so a call whose postcondition quantifies (`from_elem`,
/// `reserve`) would otherwise make every goal after a precondition unknown.
/// A binder the guard mentions stops the descent: renaming it is not needed
/// for soundness, and the implication then stays outside, as it always was.
fn guard_under_leading_foralls(
    guard: &PureExpr,
    guard_free: &std::collections::HashSet<String>,
    post: PureExpr,
) -> PureExpr {
    match post {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } if !guard_free.contains(&var) => PureExpr::Forall {
            body: Arc::new(guard_under_leading_foralls(
                guard,
                guard_free,
                Arc::unwrap_or_clone(body),
            )),
            var,
            var_sort,
            triggers,
        },
        post => PureExpr::BinOp(Arc::new(guard.clone()), BinOp::Implies, Arc::new(post)),
    }
}

/// The fail-closed `false` marker of a lane that builds it outside
/// [`CallEffects::record_injected_fail_closed_obligation`], named for
/// `TRUST_WP_AUTHORITY_TRACE`.
pub(crate) fn fail_closed_marker(site: &'static str) -> PureExpr {
    if std::env::var_os("TRUST_WP_AUTHORITY_TRACE").is_some() {
        eprintln!("[TWP_AUTH] driver injected fail-closed `false` obligation at lane `{site}`");
    }
    PureExpr::Bool(false)
}

impl CallEffects {
    /// Create an empty `CallEffects`.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Clear all accumulated effects. Currently used only in tests.
    #[cfg(test)]
    pub(crate) fn clear(&mut self) {
        self.assumptions.clear();
        self.obligations.clear();
        self.has_mutating_call_effect = false;
        self.dropped_spec_clauses = 0;
        self.dropped_clauses.clear();
        self.mapping_closures.clear();
        self.map_inv_closures.clear();
        self.map_inv_collect_sites.clear();
        self.mut_ref_result_receivers.clear();
        self.returning_path_facts.clear();
        self.user_written_false_obligations = 0;
    }

    /// Scope the postcondition assumptions ONE call just produced
    /// (`assumptions[assumptions_before..]`) under that call's own
    /// preconditions (`obligations[obligations_before..]`): each becomes
    /// `pre_1 && .. && pre_n ==> post`.
    ///
    /// The primary extractor keeps call effects in flat lists, and the
    /// verifier proves every obligation under every assumption. Without this
    /// scoping a callee's postcondition is a premise of the proof of its own
    /// precondition, although by the weakest-precondition rule
    /// `wp(call) = pre && (post ==> Q)` the postcondition is only available
    /// after the precondition holds. `v.remove(0)` on a possibly empty `Vec`
    /// verifies that way: `(^v)@.len() == v@.len() - 1` with `len >= 0`
    /// entails the owed `0 < v@.len()`.
    ///
    /// SOUND: the guarded premise is implied by the unguarded one, so this
    /// only removes derivations. Whenever the preconditions are proved (their
    /// own obligations), the guard is discharged and the postcondition is
    /// available as if it had never been guarded.
    pub(crate) fn scope_call_postconditions_under_preconditions(
        &mut self,
        obligations_before: usize,
        assumptions_before: usize,
    ) {
        if assumptions_before >= self.assumptions.len() {
            return;
        }
        // Every obligation recorded so far is a guard, not only this call's
        // own preconditions: an obligation recorded BEFORE the call (an
        // earlier call's precondition, a bounds check, a panic arm) must be
        // proved from facts established at its own program point, never from
        // a later call's postcondition (`let x = v[0]; nonempty(v);`). In the
        // weakest-precondition sequence `ob_1 && (post_1 ==> ob_2 && (post_2
        // ==> Q))` each postcondition is available only under every earlier
        // obligation. The call's own preconditions are the suffix
        // `obligations[obligations_before..]`.
        let _ = obligations_before;
        let guard = conjoin_obligations(&self.obligations);
        guard_assumptions(&mut self.assumptions[assumptions_before..], guard.as_ref());
    }

    /// Record a `Mapping::from_closure` body extraction result (#2316).
    pub(crate) fn record_mapping_closure(
        &mut self,
        result_var: PureExpr,
        body_expr: PureExpr,
        param_names: Vec<String>,
    ) {
        self.mapping_closures.push(MappingClosureInfo {
            result_var,
            body_expr,
            param_names,
        });
    }

    /// Record a `map_inv(iter, closure)` per-element ensures result (#2170).
    pub(crate) fn record_map_inv_closure(
        &mut self,
        result_var: PureExpr,
        call_block: rustc_middle::mir::BasicBlock,
        produced_len: Option<PureExpr>,
        produced_len_guard: Option<PureExpr>,
        ensures_exprs: Vec<PureExpr>,
        closure_param_names: Vec<String>,
    ) {
        self.map_inv_closures.push(MapInvClosureInfo {
            result_var,
            call_block,
            produced_len,
            produced_len_guard,
            ensures_exprs,
            closure_param_names,
        });
    }

    /// Every recorded `map_inv` info whose result symbol is the translated
    /// collect receiver `source` (a plain variable). The caller must refuse
    /// to state facts unless exactly one DISTINCT info matches: a symbol
    /// recorded with different contents (the same `map_inv` block extracted
    /// on paths with different bound expressions) is ambiguous.
    pub(crate) fn map_inv_infos_for(&self, source: &PureExpr) -> Vec<&MapInvClosureInfo> {
        let PureExpr::Var(source_name, _) = source else {
            return Vec::new();
        };
        self.map_inv_closures
            .iter()
            .filter(
                |info| matches!(&info.result_var, PureExpr::Var(name, _) if name == source_name),
            )
            .collect()
    }

    /// Record one extraction of a `map_inv` collect site (deduplicated).
    /// `facts` is empty when this extraction could not state facts; that
    /// entry then poisons the site.
    pub(crate) fn record_map_inv_collect_site(&mut self, site: String, facts: Vec<PureExpr>) {
        let entry = (site, facts);
        if !self.map_inv_collect_sites.contains(&entry) {
            self.map_inv_collect_sites.push(entry);
        }
    }

    /// Function-level assumptions from `map_inv` collect sites. Fail closed:
    /// a site contributes only when every recorded extraction
    /// of it produced the SAME non-empty fact list. Two paths reaching one
    /// collect terminator with different sources, or any extraction that
    /// stated nothing, drop the site's facts entirely; the site symbol is
    /// then unconstrained.
    pub(crate) fn map_inv_collect_assumptions(&self) -> Vec<PureExpr> {
        let mut out: Vec<PureExpr> = Vec::new();
        for (site, facts) in &self.map_inv_collect_sites {
            if facts.is_empty() {
                continue;
            }
            let distinct = self
                .map_inv_collect_sites
                .iter()
                .filter(|(other, _)| other == site)
                .count();
            if distinct != 1 {
                continue;
            }
            for fact in facts {
                if !out.contains(fact) {
                    out.push(fact.clone());
                }
            }
        }
        out
    }

    /// Push the fail-closed `false` obligation that marks a construct this
    /// extractor could not model, and COUNT it.
    ///
    /// The marker is correct and must never be dropped: it is what makes the
    /// caller unprovable instead of vacuously proved. What it must not do is
    /// license a refutation — `false` is refutable in every model, so a SAT
    /// answer over it refutes a clause trust-wp wrote, not one the program
    /// broke. The verdict gate reads this COUNT (`ParsedContract::
    /// injected_fail_closed_obligations`), which is why the marker is recorded
    /// here rather than recovered later by scanning the obligation list: a
    /// scan cannot tell this `false` from a callee's user-written
    /// `#[requires(false)]`.
    ///
    /// `site` names the lane for `TRUST_WP_AUTHORITY_TRACE`.
    pub(crate) fn record_injected_fail_closed_obligation(&mut self, site: &'static str) {
        if std::env::var_os("TRUST_WP_AUTHORITY_TRACE").is_some() {
            eprintln!("[TWP_AUTH] driver injected fail-closed `false` obligation at lane `{site}`");
        }
        self.obligations.push(PureExpr::Bool(false));
    }

    /// Push a callee precondition the USER wrote, counting it when it is the
    /// literal `false` the verdict gate would otherwise read as a marker.
    pub(crate) fn record_user_written_obligation(&mut self, obligation: PureExpr) {
        if matches!(obligation, PureExpr::Bool(false)) {
            if std::env::var_os("TRUST_WP_AUTHORITY_TRACE").is_some() {
                eprintln!(
                    "[TWP_AUTH] callee precondition substitutes to the literal `false`; \
                     it is a clause somebody WROTE, not an injected marker"
                );
            }
            self.user_written_false_obligations += 1;
        }
        self.obligations.push(obligation);
    }

    /// Record a dropped clause with provenance and emit a synthetic
    /// `false` obligation so dropped clauses fail-closed rather than
    /// being silently ignored.
    pub(crate) fn record_dropped_clause(
        &mut self,
        kind: DroppedClauseKind,
        clause: String,
        reason: String,
    ) {
        if std::env::var_os("TRUST_WP_AUTHORITY_TRACE").is_some() {
            eprintln!("[TWP_AUTH] dropped {kind:?} clause `{clause}`: {reason}");
        }
        self.dropped_clauses.push(DroppedClause {
            kind,
            clause,
            reason,
        });
        self.dropped_spec_clauses = self.dropped_clauses.len();
        // Fail-closed: a dropped obligation means verification is
        // incomplete. Insert `false` as an obligation so the solver
        // reports this function as failed rather than verified.
        self.record_injected_fail_closed_obligation("dropped-spec-clause");
    }
}

/// Explicit extraction session state shared across call-site helpers.
///
/// Passed explicitly through `mir_analysis` extraction code so every helper
/// reads and writes the same effects the caller drains; nothing is held in a
/// thread-local.
pub(crate) struct ExtractionSession<'a> {
    /// Extern specs available for call resolution during extraction.
    pub(crate) extern_specs: &'a HashMap<String, StdSpec>,
    /// Call-site assumptions/obligations collected while extracting.
    pub(crate) effects: &'a mut CallEffects,
}

impl<'a> ExtractionSession<'a> {
    pub(crate) fn new(
        extern_specs: &'a HashMap<String, StdSpec>,
        effects: &'a mut CallEffects,
    ) -> Self {
        Self {
            extern_specs,
            effects,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn forall(var: &str, body: PureExpr) -> PureExpr {
        PureExpr::Forall {
            var: var.to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: Vec::new(),
        }
    }

    fn implies(left: PureExpr, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), BinOp::Implies, Arc::new(right))
    }

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    #[test]
    fn a_guard_moves_under_the_universal_binders_it_does_not_mention() {
        let guard = var("n_ok");
        let mut assumptions = vec![forall("i", forall("j", var("p")))];
        guard_assumptions(&mut assumptions, Some(&guard));
        assert_eq!(
            assumptions,
            vec![forall("i", forall("j", implies(var("n_ok"), var("p"))))]
        );
    }

    #[test]
    fn a_binder_the_guard_mentions_keeps_the_implication_outside_it() {
        let guard = var("i");
        let mut assumptions = vec![forall("i", var("p"))];
        guard_assumptions(&mut assumptions, Some(&guard));
        assert_eq!(assumptions, vec![implies(var("i"), forall("i", var("p")))]);
    }

    #[test]
    fn call_effects_default_is_empty() {
        let effects = CallEffects::new();
        assert!(effects.assumptions.is_empty());
        assert!(effects.obligations.is_empty());
        assert_eq!(effects.dropped_spec_clauses, 0);
    }

    #[test]
    fn call_effects_default_has_empty_dropped_clauses() {
        let effects = CallEffects::new();
        assert!(effects.dropped_clauses.is_empty());
        assert!(effects.mut_ref_result_receivers.is_empty());
    }

    fn site_fact(n: i64) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("call_1_collect_bb2".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(n)),
        )
    }

    /// Two extractions of one collect site with DIFFERENT facts (two branch
    /// sources) must contribute nothing.
    #[test]
    fn map_inv_collect_site_with_conflicting_entries_states_nothing() {
        let mut effects = CallEffects::new();
        effects.record_map_inv_collect_site("call_1_collect_bb2".into(), vec![site_fact(3)]);
        effects.record_map_inv_collect_site("call_1_collect_bb2".into(), vec![site_fact(5)]);
        assert!(effects.map_inv_collect_assumptions().is_empty());
    }

    /// An extraction that stated nothing poisons the site.
    #[test]
    fn map_inv_collect_site_with_empty_entry_states_nothing() {
        let mut effects = CallEffects::new();
        effects.record_map_inv_collect_site("call_1_collect_bb2".into(), vec![site_fact(3)]);
        effects.record_map_inv_collect_site("call_1_collect_bb2".into(), Vec::new());
        assert!(effects.map_inv_collect_assumptions().is_empty());
    }

    /// Identical repeated extractions keep the facts; other sites are
    /// independent.
    #[test]
    fn map_inv_collect_site_consistent_entries_state_facts() {
        let mut effects = CallEffects::new();
        effects.record_map_inv_collect_site("call_1_collect_bb2".into(), vec![site_fact(3)]);
        effects.record_map_inv_collect_site("call_1_collect_bb2".into(), vec![site_fact(3)]);
        effects.record_map_inv_collect_site("call_4_collect_bb9".into(), Vec::new());
        assert_eq!(effects.map_inv_collect_assumptions(), vec![site_fact(3)]);
    }

    #[test]
    fn call_effects_clear_resets_all_fields() {
        let mut effects = CallEffects {
            assumptions: vec![PureExpr::Bool(true)],
            obligations: vec![PureExpr::Bool(false)],
            user_written_false_obligations: 0,
            has_mutating_call_effect: true,
            dropped_spec_clauses: 3,
            map_inv_closures: Vec::new(),
            map_inv_collect_sites: vec![("s".to_string(), vec![PureExpr::Bool(true)])],
            dropped_clauses: vec![DroppedClause {
                kind: DroppedClauseKind::Precondition,
                clause: "x > 0".to_string(),
                reason: "parse error".to_string(),
            }],
            mapping_closures: Vec::new(),
            mut_ref_result_receivers: HashMap::new(),
            returning_path_facts: vec![PureExpr::Bool(true)],
        };
        effects.clear();
        assert!(effects.assumptions.is_empty());
        assert!(effects.obligations.is_empty());
        assert_eq!(effects.dropped_spec_clauses, 0);
        assert!(effects.dropped_clauses.is_empty());
        assert!(effects.mapping_closures.is_empty());
        assert!(effects.mut_ref_result_receivers.is_empty());
        assert!(effects.returning_path_facts.is_empty());
    }

    #[test]
    fn record_dropped_clause_adds_provenance_and_false_obligation() {
        let mut effects = CallEffects::new();
        effects.record_dropped_clause(
            DroppedClauseKind::Precondition,
            "x > 0".to_string(),
            "unresolved name: x".to_string(),
        );
        assert_eq!(effects.dropped_spec_clauses, 1);
        assert_eq!(effects.dropped_clauses.len(), 1);
        assert_eq!(
            effects.dropped_clauses[0].kind,
            DroppedClauseKind::Precondition
        );
        assert_eq!(effects.dropped_clauses[0].clause, "x > 0");
        // Fail-closed: synthetic false obligation added
        assert_eq!(effects.obligations.len(), 1);
        assert_eq!(effects.obligations[0], PureExpr::Bool(false));
    }

    #[test]
    fn record_dropped_clause_multiple_accumulates() {
        let mut effects = CallEffects::new();
        effects.record_dropped_clause(
            DroppedClauseKind::Precondition,
            "x > 0".to_string(),
            "parse error".to_string(),
        );
        effects.record_dropped_clause(
            DroppedClauseKind::Postcondition,
            "result == x + 1".to_string(),
            "unresolved: result".to_string(),
        );
        assert_eq!(effects.dropped_spec_clauses, 2);
        assert_eq!(effects.dropped_clauses.len(), 2);
        assert_eq!(effects.obligations.len(), 2);
        // Both are false obligations
        assert!(effects
            .obligations
            .iter()
            .all(|o| *o == PureExpr::Bool(false)));
    }

    #[test]
    fn mapping_closure_to_forall_axiom_basic() {
        let info = MappingClosureInfo {
            result_var: PureExpr::Var("_call_5".into(), None),
            body_expr: PureExpr::BinOp(
                Arc::new(PureExpr::Var("k".into(), Some(ExprSort::Int))),
                BinOp::Mul,
                Arc::new(PureExpr::Int(2)),
            ),
            param_names: vec!["k".into()],
        };
        let axiom = info.to_forall_axiom().expect("should produce axiom");
        match &axiom {
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                assert_eq!(var, "k");
                assert_eq!(*var_sort, Some(ExprSort::Int));
                assert_eq!(triggers.len(), 1);
                // Body is: mapping.get(k) == k * 2
                match body.as_ref() {
                    PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
                        match lhs.as_ref() {
                            PureExpr::MethodCall { method, args, .. } => {
                                assert_eq!(method, "get");
                                assert_eq!(args.len(), 1);
                            }
                            other => panic!("expected MethodCall, got {other:?}"),
                        }
                        match rhs.as_ref() {
                            PureExpr::BinOp(_, BinOp::Mul, _) => {}
                            other => panic!("expected BinOp Mul, got {other:?}"),
                        }
                    }
                    other => panic!("expected BinOp Eq, got {other:?}"),
                }
            }
            other => panic!("expected Forall, got {other:?}"),
        }
    }

    #[test]
    fn mapping_closure_to_forall_axiom_empty_params() {
        let info = MappingClosureInfo {
            result_var: PureExpr::Var("_call_5".into(), None),
            body_expr: PureExpr::Int(42),
            param_names: vec![],
        };
        assert!(info.to_forall_axiom().is_none());
    }
}
