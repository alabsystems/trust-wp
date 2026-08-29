// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Explicit call-effect context for extraction.
//!
//! Replaces implicit thread-local side channels (`CALL_ASSUMPTIONS`,
//! `CALL_OBLIGATIONS`) with an explicit struct that extraction code
//! writes into and callers read from. `SPEC_DROP_WARNINGS` was removed
//! entirely in #1712.
//!
//! See: designs/2026-02-17-callbacks-mir-analysis-boundary.md

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
/// (#2316 Phase 2)
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
#[derive(Debug, Clone)]
pub(crate) struct MapInvClosureInfo {
    /// The result variable representing the `MapInv` value (e.g., `call_3`).
    pub(crate) result_var: PureExpr,
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
    pub(crate) fn to_view_axioms(&self) -> Vec<PureExpr> {
        let mut axioms = Vec::new();

        // The collected sequence value. After `.collect()`, the consuming code
        // holds the result as `result_var@` (the iterator view bridged by
        // `collect`'s `result@ == self@`): a `Seq` whose elements are the
        // produced values. A downstream collection field assignment stores
        // exactly that Seq, so the consumer reads `field` == `result_var@`.
        // The per-element view is therefore rooted at `result_view =
        // result_var@`; indexing it gives the i-th produced element, and a
        // further `@` gives that element's own view.
        let result_view = PureExpr::View(Arc::new(self.result_var.clone()));

        // The collected value's length is `result_var@.len()` — a single view.
        // `field` IS `result_var@` (the collected Seq), and the consumer reads
        // its length as `seq_len(field)`. Viewing once more (`result_var@@`)
        // would be one level too deep — it would denote the length of the view
        // of the collected Seq, not the collected Seq itself — and would not
        // unify with the `seq_len(field)` the obligation reads. (#2170)
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
    /// Extraction-only map from mut-ref result temps to the receiver they
    /// mutate. Used to commit writes like `*call_16 = 2` back into the
    /// receiver state during successor extraction.
    pub(crate) mut_ref_result_receivers: HashMap<String, PureExpr>,
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
        self.mut_ref_result_receivers.clear();
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
        produced_len: Option<PureExpr>,
        produced_len_guard: Option<PureExpr>,
        ensures_exprs: Vec<PureExpr>,
        closure_param_names: Vec<String>,
    ) {
        self.map_inv_closures.push(MapInvClosureInfo {
            result_var,
            produced_len,
            produced_len_guard,
            ensures_exprs,
            closure_param_names,
        });
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
        self.dropped_clauses.push(DroppedClause {
            kind,
            clause,
            reason,
        });
        self.dropped_spec_clauses = self.dropped_clauses.len();
        // Fail-closed: a dropped obligation means verification is
        // incomplete. Insert `false` as an obligation so the solver
        // reports this function as failed rather than verified.
        self.obligations.push(PureExpr::Bool(false));
    }
}

/// Explicit extraction session state shared across call-site helpers.
///
/// This replaces callback-owned thread-locals with an explicit context
/// passed through `mir_analysis` extraction code.
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

    #[test]
    fn call_effects_clear_resets_all_fields() {
        let mut effects = CallEffects {
            assumptions: vec![PureExpr::Bool(true)],
            obligations: vec![PureExpr::Bool(false)],
            has_mutating_call_effect: true,
            dropped_spec_clauses: 3,
            map_inv_closures: Vec::new(),
            dropped_clauses: vec![DroppedClause {
                kind: DroppedClauseKind::Precondition,
                clause: "x > 0".to_string(),
                reason: "parse error".to_string(),
            }],
            mapping_closures: Vec::new(),
            mut_ref_result_receivers: HashMap::new(),
        };
        effects.clear();
        assert!(effects.assumptions.is_empty());
        assert!(effects.obligations.is_empty());
        assert_eq!(effects.dropped_spec_clauses, 0);
        assert!(effects.dropped_clauses.is_empty());
        assert!(effects.mapping_closures.is_empty());
        assert!(effects.mut_ref_result_receivers.is_empty());
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
