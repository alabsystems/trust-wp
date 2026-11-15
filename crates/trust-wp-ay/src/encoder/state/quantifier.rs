// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use trust_wp_core::formula::{ExprSort, PureExpr};

/// Diagnostic record for synthesized trigger patterns used while encoding a quantifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SynthesizedTriggerDiagnostic {
    /// Bound variables collected for the quantifier whose triggers were synthesized.
    pub vars: Vec<String>,
    /// Trigger patterns selected by synthesis before ay term encoding.
    pub patterns: Vec<Vec<PureExpr>>,
}

/// The sort recorded for a written binder. An unknown sort remains distinct
/// from the absence of a written binder, which the lookup's outer Option names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WrittenBinderSort<'a> {
    Unannotated,
    Annotated(&'a ExprSort),
}

/// Quantifier variable naming and scope tracking state (#840, #2655).
///
/// Groups the fields used exclusively by quantifier encoding: a counter
/// for unique variable names, a depth-tracked set of currently-bound
/// variables, and nesting depth counters that control ground-pool
/// registration and invariant body inlining.
///
/// All fields private; access through typed methods. (#1584)
pub(crate) struct QuantifierState {
    /// Counter for generating unique quantifier variable names (qvar_0, qvar_1, ...).
    counter: usize,
    /// Variable names currently bound by enclosing quantifiers, with nesting depth.
    ///
    /// When encoding View(Var(v)) inside a quantifier scope where v is bound,
    /// the view collapses to the bound variable itself (the bound variable already
    /// represents the logical value). Without this, View normalization creates a
    /// fresh `v_view` variable that ay doesn't recognize as the bound variable,
    /// causing trigger validation failures. (#579)
    ///
    /// Uses a depth counter (not a set) so that nested quantifiers binding the
    /// same variable name don't prematurely remove the outer binding when the
    /// inner quantifier's cleanup runs. (#579 audit)
    bound_vars: HashMap<String, usize>,
    /// Per-top-level-encoding record of synthesized trigger patterns.
    synthesized_triggers: Vec<SynthesizedTriggerDiagnostic>,
    /// Nesting depth of quantifier body encoding contexts.
    ///
    /// Incremented when encoding inside a quantifier scope (e.g., logic fn
    /// body, spec axiom body, type invariant body) where variables are bound.
    /// When > 0, inner `LogicFnCall` applications should NOT be registered
    /// with the ground pool because their arguments are bound variables,
    /// not ground terms. (#1965, Lane 5, #2655)
    quantifier_depth: usize,
    /// Depth of existential quantifier nesting. When > 0, invariant body
    /// inlining fires in `encode_bool_method_predicate` (#726). Forall scopes
    /// do NOT increment this -- ay-dpll handles forall via Skolemization +
    /// E-matching, which requires UF applications to remain as triggers.
    /// (#2655)
    exists_quantifier_depth: usize,
    /// Subset of `bound_vars` that are MATCH-ARM PATTERN BINDERS (bound to a
    /// destructor payload projection), with nesting depth. Distinguished from
    /// logic-fn formals / genuine quantifier binders for the Final-collapse
    /// audit Fix A guard: only the match-binder collapse target is a payload
    /// with NO prophecy slot, where collapsing `^v` onto the current-value
    /// projection asserts the inversion `^v == *v` (take_first_mut). The
    /// logic-fn-formal collapse lane is driver-split and stays untouched.
    match_binder_vars: HashMap<String, usize>,
    /// Subset of `bound_vars` bound by a `forall`/`exists` the contract text
    /// writes, innermost scope last, each with the sort the text wrote for it.
    /// Such a binder ranges over every value of its type, a borrow's final
    /// value included, so `^q` of one is never the binder itself unless that
    /// sort certainly holds no borrow (D-127); a logic-fn formal or an
    /// instantiation parameter is bound elsewhere and keeps the driver-split
    /// reading.
    written_binder_vars: HashMap<String, Vec<Option<ExprSort>>>,
    /// Nesting depth of BINDER-ERASING SUBSTITUTION scopes (tract19).
    ///
    /// Several lanes discharge a logically-bound expression by substituting a
    /// ground value for the binder at the PureExpr level and re-encoding the
    /// result: the existential witness probe (`pure_quantifier.rs`, `x := 0/1/-1`
    /// or a harvested ground index) and recursive logic-fn ground unfolding
    /// (`logic_fn/ground_instances.rs`, formals := call arguments).
    ///
    /// Those substitutions run BEFORE encoding, so a body mentioning `^x`
    /// arrives as `Final(Int(c))` with the binder gone, and Phase 1's rule
    /// "quantifier-bound variables and logic-fn formals are pure logical values
    /// without temporal state, so `Final(Var(v)) -> v`" can no longer recognise
    /// it.
    ///
    /// This flag restores that recognition, and ONLY that. A temporal wrapper
    /// over a literal inside such a scope is the substituted image of a wrapper
    /// over a BOUND VARIABLE, which Phase 1 already collapses — licensing it
    /// here changes no soundness property, it just keeps the lane working.
    /// Everywhere else a wrapper over a literal is the driver's substituted
    /// value of a BORROWED PLACE, where `Final` must refuse fail-closed
    /// (`AYEncoder::refuse_prophecy_over_constant`). The flag is deliberately a
    /// scope marker and NOT ambient quantifier depth: a user postcondition
    /// wrapped in `forall<i> ...` must stay refused.
    binder_substitution_depth: usize,
}

impl QuantifierState {
    pub(crate) fn new() -> Self {
        Self {
            counter: 0,
            bound_vars: HashMap::new(),
            synthesized_triggers: Vec::new(),
            quantifier_depth: 0,
            exists_quantifier_depth: 0,
            match_binder_vars: HashMap::new(),
            written_binder_vars: HashMap::new(),
            binder_substitution_depth: 0,
        }
    }

    /// Allocate the next unique quantifier variable ID.
    ///
    /// Each call returns a monotonically increasing ID used for
    /// generating unique SMT variable names (`qvar_{name}_{id}`).
    pub(in crate::encoder) fn next_id(&mut self) -> usize {
        let id = self.counter;
        self.counter += 1;
        id
    }

    /// Record a variable as bound in a quantifier scope, incrementing its nesting depth.
    ///
    /// Returns the previous depth (0 if newly bound). The depth counter prevents
    /// nested quantifiers binding the same name from interfering with each other.
    pub(in crate::encoder) fn bind_var(&mut self, var: String) -> usize {
        let depth = self.bound_vars.entry(var).or_insert(0);
        let prev = *depth;
        *depth += 1;
        prev
    }

    /// Decrement the binding depth of a variable. Removes the entry when depth reaches 0.
    ///
    /// # Panics
    ///
    /// Panics if the variable is not currently bound (invariant violation).
    pub(in crate::encoder) fn unbind_var(&mut self, var: &str) {
        let depth = self
            .bound_vars
            .get_mut(var)
            .expect("invariant: bound variable must exist during quantifier cleanup");
        *depth -= 1;
        if *depth == 0 {
            self.bound_vars.remove(var);
        }
    }

    /// Check if a specific variable is currently bound in a quantifier scope.
    pub(in crate::encoder) fn is_bound(&self, var: &str) -> bool {
        self.bound_vars.get(var).copied().unwrap_or(0) > 0
    }

    /// Record a variable as a match-arm pattern binder (Fix A guard scope).
    pub(in crate::encoder) fn bind_match_binder(&mut self, var: String) {
        *self.match_binder_vars.entry(var).or_insert(0) += 1;
    }

    /// Decrement the match-binder depth; removes the entry at 0.
    ///
    /// # Panics
    ///
    /// Panics if the variable is not currently marked (invariant violation).
    pub(in crate::encoder) fn unbind_match_binder(&mut self, var: &str) {
        let depth = self
            .match_binder_vars
            .get_mut(var)
            .expect("invariant: match binder must exist during match-arm cleanup");
        *depth -= 1;
        if *depth == 0 {
            self.match_binder_vars.remove(var);
        }
    }

    /// Check if a variable is currently a match-arm pattern binder.
    pub(in crate::encoder) fn is_match_binder(&self, var: &str) -> bool {
        self.match_binder_vars.get(var).copied().unwrap_or(0) > 0
    }

    /// Record a variable as bound by a written `forall`/`exists`, with the
    /// sort the text wrote for it (`None` where it wrote none or the parser
    /// did not keep it).
    pub(in crate::encoder) fn bind_written_binder(&mut self, var: String, sort: Option<ExprSort>) {
        self.written_binder_vars.entry(var).or_default().push(sort);
    }

    /// Pop the innermost written binding of `var`; removes the entry when
    /// none is left.
    ///
    /// # Panics
    ///
    /// Panics if the variable is not currently marked (invariant violation).
    pub(in crate::encoder) fn unbind_written_binder(&mut self, var: &str) {
        let scopes = self
            .written_binder_vars
            .get_mut(var)
            .expect("invariant: written binder must exist during quantifier cleanup");
        scopes.pop();
        if scopes.is_empty() {
            self.written_binder_vars.remove(var);
        }
    }

    /// The innermost written binding of `var`, keeping an unannotated written
    /// `forall`/`exists` distinct from an absent written binder.
    pub(in crate::encoder) fn written_binder(&self, var: &str) -> Option<WrittenBinderSort<'_>> {
        self.written_binder_vars
            .get(var)
            .and_then(|scopes| scopes.last())
            .map(|sort| match sort {
                None => WrittenBinderSort::Unannotated,
                Some(sort) => WrittenBinderSort::Annotated(sort),
            })
    }

    /// Check if any variables are currently bound in a quantifier scope.
    pub(in crate::encoder) fn has_bound_vars(&self) -> bool {
        !self.bound_vars.is_empty()
    }

    /// Clear synthesized-trigger diagnostics before a new top-level encode.
    pub(in crate::encoder) fn clear_synthesized_triggers(&mut self) {
        self.synthesized_triggers.clear();
    }

    /// Record synthesized trigger patterns used for one quantifier.
    pub(in crate::encoder) fn record_synthesized_triggers(
        &mut self,
        vars: &[String],
        patterns: &[Vec<PureExpr>],
    ) {
        self.synthesized_triggers
            .push(SynthesizedTriggerDiagnostic {
                vars: vars.to_vec(),
                patterns: patterns.to_vec(),
            });
    }

    /// Return synthesized-trigger diagnostics from the most recent top-level encode.
    #[cfg(test)]
    pub(in crate::encoder) fn synthesized_triggers(&self) -> &[SynthesizedTriggerDiagnostic] {
        &self.synthesized_triggers
    }

    // ── Quantifier depth tracking (#2655) ──────────────────────────────

    /// Current quantifier nesting depth. When > 0, the encoder is inside
    /// a quantifier body and ground-pool registration should be suppressed.
    pub(in crate::encoder) fn quantifier_depth(&self) -> usize {
        self.quantifier_depth
    }

    /// Increment quantifier nesting depth (entering a quantifier body).
    pub(in crate::encoder) fn inc_quantifier_depth(&mut self) {
        self.quantifier_depth += 1;
    }

    /// Decrement quantifier nesting depth (leaving a quantifier body).
    pub(in crate::encoder) fn dec_quantifier_depth(&mut self) {
        self.quantifier_depth -= 1;
    }

    /// Current existential quantifier nesting depth. When > 0, invariant
    /// body inlining fires in `encode_bool_method_predicate`.
    pub(in crate::encoder) fn exists_quantifier_depth(&self) -> usize {
        self.exists_quantifier_depth
    }

    /// Increment existential quantifier nesting depth.
    pub(in crate::encoder) fn inc_exists_quantifier_depth(&mut self) {
        self.exists_quantifier_depth += 1;
    }

    /// Decrement existential quantifier nesting depth.
    pub(in crate::encoder) fn dec_exists_quantifier_depth(&mut self) {
        self.exists_quantifier_depth -= 1;
    }

    /// Whether encoding is inside a binder-erasing substitution scope. See
    /// [`Self::binder_substitution_depth`]. (tract19)
    pub(in crate::encoder) fn in_binder_substitution(&self) -> bool {
        self.binder_substitution_depth > 0
    }

    /// Enter a binder-erasing substitution scope.
    pub(in crate::encoder) fn inc_binder_substitution_depth(&mut self) {
        self.binder_substitution_depth += 1;
    }

    /// Leave a binder-erasing substitution scope.
    pub(in crate::encoder) fn dec_binder_substitution_depth(&mut self) {
        self.binder_substitution_depth -= 1;
    }

    /// Test-only: set quantifier depth directly for testing ground-pool guards. (#2655)
    #[cfg(test)]
    pub(in crate::encoder) fn set_quantifier_depth(&mut self, depth: usize) {
        self.quantifier_depth = depth;
    }
}

#[cfg(test)]
mod written_binder_tests {
    use super::*;

    #[test]
    fn unknown_inner_binder_never_inherits_an_outer_sort() {
        let mut state = QuantifierState::new();
        assert_eq!(state.written_binder("q"), None);
        state.bind_written_binder("q".into(), Some(ExprSort::Int));
        assert_eq!(
            state.written_binder("q"),
            Some(WrittenBinderSort::Annotated(&ExprSort::Int))
        );
        state.bind_written_binder("q".into(), None);
        assert_eq!(
            state.written_binder("q"),
            Some(WrittenBinderSort::Unannotated)
        );
        state.bind_written_binder("q".into(), Some(ExprSort::Bool));
        assert_eq!(
            state.written_binder("q"),
            Some(WrittenBinderSort::Annotated(&ExprSort::Bool))
        );
        state.unbind_written_binder("q");
        assert_eq!(
            state.written_binder("q"),
            Some(WrittenBinderSort::Unannotated)
        );
        state.unbind_written_binder("q");
        assert_eq!(
            state.written_binder("q"),
            Some(WrittenBinderSort::Annotated(&ExprSort::Int))
        );
        state.unbind_written_binder("q");
        assert_eq!(state.written_binder("q"), None);
    }
}
