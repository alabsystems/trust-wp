// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort hint registration and mutation helpers.

use std::collections::HashSet;

#[cfg(any(test, feature = "sep-logic"))]
use trust_wp_core::formula::Formula;
use trust_wp_core::formula::{ExprSort, PureExpr};

#[cfg(any(test, feature = "sep-logic"))]
use super::hint_collection::collect_formula_sort_hints;
use super::{
    hint_collection::{collect_all_sort_hints, collect_names_as_bool, SortHintAccumulator},
    mapping_expr_sort, DerivedKind,
};
use crate::encoder::AYEncoder;

/// Propagate sort hints from derived names back to base names. (#994, #1948)
/// Fixed-point loop: keep propagating until no new names are produced.
/// Rules:
///   `final_{x}_view` -> `{x}_view`   (strip final_ prefix)
///   `{x}_view` -> `{x}`              (strip _view suffix)
/// The `_view -> base` rule skips names ending with `_current` to prevent
/// over-tagging of mut-ref dereferenced values. (#1948)
fn propagate_name_chain_hints(names: &mut HashSet<String>) {
    loop {
        let mut new_names = Vec::new();
        for name in names.iter() {
            if let Some(derived) = DerivedKind::peel_final_view_prefix(name) {
                if !names.contains(&derived) {
                    new_names.push(derived);
                }
            } else if let Some((DerivedKind::View, rest)) = DerivedKind::strip_from(name) {
                if !matches!(
                    DerivedKind::strip_from(rest),
                    Some((DerivedKind::Current, _))
                ) {
                    let derived = rest.to_string();
                    if !names.contains(&derived) {
                        new_names.push(derived);
                    }
                }
            }
        }
        if new_names.is_empty() {
            break;
        }
        for name in new_names {
            names.insert(name);
        }
    }
}

fn promote_ambiguous_seq_hints(acc: &mut SortHintAccumulator) {
    let candidates: Vec<String> = acc.ambiguous_seqs.iter().cloned().collect();
    for name in candidates {
        if acc.seqs.contains(&name)
            || acc.fmaps.contains(&name)
            || acc.mappings.contains(&name)
            || acc.bool_vars.contains(&name)
        {
            continue;
        }
        let view_name = DerivedKind::View.format_name(&name);
        if acc.fmaps.contains(&view_name) {
            acc.fmaps.insert(name);
        } else if acc.seqs.contains(&view_name) {
            acc.seqs.insert(name);
        }
    }
}

pub(crate) fn collect_registered_sort_hints<'a>(
    exprs: impl IntoIterator<Item = &'a PureExpr>,
) -> SortHintAccumulator {
    let mut acc = SortHintAccumulator::new();
    for expr in exprs {
        collect_all_sort_hints(expr, &mut acc);
    }
    // Evidence-complete Bool veto: variables compared (Eq/Ne) against an
    // integer literal outside {0,1} cannot be Bool — strip them from the
    // heuristic Bool mint BEFORE propagation/promotion, as if the spurious
    // hint had never been minted. Without this, hash-iteration order of the
    // driver ghost maps decides whether the Bool hint lands on a variable
    // that also carries a `== 2`-style premise, and when it does the premise
    // is fabricated away (`__trust_wp_unencodable_eq_*`), yielding a
    // model-validated false counterexample (arc_and_rc flake).
    for name in &acc.int_literal_eq_vars {
        acc.bool_vars.remove(name);
    }
    // Propagate Seq/FMap/Mapping hints through the naming chain:
    //   `final_{x}_view` -> `{x}_view` -> `{x}`
    // Same `_current` guard applies for both. (#994, #1948)
    propagate_name_chain_hints(&mut acc.seqs);
    propagate_name_chain_hints(&mut acc.fmaps);
    propagate_name_chain_hints(&mut acc.mappings);
    promote_ambiguous_seq_hints(&mut acc);
    acc
}

impl AYEncoder {
    /// Pre-register all known sort hints (Bool, Seq, FMap) from a batch of expressions.
    /// This is the canonical pre-scan API used by verifier entry points. (#564)
    pub(crate) fn register_sort_hints(&mut self, exprs: &[PureExpr]) {
        let acc = collect_registered_sort_hints(exprs.iter());
        self.apply_sort_hint_accumulator(acc);
        self.mark_sort_hints_registered();
    }

    /// Register formula expressions as Bool-requiring. (#544)
    pub(crate) fn register_formula_sort_hints(&mut self, formulas: &[PureExpr]) {
        let mut bool_var_names = HashSet::new();
        let mut bool_fn_names = HashSet::new();
        for expr in formulas {
            collect_names_as_bool(expr, &mut bool_var_names, &mut bool_fn_names);
        }
        for name in bool_var_names {
            self.record_sort_hint(name, ExprSort::Bool);
        }
        for name in bool_fn_names {
            self.record_sort_hint(name, ExprSort::Bool);
        }
    }

    /// Register ONLY logic function Bool return sort hints from formula-position
    /// expressions. Unlike `register_formula_sort_hints`, this does NOT add
    /// variable-level Bool hints -- those are handled by
    /// `collect_variable_usage_as_formula` in the pre-declaration system.
    ///
    /// This is needed because logic fn return sorts are determined at declaration
    /// time by looking up `sort_hints[fn_name]`, which is not covered by the
    /// VarUsage system. (#1965, sort-authority-cutover)
    pub(crate) fn register_formula_fn_sort_hints(&mut self, formulas: &[PureExpr]) {
        let mut bool_var_names = HashSet::new();
        let mut bool_fn_names = HashSet::new();
        for expr in formulas {
            collect_names_as_bool(expr, &mut bool_var_names, &mut bool_fn_names);
        }
        // Only register fn names -- variable hints are handled by predeclaration.
        for name in bool_fn_names {
            self.record_sort_hint(name, ExprSort::Bool);
        }
    }

    /// Register sort hints from a Formula body. (#544, #1805)
    #[cfg(any(test, feature = "sep-logic"))]
    pub(crate) fn register_formula_body_sort_hints(&mut self, formula: &Formula) {
        let mut acc = SortHintAccumulator::new();
        collect_formula_sort_hints(formula, &mut acc);
        self.apply_sort_hint_accumulator(acc);
    }

    /// Mark a variable name as needing Bool sort. (#544)
    pub(crate) fn mark_bool_var(&mut self, name: &str) {
        self.record_sort_hint(name.to_string(), ExprSort::Bool);
    }

    /// Record a sort hint. Collection-type hints take priority over Bool,
    /// and FMap takes priority over Seq (from the ambiguous-method heuristic).
    /// (#1517, #1778, #2316, #994)
    pub(crate) fn record_sort_hint(&mut self, name: String, hint: ExprSort) {
        self.sort_resolver.record_sort_hint(name, hint);
    }

    /// Record a sort hint only if the name has no existing entry. (#1584)
    pub(crate) fn record_sort_hint_if_absent(&mut self, name: String, hint: ExprSort) {
        self.sort_resolver.record_sort_hint_if_absent(name, hint);
    }

    /// Promote ambiguous collection method candidates (bare Var receivers of
    /// `len`/`get`/`index`) to Seq or FMap when view-derived evidence exists.
    /// (#994)
    ///
    /// Priority: (1) FMap evidence from `{name}_view`, (2) Seq evidence from
    /// `{name}_view`, (3) no action — leave unclassified.
    ///
    /// Previously, the fallback unconditionally promoted to Seq, which caused
    /// FMap-only receivers (using only `len`/`contains`/`get` without `lookup`
    /// or `merge`) to be misclassified as Seq. The Seq path then crashed via
    /// `coerce_to_seq` refusing FMap sort. Without evidence, the encoding-time
    /// dispatch handles unclassified receivers safely:
    ///
    /// - `len`: Seq? -> FMap? -> FSet (generic UF with non-negativity axiom)
    /// - `index`/`get`: Seq? -> FMap (correct default for maps)
    ///
    /// Fixes 7 pre-existing test failures. (#994)
    fn promote_ambiguous_seqs(&mut self, candidates: HashSet<String>) {
        for name in candidates {
            if self.has_sort_hint(&name) {
                continue;
            }
            let view_name = DerivedKind::View.format_name(&name);
            if self.sort_hint_matches(&view_name, &ExprSort::FMap) {
                self.record_sort_hint(name, ExprSort::FMap);
            } else if self.sort_hint_matches(&view_name, &ExprSort::Seq) {
                self.record_sort_hint(name, ExprSort::Seq);
            }
            // No evidence: leave unclassified. The encoding-time three-way
            // dispatch (is_seq_receiver → is_fmap_receiver → fallback) handles
            // unclassified receivers without crashing. (#994)
        }
    }

    fn apply_sort_hint_accumulator(&mut self, acc: SortHintAccumulator) {
        for name in acc.seqs {
            self.record_sort_hint(name, ExprSort::Seq);
        }
        for name in acc.bool_vars {
            self.record_sort_hint(name, ExprSort::Bool);
        }
        for name in acc.bool_fns {
            self.record_sort_hint(name, ExprSort::Bool);
        }
        for name in acc.fmaps {
            self.record_sort_hint(name, ExprSort::FMap);
        }
        for name in acc.mappings {
            self.record_sort_hint(name, mapping_expr_sort());
        }
        self.promote_ambiguous_seqs(acc.ambiguous_seqs);
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, sync::Arc};

    use ntest::timeout;
    use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

    use super::{collect_registered_sort_hints, propagate_name_chain_hints};

    /// `Var("b", Bool) == x@` — the Eq-arm "one side infers Bool" rule mints
    /// a heuristic Bool hint for `x` (descending through the View wrapper).
    fn bool_poison_eq(var_name: &str) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("b".to_string(), Some(ExprSort::Bool))),
            BinOp::Eq,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                var_name.to_string(),
                None,
            )))),
        )
    }

    /// `x@ == N` — int-literal equality premise.
    fn int_literal_eq(var_name: &str, literal: i64) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                var_name.to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(literal)),
        )
    }

    /// Sanity: without the literal premise, the Eq-arm Bool mint fires for
    /// the View-wrapped var. This proves the veto tests below actually
    /// exercise the mint-then-veto path. (arc_and_rc sort-plan flake)
    #[test]
    #[timeout(30000)]
    fn eq_arm_bool_mint_fires_without_literal_evidence() {
        let acc = collect_registered_sort_hints([bool_poison_eq("x")].iter());
        assert!(
            acc.bool_vars.contains("x"),
            "Bool-infers-side Eq mint should tag the peer var: {:?}",
            acc.bool_vars
        );
    }

    /// The int-literal-equality veto strips the heuristic Bool mint in BOTH
    /// expression orders — the veto is collected during the same traversal
    /// and applied after it, so hash/iteration order cannot decide whether
    /// the Bool hint survives. (arc_and_rc sort-plan flake)
    #[test]
    #[timeout(30000)]
    fn int_literal_eq_veto_strips_bool_mint_in_both_orders() {
        let poison = bool_poison_eq("x");
        let literal = int_literal_eq("x", 2);
        for exprs in [
            [poison.clone(), literal.clone()],
            [literal.clone(), poison.clone()],
        ] {
            let acc = collect_registered_sort_hints(exprs.iter());
            assert!(
                !acc.bool_vars.contains("x"),
                "x@ == 2 must veto the heuristic Bool mint for x \
                 (order {exprs:?}), got bool_vars {:?}",
                acc.bool_vars
            );
        }
    }

    /// In-range literals {0, 1} are legitimately encodable against Bool via
    /// ay's 0/1 bridge and must NOT veto the Bool mint.
    #[test]
    #[timeout(30000)]
    fn in_range_literal_does_not_veto_bool_mint() {
        for literal in [0, 1] {
            let exprs = [bool_poison_eq("x"), int_literal_eq("x", literal)];
            let acc = collect_registered_sort_hints(exprs.iter());
            assert!(
                acc.bool_vars.contains("x"),
                "x@ == {literal} is in-range and must NOT veto the Bool mint"
            );
        }
    }

    /// The `_current` guard prevents `self__current_view -> self__current`
    /// propagation. Without this guard, mut-ref parameters get tagged Seq
    /// causing ay sort mismatch panics. (#1948)
    #[test]
    #[timeout(30000)]
    fn propagate_blocks_current_suffix_from_view_stripping() {
        let mut names: HashSet<String> = ["self__current_view".to_string()].into_iter().collect();
        propagate_name_chain_hints(&mut names);

        assert!(
            names.contains("self__current_view"),
            "original name should remain"
        );
        assert!(
            !names.contains("self__current"),
            "_current suffix must NOT be derived from _view stripping (#1948)"
        );
    }

    /// Normal `_view` stripping works when base does not end with `_current`.
    #[test]
    #[timeout(30000)]
    fn propagate_strips_view_for_non_current_base() {
        let mut names: HashSet<String> = ["self__view".to_string()].into_iter().collect();
        propagate_name_chain_hints(&mut names);

        assert!(
            names.contains("self_"),
            "base name without _current should be derived from _view stripping"
        );
    }

    /// `final_{x}_view -> {x}_view` propagation works in all cases.
    #[test]
    #[timeout(30000)]
    fn propagate_strips_final_prefix() {
        let mut names: HashSet<String> = ["final_self__view".to_string()].into_iter().collect();
        propagate_name_chain_hints(&mut names);

        assert!(
            names.contains("self__view"),
            "final_ prefix should be stripped to produce base_view"
        );
        assert!(
            names.contains("self_"),
            "second pass should strip _view from self__view"
        );
    }

    /// `final_` stripping should use the shared derived-name classifier even
    /// when the remainder still carries an `old_` prefix. (#2020 Slice 3)
    #[test]
    #[timeout(30000)]
    fn propagate_strips_final_prefix_for_old_view_chain() {
        let mut names: HashSet<String> = ["final_old_self__view".to_string()].into_iter().collect();
        propagate_name_chain_hints(&mut names);

        assert!(
            names.contains("old_self__view"),
            "final_ prefix stripping should preserve the old_+_view derived name"
        );
        assert!(
            names.contains("old_self_"),
            "second pass should still strip _view after the final_ prefix is removed"
        );
    }

    /// Full chain: `final_self__current_view` -> `self__current_view` -> BLOCKED.
    /// The `_current` guard prevents the second step from producing `self__current`.
    #[test]
    #[timeout(30000)]
    fn propagate_full_chain_blocked_at_current() {
        let mut names: HashSet<String> = ["final_self__current_view".to_string()]
            .into_iter()
            .collect();
        propagate_name_chain_hints(&mut names);

        assert!(
            names.contains("self__current_view"),
            "final_ prefix stripping should produce self__current_view"
        );
        assert!(
            !names.contains("self__current"),
            "self__current_view -> self__current must be blocked by _current guard (#1948)"
        );
    }

    /// Empty input produces no new names.
    #[test]
    #[timeout(30000)]
    fn propagate_empty_is_noop() {
        let mut names: HashSet<String> = HashSet::new();
        propagate_name_chain_hints(&mut names);
        assert!(names.is_empty());
    }
}
