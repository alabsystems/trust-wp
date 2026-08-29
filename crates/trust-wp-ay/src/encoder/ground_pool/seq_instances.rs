// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq ground instance assertions.
//!
//! Extracted from `ground_pool.rs` as part of encoder decomposition (#1988).

use ay_dpll::api::{Sort, Term, TermKind};

fn ground_seq_alias_root(parent: &mut std::collections::HashMap<Term, Term>, term: Term) -> Term {
    let parent_term = *parent.entry(term).or_insert(term);
    if parent_term == term {
        return term;
    }
    let root = ground_seq_alias_root(parent, parent_term);
    parent.insert(term, root);
    root
}

fn union_ground_seq_alias_terms(
    parent: &mut std::collections::HashMap<Term, Term>,
    lhs: Term,
    rhs: Term,
) {
    let lhs_root = ground_seq_alias_root(parent, lhs);
    let rhs_root = ground_seq_alias_root(parent, rhs);
    if lhs_root != rhs_root {
        parent.insert(rhs_root, lhs_root);
    }
}

impl super::super::AYEncoder {
    fn assertions_contain_seq_application(&self, expected: &str) -> bool {
        self.solver.assertions().into_iter().any(|assertion| {
            self.term_contains_seq_application(
                assertion,
                expected,
                &mut std::collections::HashSet::new(),
            )
        })
    }

    fn term_contains_seq_application(
        &self,
        term: Term,
        expected: &str,
        seen: &mut std::collections::HashSet<Term>,
    ) -> bool {
        if !seen.insert(term) {
            return false;
        }
        if matches!(
            self.solver.term_kind(term),
            TermKind::App { ref name, .. } if name == expected
        ) {
            return true;
        }
        self.solver
            .term_children(term)
            .into_iter()
            .any(|child| self.term_contains_seq_application(child, expected, seen))
    }

    fn asserted_equality_pairs(&self) -> Vec<(Term, Term)> {
        self.solver
            .assertions()
            .into_iter()
            .filter_map(|assertion| {
                let TermKind::App { name, num_args: 2 } = self.solver.term_kind(assertion) else {
                    return None;
                };
                if name != "=" {
                    return None;
                }
                let children = self.solver.term_children(assertion);
                let [lhs, rhs] = children.as_slice() else {
                    return None;
                };
                Some((*lhs, *rhs))
            })
            .collect()
    }

    pub(super) fn asserted_equality_closure(&self, target: Term, limit: usize) -> Vec<Term> {
        let pairs = self.asserted_equality_pairs();
        let target_sort = self.solver.get_sort(target);
        let mut seen = std::collections::HashSet::from([target]);
        let mut frontier = vec![target];
        while let Some(current) = frontier.pop() {
            if seen.len() >= limit {
                break;
            }
            for (lhs, rhs) in &pairs {
                let next = if *lhs == current {
                    *rhs
                } else if *rhs == current {
                    *lhs
                } else {
                    continue;
                };
                if self.solver.get_sort(next) == target_sort && seen.insert(next) {
                    frontier.push(next);
                }
            }
        }
        seen.remove(&target);
        seen.into_iter().collect()
    }

    fn asserted_or_true_term(&self, term: Term) -> bool {
        if self.term_int_comparison_holds(term) == Some(true) {
            return true;
        }
        let term_text = self.solver.format_term(term);
        self.solver
            .assertions()
            .iter()
            .any(|assertion| *assertion == term || self.solver.format_term(*assertion) == term_text)
    }

    fn assertions_contain_negation_of(&mut self, term: Term) -> bool {
        let negated = self.solver.not(term);
        let negated_text = self.solver.format_term(negated);
        self.solver.assertions().iter().any(|assertion| {
            *assertion == negated || self.solver.format_term(*assertion) == negated_text
        })
    }

    fn assert_seq_get_inbounds_option_facts(
        &mut self,
        antecedent: Option<Term>,
        get_term: Term,
        index_term: Term,
    ) -> usize {
        let is_option_decl =
            self.get_or_declare_spec_func("__trust_wp_is_option", &[Sort::Int], Sort::Bool);
        let is_some_decl = self.get_or_declare_constructor_tester_for_sort("is_some", &Sort::Int);
        let unwrap_decl =
            self.get_or_declare_accessor_for_sorts("spec_unwrap", &Sort::Int, &Sort::Int);

        let is_option = self.solver.apply(&is_option_decl, &[get_term]);
        let is_some = self.solver.apply(&is_some_decl, &[get_term]);
        let unwrap = self.solver.apply(&unwrap_decl, &[get_term]);
        let unwrap_eq = self.eq_term(unwrap, index_term);

        match antecedent {
            Some(guard) => {
                let facts = self.solver.and_many(&[is_option, is_some, unwrap_eq]);
                let implication = self.solver.implies(guard, facts);
                self.assert_solver_term("ground/seq_get_inbounds_option_facts", implication);
                1
            }
            None => {
                self.assert_solver_term("ground/seq_get_inbounds_is_option", is_option);
                self.assert_solver_term("ground/seq_get_inbounds_is_some", is_some);
                self.assert_solver_term("ground/seq_get_inbounds_unwrap", unwrap_eq);
                let mut count = 3;
                if let Some(datatype) = self.get_datatype_decl("OptionInt").cloned() {
                    let native_some =
                        self.solver
                            .datatype_constructor(&datatype, "Some", &[index_term]);
                    let native_eq = self.eq_term(get_term, native_some);
                    let has_negated_native_eq = self.assertions_contain_negation_of(native_eq);
                    self.assert_solver_term("ground/seq_get_inbounds_native_some", native_eq);
                    count += 1;
                    if has_negated_native_eq {
                        let false_term = self.solver.bool_const(false);
                        self.assert_solver_term(
                            "ground/seq_get_inbounds_native_conflict",
                            false_term,
                        );
                        count += 1;
                    }
                }
                count
            }
        }
    }

    fn assert_seq_get_oob_option_facts(
        &mut self,
        antecedent: Option<Term>,
        get_term: Term,
    ) -> usize {
        let is_option_decl =
            self.get_or_declare_spec_func("__trust_wp_is_option", &[Sort::Int], Sort::Bool);
        let is_some_decl = self.get_or_declare_constructor_tester_for_sort("is_some", &Sort::Int);

        let is_option = self.solver.apply(&is_option_decl, &[get_term]);
        let is_some = self.solver.apply(&is_some_decl, &[get_term]);
        let not_is_some = self.solver.not(is_some);

        match antecedent {
            Some(guard) => {
                let facts = self.solver.and(is_option, not_is_some);
                let implication = self.solver.implies(guard, facts);
                self.assert_solver_term("ground/seq_get_oob_option_facts", implication);
                1
            }
            None => {
                self.assert_solver_term("ground/seq_get_oob_is_option", is_option);
                self.assert_solver_term("ground/seq_get_oob_not_is_some", not_is_some);
                let mut count = 2;
                if let Some(datatype) = self.get_datatype_decl("OptionInt").cloned() {
                    if let Some(native_none) = self.axiom_datatype_constructor(
                        "ground/seq_get_oob_native_none",
                        &datatype,
                        "None",
                        &[],
                    ) {
                        let native_eq = self.eq_term(get_term, native_none);
                        let has_negated_native_eq = self.assertions_contain_negation_of(native_eq);
                        self.assert_solver_term("ground/seq_get_oob_native_none", native_eq);
                        count += 1;
                        if has_negated_native_eq {
                            let false_term = self.solver.bool_const(false);
                            self.assert_solver_term(
                                "ground/seq_get_oob_native_conflict",
                                false_term,
                            );
                            count += 1;
                        }
                    }
                }
                count
            }
        }
    }

    fn assert_guarded_seq_ground_term(
        &mut self,
        label: &str,
        path_conditions: &[Term],
        guards: &[Term],
        body: Term,
    ) {
        let mut all_guards = Vec::with_capacity(path_conditions.len() + guards.len());
        all_guards.extend_from_slice(path_conditions);
        all_guards.extend_from_slice(guards);

        let term = match all_guards.as_slice() {
            [] => body,
            [single] => self.solver.implies(*single, body),
            _ => {
                let guard = self.solver.and_many(&all_guards);
                self.solver.implies(guard, body)
            }
        };
        self.assert_solver_term(label, term);
    }

    fn seq_ground_in_bounds_guard(&mut self, index: Term, len: Term) -> Term {
        let zero = self.solver.int_const(0);
        let ge_zero = self.solver.ge(index, zero);
        let lt_len = self.solver.lt(index, len);
        self.solver.and(ge_zero, lt_len)
    }

    fn seq_select_index_source(&self, term: Term) -> Option<(Term, Term, Term)> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "select" {
            return None;
        }
        let children = self.solver.term_children(term);
        let [array, shifted_index] = children.as_slice() else {
            return None;
        };

        let seq_term = match self.solver.term_kind(*array) {
            TermKind::App {
                name: array_name,
                num_args: 1,
            } if array_name == "seq_array" => {
                let array_children = self.solver.term_children(*array);
                let [seq_term] = array_children.as_slice() else {
                    return None;
                };
                *seq_term
            }
            _ => self
                .seq_state
                .seq_array_aux_entries()
                .find_map(|(receiver, proxy)| (proxy == *array).then_some(receiver))?,
        };

        let TermKind::App {
            name: shift_name,
            num_args: 2,
        } = self.solver.term_kind(*shifted_index)
        else {
            return None;
        };
        if shift_name != "+" {
            return None;
        }
        let shift_children = self.solver.term_children(*shifted_index);
        let [left, right] = shift_children.as_slice() else {
            return None;
        };

        let offset_receiver = |candidate: Term| -> Option<Term> {
            if let TermKind::App { name, num_args: 1 } = self.solver.term_kind(candidate) {
                if name == "seq_offset" {
                    let children = self.solver.term_children(candidate);
                    if let [receiver] = children.as_slice() {
                        return Some(*receiver);
                    }
                }
            }
            self.seq_state
                .seq_offset_aux_entries()
                .find_map(|(receiver, proxy)| (proxy == candidate).then_some(receiver))
        };

        if offset_receiver(*left) == Some(seq_term) {
            return Some((seq_term, *right, term));
        }
        if offset_receiver(*right) == Some(seq_term) {
            return Some((seq_term, *left, term));
        }
        None
    }

    fn collect_seq_select_index_sources_from_term(
        &self,
        term: Term,
        seen: &mut std::collections::HashSet<Term>,
        entries: &mut Vec<(Term, Term, Term)>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let Some(source) = self.seq_select_index_source(term) {
            entries.push(source);
        }
        for child in self.solver.term_children(term) {
            self.collect_seq_select_index_sources_from_term(child, seen, entries);
        }
    }

    fn collect_ground_equality_relations_from_term(
        &self,
        term: Term,
        seen: &mut std::collections::HashSet<Term>,
        equalities: &mut Vec<(Term, Term)>,
        disequalities: &mut Vec<(Term, Term)>,
    ) {
        if !seen.insert(term) {
            return;
        }

        match self.solver.term_kind(term) {
            TermKind::Not => {
                let children = self.solver.term_children(term);
                if let [inner] = children.as_slice() {
                    if let TermKind::App { name, num_args: 2 } = self.solver.term_kind(*inner) {
                        if name == "=" {
                            let eq_children = self.solver.term_children(*inner);
                            if let [left, right] = eq_children.as_slice() {
                                disequalities.push((*left, *right));
                            }
                        }
                    }
                }
            }
            TermKind::App { name, num_args: 2 } => {
                let children = self.solver.term_children(term);
                if let [left, right] = children.as_slice() {
                    match name.as_str() {
                        "=" => equalities.push((*left, *right)),
                        "distinct" | "!=" => disequalities.push((*left, *right)),
                        _ => {}
                    }
                }
            }
            _ => {}
        }

        for child in self.solver.term_children(term) {
            self.collect_ground_equality_relations_from_term(
                child,
                seen,
                equalities,
                disequalities,
            );
        }
    }

    fn relation_other_side(relation: (Term, Term), anchor: Term) -> Option<Term> {
        if relation.0 == anchor {
            Some(relation.1)
        } else if relation.1 == anchor {
            Some(relation.0)
        } else {
            None
        }
    }

    fn relation_contains(relations: &[(Term, Term)], left: Term, right: Term) -> bool {
        relations.iter().any(|relation| {
            (relation.0 == left && relation.1 == right)
                || (relation.0 == right && relation.1 == left)
        })
    }

    fn assert_seq_pivot_distinct_order_instance(
        &mut self,
        left_index: Term,
        left_value: Term,
        right_index: Term,
        right_value: Term,
        pivot: Term,
        label: &str,
    ) {
        let left_differs_from_pivot = self.solver.neq(left_value, pivot);
        let pivot_eq_right = self.eq_term(pivot, right_value);
        let left_le_right = self.solver.le(left_index, right_index);
        let one = self.solver.int_const(1);
        let left_plus_one = self.solver.add(left_index, one);
        let left_succ_le_right = self.solver.le(left_plus_one, right_index);
        let guard = self
            .solver
            .and_many(&[left_differs_from_pivot, pivot_eq_right, left_le_right]);
        let ordered = self.solver.implies(guard, left_succ_le_right);
        self.assert_solver_term(label, ordered);
    }

    fn assert_seq_index_distinctness_ground_instances(&mut self, remaining_budget: usize) -> usize {
        const INDEX_DISTINCTNESS_BUDGET: usize = 80;

        let mut count = 0;
        if remaining_budget == 0 {
            return 0;
        }

        let mut entries: Vec<_> = self.seq_state.all_seq_index_sources().into_iter().collect();
        let assertions = self.solver.assertions();
        let mut seen_terms = std::collections::HashSet::new();
        let mut equality_seen_terms = std::collections::HashSet::new();
        let mut equalities = Vec::new();
        let mut disequalities = Vec::new();
        for assertion in assertions {
            self.collect_seq_select_index_sources_from_term(
                assertion,
                &mut seen_terms,
                &mut entries,
            );
            self.collect_ground_equality_relations_from_term(
                assertion,
                &mut equality_seen_terms,
                &mut equalities,
                &mut disequalities,
            );
        }
        let mut seen_entries = std::collections::HashSet::new();
        entries.retain(|entry| seen_entries.insert(*entry));
        let mut seen_equalities = std::collections::HashSet::new();
        equalities.retain(|relation| seen_equalities.insert(*relation));
        let mut seen_disequalities = std::collections::HashSet::new();
        disequalities.retain(|relation| seen_disequalities.insert(*relation));

        let budget = INDEX_DISTINCTNESS_BUDGET.min(remaining_budget);
        for left_pos in 0..entries.len() {
            for right_pos in (left_pos + 1)..entries.len() {
                if count >= budget {
                    return count;
                }
                let (left_seq, left_index, left_value) = entries[left_pos];
                let (right_seq, right_index, right_value) = entries[right_pos];
                if left_seq != right_seq {
                    continue;
                }
                if left_index == right_index || left_value == right_value {
                    continue;
                }

                let values_differ = self.solver.neq(left_value, right_value);
                let indices_differ = self.solver.neq(left_index, right_index);
                let distinct_implies_distinct = self.solver.implies(values_differ, indices_differ);
                self.assert_solver_term(
                    "ground/seq_index_value_distinct_implies_index_distinct",
                    distinct_implies_distinct,
                );
                count += 1;

                if count >= budget {
                    return count;
                }
                let left_le_right = self.solver.le(left_index, right_index);
                let one = self.solver.int_const(1);
                let left_plus_one = self.solver.add(left_index, one);
                let left_succ_le_right = self.solver.le(left_plus_one, right_index);
                let guard = self.solver.and(left_le_right, values_differ);
                let ordered = self.solver.implies(guard, left_succ_le_right);
                self.assert_solver_term("ground/seq_index_value_distinct_order_left", ordered);
                count += 1;

                if count >= budget {
                    return count;
                }
                let right_le_left = self.solver.le(right_index, left_index);
                let one = self.solver.int_const(1);
                let right_plus_one = self.solver.add(right_index, one);
                let right_succ_le_left = self.solver.le(right_plus_one, left_index);
                let guard = self.solver.and(right_le_left, values_differ);
                let ordered = self.solver.implies(guard, right_succ_le_left);
                self.assert_solver_term("ground/seq_index_value_distinct_order_right", ordered);
                count += 1;

                for disequality in &disequalities {
                    if count >= budget {
                        return count;
                    }
                    if let Some(pivot) = Self::relation_other_side(*disequality, left_value) {
                        if Self::relation_contains(&equalities, pivot, right_value) {
                            self.assert_seq_pivot_distinct_order_instance(
                                left_index,
                                left_value,
                                right_index,
                                right_value,
                                pivot,
                                "ground/seq_index_pivot_distinct_order_left",
                            );
                            count += 1;
                        }
                    }
                    if count >= budget {
                        return count;
                    }
                    if let Some(pivot) = Self::relation_other_side(*disequality, right_value) {
                        if Self::relation_contains(&equalities, pivot, left_value) {
                            self.assert_seq_pivot_distinct_order_instance(
                                right_index,
                                right_value,
                                left_index,
                                left_value,
                                pivot,
                                "ground/seq_index_pivot_distinct_order_right",
                            );
                            count += 1;
                        }
                    }
                }
            }
        }

        count
    }

    fn assert_seq_subsequence_ground_instances(&mut self, remaining_budget: usize) -> usize {
        let mut count = 0;
        if remaining_budget == 0 {
            return 0;
        }

        macro_rules! budget_guard {
            () => {
                if count >= remaining_budget {
                    return count;
                }
            };
        }

        let entries: Vec<(Term, Vec<Term>, Vec<Term>)> = self
            .ground_pool
            .entries_for("seq_subsequence")
            .map(|es| {
                es.iter()
                    .map(|e| {
                        (
                            e.application,
                            e.arg_terms.clone(),
                            e.path_conditions.clone(),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();

        for (app, args, path_conditions) in &entries {
            if args.len() != 3 {
                continue;
            }
            budget_guard!();
            let Ok(len_subsequence) = self.seq_len_term(*app) else {
                continue;
            };
            let zero = self.solver.int_const(0);
            let width = self.solver.sub(args[2], args[1]);
            let nonnegative_width = self.solver.ge(width, zero);
            let bounded_width = self.solver.ite(nonnegative_width, width, zero);
            let eq = self.eq_term(len_subsequence, bounded_width);
            self.assert_guarded_seq_ground_term(
                "ground/seq_subsequence_len",
                path_conditions,
                &[],
                eq,
            );
            count += 1;
        }

        const SUBSEQUENCE_INDEX_BUDGET: usize = 80;
        let mut index_count = 0;
        'subsequence_outer: for (app, args, path_conditions) in &entries {
            if args.len() != 3 {
                continue;
            }
            let indexed_terms = self.seq_state.seq_index_sources_for_seq(app);
            if indexed_terms.is_empty() {
                continue;
            }
            let Ok(len_subsequence) = self.seq_len_term(*app) else {
                continue;
            };

            for (subsequence_index_result, index) in indexed_terms {
                if index_count >= SUBSEQUENCE_INDEX_BUDGET {
                    break 'subsequence_outer;
                }
                budget_guard!();
                let base_index = self.solver.add(args[1], index);
                let Ok(base_index_result) = self.seq_index_term(args[0], base_index) else {
                    continue;
                };
                let in_bounds = self.seq_ground_in_bounds_guard(index, len_subsequence);
                let eq = self.eq_term(subsequence_index_result, base_index_result);
                self.assert_guarded_seq_ground_term(
                    "ground/seq_subsequence_index",
                    path_conditions,
                    &[in_bounds],
                    eq,
                );
                count += 1;
                index_count += 1;
            }
        }

        count
    }

    fn assert_seq_reverse_ground_instances(&mut self, remaining_budget: usize) -> usize {
        let mut count = 0;
        if remaining_budget == 0 {
            return 0;
        }

        macro_rules! budget_guard {
            () => {
                if count >= remaining_budget {
                    return count;
                }
            };
        }

        let entries: Vec<(Term, Vec<Term>, Vec<Term>)> = self
            .ground_pool
            .entries_for("seq_reverse")
            .map(|es| {
                es.iter()
                    .map(|e| {
                        (
                            e.application,
                            e.arg_terms.clone(),
                            e.path_conditions.clone(),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();

        let seq_funcs = self.seq_funcs_clone();
        let authenticated_alias_pairs =
            self.authenticated_seq_component_alias_pairs_from_assertions();
        let reverse_observed =
            !entries.is_empty() || self.assertions_contain_seq_application("seq_reverse");
        let reverse_funcs = seq_funcs.as_ref().filter(|_| reverse_observed);
        if let Some(funcs) = reverse_funcs {
            // Dedup `reverse(seq_empty) = seq_empty` across check_sat cycles.
            // `assert_standard_ground_instances` runs from `check_sat` every
            // time the encoder reaches scope 0; without dedup the axiom is
            // re-emitted N times per VC. For nested-loop VCs (e.g. 100doors)
            // the cumulative re-emission inflates the assertion count enough
            // to trigger ay #8596 false_term preprocessing pathology. See
            // designs/2026-05-19-100doors-vec-sort-leakage.md.
            if self.mark_logic_fn_axiom_asserted("ground/seq_reverse_empty".to_string()) {
                budget_guard!();
                let rev_empty = self.solver.apply(&funcs.seq_reverse, &[funcs.seq_empty]);
                let eq = self.seq_aware_equality_term(rev_empty, funcs.seq_empty);
                self.assert_solver_term("ground/seq_reverse_empty", eq);
                count += 1;
            }
        }

        for (app, args, path_conditions) in &entries {
            if args.len() != 1 {
                continue;
            }
            if let Some(funcs) = &seq_funcs {
                budget_guard!();
                let base_is_empty = self.seq_aware_equality_term(args[0], funcs.seq_empty);
                let reverse_is_empty = self.seq_aware_equality_term(*app, funcs.seq_empty);
                self.assert_guarded_seq_ground_term(
                    "ground/seq_reverse_empty_alias",
                    path_conditions,
                    &[base_is_empty],
                    reverse_is_empty,
                );
                count += 1;

                let mut aliases: std::collections::HashSet<Term> = self
                    .asserted_equality_closure(args[0], 48)
                    .into_iter()
                    .collect();
                for (lhs, rhs) in &authenticated_alias_pairs {
                    if *lhs == args[0] {
                        aliases.insert(*rhs);
                    } else if *rhs == args[0] {
                        aliases.insert(*lhs);
                    }
                }
                for alias in aliases {
                    budget_guard!();
                    let alias_reverse = self.solver.apply(&funcs.seq_reverse, &[alias]);
                    let eq = self.seq_aware_equality_term(alias_reverse, *app);
                    self.assert_guarded_seq_ground_term(
                        "ground/seq_reverse_alias_congruence",
                        path_conditions,
                        &[],
                        eq,
                    );
                    count += 1;
                }
            }
            budget_guard!();
            let Ok(len_reverse) = self.seq_len_term(*app) else {
                continue;
            };
            let Ok(len_base) = self.seq_len_term(args[0]) else {
                continue;
            };
            let eq = self.eq_term(len_reverse, len_base);
            self.assert_guarded_seq_ground_term("ground/seq_reverse_len", path_conditions, &[], eq);
            count += 1;
        }

        const REVERSE_INDEX_BUDGET: usize = 80;
        const REVERSE_OBSERVED_INDEX_BUDGET: usize = 120;
        let mut index_count = 0;
        let mut observed_index_count = 0;
        'reverse_outer: for (app, args, path_conditions) in &entries {
            if args.len() != 1 {
                continue;
            }
            let base_seq = args[0];
            let reverse_indexed_terms = self.seq_state.seq_index_sources_for_seq(app);
            if reverse_indexed_terms.is_empty() {
                continue;
            }
            let Ok(len_base) = self.seq_len_term(base_seq) else {
                continue;
            };
            let one = self.solver.int_const(1);

            for (reverse_index_result, reverse_index) in reverse_indexed_terms {
                if index_count >= REVERSE_INDEX_BUDGET {
                    break 'reverse_outer;
                }
                budget_guard!();
                let len_minus_one = self.solver.sub(len_base, one);
                let mirror_index = self.solver.sub(len_minus_one, reverse_index);
                let observed_base_indices = self.seq_state.seq_index_sources_for_seq(&base_seq);
                let Ok(base_index_result) = self.seq_index_term(base_seq, mirror_index) else {
                    continue;
                };
                let in_bounds = self.seq_ground_in_bounds_guard(reverse_index, len_base);
                let eq = self.eq_term(reverse_index_result, base_index_result);
                self.assert_guarded_seq_ground_term(
                    "ground/seq_reverse_index",
                    path_conditions,
                    &[in_bounds],
                    eq,
                );
                count += 1;
                index_count += 1;

                for (observed_result, observed_index) in observed_base_indices {
                    if observed_index_count >= REVERSE_OBSERVED_INDEX_BUDGET {
                        continue;
                    }
                    budget_guard!();
                    let mirror_matches_observed = self.eq_term(observed_index, mirror_index);
                    let observed_eq = self.eq_term(reverse_index_result, observed_result);
                    self.assert_guarded_seq_ground_term(
                        "ground/seq_reverse_index_observed",
                        path_conditions,
                        &[in_bounds, mirror_matches_observed],
                        observed_eq,
                    );
                    count += 1;
                    observed_index_count += 1;
                }
            }
        }

        count
    }

    /// Ground instances for Seq axioms.
    ///
    /// Exposed as `pub(crate)` so loop verification phases can pre-assert Seq
    /// ground facts (e.g., `len(push_back(s,x)) == len(s) + 1`) before the
    /// axiom-free probe without pulling in FMap/FSet instances that can
    /// interfere with proof dynamics, while still respecting a caller-provided
    /// remaining budget. (#2323, #2707)
    #[allow(clippy::too_many_lines)]
    pub(crate) fn assert_seq_ground_instances(&mut self, remaining_budget: usize) -> usize {
        let mut count = 0;

        if remaining_budget == 0 {
            tracing::debug!(
                count,
                budget = remaining_budget,
                "seq ground instances: remaining budget exhausted before assertion (#2707)"
            );
            return 0;
        }

        macro_rules! budget_guard {
            () => {
                if count >= remaining_budget {
                    tracing::debug!(
                        count,
                        budget = remaining_budget,
                        "seq ground instances: remaining budget exhausted (#2707)"
                    );
                    return count;
                }
            };
        }

        // seq_len(s) >= 0 for each observed seq_len application. Dedup by
        // the proxy term identity to prevent re-emission across check_sat
        // cycles at scope 0 (see ground/seq_reverse_empty above).
        let entries: Vec<Vec<Term>> = self
            .ground_pool
            .entries_for("seq_len")
            .map(|es| es.iter().map(|e| e.arg_terms.clone()).collect())
            .unwrap_or_default();
        if !entries.is_empty() {
            let zero = self.solver.int_const(0);
            if self.seq_funcs_ref().is_some() {
                for args in &entries {
                    if args.len() == 1 {
                        let Ok(len_app) = self.seq_len_term(args[0]) else {
                            continue;
                        };
                        let dedup_key = format!(
                            "ground/seq_len_nonneg::{}",
                            self.solver.format_term(len_app)
                        );
                        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
                            continue;
                        }
                        budget_guard!();
                        let ge_zero = self.solver.ge(len_app, zero);
                        self.assert_solver_term("ground/seq_len_nonneg", ge_zero);
                        count += 1;
                    }
                }
            }
        }

        // Finite instances of the non-recursive concat algebra for each
        // concrete concat term observed in the VC. These replace the global
        // quantified length, identity, and associativity schemas, whose
        // interaction can make native E-matching diverge even on a tiny SAT
        // query. Generated counterpart terms are deliberately not registered
        // in the ground pool, so this pass cannot self-expand.
        let concat_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("seq_concat")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();
        if !concat_entries.is_empty() {
            if let Some(funcs) = self.seq_funcs_clone() {
                let concat_args_by_app: std::collections::HashMap<Term, (Term, Term)> =
                    concat_entries
                        .iter()
                        .filter(|(_, args)| args.len() == 2)
                        .map(|(app, args)| (*app, (args[0], args[1])))
                        .collect();

                for (concat_app, args) in &concat_entries {
                    if args.len() != 2 {
                        continue;
                    }
                    let left = args[0];
                    let right = args[1];

                    // Axiom 15: len(concat(s1, s2)) = len(s1) + len(s2).
                    budget_guard!();
                    let dedup_key = format!("ground/seq_concat_len::{concat_app}");
                    if self.mark_logic_fn_axiom_asserted(dedup_key) {
                        let Ok(len_concat) = self.seq_len_term(*concat_app) else {
                            continue;
                        };
                        let Ok(len_s1) = self.seq_len_term(left) else {
                            continue;
                        };
                        let Ok(len_s2) = self.seq_len_term(right) else {
                            continue;
                        };
                        let sum = self.solver.add(len_s1, len_s2);
                        let eq = self.eq_term(len_concat, sum);
                        self.assert_solver_term("ground/seq_concat_len", eq);
                        count += 1;
                    }

                    // Axioms 15c/15d: concrete left and right identities.
                    if left == funcs.seq_empty {
                        budget_guard!();
                        let dedup_key = format!("ground/seq_concat_left_identity::{concat_app}");
                        if self.mark_logic_fn_axiom_asserted(dedup_key) {
                            let eq = self.seq_aware_equality_term(*concat_app, right);
                            self.assert_solver_term("ground/seq_concat_left_identity", eq);
                            count += 1;
                        }
                    }
                    if right == funcs.seq_empty {
                        budget_guard!();
                        let dedup_key = format!("ground/seq_concat_right_identity::{concat_app}");
                        if self.mark_logic_fn_axiom_asserted(dedup_key) {
                            let eq = self.seq_aware_equality_term(*concat_app, left);
                            self.assert_solver_term("ground/seq_concat_right_identity", eq);
                            count += 1;
                        }
                    }

                    // Axiom 18, instantiated in either observed nesting
                    // direction. It is enough for one side to be an observed
                    // nested concat; the equality constructs the counterpart.
                    if let Some((a, b)) = concat_args_by_app.get(&left).copied() {
                        budget_guard!();
                        let dedup_key = format!("ground/seq_concat_assoc_left::{concat_app}");
                        if self.mark_logic_fn_axiom_asserted(dedup_key) {
                            let b_right = self.solver.apply(&funcs.seq_concat, &[b, right]);
                            let counterpart = self.solver.apply(&funcs.seq_concat, &[a, b_right]);
                            let eq = self.seq_aware_equality_term(*concat_app, counterpart);
                            self.assert_solver_term("ground/seq_concat_assoc_left", eq);
                            count += 1;
                        }
                    }
                    if let Some((b, c)) = concat_args_by_app.get(&right).copied() {
                        budget_guard!();
                        let dedup_key = format!("ground/seq_concat_assoc_right::{concat_app}");
                        if self.mark_logic_fn_axiom_asserted(dedup_key) {
                            let left_b = self.solver.apply(&funcs.seq_concat, &[left, b]);
                            let counterpart = self.solver.apply(&funcs.seq_concat, &[left_b, c]);
                            let eq = self.seq_aware_equality_term(counterpart, *concat_app);
                            self.assert_solver_term("ground/seq_concat_assoc_right", eq);
                            count += 1;
                        }
                    }
                }
            }
        }

        budget_guard!();
        count += self.assert_seq_subsequence_ground_instances(remaining_budget - count);

        budget_guard!();
        count += self.assert_seq_reverse_ground_instances(remaining_budget - count);

        budget_guard!();
        count += self.assert_seq_index_distinctness_ground_instances(remaining_budget - count);

        // seq_get Option semantics (axioms 8a/8b): for each observed seq_get(s, i),
        // assert in-bounds => Some(index_logic(s, i)) and out-of-bounds => None().
        // These ground instances compensate for ay-dpll's single-round E-matching
        // not firing the quantified axioms on concrete get applications. (#2288)
        let get_entries: Vec<Vec<Term>> = self
            .ground_pool
            .entries_for("seq_get")
            .map(|es| es.iter().map(|e| e.arg_terms.clone()).collect())
            .unwrap_or_default();
        if !get_entries.is_empty() {
            if let Some(funcs) = self.seq_funcs_clone() {
                let some_smt = trust_wp_core::logic::logic_fn_smt_name("Some");
                let none_smt = trust_wp_core::logic::logic_fn_smt_name("None");
                let some_decl = self.get_or_declare_logic_func(
                    &some_smt,
                    &[ay_dpll::api::Sort::Int],
                    ay_dpll::api::Sort::Int,
                );
                let none_decl =
                    self.get_or_declare_logic_func(&none_smt, &[], ay_dpll::api::Sort::Int);

                for args in &get_entries {
                    if args.len() == 2 {
                        let s = args[0];
                        let i = args[1];
                        let get_s_i = self.solver.apply(&funcs.seq_get, &[s, i]);
                        let Ok(len_s) = self.seq_len_term(s) else {
                            continue;
                        };
                        let zero = self.solver.int_const(0);

                        // 8a: 0 <= i < len(s) => get(s, i) = Some(index_logic(s, i))
                        budget_guard!();
                        let i_ge_0 = self.solver.ge(i, zero);
                        let i_lt_len = self.solver.lt(i, len_s);
                        let in_bounds = self.solver.and(i_ge_0, i_lt_len);
                        let Ok(index_s_i) = self.seq_index_term(s, i) else {
                            continue;
                        };
                        let some_val = self.solver.apply(&some_decl, &[index_s_i]);
                        let eq = self.eq_term(get_s_i, some_val);
                        if self.asserted_or_true_term(i_ge_0)
                            && self.asserted_or_true_term(i_lt_len)
                        {
                            count +=
                                self.assert_seq_get_inbounds_option_facts(None, get_s_i, index_s_i);
                            self.assert_solver_term("ground/seq_get_inbounds_direct", eq);
                            count += 1;
                            continue;
                        }
                        count += self.assert_seq_get_inbounds_option_facts(
                            Some(in_bounds),
                            get_s_i,
                            index_s_i,
                        );
                        let impl_term = self.solver.implies(in_bounds, eq);
                        self.assert_solver_term("ground/seq_get_inbounds", impl_term);
                        count += 1;

                        // 8b: (i < 0 || i >= len(s)) => get(s, i) = None()
                        budget_guard!();
                        let i_lt_0 = self.solver.lt(i, zero);
                        let i_ge_len = self.solver.ge(i, len_s);
                        let out_of_bounds = self.solver.or(i_lt_0, i_ge_len);
                        let none_val = self.solver.apply(&none_decl, &[]);
                        let eq = self.eq_term(get_s_i, none_val);
                        if self.asserted_or_true_term(i_lt_0)
                            || self.asserted_or_true_term(i_ge_len)
                        {
                            count += self.assert_seq_get_oob_option_facts(None, get_s_i);
                            self.assert_solver_term("ground/seq_get_oob_direct", eq);
                            count += 1;
                            continue;
                        }
                        count += self.assert_seq_get_oob_option_facts(Some(out_of_bounds), get_s_i);
                        let impl_term = self.solver.implies(out_of_bounds, eq);
                        self.assert_solver_term("ground/seq_get_oob", impl_term);
                        count += 1;
                    }
                }
            }
        }

        // seq_push_back len: len(push_back(s, x)) = len(s) + 1.
        // Shape constraints already enforce this via Array+Length projectors,
        // but the ground instance helps when ay can't resolve the shape
        // (e.g., push_back result appears only in spec-level expressions). (#2288)
        let push_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("seq_push_back")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();
        let pf_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("seq_push_front")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();
        let reverse_algebra_observed = self
            .ground_pool
            .entries_for("seq_reverse")
            .is_some_and(|entries| !entries.is_empty())
            || self.assertions_contain_seq_application("seq_reverse");
        if !push_entries.is_empty() {
            if let Some(funcs) = self.seq_funcs_clone() {
                const TRUST_WP_R4_FRONT_BRIDGE_BUDGET: usize = 40;
                let mut r4_front_bridge_count = 0;
                let concat_algebra_observed = !concat_entries.is_empty()
                    || self.assertions_contain_seq_application("seq_concat");
                let one = self.solver.int_const(1);
                for (app, args) in &push_entries {
                    if args.len() == 2 {
                        budget_guard!();
                        let Ok(len_push) = self.seq_len_term(*app) else {
                            continue;
                        };
                        let Ok(len_s) = self.seq_len_term(args[0]) else {
                            continue;
                        };
                        let len_plus_1 = self.solver.add(len_s, one);
                        let eq = self.eq_term(len_push, len_plus_1);
                        self.assert_solver_term("ground/seq_push_back_len", eq);
                        count += 1;

                        // Concrete R4 instance for the observed push_back term:
                        // reverse(push_back(s, x)) = push_front(reverse(s), x).
                        //
                        // This gives loop-preservation proofs a direct equality
                        // at the body-effect term instead of relying on the
                        // quantified reverse axiom to fire in the same round as
                        // ext_eq's own quantified obligations. (#2116)
                        // Keep native reverse/front algebra demand-driven. An
                        // Array+Len+Offset-only push-back query does not observe
                        // these terms, and manufacturing them can make an
                        // otherwise model-validatable QF_AUFLIA SAT query
                        // incomplete in ay. (#2828)
                        if reverse_algebra_observed {
                            budget_guard!();
                            let rev_push = self.solver.apply(&funcs.seq_reverse, &[*app]);
                            let rev_s = self.solver.apply(&funcs.seq_reverse, &[args[0]]);
                            let push_front_rev =
                                self.solver.apply(&funcs.seq_push_front, &[rev_s, args[1]]);
                            let r4_eq = self.seq_aware_equality_term(rev_push, push_front_rev);
                            self.assert_solver_term("ground/seq_reverse_push_back", r4_eq);
                            count += 1;

                            let mut aliases: std::collections::HashSet<Term> = self
                                .asserted_equality_closure(rev_s, 48)
                                .into_iter()
                                .collect();
                            for (lhs, rhs) in
                                self.authenticated_seq_component_alias_pairs_from_assertions()
                            {
                                if lhs == rev_s {
                                    aliases.insert(rhs);
                                } else if rhs == rev_s {
                                    aliases.insert(lhs);
                                }
                            }
                            for alias in aliases {
                                budget_guard!();
                                let push_front_alias =
                                    self.solver.apply(&funcs.seq_push_front, &[alias, args[1]]);
                                let eq =
                                    self.seq_aware_equality_term(push_front_alias, push_front_rev);
                                self.assert_solver_term(
                                    "ground/seq_reverse_push_back_alias_congruence",
                                    eq,
                                );
                                count += 1;
                            }

                            // Component-level congruence for observed
                            // push_front applications. A positive semantic Seq
                            // equality may contain the empty-length disjunct,
                            // so it is not always recoverable as three
                            // unconditional component aliases. Keep that exact
                            // equality as the guard and instantiate only at
                            // observed applications with the same element.
                            for (push_front_app, push_front_args) in &pf_entries {
                                if r4_front_bridge_count >= TRUST_WP_R4_FRONT_BRIDGE_BUDGET {
                                    break;
                                }
                                if push_front_args.len() != 2 || push_front_args[1] != args[1] {
                                    continue;
                                }
                                budget_guard!();
                                let same_base =
                                    self.seq_aware_equality_term(push_front_args[0], rev_s);
                                let same_result =
                                    self.seq_aware_equality_term(*push_front_app, push_front_rev);
                                let bridge = self.solver.implies(same_base, same_result);
                                self.assert_solver_term(
                                    "ground/seq_reverse_push_back_front_congruence",
                                    bridge,
                                );
                                count += 1;
                                r4_front_bridge_count += 1;
                            }
                        }
                    }
                }

                // Ground push_back-singleton equivalence (#2465, #2116):
                // For each push_back(s, x), assert push_back(s, x) = concat(s, singleton(x)).
                // This lets concrete concat algebra apply to push_back terms
                // while preserving the push_back UF for R4 reverse triggering.
                for (push_app, push_args) in &push_entries {
                    if !concat_algebra_observed {
                        break;
                    }
                    if push_args.len() != 2 {
                        continue;
                    }
                    let s = push_args[0];
                    let x = push_args[1];
                    budget_guard!();
                    let singleton = self.solver.apply(&funcs.seq_singleton, &[x]);
                    let concat_equiv = self.solver.apply(&funcs.seq_concat, &[s, singleton]);
                    let eq = self.seq_aware_equality_term(*push_app, concat_equiv);
                    self.assert_solver_term("ground/push_back_singleton_equiv", eq);
                    count += 1;
                }
            }
        }

        if !pf_entries.is_empty() {
            if let Some(funcs) = self.seq_funcs_clone() {
                for (app, args) in &pf_entries {
                    if args.len() == 2 && reverse_algebra_observed {
                        // Concrete R5 instance for the observed push_front term:
                        // reverse(push_front(s, x)) = push_back(reverse(s), x).
                        budget_guard!();
                        let rev_push = self.solver.apply(&funcs.seq_reverse, &[*app]);
                        let rev_s = self.solver.apply(&funcs.seq_reverse, &[args[0]]);
                        let push_back_rev =
                            self.solver.apply(&funcs.seq_push_back, &[rev_s, args[1]]);
                        let r5_eq = self.seq_aware_equality_term(rev_push, push_back_rev);
                        self.assert_solver_term("ground/seq_reverse_push_front", r5_eq);
                        count += 1;
                    }
                }
            }
        }

        // Push_back-concat bridge (#2116, #2465): for each observed
        // push_back(s, x) and each observed concat(a, b), assert:
        //   concat(push_back(s, x), b) = concat(s, push_front(x, b))
        //
        // This algebraic identity creates intermediate E-graph terms that,
        // combined with an iterator step transition fact (push_front(v, iter') = iter),
        // allow congruence closure to chain the primed ext_eq concat term
        // back to the old ext_eq concat term. Without this, the Tseitin
        // ext_eq variable for the primed invariant cannot be forced true.
        //
        // The cross-product is bounded by the smaller of TRUST_WP_BRIDGE_BUDGET (80)
        // and the caller-provided remaining budget. (#2671, #2707)
        // Reduced from 200 (#2688): ghost iterator tests generate many
        // push_back + concat entries from produces transitivity chains, and
        // the cross-product dominates solver time. 80 instances covers the
        // typical verification needs while leaving room for other families.
        const TRUST_WP_BRIDGE_BUDGET: usize = 80;
        let bridge_budget = TRUST_WP_BRIDGE_BUDGET.min(remaining_budget.saturating_sub(count));
        if !push_entries.is_empty() && !concat_entries.is_empty() && bridge_budget > 0 {
            let mut bridge_count = 0;
            if let Some(funcs) = self.seq_funcs_clone() {
                // Priority-sort concat entries: entries whose first arg matches a
                // push_back first arg are structurally relevant (the concat builds
                // on the push_back result) and should be generated first before
                // hitting the budget. This ensures the most useful bridges survive
                // budget truncation. (#2708)
                let pb_first_args: std::collections::HashSet<Term> = push_entries
                    .iter()
                    .filter(|(_, args)| args.len() == 2)
                    .map(|(_, args)| args[0])
                    .collect();
                let (hi_pri, lo_pri): (Vec<_>, Vec<_>) = concat_entries
                    .iter()
                    .map(|(_, args)| args)
                    .filter(|args| args.len() == 2)
                    .partition(|args| pb_first_args.contains(&args[0]));

                'bridge_outer: for (push_app, push_args) in &push_entries {
                    if push_args.len() != 2 {
                        continue;
                    }
                    let s = push_args[0];
                    let x = push_args[1];
                    for concat_args in hi_pri.iter().chain(lo_pri.iter()) {
                        if bridge_count >= bridge_budget {
                            break 'bridge_outer;
                        }
                        let b = concat_args[1]; // tail of concat
                                                // LHS: concat(push_back(s, x), b)
                        let lhs = self.solver.apply(&funcs.seq_concat, &[*push_app, b]);
                        // RHS: concat(s, push_front(x, b))
                        let pf = self.solver.apply(&funcs.seq_push_front, &[b, x]);
                        let rhs = self.solver.apply(&funcs.seq_concat, &[s, pf]);
                        let eq = self.seq_aware_equality_term(lhs, rhs);
                        budget_guard!();
                        self.assert_solver_term("ground/push_back_concat_bridge", eq);
                        count += 1;
                        bridge_count += 1;
                    }
                }

                tracing::debug!(
                    bridge_count,
                    bridge_budget,
                    candidates = push_entries.len() * concat_entries.len(),
                    hi_pri = hi_pri.len(),
                    lo_pri = lo_pri.len(),
                    "push_back-concat bridge complete (#2708)"
                );
            }
        }

        // Finite component preservation bridge: observed iterator VCs use
        // aliases for both operation results:
        //
        //   new_left = push_back(s, x)
        //   old_right = push_front(b, x)
        //
        // The algebraic bridge above relates the operation applications, but
        // a proxy-backed lane deliberately has no native Seq carrier equality
        // with which UF congruence could transfer that result to the two
        // observed concat applications.  Instantiate the same theorem over
        // their authenticated Array/Len/Offset equalities instead:
        //
        //   (new_left == push_back(s, x) && old_right == push_front(b, x))
        //     => concat(s, old_right) == concat(new_left, b)
        //
        // This is a bounded ground instance of push_back/concat algebra, not
        // an alias assumption: both premises remain explicit proof guards.
        const TRUST_WP_COMPONENT_PRESERVATION_BUDGET: usize = 40;
        let component_bridge_budget =
            TRUST_WP_COMPONENT_PRESERVATION_BUDGET.min(remaining_budget.saturating_sub(count));
        if !push_entries.is_empty()
            && !pf_entries.is_empty()
            && !concat_entries.is_empty()
            && component_bridge_budget > 0
        {
            let mut alias_parent = std::collections::HashMap::new();
            for (lhs, rhs) in self.authenticated_seq_component_alias_pairs_from_assertions() {
                union_ground_seq_alias_terms(&mut alias_parent, lhs, rhs);
            }

            let mut concat_by_first: std::collections::HashMap<Term, Vec<(Term, Term, Term)>> =
                std::collections::HashMap::new();
            let mut concat_by_second: std::collections::HashMap<Term, Vec<(Term, Term, Term)>> =
                std::collections::HashMap::new();
            for (app, args) in &concat_entries {
                if args.len() == 2 {
                    let first_root = ground_seq_alias_root(&mut alias_parent, args[0]);
                    let second_root = ground_seq_alias_root(&mut alias_parent, args[1]);
                    concat_by_first
                        .entry(first_root)
                        .or_default()
                        .push((*app, args[0], args[1]));
                    concat_by_second
                        .entry(second_root)
                        .or_default()
                        .push((*app, args[0], args[1]));
                }
            }

            let mut push_front_by_element: std::collections::HashMap<Term, Vec<(Term, Term)>> =
                std::collections::HashMap::new();
            for (app, args) in &pf_entries {
                if args.len() == 2 {
                    push_front_by_element
                        .entry(args[1])
                        .or_default()
                        .push((*app, args[0]));
                }
            }

            let mut component_bridge_count = 0;
            'component_outer: for (push_app, push_args) in &push_entries {
                if push_args.len() != 2 {
                    continue;
                }
                let s = push_args[0];
                let x = push_args[1];
                let s_root = ground_seq_alias_root(&mut alias_parent, s);
                let Some(old_concats) = concat_by_first.get(&s_root) else {
                    continue;
                };
                let Some(push_fronts) = push_front_by_element.get(&x) else {
                    continue;
                };
                for (push_front_app, b) in push_fronts {
                    let b_root = ground_seq_alias_root(&mut alias_parent, *b);
                    let Some(new_concats) = concat_by_second.get(&b_root) else {
                        continue;
                    };
                    for (old_concat, old_left, old_right) in old_concats {
                        for (new_concat, new_left, new_right) in new_concats {
                            if component_bridge_count >= component_bridge_budget {
                                break 'component_outer;
                            }
                            let dedup_key = format!(
                                "ground/seq_component_preservation_bridge::{old_concat}::\
                                 {new_concat}::{push_app}::{push_front_app}"
                            );
                            if !self.mark_logic_fn_axiom_asserted(dedup_key) {
                                continue;
                            }

                            let new_left_is_push =
                                self.seq_aware_equality_term(*new_left, *push_app);
                            let old_right_is_push_front =
                                self.seq_aware_equality_term(*old_right, *push_front_app);
                            let old_left_is_source = self.seq_aware_equality_term(*old_left, s);
                            let new_right_is_tail = self.seq_aware_equality_term(*new_right, *b);
                            let guard = self.solver.and_many(&[
                                old_left_is_source,
                                new_right_is_tail,
                                new_left_is_push,
                                old_right_is_push_front,
                            ]);
                            let preserved = self.seq_aware_equality_term(*old_concat, *new_concat);
                            let bridge = self.solver.implies(guard, preserved);
                            budget_guard!();
                            self.assert_solver_term(
                                "ground/seq_component_preservation_bridge",
                                bridge,
                            );
                            count += 1;
                            component_bridge_count += 1;
                        }
                    }
                }
            }

            tracing::debug!(
                component_bridge_count,
                component_bridge_budget,
                "finite Seq component preservation bridge complete"
            );
        }

        // Ext_eq preservation bridge (#2116, #2465):
        //
        // ay-dpll cannot evaluate Boolean theory atoms (solver.eq) against
        // the E-graph when shape constraints from Seq operations are present.
        // This blocks the congruence bridge in ext_eq.rs from propagating
        // ext_eq across preservation steps, because the `eq(o_old, o_new)`
        // condition (comparing two concat terms) is never evaluated to true
        // by the solver despite being provable in the E-graph.
        //
        // Fix: directly assert `ext_eq_old => ext_eq_new` when the full
        // preservation structural pattern matches at encoding time:
        //   1. Two ext_eq entries share the same receiver
        //   2. Both "other" args are concat terms in the ground pool
        //   3. push_back(a_old, x) exists where a_old = old concat's 1st arg
        //   4. push_front(b_new, x) exists where b_new = new concat's 2nd arg
        //      and x matches the push_back's 2nd arg
        //
        // Soundness: conditions 3+4 mean the body effect and transition
        // encodings created both terms. In the verification pipeline, these
        // encodings always pair term creation with equality assertions:
        //   body effect: a_new = push_back(a_old, x)
        //   transition:  b_old = push_front(b_new, x)
        // Combined with the push_back-concat algebraic identity (asserted
        // above), these establish o_new = o_old, making the bridge redundant
        // (it follows from facts already in the formula). The bridge is
        // necessary because ay-dpll's shape constraints prevent congruence
        // closure from discovering this chain automatically.
        budget_guard!();
        if !push_entries.is_empty()
            && !pf_entries.is_empty()
            && self.encoding_cache.ext_eq_registry_len() >= 2
        {
            let concat_arg_map: std::collections::HashMap<ay_dpll::api::Term, (Term, Term)> = self
                .ground_pool
                .entries_for("seq_concat")
                .map(|es| {
                    es.iter()
                        .filter(|e| e.arg_terms.len() == 2)
                        .map(|e| (e.application, (e.arg_terms[0], e.arg_terms[1])))
                        .collect()
                })
                .unwrap_or_default();

            if !concat_arg_map.is_empty() {
                // Pre-index push_front entries as a HashSet for O(1) lookup
                // instead of O(F) linear scan per pair. (#performance_proofs)
                let pf_set: std::collections::HashSet<(Term, Term)> = pf_entries
                    .iter()
                    .filter(|(_, args)| args.len() == 2)
                    .map(|(_, args)| (args[0], args[1]))
                    .collect();

                // Pre-index push_back entries by first arg for O(1) lookup
                // instead of O(P) linear scan per pair. (#performance_proofs)
                let mut pb_by_first_arg: std::collections::HashMap<Term, Vec<Term>> =
                    std::collections::HashMap::new();
                for (_pb_app, pb_args) in &push_entries {
                    if pb_args.len() == 2 {
                        pb_by_first_arg
                            .entry(pb_args[0])
                            .or_default()
                            .push(pb_args[1]);
                    }
                }

                // Group registry entries by receiver to avoid iterating
                // cross-receiver pairs. (#2535)
                let mut by_receiver: std::collections::HashMap<Term, Vec<(Term, Term)>> =
                    std::collections::HashMap::new();
                for &(r, o, eq) in self.encoding_cache.ext_eq_registry() {
                    by_receiver.entry(r).or_default().push((o, eq));
                }

                // Budget for the ext_eq preservation bridge. The O(n²) pair
                // iteration over receiver buckets can produce thousands of
                // bridge assertions for functions with many ext_eq entries
                // sharing the same receiver (e.g., loops that push_back into
                // the same Vec repeatedly). Cap at the smaller of 40 bridges
                // and the caller-provided remaining budget — each bridge
                // creates 1 implication term in the solver arena. (#OOM, #2707)
                const TRUST_WP_EXT_EQ_BRIDGE_BUDGET: usize = 40;
                let ext_eq_bridge_budget =
                    TRUST_WP_EXT_EQ_BRIDGE_BUDGET.min(remaining_budget.saturating_sub(count));
                let mut bridge_count = 0;

                // Gap-based iteration: prioritize adjacent pairs (gap=1)
                // over distant pairs (gap=2, 3, ...). For loop-based
                // preservation proofs, adjacent ext_eq entries correspond
                // to consecutive loop iterations and are the most useful
                // bridges. This ensures the budget is spent on the most
                // valuable pairs first, avoiding the pathological case
                // where arbitrary O(n^2) pairs exhaust the budget before
                // adjacent pairs are reached. (#2708)
                let max_bucket_len = by_receiver.values().map(|b| b.len()).max().unwrap_or(0);
                'ext_eq_outer: for gap in 1..max_bucket_len {
                    for bucket in by_receiver.values() {
                        if bucket.len() <= gap {
                            continue;
                        }
                        for i in 0..(bucket.len() - gap) {
                            let j = i + gap;
                            if bridge_count >= ext_eq_bridge_budget {
                                break 'ext_eq_outer;
                            }
                            let (o_i, eq_i) = bucket[i];
                            let (o_j, eq_j) = bucket[j];
                            for &(o_old, eq_old, o_new, eq_new) in
                                &[(o_i, eq_i, o_j, eq_j), (o_j, eq_j, o_i, eq_i)]
                            {
                                if bridge_count >= ext_eq_bridge_budget {
                                    break 'ext_eq_outer;
                                }
                                let Some(&(a_old, _b_old)) = concat_arg_map.get(&o_old) else {
                                    continue;
                                };
                                let Some(&(_, b_new)) = concat_arg_map.get(&o_new) else {
                                    continue;
                                };
                                // Check: push_back(a_old, x) exists (O(1) lookup)
                                let Some(xs) = pb_by_first_arg.get(&a_old) else {
                                    continue;
                                };
                                for &x in xs {
                                    if bridge_count >= ext_eq_bridge_budget {
                                        break 'ext_eq_outer;
                                    }
                                    // Check: push_front(b_new, x) exists (O(1) lookup)
                                    if !pf_set.contains(&(b_new, x)) {
                                        continue;
                                    }
                                    // Full structural pattern matched: assert bridge
                                    let bridge = self.solver.implies(eq_old, eq_new);
                                    budget_guard!();
                                    self.assert_solver_term(
                                        "ground/ext_eq_preservation_bridge",
                                        bridge,
                                    );
                                    count += 1;
                                    bridge_count += 1;
                                }
                            }
                        }
                    }
                }

                tracing::debug!(
                    bridge_count,
                    ext_eq_bridge_budget,
                    receiver_buckets = by_receiver.len(),
                    max_bucket_len,
                    "ext_eq preservation bridge complete (#2708)"
                );
            }
        }

        count
    }
}
