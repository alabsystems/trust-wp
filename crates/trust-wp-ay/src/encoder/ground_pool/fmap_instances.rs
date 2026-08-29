// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FMap ground instance assertions.
//!
//! Extracted from `ground_pool.rs` as part of encoder decomposition (#1988).

use ay_dpll::api::{FuncDecl, Sort, Term, TermKind};

fn parse_leading_usize(suffix: &str) -> Option<usize> {
    let digits_len = suffix.bytes().take_while(u8::is_ascii_digit).count();
    if digits_len == 0 {
        return None;
    }
    suffix[..digits_len].parse::<usize>().ok()
}

/// Per-family budget for FMap ground instances. Caps the total
/// number of FMap assertions regardless of remaining global budget.
/// High enough for typical single-function verification, low enough
/// to prevent the insert x contains/lookup cross-product from
/// overwhelming the solver. (#2707)
const TRUST_WP_FMAP_FAMILY_BUDGET: usize = 80;

/// Per-sub-loop budget for insert-contains and insert-lookup frame
/// assertions within FMap. Prevents any single cross-product category
/// (I x C or I x L) from consuming the entire family budget, leaving
/// room for merge-contains, len non-negativity, and base insert facts.
/// Set to half the family budget so both insert-contains and
/// insert-lookup get a fair share. (#2707)
const TRUST_WP_FMAP_INSERT_CROSS_BUDGET: usize = 40;

/// Per-sub-loop budget for merge-contains cross-product assertions.
/// Prevents O(M x C) blowup from consuming the entire family budget. (#2707)
const TRUST_WP_FMAP_MERGE_CROSS_BUDGET: usize = 40;

impl super::super::AYEncoder {
    fn direct_asserted_equality_sides(&self, assertion: Term) -> Option<(Term, Term)> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(assertion) else {
            return None;
        };
        if name != "=" {
            return None;
        }
        let children = self.solver.term_children(assertion);
        let [left, right] = children.as_slice() else {
            return None;
        };
        Some((*left, *right))
    }

    fn asserted_term_equality(&self, lhs: Term, rhs: Term) -> bool {
        lhs == rhs
            || self.solver.assertions().iter().any(|assertion| {
                self.direct_asserted_equality_sides(*assertion)
                    .is_some_and(|(left, right)| {
                        (left == lhs && right == rhs) || (left == rhs && right == lhs)
                    })
            })
    }

    fn native_constructor_arg_terms(&self, term: Term) -> Option<Vec<Term>> {
        let TermKind::App { name, num_args } = self.solver.term_kind(term) else {
            return None;
        };
        let term_sort = self.solver.get_sort(term);
        for datatype in self.datatypes_iter() {
            let datatype_sort = Sort::Datatype(datatype.clone());
            let datatype_term_sort = datatype_sort.as_term_sort();
            if term_sort != datatype_sort && term_sort != datatype_term_sort {
                continue;
            }
            for constructor in &datatype.constructors {
                if constructor.name == name && constructor.fields.len() == num_args {
                    return Some(self.solver.term_children(term));
                }
            }
        }
        None
    }

    fn asserted_native_constructor_args_for_value(&self, value: Term) -> Vec<Vec<Term>> {
        let mut aliases = Vec::new();
        if let Some(args) = self.native_constructor_arg_terms(value) {
            aliases.push(args);
        }
        for assertion in self.solver.assertions() {
            let Some((left, right)) = self.direct_asserted_equality_sides(assertion) else {
                continue;
            };
            let candidate = if left == value {
                right
            } else if right == value {
                left
            } else {
                continue;
            };
            if let Some(args) = self.native_constructor_arg_terms(candidate) {
                aliases.push(args);
            }
        }
        aliases
    }

    fn fmap_contains_decl_for_terms(&mut self, map: Term, key: Term) -> FuncDecl {
        let map_sort = self.solver.get_sort(map);
        let key_sort = self.solver.get_sort(key);
        self.get_or_declare_spec_fn("fmap_contains", &[map_sort, key_sort], Sort::Bool)
    }

    fn fmap_lookup_decl_for_terms(&mut self, map: Term, key: Term, value_sort: Sort) -> FuncDecl {
        let map_sort = self.solver.get_sort(map);
        let key_sort = self.solver.get_sort(key);
        self.get_or_declare_spec_fn("fmap_lookup", &[map_sort, key_sort], value_sort)
    }

    fn observed_lookup_sort(
        &self,
        lookup_entries: &[(Term, Vec<Term>)],
        map: Term,
        key: Term,
    ) -> Option<Sort> {
        lookup_entries
            .iter()
            .find(|(_, args)| {
                args.len() == 2
                    && args[0] == map
                    && args[1] == key
                    && self.solver.get_sort(args[1]) == self.solver.get_sort(key)
            })
            .map(|(application, _)| self.solver.get_sort(*application))
    }

    fn tuple_field_accessors_for_domain(&self, receiver_sort: &Sort) -> Vec<(usize, FuncDecl)> {
        let smt_field_prefix = trust_wp_core::logic::logic_fn_smt_name(
            trust_wp_core::formula::internal::tuple_lowering::TUPLE_FIELD_LOGIC_FN_PREFIX,
        );

        self.logic_funcs_iter()
            .filter_map(|(name, decl)| {
                let suffix = name.strip_prefix(&smt_field_prefix)?;
                let index = parse_leading_usize(suffix)?;
                (decl.domain().first() == Some(receiver_sort)).then_some((index, decl.clone()))
            })
            .collect()
    }

    fn fmap_payload_projection_pairs(
        &mut self,
        lookup_value: Term,
        inserted_value: Term,
    ) -> Vec<(Term, Term)> {
        let value_sort = self.solver.get_sort(inserted_value);
        if self.solver.get_sort(lookup_value) != value_sort {
            return Vec::new();
        }

        let accessors = self.tuple_field_accessors_for_domain(&value_sort);
        let mut pairs = Vec::new();
        for (index, accessor_decl) in accessors {
            let lookup_projection = self.solver.apply(&accessor_decl, &[lookup_value]);
            let inserted_projection = self.solver.apply(&accessor_decl, &[inserted_value]);
            pairs.push((lookup_projection, inserted_projection));

            if let Some((selector_name, selector_sort)) =
                self.native_positional_field_selector(&value_sort, index)
            {
                if let (Ok(lookup_selector), Ok(inserted_selector)) = (
                    self.solver.try_datatype_selector(
                        &selector_name,
                        lookup_value,
                        selector_sort.clone(),
                    ),
                    self.solver.try_datatype_selector(
                        &selector_name,
                        inserted_value,
                        selector_sort,
                    ),
                ) {
                    pairs.push((lookup_selector, inserted_selector));
                }
            }
        }

        pairs
    }

    fn fmap_payload_direct_constructor_projection_pairs(
        &mut self,
        lookup_value: Term,
        inserted_value: Term,
    ) -> Vec<(Term, Term)> {
        let value_sort = self.solver.get_sort(inserted_value);
        if self.solver.get_sort(lookup_value) != value_sort {
            return Vec::new();
        }

        let accessors = self.tuple_field_accessors_for_domain(&value_sort);
        let constructor_aliases = self.asserted_native_constructor_args_for_value(inserted_value);
        let mut pairs = Vec::new();
        for arg_terms in constructor_aliases {
            for (index, accessor_decl) in &accessors {
                let Some(arg_term) = arg_terms.get(*index).copied() else {
                    continue;
                };
                if accessor_decl.range() != &self.solver.get_sort(arg_term) {
                    continue;
                }
                let lookup_projection = self.solver.apply(accessor_decl, &[lookup_value]);
                pairs.push((lookup_projection, arg_term));
            }
        }
        pairs
    }

    fn fmap_payload_projection_pairs_including_constructor_aliases(
        &mut self,
        lookup_value: Term,
        inserted_value: Term,
    ) -> Vec<(Term, Term)> {
        let mut pairs = self.fmap_payload_projection_pairs(lookup_value, inserted_value);
        pairs.extend(
            self.fmap_payload_direct_constructor_projection_pairs(lookup_value, inserted_value),
        );
        pairs
    }

    /// Ground instances for FMap axioms.
    #[allow(clippy::too_many_lines)]
    pub(super) fn assert_fmap_ground_instances(&mut self, remaining_budget: usize) -> usize {
        let mut count = 0;
        // FMap keeps its historical per-family cap of 80, but the effective
        // budget is now the smaller of that cap and the caller's remaining
        // shared cross-product budget. (#2707)
        let budget = remaining_budget.min(TRUST_WP_FMAP_FAMILY_BUDGET);

        if budget == 0 {
            tracing::debug!(
                count,
                budget,
                remaining_budget,
                "fmap ground instances: effective budget exhausted before assertion (#2707)"
            );
            return 0;
        }

        macro_rules! budget_guard {
            () => {
                if count >= budget {
                    tracing::debug!(
                        count,
                        budget,
                        remaining_budget,
                        "fmap ground instances: effective budget exhausted (#2707)"
                    );
                    return count;
                }
            };
        }

        let insert_decl = self.spec_func_decl_cloned("fmap_insert");
        let len_decl = self.spec_func_decl_cloned("fmap_len");

        // For each fmap_insert(m, k, v) application:
        //   - contains(insert(m, k, v), k) = true
        //   - lookup(insert(m, k, v), k) = v
        let insert_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fmap_insert")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();
        let contains_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fmap_contains")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();
        let lookup_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fmap_lookup")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        if insert_decl.is_some() {
            for (app, args) in &insert_entries {
                if count >= budget {
                    break;
                }
                if args.len() != 3 {
                    continue;
                }
                let (m, k, v) = (args[0], args[1], args[2]);
                let insert_app = *app;

                // insert-contains: contains(insert(m, k, v), k) = true
                budget_guard!();
                let contains_decl = self.fmap_contains_decl_for_terms(insert_app, k);
                let contains_ins_k = self.solver.apply(&contains_decl, &[insert_app, k]);
                self.assert_solver_term("ground/fmap_insert_contains", contains_ins_k);
                count += 1;

                // insert-lookup: lookup(insert(m, k, v), k) = v
                budget_guard!();
                let lookup_decl =
                    self.fmap_lookup_decl_for_terms(insert_app, k, self.solver.get_sort(v));
                let lookup_ins_k = self.solver.apply(&lookup_decl, &[insert_app, k]);
                self.assert_ground_equality_with_seq_propagation(
                    "ground/fmap_insert_lookup",
                    lookup_ins_k,
                    v,
                );
                count += 1;

                for (lookup_projection, inserted_projection) in self
                    .fmap_payload_projection_pairs_including_constructor_aliases(lookup_ins_k, v)
                {
                    budget_guard!();
                    self.assert_ground_equality_with_seq_propagation(
                        "ground/fmap_insert_lookup_projection",
                        lookup_projection,
                        inserted_projection,
                    );
                    count += 1;
                }

                // insert-len: len(insert(m, k, v)) = ite(contains(m, k), len(m), len(m) + 1)
                if let Some(len_decl) = len_decl.as_ref() {
                    budget_guard!();
                    let contains_decl = self.fmap_contains_decl_for_terms(m, k);
                    let contains_m_k = self.solver.apply(&contains_decl, &[m, k]);
                    let len_ins = if self.use_fmap_len_proxies() {
                        self.fmap_len_term(insert_app)
                    } else {
                        self.solver.apply(len_decl, &[insert_app])
                    };
                    let len_m = if self.use_fmap_len_proxies() {
                        self.fmap_len_term(m)
                    } else {
                        self.solver.apply(len_decl, &[m])
                    };
                    let one = self.solver.int_const(1);
                    let len_plus_1 = self.solver.add(len_m, one);
                    let ite_len = self.solver.ite(contains_m_k, len_m, len_plus_1);
                    let eq = self.eq_term(len_ins, ite_len);
                    self.assert_solver_term("ground/fmap_insert_len", eq);
                    count += 1;
                }

                // Eager per-query insert semantics for observed contains/lookup
                // calls. This avoids relying on quantified insert frame axioms
                // when loop VCs query `insert(m, k, v)` at a skolem key. (#2116)
                //
                // Budget-gated: these cross-product loops are O(I×C) and O(I×L).
                // Without the effective `min(remaining_budget, 80)` cap, a
                // function with many insert + contains/lookup operations can
                // produce thousands of assertions. (#OOM, #2707)
                // Per-sub-loop budget for insert-contains cross-product (#2707):
                // prevents I×C from consuming the entire family budget.
                if count < budget {
                    let mut insert_contains_count = 0;
                    for (contains_app, c_args) in &contains_entries {
                        if count >= budget
                            || insert_contains_count >= TRUST_WP_FMAP_INSERT_CROSS_BUDGET
                        {
                            break;
                        }
                        if c_args.len() != 2 {
                            continue;
                        }
                        let receiver = c_args[0];
                        let key2 = c_args[1];
                        if self.solver.get_sort(receiver) != self.solver.get_sort(insert_app)
                            || self.solver.get_sort(key2) != self.solver.get_sort(k)
                        {
                            continue;
                        }

                        let contains_decl = self.fmap_contains_decl_for_terms(receiver, key2);
                        let same_receiver = if receiver == insert_app {
                            self.solver.bool_const(true)
                        } else {
                            self.eq_term(receiver, insert_app)
                        };
                        let keys_equal = self.eq_term(k, key2);
                        let keys_differ = self.solver.not(keys_equal);
                        let same_entry = self.solver.and(same_receiver, keys_equal);
                        let same_entry_asserted = self.asserted_term_equality(receiver, insert_app)
                            && self.asserted_term_equality(k, key2);
                        let same_receiver_distinct_key =
                            self.solver.and(same_receiver, keys_differ);
                        let contains_ins_k2 = *contains_app;
                        let contains_m_k2 = self.solver.apply(&contains_decl, &[m, key2]);

                        budget_guard!();
                        let same_key = if same_entry_asserted {
                            contains_ins_k2
                        } else {
                            self.solver.implies(same_entry, contains_ins_k2)
                        };
                        self.assert_solver_term("ground/fmap_insert_contains_same_key", same_key);
                        count += 1;
                        insert_contains_count += 1;

                        budget_guard!();
                        let frame_eq = self.eq_term(contains_ins_k2, contains_m_k2);
                        let frame = self.solver.implies(same_receiver_distinct_key, frame_eq);
                        self.assert_solver_term("ground/fmap_insert_contains_frame", frame);
                        count += 1;
                        insert_contains_count += 1;
                    }
                }

                // Per-sub-loop budget for insert-lookup cross-product (#2707):
                // prevents I×L from consuming the entire family budget.
                if count < budget {
                    let mut insert_lookup_count = 0;
                    for (lookup_app, l_args) in &lookup_entries {
                        if count >= budget
                            || insert_lookup_count >= TRUST_WP_FMAP_INSERT_CROSS_BUDGET
                        {
                            break;
                        }
                        if l_args.len() != 2 {
                            continue;
                        }
                        let receiver = l_args[0];
                        let key2 = l_args[1];
                        if self.solver.get_sort(receiver) != self.solver.get_sort(insert_app)
                            || self.solver.get_sort(key2) != self.solver.get_sort(k)
                        {
                            continue;
                        }

                        let lookup_value_sort = self.solver.get_sort(*lookup_app);
                        let lookup_decl =
                            self.fmap_lookup_decl_for_terms(receiver, key2, lookup_value_sort);
                        let same_receiver = if receiver == insert_app {
                            self.solver.bool_const(true)
                        } else {
                            self.eq_term(receiver, insert_app)
                        };
                        let keys_equal = self.eq_term(k, key2);
                        let keys_differ = self.solver.not(keys_equal);
                        let same_entry = self.solver.and(same_receiver, keys_equal);
                        let same_entry_asserted = self.asserted_term_equality(receiver, insert_app)
                            && self.asserted_term_equality(k, key2);
                        let same_receiver_distinct_key =
                            self.solver.and(same_receiver, keys_differ);
                        let lookup_ins_k2 = *lookup_app;
                        let lookup_m_k2 = self.solver.apply(&lookup_decl, &[m, key2]);

                        budget_guard!();
                        if same_entry_asserted {
                            self.assert_ground_equality_with_seq_propagation(
                                "ground/fmap_insert_lookup_same_key",
                                lookup_ins_k2,
                                v,
                            );
                        } else {
                            let same_key_eq = self.seq_aware_equality_term(lookup_ins_k2, v);
                            let same_key = self.solver.implies(same_entry, same_key_eq);
                            self.assert_solver_term("ground/fmap_insert_lookup_same_key", same_key);
                        }
                        count += 1;
                        insert_lookup_count += 1;

                        for (lookup_projection, inserted_projection) in self
                            .fmap_payload_projection_pairs_including_constructor_aliases(
                                lookup_ins_k2,
                                v,
                            )
                        {
                            if count >= budget
                                || insert_lookup_count >= TRUST_WP_FMAP_INSERT_CROSS_BUDGET
                            {
                                break;
                            }
                            if same_entry_asserted {
                                self.assert_ground_equality_with_seq_propagation(
                                    "ground/fmap_insert_lookup_projection_same_key",
                                    lookup_projection,
                                    inserted_projection,
                                );
                            } else {
                                let projection_eq = self.seq_aware_equality_term(
                                    lookup_projection,
                                    inserted_projection,
                                );
                                let projection_same_key =
                                    self.solver.implies(same_entry, projection_eq);
                                self.assert_solver_term(
                                    "ground/fmap_insert_lookup_projection_same_key",
                                    projection_same_key,
                                );
                            }
                            count += 1;
                            insert_lookup_count += 1;
                        }

                        budget_guard!();
                        let frame_eq = self.eq_term(lookup_ins_k2, lookup_m_k2);
                        let frame = self.solver.implies(same_receiver_distinct_key, frame_eq);
                        self.assert_solver_term("ground/fmap_insert_lookup_frame", frame);
                        count += 1;
                        insert_lookup_count += 1;
                    }
                }
            }
        }

        // fmap_len non-negativity for each observed len application.
        //
        // Staged retirement (CAP-80): this is the only FMap family whose
        // quantified axiom is binder-exact (`forall m. fmap_len(m) >= 0`),
        // i.e. inside ay's decided rank-9 fragment. When that universal was
        // actually asserted for this solve (coverage flag, set only by
        // `assert_fmap_axioms` in non-proxy len mode) AND the retirement
        // stage is >= 1, the ground copies are redundant consequences and
        // are skipped — the quantifier passes through to ay instead. Both
        // conditions are fail-closed: proxy mode (`Logic::All`), non-Int
        // legacy signatures, and encoder users that never assert the FMap
        // axioms keep the ground family as the sole semantic source. See
        // `ground_pool::retirement`.
        let len_nonneg_demoted = super::retirement::family_demoted(
            super::retirement::classify(super::retirement::FmapGroundFamily::LenNonneg),
            self.fmap_quantified_coverage.len_nonneg,
            self.ground_pool_retirement_stage(),
        );
        let len_entries: Vec<Vec<Term>> = self
            .ground_pool
            .entries_for("fmap_len")
            .map(|es| es.iter().map(|e| e.arg_terms.clone()).collect())
            .unwrap_or_default();
        if let Some(len_decl) = len_decl.as_ref() {
            if len_nonneg_demoted {
                tracing::debug!(
                    family = "fmap_len_nonneg",
                    stage = self.ground_pool_retirement_stage(),
                    quantified_axiom_asserted = self.fmap_quantified_coverage.len_nonneg,
                    entries = len_entries.len(),
                    "fmap ground instances: binder-exact family demoted to ay \
                     quantifier passthrough (CAP-80 staged retirement)"
                );
            } else {
                let zero = self.solver.int_const(0);
                for args in &len_entries {
                    if args.len() == 1 {
                        budget_guard!();
                        let len_app = if self.use_fmap_len_proxies() {
                            self.fmap_len_term(args[0])
                        } else {
                            self.solver.apply(len_decl, &[args[0]])
                        };
                        let ge_zero = self.solver.ge(len_app, zero);
                        self.assert_solver_term("ground/fmap_len_nonneg", ge_zero);
                        count += 1;
                    }
                }
            }
        }

        // fmap_merge contains-forward: for each merge(m1, m2), assert
        // membership propagation from both source maps. (#2288)
        // Mirrors quantified axioms: merge-contains-forward-left/right.
        let merge_decl = self.spec_func_decl_cloned("fmap_merge");
        let merge_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fmap_merge")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        if merge_decl.is_some() {
            // Collect observed fmap_contains ground entries for cross-referencing
            let contains_entries: Vec<Vec<Term>> = self
                .ground_pool
                .entries_for("fmap_contains")
                .map(|es| es.iter().map(|e| e.arg_terms.clone()).collect())
                .unwrap_or_default();

            for (merge_app, merge_args) in &merge_entries {
                if count >= budget {
                    break;
                }
                if merge_args.len() != 2 {
                    continue;
                }
                let m1 = merge_args[0];
                let m2 = merge_args[1];
                let merge_term = *merge_app;

                // For each key k observed in a contains(_, k) call, assert
                // merge-related ground instances when the receiver matches merge_term.
                // Per-sub-loop budget prevents O(M×C) blowup. (#2707)
                let mut merge_contains_count = 0;
                for c_args in &contains_entries {
                    if count >= budget || merge_contains_count >= TRUST_WP_FMAP_MERGE_CROSS_BUDGET {
                        break;
                    }
                    if c_args.len() != 2 {
                        continue;
                    }
                    let c_receiver = c_args[0];
                    let k = c_args[1];

                    // Only fire when contains is applied to the merge result
                    if c_receiver != merge_term {
                        continue;
                    }

                    // contains(m1, k) => contains(merge(m1, m2), k)
                    let contains_decl = self.fmap_contains_decl_for_terms(merge_term, k);
                    let c_m1_k = self.solver.apply(&contains_decl, &[m1, k]);
                    let c_merge_k = self.solver.apply(&contains_decl, &[merge_term, k]);
                    let fwd_left = self.solver.implies(c_m1_k, c_merge_k);
                    budget_guard!();
                    self.assert_solver_term("ground/fmap_merge_contains_left", fwd_left);
                    count += 1;
                    merge_contains_count += 1;

                    // contains(m2, k) => contains(merge(m1, m2), k)
                    let c_m2_k = self.solver.apply(&contains_decl, &[m2, k]);
                    let fwd_right = self.solver.implies(c_m2_k, c_merge_k);
                    budget_guard!();
                    self.assert_solver_term("ground/fmap_merge_contains_right", fwd_right);
                    count += 1;
                    merge_contains_count += 1;

                    // contains(merge(m1, m2), k) => contains(m1, k) || contains(m2, k)
                    let m1_or_m2 = self.solver.or(c_m1_k, c_m2_k);
                    let bwd = self.solver.implies(c_merge_k, m1_or_m2);
                    budget_guard!();
                    self.assert_solver_term("ground/fmap_merge_contains_bwd", bwd);
                    count += 1;
                    merge_contains_count += 1;

                    // Left-bias lookup: contains(m1, k) => lookup(merge, k) = lookup(m1, k)
                    let lookup_value_sort = self
                        .observed_lookup_sort(&lookup_entries, merge_term, k)
                        .unwrap_or(Sort::Int);
                    let lookup_decl =
                        self.fmap_lookup_decl_for_terms(merge_term, k, lookup_value_sort);
                    let l_merge_k = self.solver.apply(&lookup_decl, &[merge_term, k]);
                    let l_m1_k = self.solver.apply(&lookup_decl, &[m1, k]);
                    let eq = self.eq_term(l_merge_k, l_m1_k);
                    let lookup_left = self.solver.implies(c_m1_k, eq);
                    budget_guard!();
                    self.assert_solver_term("ground/fmap_merge_lookup_left", lookup_left);
                    count += 1;
                    merge_contains_count += 1;

                    // Right-only lookup: !contains(m1, k) && contains(m2, k) =>
                    //   lookup(merge, k) = lookup(m2, k)
                    // Mirrors the quantified axiom in axioms.rs (Merge-lookup-right-only).
                    let not_c_m1_k = self.solver.not(c_m1_k);
                    let premise = self.solver.and(not_c_m1_k, c_m2_k);
                    let l_m2_k = self.solver.apply(&lookup_decl, &[m2, k]);
                    let eq_right = self.eq_term(l_merge_k, l_m2_k);
                    let lookup_right = self.solver.implies(premise, eq_right);
                    budget_guard!();
                    self.assert_solver_term("ground/fmap_merge_lookup_right", lookup_right);
                    count += 1;
                    merge_contains_count += 1;
                }
            }
        }

        count
    }
}
