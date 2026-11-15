// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mapping ground instance assertions (#2317).
//!
//! Asserts concrete (non-quantified) instances of Mapping read-over-write
//! axioms for observed ground applications. Compensates for ay-dpll's
//! single-round E-matching limitation.

/// Per-family budget for Mapping ground instances. Caps the total
/// number of Mapping assertions regardless of remaining global budget.
/// The mapping_cst x mapping_get cross-product is O(C x K) and can
/// dominate the shared budget without this cap. (#2707)
const TRUST_WP_MAPPING_FAMILY_BUDGET: usize = 60;

impl super::super::AYEncoder {
    /// Ground instances for Mapping axioms.
    ///
    /// For each observed `mapping_set(m, k, v)` application:
    /// - `mapping_get(mapping_set(m, k, v), k) = v` (same-key read)
    ///
    /// The constant-map `mapping_cst(v) × mapping_get(_, k)` cross-product is
    /// capped by the caller-provided remaining budget so Mapping cannot outrun
    /// the shared standard-library ceiling on its own. (#2707)
    pub(super) fn assert_mapping_ground_instances(&mut self, remaining_budget: usize) -> usize {
        let mut count = 0usize;
        let budget = remaining_budget.min(TRUST_WP_MAPPING_FAMILY_BUDGET);

        if budget == 0 {
            tracing::debug!(
                count,
                budget,
                remaining_budget,
                "mapping ground instances: budget exhausted before assertion (#2707)"
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
                        "mapping ground instances: budget exhausted (#2707)"
                    );
                    return count;
                }
            };
        }

        let get_decl = self.spec_func_decl_cloned("mapping_get");

        // Collect set entries before iteration to avoid borrow conflict
        let set_entries: Vec<(ay_dpll::api::Term, Vec<ay_dpll::api::Term>)> = self
            .ground_pool
            .entries_for("mapping_set")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        // Collect cst entries: mapping_cst(v) → (application, [v])
        let cst_entries: Vec<(ay_dpll::api::Term, Vec<ay_dpll::api::Term>)> = self
            .ground_pool
            .entries_for("mapping_cst")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        // Collect observed get entries for set frame and constant-map cross-product
        let get_entries: Vec<(ay_dpll::api::Term, Vec<ay_dpll::api::Term>)> = self
            .ground_pool
            .entries_for("mapping_get")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();
        let get_keys: Vec<ay_dpll::api::Term> = get_entries
            .iter()
            .filter_map(|(_, args)| args.get(1).copied())
            .collect();

        if let Some(get_decl) = get_decl.as_ref() {
            for (app, args) in &set_entries {
                if args.len() != 3 {
                    continue;
                }
                let (_m, k, v) = (args[0], args[1], args[2]);
                let set_app = *app;

                // set-get same key: mapping_get(mapping_set(m, k, v), k) = v
                budget_guard!();
                let get_set_k = self.solver.apply(get_decl, &[set_app, k]);
                let eq = self.eq_term(get_set_k, v);
                self.assert_solver_term("ground/mapping_set_get", eq);
                count = count.saturating_add(1);

                for (get_app, get_args) in &get_entries {
                    if get_args.len() != 2 {
                        continue;
                    }
                    let receiver = get_args[0];
                    let k2 = get_args[1];
                    if self.solver.get_sort(receiver) != self.solver.get_sort(set_app)
                        || self.solver.get_sort(k2) != self.solver.get_sort(k)
                    {
                        continue;
                    }

                    // set-get frame:
                    // receiver = mapping_set(m, k, v) ∧ k != k2
                    //   ⇒ mapping_get(receiver, k2) = mapping_get(m, k2)
                    budget_guard!();
                    let same_receiver = if receiver == set_app {
                        self.solver.bool_const(true)
                    } else {
                        self.eq_term(receiver, set_app)
                    };
                    let keys_differ = {
                        let keys_equal = self.eq_term(k, k2);
                        self.solver.not(keys_equal)
                    };
                    let premise = self.solver.and(same_receiver, keys_differ);
                    let get_m_k2 = self.solver.apply(get_decl, &[_m, k2]);
                    let frame_eq = self.eq_term(*get_app, get_m_k2);
                    let frame = self.solver.implies(premise, frame_eq);
                    self.assert_solver_term("ground/mapping_set_get_frame", frame);
                    count = count.saturating_add(1);
                }
            }

            // cst-get: mapping_get(mapping_cst(v), k) = v for each observed key k
            for (cst_app, args) in &cst_entries {
                if args.len() != 1 {
                    continue;
                }
                let v = args[0];
                for &k in &get_keys {
                    budget_guard!();
                    let get_cst_k = self.solver.apply(get_decl, &[*cst_app, k]);
                    let eq = self.eq_term(get_cst_k, v);
                    self.assert_solver_term("ground/mapping_cst_get", eq);
                    count = count.saturating_add(1);
                }
            }
        }

        // closure-get instances. Factored into its own method so the SCOPED
        // per-obligation solve (check_sat, num_scopes > 0) can emit them too —
        // `assert_standard_ground_instances` (this function's only standard
        // caller) runs ONLY for unscoped solves, but the function/postcondition
        // obligation pushes its negated goal in a scope, which is exactly where
        // cell/01_basic's `mapping_get(c@, v + 2)` goal lives. See the method
        // doc for the soundness argument.
        count += self.assert_mapping_closure_get_instances(budget.saturating_sub(count));

        count
    }

    /// Assert ground instances of every registered single-parameter predicate
    /// closure's defining axiom at the concrete keys observed in the obligation.
    ///
    /// A closure such as `c@ == |z: u32| z@ % 2 == 0` is lowered by
    /// `encode_closure_in_logic` to a fresh `Mapping` constant with the defining
    /// universal `forall z. mapping_get(closure_map, z) == body_int`. ay-dpll's
    /// single-round E-matching routinely fails to fire that axiom at the
    /// obligation's concrete keys (e.g. `v`, `v + 2`), leaving an
    /// otherwise-provable goal at `quantifier-unhandled`. Re-materializing the
    /// ground instance `mapping_get(closure_map, k) == body_int[z := k]` for
    /// each observed key `k` lets the proof close by pure congruence + theory
    /// reasoning, without instantiating the universal.
    ///
    /// Observed keys are gathered from BOTH the ground-pool `mapping_get`
    /// entries (registered during encoding) AND a scan of the live solver
    /// assertion stack. The latter is essential: the obligation's negated goal
    /// — e.g. `mapping_get(c@, v + 2) == 0` for the `set(v + 2)` precondition —
    /// is asserted directly into the solver but is NEVER registered as a
    /// ground-pool term application, so without the scan the ground-pool keys
    /// only carry `v` (from `get`'s ensures) and the closure body is never
    /// materialized at `v + 2`. The receivers are tied by the precondition
    /// `c@ == closure_map`, so once both keys are instantiated the obligation
    /// closes by EUF congruence (verified on ay HEAD).
    ///
    /// SOUND, zero false-accept risk: each emitted instance is a ground instance
    /// of the already-asserted closure universal, so it is entailed in every
    /// model and only lets the incomplete matcher close a genuine proof — it can
    /// never eliminate a real counterexample. (#985, #2316)
    pub(crate) fn assert_mapping_closure_get_instances(&mut self, budget: usize) -> usize {
        if budget == 0 {
            return 0;
        }
        let closure_axioms = self.closure_mapping_axioms.clone();
        if closure_axioms.is_empty() {
            return 0;
        }
        let Some(get_decl) = self.spec_func_decl_cloned("mapping_get") else {
            return 0;
        };

        // Seed observed keys from the ground-pool entries, then augment with the
        // keys present only in the live assertion stack (incl. the negated goal).
        let mut closure_keys: Vec<ay_dpll::api::Term> = self
            .ground_pool
            .entries_for("mapping_get")
            .map(|es| {
                es.iter()
                    .filter_map(|e| e.arg_terms.get(1).copied())
                    .collect()
            })
            .unwrap_or_default();
        let mut seen_keys: std::collections::HashSet<ay_dpll::api::Term> =
            closure_keys.iter().copied().collect();
        self.collect_mapping_get_keys_from_assertions(&mut closure_keys, &mut seen_keys);

        let mut count = 0usize;
        for (closure_map, bound_var, body_int) in &closure_axioms {
            let var_sort = self.solver.get_sort(*bound_var);
            for &k in &closure_keys {
                if count >= budget {
                    return count;
                }
                if self.solver.get_sort(k) != var_sort {
                    continue;
                }
                let get_closure_k = self.solver.apply(&get_decl, &[*closure_map, k]);
                let body_k = self.solver.substitute(*body_int, &[*bound_var], &[k]);
                // Keep the value-level ITE form `get == ite(pred, 1, 0)` (see
                // `eq_term_no_ite_expand`): the default expanding equality turns
                // this into a boolean-level ITE that the combined theory solver
                // churns on, which is exactly what left cell/01_basic
                // quantifier-unhandled.
                let eq = self.eq_term_no_ite_expand(get_closure_k, body_k);
                self.assert_solver_term("ground/mapping_closure_get", eq);
                count = count.saturating_add(1);
            }
        }
        count
    }

    /// Collect the key arguments of every ground `mapping_get(_, key)`
    /// application reachable from the solver's current assertion stack, appending
    /// any not already in `seen_keys` to `keys`. Used by the closure-get
    /// instantiation so the closure body is materialized at keys that appear
    /// only in the obligation's negated goal (e.g. cell/01_basic's `v + 2`),
    /// which are asserted into the solver but never registered as ground-pool
    /// term applications.
    ///
    /// Quantifier (`Forall`/`Exists`) bodies are deliberately NOT traversed: a
    /// `mapping_get` under a binder may use the BOUND variable as its key, and
    /// hoisting that out as a free "ground" key would be malformed (the bound
    /// variable would escape its quantifier). Only keys appearing in the
    /// quantifier-free portion of the stack are genuine ground terms.
    fn collect_mapping_get_keys_from_assertions(
        &self,
        keys: &mut Vec<ay_dpll::api::Term>,
        seen_keys: &mut std::collections::HashSet<ay_dpll::api::Term>,
    ) {
        let assertions = self.solver.assertions();
        let mut visited: std::collections::HashSet<ay_dpll::api::Term> =
            std::collections::HashSet::new();
        for assertion in assertions {
            self.collect_mapping_get_keys_from_term(assertion, keys, seen_keys, &mut visited);
        }
    }

    fn collect_mapping_get_keys_from_term(
        &self,
        term: ay_dpll::api::Term,
        keys: &mut Vec<ay_dpll::api::Term>,
        seen_keys: &mut std::collections::HashSet<ay_dpll::api::Term>,
        visited: &mut std::collections::HashSet<ay_dpll::api::Term>,
    ) {
        if !visited.insert(term) {
            return;
        }
        match self.solver.term_kind(term) {
            // Do not descend into binders — see the doc comment on
            // `collect_mapping_get_keys_from_assertions`.
            ay_dpll::api::TermKind::Forall | ay_dpll::api::TermKind::Exists => return,
            ay_dpll::api::TermKind::App { name, .. } if name == "mapping_get" => {
                let children = self.solver.term_children(term);
                if children.len() == 2 && seen_keys.insert(children[1]) {
                    keys.push(children[1]);
                }
            }
            _ => {}
        }
        for child in self.solver.term_children(term) {
            self.collect_mapping_get_keys_from_term(child, keys, seen_keys, visited);
        }
    }
}
