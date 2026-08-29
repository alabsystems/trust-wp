// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Iterator `produces` reflexivity, transitivity, and ground instantiation axioms.
//!
//! This module encodes the two fundamental laws of the `IteratorSpec::produces`
//! relation (reflexivity and transitivity) as quantified SMT axioms, plus
//! ground transitivity instances for observed `produces` calls under a three-tier
//! cap system (#2688, #2671, #3313):
//! - 2-hop: always (calls 1 to `TRUST_WP_PRODUCES_GROUND_CAP` = 6)
//! - 3-hop: calls 1 to `TRUST_WP_PRODUCES_THREE_HOP_CAP` (4)
//! - 4-hop: calls 1 to `TRUST_WP_PRODUCES_FOUR_HOP_CAP` (4)
//!
//! A hard storage cap (`TRUST_WP_PRODUCES_GROUND_CAP * 2 = 12`) in `ProducesGroundCalls::insert()`
//! prevents the per-symbol tracker from growing unboundedly after the cap is hit. (#2709)
//!
//! Extracted from `axioms.rs` in #1528 Phase 3.
//!
//! # Panic isolation bypass (#1806)
//!
//! Axiom calls in this module use `self.solver.assert_term()` directly rather
//! than the panic-isolated `self.assert_solver_term()` wrapper from `solver.rs`.
//! See `axioms.rs` module docs for rationale.

use ay_dpll::api::{FuncDecl, Sort, Term};
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::{
    ground_pool::AxiomKind,
    produces_ground::{is_adapter_produces_symbol, ProducesGroundCall},
    sort_context::is_seq_family_sort,
    AYEncoder,
};

fn should_emit_produces_ground_chain(is_adapter: bool, chain: &[ProducesGroundCall]) -> bool {
    if chain.len() <= 2 && !is_adapter {
        return true;
    }

    chain
        .windows(2)
        .all(|adjacent| adjacent[0].to == adjacent[1].from)
}

impl AYEncoder {
    /// Assert produces reflexivity and transitivity axioms (#379).
    ///
    /// These encode the two fundamental laws of the `IteratorSpec::produces` relation:
    ///
    /// **Reflexivity:** `forall iter. produces(iter, seq_empty, iter)`
    /// An iterator that produces nothing stays in the same state.
    ///
    /// **Transitivity:** `forall a ab b bc c. produces(a, ab, b) && produces(b, bc, c)
    ///   ==> produces(a, concat(ab, bc), c)`
    /// If iterator state `a` produces `ab` to reach `b`, and `b` produces `bc` to
    /// reach `c`, then `a` produces the concatenation `ab ++ bc` to reach `c`.
    ///
    /// Called lazily from `encode_produces_predicate` on first use of each
    /// concrete `produces` SMT function symbol.
    #[allow(clippy::similar_names)] // Mathematical convention: a, ab, b, bc, c
    pub(crate) fn assert_produces_axioms(&mut self, produces_func: &FuncDecl) {
        let func_name = produces_func.name().to_string();
        let dedup_key = format!("produces_axioms::{func_name}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        let param_sorts = produces_func.domain();
        if param_sorts.len() != 3 {
            return;
        }
        let state_sort = param_sorts[0].clone();
        let visited_sort = param_sorts[1].clone();
        let succ_sort = param_sorts[2].clone();
        if state_sort != succ_sort {
            // IteratorSpec laws require homogeneous state transitions.
            return;
        }

        let seq_sort = self.get_seq_sort();
        if visited_sort != seq_sort {
            return;
        }
        let seq_funcs = self.ensure_seq_theory();

        // Get seq_empty and seq_concat from the Seq function table
        let seq_empty_term = seq_funcs.seq_empty;
        let seq_concat_decl = seq_funcs.seq_concat.clone();

        // --- Reflexivity: forall iter. produces(iter, seq_empty, iter) ---
        let refl_iter = self
            .solver
            .fresh_var("produces_refl_iter", state_sort.clone());
        let refl_body = self
            .solver
            .apply(produces_func, &[refl_iter, seq_empty_term, refl_iter]);
        // Trigger: produces(iter, seq_empty, iter) — instantiate when a produces
        // application with seq_empty appears (#1586).
        let refl_axiom = self
            .solver
            .forall_with_triggers(&[refl_iter], refl_body, &[&[refl_body]]);
        self.solver.assert_term(refl_axiom);

        // --- Transitivity: forall a ab b bc c.
        //       produces(a, ab, b) && produces(b, bc, c)
        //         ==> produces(a, concat(ab, bc), c) ---
        let trans_a = self
            .solver
            .fresh_var("produces_trans_a", state_sort.clone());
        let trans_ab = self
            .solver
            .fresh_var("produces_trans_ab", visited_sort.clone());
        let trans_b = self
            .solver
            .fresh_var("produces_trans_b", state_sort.clone());
        let trans_bc = self.solver.fresh_var("produces_trans_bc", visited_sort);
        let trans_c = self.solver.fresh_var("produces_trans_c", state_sort);

        let prod_a_ab_b = self
            .solver
            .apply(produces_func, &[trans_a, trans_ab, trans_b]);
        let prod_b_bc_c = self
            .solver
            .apply(produces_func, &[trans_b, trans_bc, trans_c]);
        let premise = self.solver.and(prod_a_ab_b, prod_b_bc_c);

        let ab_bc = self.solver.apply(&seq_concat_decl, &[trans_ab, trans_bc]);
        let prod_a_abbc_c = self.solver.apply(produces_func, &[trans_a, ab_bc, trans_c]);

        let trans_body = self.solver.implies(premise, prod_a_abbc_c);
        // Use a multi-trigger over both premises so E-matching binds all
        // quantified vars together (a, ab, b, bc, c). Single-pattern
        // auto-triggers cannot bind `b` and `bc` from one produces call.
        let trans_axiom = self.solver.forall_with_triggers(
            &[trans_a, trans_ab, trans_b, trans_bc, trans_c],
            trans_body,
            &[&[prod_a_ab_b, prod_b_bc_c]],
        );
        self.solver.assert_term(trans_axiom);
    }

    /// Materialize the user's `produces` logic-function body in the invariant
    /// symbol's argument frame (#produces-body-materialization).
    ///
    /// # Motivation
    ///
    /// The loop invariant `iter_old.produces(produced, it)` encodes to the
    /// opaque Bool UF `method_produces_3_<sorts>` (see
    /// `encode_produces_predicate`). The user's `#[logic(open)] fn produces`
    /// definition, however, is registered under the disjoint symbol
    /// `logic_produces` via `register_logic_fn`, and its body (in particular the
    /// index property `forall<i> 0 <= i < visited.len() ==> visited[i] == ...`)
    /// is therefore never applied to the invariant symbol's arguments. The
    /// solver consequently has no way to learn what `method_produces(a, s, b)`
    /// *means* and the loop obligations stay SAT.
    ///
    /// This bridges the two symbols by emitting the forward direction of the
    /// open `produces` logic function's defining biconditional in the
    /// `method_produces` frame:
    ///
    /// ```text
    /// forall a, s, b. method_produces(a, s, b) ==> body[self/a, visited/s, o/b]
    /// ```
    ///
    /// triggered on `method_produces(a, s, b)`.
    ///
    /// # Soundness (completeness-only)
    ///
    /// This is the EXACT body the user wrote for the open `produces` logic
    /// function — reused verbatim from the ground-pool `Defining` axiom entry
    /// (the same `PureExpr` that feeds `logic_produces`). For an open logic
    /// function `f(args) <=> body(args)` is a valid definition, so either
    /// direction of it is a valid consequence; we emit the forward direction
    /// `f(args) ==> body(args)`. The axiom can never make a false formula UNSAT:
    /// worst case the solver fails to instantiate it and the obligation stays
    /// SAT/Unknown. We do NOT hand-roll a body here — a stronger/different body
    /// would risk unsoundness. (The reverse direction is omitted purely for
    /// solver performance; see the emission site below.)
    ///
    /// Only fires when:
    /// - the produces UF is homogeneous (state = succ sort) with a Seq visited
    ///   slot (the IteratorSpec shape), and
    /// - a matching open `produces` defining axiom exists in the ground pool
    ///   (i.e. the user actually defined an open `produces` body). Opaque
    ///   `produces` definitions register no `Defining` ground-pool entry, so this
    ///   is a no-op for them — preserving the abstract reflexivity/transitivity
    ///   treatment.
    pub(crate) fn assert_user_produces_body_definition(&mut self, produces_func: &FuncDecl) {
        if self.quantifier_state.quantifier_depth() > 0 {
            // Bound variables in scope: the fresh quantifier we would emit could
            // capture them. Defer to a top-level produces application.
            return;
        }

        let func_name = produces_func.name().to_string();
        let dedup_key = format!("produces_body_def::{func_name}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        let param_sorts = produces_func.domain();
        if param_sorts.len() != 3 {
            return;
        }
        let state_sort = param_sorts[0].clone();
        let visited_sort = param_sorts[1].clone();
        let succ_sort = param_sorts[2].clone();
        if state_sort != succ_sort {
            return;
        }
        let seq_sort = self.get_seq_sort();
        if visited_sort != seq_sort {
            return;
        }

        // Locate the open `produces` logic-function body. It is registered with
        // the ground pool as a `Defining` axiom keyed by `logic_produces`. We
        // reuse its body PureExpr verbatim (the same translation that feeds the
        // `logic_produces` defining axiom) so the materialized definition is
        // identical to the user's open definition.
        let produces_smt_name = trust_wp_core::logic::logic_fn_smt_name("produces");
        let Some((params, body)) = self
            .ground_pool
            .axioms()
            .iter()
            .find(|a| {
                a.fn_symbol == produces_smt_name
                    && a.kind == AxiomKind::Defining
                    && a.params.len() == 3
            })
            .map(|a| (a.params.clone(), a.body.clone()))
        else {
            // No open `produces` body available (opaque produces, or a built-in
            // iterator whose produces is handled by the driver rewrite). Leave
            // the abstract refl/trans treatment in place.
            return;
        };

        // Gate: only materialize "simple" produces bodies. Heavy adapter bodies
        // (e.g. `Skip`, `Take`, `Map`) define `produces` in terms of an
        // EXISTENTIAL over an auxiliary sequence and a NESTED `produces` call on
        // the inner iterator. Materializing such a body in the invariant frame
        // arms an expensive nested quantifier that the E-matcher cannot
        // dispatch within budget, turning fast (counterexample) loop VCs into
        // hard TIMEOUTS — a completeness regression (observed flipping
        // `iterators/04_skip` from pass to timeout). Restricting to bodies with
        // no existential and no nested iterator-spec call keeps the win on the
        // arithmetic produces definitions (Range and friends) while never
        // burdening the adapters, which keep their abstract refl/trans
        // treatment. Soundness is unaffected either way (this is an additive,
        // completeness-only axiom).
        if !Self::produces_body_is_materializable(&body) {
            return;
        }

        // Bind the three logic-fn params to fresh bound vars carrying the
        // method_produces domain sorts: self -> state, visited -> Seq, o -> succ.
        let bound_sorts = [state_sort, visited_sort.clone(), succ_sort];
        let mut bound_vars: Vec<Term> = Vec::with_capacity(3);
        let mut old_bindings: Vec<(String, Option<Term>)> = Vec::with_capacity(3);
        let mut old_sorts: Vec<(String, Option<Sort>)> = Vec::with_capacity(3);

        for (param, sort) in params.iter().zip(bound_sorts.iter()) {
            let qvar_id = self.next_quantifier_var_id();
            let bound_var = self
                .solver
                .fresh_var(&format!("produces_body_{param}_{qvar_id}"), sort.clone());
            bound_vars.push(bound_var);
            if is_seq_family_sort(sort) {
                self.record_sort_hint(param.clone(), ExprSort::Seq);
            }
            old_sorts.push((
                param.clone(),
                self.insert_var_sort(param.clone(), sort.clone()),
            ));
            old_bindings.push((param.clone(), self.insert_var(param.clone(), bound_var)));
            self.bind_quantifier_var(param.clone());
        }

        self.quantifier_state.inc_quantifier_depth();
        let body_result = self.encode_pure(&body);
        self.quantifier_state.dec_quantifier_depth();

        for param in params.iter().rev() {
            self.unbind_quantifier_var(param);
        }
        for (name, old_sort) in old_sorts {
            self.restore_var_sort(&name, old_sort);
        }
        for (name, old) in old_bindings {
            self.restore_var(&name, old);
        }

        let body_term = match body_result {
            Ok(term) => term,
            Err(_) => return,
        };

        // method_produces(a, s, b) ==> body[self/a, visited/s, o/b]
        //
        // We emit the FORWARD direction only. This is the load-bearing direction
        // for loop reasoning: from the known invariant fact
        // `method_produces(iter_old, produced, it)` it makes the index property
        // (and the other body clauses) available about `produced`. It is one
        // direction of the true biconditional definition of the open `produces`
        // logic function, hence still completeness-only (can never make a false
        // formula UNSAT). The reverse direction (`body ==> produces`) is far
        // heavier — it forces the solver to discharge the nested index forall to
        // ESTABLISH a produces fact — and is not needed to CONSUME the loop
        // invariant, so we omit it to avoid a quantifier blow-up on the loop VCs.
        let fn_application = self.solver.apply(produces_func, &bound_vars);
        let implication = self.solver.implies(fn_application, body_term);
        let axiom =
            self.solver
                .forall_with_triggers(&bound_vars, implication, &[&[fn_application]]);
        self.solver.assert_term(axiom);
    }

    /// Whether the open `produces` body is light enough to materialize in the
    /// invariant frame without risking a quantifier blow-up.
    ///
    /// Heavy iterator-adapter `produces` definitions (`Skip`, `Take`, `Map`,
    /// ...) introduce an existential over an auxiliary sequence and recurse into
    /// the inner iterator's `produces`/`completed`. Arming that as an invariant-
    /// frame axiom turns fast loop VCs into timeouts. Arithmetic definitions
    /// (e.g. `Range`) contain only bounded index `forall`s and direct accessors,
    /// which the E-matcher dispatches cheaply.
    fn produces_body_is_materializable(body: &PureExpr) -> bool {
        !body.any_recursive(|node| {
            matches!(node, PureExpr::Exists { .. })
                || matches!(
                    node,
                    PureExpr::MethodCall { method, .. }
                        if matches!(
                            method.as_str(),
                            "produces" | "produces_back" | "completed"
                        )
                )
        })
    }

    /// Assert concrete transitivity instances for observed `produces` calls.
    ///
    /// The quantified transitivity axiom is retained as the specification-level
    /// encoding. These ground instances provide a solver-stable path for current
    /// VC terms when multi-pattern E-matching cannot bind all quantified vars.
    ///
    /// # Incremental strategy (#935, #954)
    ///
    /// Only asserts NEW 2-hop, 3-hop, and (conditionally) 4-hop combinations
    /// involving the newly added call. For N prior calls + 1 new call, this
    /// emits O(N) new 2-hop and O(N^2) new 3-hop instances. 3-hop instances
    /// are disabled when N > `TRUST_WP_PRODUCES_THREE_HOP_CAP` (4) (#2671, #2688), and 4-hop
    /// instances are disabled when N > `TRUST_WP_PRODUCES_FOUR_HOP_CAP` (4). (#2688)
    pub(crate) fn assert_produces_ground_transitivity(
        &mut self,
        produces_func: &FuncDecl,
        from: Term,
        visited: Term,
        to: Term,
    ) {
        // Ground transitivity is only valid for truly ground applications.
        // Quantifier bodies carry bound variables, and reusing them here can
        // re-assert the "ground" chain over non-ground terms, which in turn
        // recreates the same sort-mismatch panic this helper is meant to
        // avoid. Keep the quantified law enabled, but skip the ground-instance
        // path until we leave quantifier scope. (#994)
        if self.quantifier_state.quantifier_depth() > 0 {
            return;
        }

        let param_sorts = produces_func.domain();
        if param_sorts.len() != 3 || param_sorts.first() != param_sorts.get(2) {
            return;
        }

        let seq_sort = self.get_seq_sort();
        if param_sorts[1].clone() != seq_sort {
            return;
        }
        let seq_funcs = self.ensure_seq_theory();
        let seq_concat_decl = seq_funcs.seq_concat.clone();
        let seq_empty_term = seq_funcs.seq_empty;
        let visited = self.bridge_int_to_seq_carrier(visited);

        let new_call = ProducesGroundCall { from, visited, to };
        let func_name = produces_func.name().to_string();
        let is_adapter = is_adapter_produces_symbol(&func_name);

        // Insert into the tracker (O(1) dedup via HashSet). (#935)
        let Some((is_capped, is_four_hop_disabled, is_three_hop_disabled, prior_calls, all_calls)) =
            self.record_produces_ground_call(&func_name, new_call)
        else {
            return; // Already recorded — no new combinations needed.
        };

        // Ground reflexivity: assert produces(t, seq_empty, t) for each state
        // term observed in this call. This is O(1) per ground call and avoids
        // relying on the generic quantified produces axioms for concrete
        // verifier obligations.
        // Placed BEFORE the cap check: reflexivity is O(1) per call and must
        // fire even when ground transitivity instances are capped. (#1928)
        let state_sort = &param_sorts[0];
        let refl_from = self
            .solver
            .apply(produces_func, &[from, seq_empty_term, from]);
        self.solver.assert_term(refl_from);
        if to != from {
            let refl_to = self.solver.apply(produces_func, &[to, seq_empty_term, to]);
            self.solver.assert_term(refl_to);
        }

        // When the cap is exceeded, rely solely on the quantified transitivity
        // axiom and skip ground instance generation. (#935)
        if is_capped {
            return;
        }

        // 2-hop: assert pairs involving new_call that weren't asserted before.
        // new_call as left with every prior call as right, and vice versa,
        // plus new_call paired with itself.
        for prior in &prior_calls {
            if should_emit_produces_ground_chain(is_adapter, &[new_call, *prior]) {
                self.assert_produces_ground_transitivity_instance(
                    produces_func,
                    &seq_concat_decl,
                    state_sort,
                    new_call,
                    *prior,
                );
            }
            if should_emit_produces_ground_chain(is_adapter, &[*prior, new_call]) {
                self.assert_produces_ground_transitivity_instance(
                    produces_func,
                    &seq_concat_decl,
                    state_sort,
                    *prior,
                    new_call,
                );
            }
        }
        if should_emit_produces_ground_chain(is_adapter, &[new_call, new_call]) {
            self.assert_produces_ground_transitivity_instance(
                produces_func,
                &seq_concat_decl,
                state_sort,
                new_call,
                new_call,
            );
        }

        // 3-hop: assert triples where at least one position is new_call.
        // Three patterns: (new, *, *), (*, new, *), (*, *, new) minus overlaps.
        // Disabled when call count exceeds TRUST_WP_PRODUCES_THREE_HOP_CAP (4) to avoid
        // the O(N^2) explosion on iterator-heavy tests. The quantified
        // transitivity axiom handles 3+ hop chains. (#2688)
        if !is_three_hop_disabled {
            let mut emitted_triples = std::collections::HashSet::new();
            let triple_key = |calls: [ProducesGroundCall; 3]| {
                calls.map(|call| (call.from, call.visited, call.to))
            };
            for a in &all_calls {
                for b in &all_calls {
                    let new_left = [new_call, *a, *b];
                    if should_emit_produces_ground_chain(is_adapter, &new_left)
                        && emitted_triples.insert(triple_key(new_left))
                    {
                        self.assert_produces_ground_transitivity_three_hop_instance(
                            produces_func,
                            &seq_concat_decl,
                            state_sort,
                            new_left[0],
                            new_left[1],
                            new_left[2],
                        );
                    }

                    let new_middle = [*a, new_call, *b];
                    if should_emit_produces_ground_chain(is_adapter, &new_middle)
                        && emitted_triples.insert(triple_key(new_middle))
                    {
                        self.assert_produces_ground_transitivity_three_hop_instance(
                            produces_func,
                            &seq_concat_decl,
                            state_sort,
                            new_middle[0],
                            new_middle[1],
                            new_middle[2],
                        );
                    }

                    let new_right = [*a, *b, new_call];
                    if should_emit_produces_ground_chain(is_adapter, &new_right)
                        && emitted_triples.insert(triple_key(new_right))
                    {
                        self.assert_produces_ground_transitivity_three_hop_instance(
                            produces_func,
                            &seq_concat_decl,
                            state_sort,
                            new_right[0],
                            new_right[1],
                            new_right[2],
                        );
                    }
                }
            }
        }

        // 4-hop: quadruples where at least one position is new_call. (#954)
        // Disabled when call count exceeds TRUST_WP_PRODUCES_FOUR_HOP_CAP (4) to avoid
        // the O(N^3) explosion that causes iterator-heavy test timeouts. The
        // quantified transitivity axiom handles 4+ hop chains when ground
        // instances are insufficient. (#2688)
        if !is_four_hop_disabled {
            self.assert_produces_ground_four_hop_combinations(
                produces_func,
                &seq_concat_decl,
                state_sort,
                new_call,
                &all_calls,
                is_adapter,
            );
        }
    }

    fn assert_produces_ground_four_hop_combinations(
        &mut self,
        produces_func: &FuncDecl,
        seq_concat_decl: &FuncDecl,
        state_sort: &Sort,
        new_call: ProducesGroundCall,
        all_calls: &[ProducesGroundCall],
        is_adapter: bool,
    ) {
        let mut emitted_quads = std::collections::HashSet::new();
        let quad_key =
            |calls: [ProducesGroundCall; 4]| calls.map(|call| (call.from, call.visited, call.to));

        for a in all_calls {
            for b in all_calls {
                for c in all_calls {
                    let new_first = [new_call, *a, *b, *c];
                    if should_emit_produces_ground_chain(is_adapter, &new_first)
                        && emitted_quads.insert(quad_key(new_first))
                    {
                        self.assert_produces_ground_transitivity_four_hop_instance(
                            produces_func,
                            seq_concat_decl,
                            state_sort,
                            &new_first,
                        );
                    }

                    let new_second = [*a, new_call, *b, *c];
                    if should_emit_produces_ground_chain(is_adapter, &new_second)
                        && emitted_quads.insert(quad_key(new_second))
                    {
                        self.assert_produces_ground_transitivity_four_hop_instance(
                            produces_func,
                            seq_concat_decl,
                            state_sort,
                            &new_second,
                        );
                    }

                    let new_third = [*a, *b, new_call, *c];
                    if should_emit_produces_ground_chain(is_adapter, &new_third)
                        && emitted_quads.insert(quad_key(new_third))
                    {
                        self.assert_produces_ground_transitivity_four_hop_instance(
                            produces_func,
                            seq_concat_decl,
                            state_sort,
                            &new_third,
                        );
                    }

                    let new_fourth = [*a, *b, *c, new_call];
                    if should_emit_produces_ground_chain(is_adapter, &new_fourth)
                        && emitted_quads.insert(quad_key(new_fourth))
                    {
                        self.assert_produces_ground_transitivity_four_hop_instance(
                            produces_func,
                            seq_concat_decl,
                            state_sort,
                            &new_fourth,
                        );
                    }
                }
            }
        }
    }

    fn assert_produces_ground_transitivity_instance(
        &mut self,
        produces_func: &FuncDecl,
        seq_concat_decl: &FuncDecl,
        _state_sort: &Sort,
        left: ProducesGroundCall,
        right: ProducesGroundCall,
    ) {
        let left_pred = self
            .solver
            .apply(produces_func, &[left.from, left.visited, left.to]);
        let right_pred = self
            .solver
            .apply(produces_func, &[right.from, right.visited, right.to]);
        let premise = if left.to == right.from {
            self.solver.and(left_pred, right_pred)
        } else {
            let mids_equal = self.eq_term(left.to, right.from);
            self.solver.and_many(&[left_pred, right_pred, mids_equal])
        };

        let left_visited = self.bridge_int_to_seq_carrier(left.visited);
        let right_visited = self.bridge_int_to_seq_carrier(right.visited);
        let joined_visited = self
            .solver
            .apply(seq_concat_decl, &[left_visited, right_visited]);
        let conclusion = self
            .solver
            .apply(produces_func, &[left.from, joined_visited, right.to]);

        let trans_instance = self.solver.implies(premise, conclusion);
        self.solver.assert_term(trans_instance);
    }

    fn assert_produces_ground_transitivity_three_hop_instance(
        &mut self,
        produces_func: &FuncDecl,
        seq_concat_decl: &FuncDecl,
        _state_sort: &Sort,
        first: ProducesGroundCall,
        second: ProducesGroundCall,
        third: ProducesGroundCall,
    ) {
        let first_pred = self
            .solver
            .apply(produces_func, &[first.from, first.visited, first.to]);
        let second_pred = self
            .solver
            .apply(produces_func, &[second.from, second.visited, second.to]);
        let third_pred = self
            .solver
            .apply(produces_func, &[third.from, third.visited, third.to]);
        // Omit mid-point equality conjuncts when syntactically equal (#2688).
        let mut conjuncts = vec![first_pred, second_pred, third_pred];
        if first.to != second.from {
            conjuncts.push(self.eq_term(first.to, second.from));
        }
        if second.to != third.from {
            conjuncts.push(self.eq_term(second.to, third.from));
        }
        let premise = self.solver.and_many(&conjuncts);

        let first_visited = self.bridge_int_to_seq_carrier(first.visited);
        let second_visited = self.bridge_int_to_seq_carrier(second.visited);
        let third_visited = self.bridge_int_to_seq_carrier(third.visited);
        let first_two = self
            .solver
            .apply(seq_concat_decl, &[first_visited, second_visited]);
        let all_three = self
            .solver
            .apply(seq_concat_decl, &[first_two, third_visited]);
        let conclusion = self
            .solver
            .apply(produces_func, &[first.from, all_three, third.to]);

        let trans_instance = self.solver.implies(premise, conclusion);
        self.solver.assert_term(trans_instance);
    }

    fn assert_produces_ground_transitivity_four_hop_instance(
        &mut self,
        produces_func: &FuncDecl,
        seq_concat_decl: &FuncDecl,
        _state_sort: &Sort,
        chain: &[ProducesGroundCall; 4],
    ) {
        let &[first, second, third, fourth] = chain;
        let first_pred = self
            .solver
            .apply(produces_func, &[first.from, first.visited, first.to]);
        let second_pred = self
            .solver
            .apply(produces_func, &[second.from, second.visited, second.to]);
        let third_pred = self
            .solver
            .apply(produces_func, &[third.from, third.visited, third.to]);
        let fourth_pred = self
            .solver
            .apply(produces_func, &[fourth.from, fourth.visited, fourth.to]);
        // Omit mid-point equality conjuncts when syntactically equal (#2688).
        let mut conjuncts = vec![first_pred, second_pred, third_pred, fourth_pred];
        if first.to != second.from {
            conjuncts.push(self.eq_term(first.to, second.from));
        }
        if second.to != third.from {
            conjuncts.push(self.eq_term(second.to, third.from));
        }
        if third.to != fourth.from {
            conjuncts.push(self.eq_term(third.to, fourth.from));
        }
        let premise = self.solver.and_many(&conjuncts);

        let first_visited = self.bridge_int_to_seq_carrier(first.visited);
        let second_visited = self.bridge_int_to_seq_carrier(second.visited);
        let third_visited = self.bridge_int_to_seq_carrier(third.visited);
        let fourth_visited = self.bridge_int_to_seq_carrier(fourth.visited);
        let first_two = self
            .solver
            .apply(seq_concat_decl, &[first_visited, second_visited]);
        let first_three = self
            .solver
            .apply(seq_concat_decl, &[first_two, third_visited]);
        let all_four = self
            .solver
            .apply(seq_concat_decl, &[first_three, fourth_visited]);
        let conclusion = self
            .solver
            .apply(produces_func, &[first.from, all_four, fourth.to]);

        let trans_instance = self.solver.implies(premise, conclusion);
        self.solver.assert_term(trans_instance);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ADAPTER_PRODUCES_SYMBOL: &str =
        "method_produces_3_u636f72653a3a697465723a3a4d6170_s_u636f72653a3a697465723a3a4d6170";
    const CONCRETE_PRODUCES_SYMBOL: &str = "method_produces_3_i_s_i";

    fn declare_test_produces_func(encoder: &mut AYEncoder, name: &str) -> FuncDecl {
        let seq_sort = encoder.get_seq_sort();
        encoder
            .solver_mut()
            .declare_fun(name, &[Sort::Int, seq_sort, Sort::Int], Sort::Bool)
    }

    fn make_test_call(
        encoder: &mut AYEncoder,
        from: &str,
        visited: &str,
        to: &str,
    ) -> ProducesGroundCall {
        let seq_sort = encoder.get_seq_sort();
        let from = encoder.solver_mut().declare_const(from, Sort::Int);
        let visited = encoder.solver_mut().declare_const(visited, seq_sort);
        let to = encoder.solver_mut().declare_const(to, Sort::Int);
        ProducesGroundCall { from, visited, to }
    }

    fn assert_test_call(
        encoder: &mut AYEncoder,
        produces_func: &FuncDecl,
        call: ProducesGroundCall,
    ) {
        encoder.assert_produces_ground_transitivity(
            produces_func,
            call.from,
            call.visited,
            call.to,
        );
    }

    #[test]
    fn produces_axioms_adapter_chain_filter_requires_syntactic_adjacency() {
        let mut encoder = AYEncoder::new();
        let ab = make_test_call(&mut encoder, "a", "ab", "b");
        let bc = make_test_call(&mut encoder, "b", "bc", "c");
        let cd = make_test_call(&mut encoder, "c", "cd", "d");
        let de = make_test_call(&mut encoder, "d", "de", "e");

        assert!(should_emit_produces_ground_chain(true, &[ab, bc]));
        assert!(should_emit_produces_ground_chain(true, &[ab, bc, cd]));
        assert!(!should_emit_produces_ground_chain(true, &[ab, de]));
        assert!(should_emit_produces_ground_chain(false, &[ab, de]));
        assert!(!should_emit_produces_ground_chain(false, &[ab, de, cd]));
    }

    #[test]
    fn produces_axioms_adapter_ground_instances_skip_non_syntactic_pairs() {
        let mut encoder = AYEncoder::new();
        let _seq_funcs = encoder.ensure_seq_theory();
        let produces_func = declare_test_produces_func(&mut encoder, ADAPTER_PRODUCES_SYMBOL);
        let baseline_assertions = encoder.solver().assertions().len();

        let ab = make_test_call(&mut encoder, "a", "ab", "b");
        let de = make_test_call(&mut encoder, "d", "de", "e");
        assert_test_call(&mut encoder, &produces_func, ab);
        assert_test_call(&mut encoder, &produces_func, de);

        assert_eq!(
            encoder.solver().assertions().len(),
            baseline_assertions + 4,
            "adapter ground transitivity should only emit endpoint reflexivity for non-syntactic chains"
        );
    }

    #[test]
    fn produces_axioms_adapter_ground_instances_keep_syntactic_pairs() {
        let mut encoder = AYEncoder::new();
        let _seq_funcs = encoder.ensure_seq_theory();
        let produces_func = declare_test_produces_func(&mut encoder, ADAPTER_PRODUCES_SYMBOL);
        let baseline_assertions = encoder.solver().assertions().len();

        let ab = make_test_call(&mut encoder, "a", "ab", "b");
        let bc = make_test_call(&mut encoder, "b", "bc", "c");
        assert_test_call(&mut encoder, &produces_func, ab);
        assert_test_call(&mut encoder, &produces_func, bc);

        assert!(
            encoder.solver().assertions().len() > baseline_assertions,
            "adapter ground transitivity should still emit syntactically chained instances"
        );
    }

    #[test]
    fn produces_axioms_concrete_ground_instances_keep_equality_guarded_pairs() {
        let mut encoder = AYEncoder::new();
        let _seq_funcs = encoder.ensure_seq_theory();
        let produces_func = declare_test_produces_func(&mut encoder, CONCRETE_PRODUCES_SYMBOL);
        let baseline_assertions = encoder.solver().assertions().len();

        let ab = make_test_call(&mut encoder, "a", "ab", "b");
        assert_test_call(&mut encoder, &produces_func, ab);

        assert!(
            encoder.solver().assertions().len() > baseline_assertions,
            "non-adapter produces symbols should retain equality-guarded ground instances"
        );
    }

    #[test]
    fn produces_axioms_concrete_high_hop_skips_non_syntactic_chains() {
        let mut encoder = AYEncoder::new();
        let _seq_funcs = encoder.ensure_seq_theory();
        let produces_func = declare_test_produces_func(&mut encoder, CONCRETE_PRODUCES_SYMBOL);
        let baseline_assertions = encoder.solver().assertions().len();

        let ab = make_test_call(&mut encoder, "a", "ab", "b");
        let de = make_test_call(&mut encoder, "d", "de", "e");
        let hi = make_test_call(&mut encoder, "h", "hi", "i");
        assert_test_call(&mut encoder, &produces_func, ab);
        assert_test_call(&mut encoder, &produces_func, de);
        assert_test_call(&mut encoder, &produces_func, hi);

        let emitted = encoder.solver().assertions().len() - baseline_assertions;
        assert_eq!(
            emitted, 15,
            "non-adjacent concrete calls should keep 2-hop equality-guarded instances \
             and endpoint reflexivity but skip 3-hop/4-hop combinations"
        );
    }

    #[test]
    fn produces_ground_transitivity_bridges_int_visited_carriers() {
        let mut encoder = AYEncoder::new();
        let _seq_funcs = encoder.ensure_seq_theory();
        let produces_func = declare_test_produces_func(&mut encoder, CONCRETE_PRODUCES_SYMBOL);
        let a = encoder.solver_mut().declare_const("a", Sort::Int);
        let ab = encoder
            .solver_mut()
            .declare_const("ab_int_carrier", Sort::Int);
        let b = encoder.solver_mut().declare_const("b", Sort::Int);
        let bc = encoder
            .solver_mut()
            .declare_const("bc_int_carrier", Sort::Int);
        let c = encoder.solver_mut().declare_const("c", Sort::Int);

        encoder.assert_produces_ground_transitivity(&produces_func, a, ab, b);
        encoder.assert_produces_ground_transitivity(&produces_func, b, bc, c);

        assert!(
            encoder.solver().assertions().len() > 0,
            "Int fallback visited carriers should be bridged before seq_concat ground instances"
        );
    }

    // ---- produces body materialization (#produces-body) ----

    use std::sync::Arc;

    use trust_wp_core::{
        formula::{BinOp, ExprSort, PureExpr},
        logic::{LogicFnDef, LogicMode},
    };

    fn arithmetic_produces_body() -> PureExpr {
        // visited.len() == o.start@ - self.start@
        let visited_len = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("visited".to_string(), Some(ExprSort::Seq))),
            method: "len".to_string(),
            args: vec![],
        };
        let start_self = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
            method: "start_log".to_string(),
            args: vec![],
        };
        let start_o = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("o".to_string(), None)),
            method: "start_log".to_string(),
            args: vec![],
        };
        PureExpr::BinOp(
            Arc::new(visited_len),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(start_o),
                BinOp::Sub,
                Arc::new(start_self),
            )),
        )
    }

    fn adapter_produces_body() -> PureExpr {
        // exists<s: Seq> self.iter.produces(s, o.iter)
        let nested = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
                method: "iter".to_string(),
                args: vec![],
            }),
            method: "produces".to_string(),
            args: vec![
                PureExpr::Var("s".to_string(), Some(ExprSort::Seq)),
                PureExpr::Var("o".to_string(), None),
            ],
        };
        PureExpr::Exists {
            var: "s".to_string(),
            var_sort: Some(ExprSort::Seq),
            body: Arc::new(nested),
            triggers: vec![],
        }
    }

    #[test]
    fn arithmetic_produces_body_is_materializable() {
        assert!(AYEncoder::produces_body_is_materializable(
            &arithmetic_produces_body()
        ));
    }

    #[test]
    fn adapter_produces_body_with_existential_is_not_materializable() {
        // Skip/Take/Map-style bodies (existential + nested produces) must be
        // skipped to avoid the loop-VC quantifier blow-up (04_skip regression).
        assert!(!AYEncoder::produces_body_is_materializable(
            &adapter_produces_body()
        ));
    }

    #[test]
    fn nested_produces_without_existential_is_not_materializable() {
        let body = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("self".to_string(), None)),
            method: "produces".to_string(),
            args: vec![
                PureExpr::Var("visited".to_string(), Some(ExprSort::Seq)),
                PureExpr::Var("o".to_string(), None),
            ],
        };
        assert!(!AYEncoder::produces_body_is_materializable(&body));
    }

    fn open_produces_logic_fn(body: PureExpr) -> LogicFnDef {
        LogicFnDef::new(
            "produces".to_string(),
            "test::produces".to_string(),
            vec!["self".to_string(), "visited".to_string(), "o".to_string()],
            body,
        )
        .with_mode(LogicMode::Open)
        .with_return_sort(Some(ExprSort::Bool))
        .with_param_sorts(vec![
            Some(ExprSort::Int),
            Some(ExprSort::Seq),
            Some(ExprSort::Int),
        ])
    }

    fn has_forall_assertion(encoder: &AYEncoder) -> bool {
        use ay_dpll::api::TermKind;
        let solver = encoder.solver();
        solver.assertions().into_iter().any(|assertion| {
            let mut stack = vec![assertion];
            let mut seen = std::collections::HashSet::new();
            while let Some(term) = stack.pop() {
                if !seen.insert(term) {
                    continue;
                }
                if matches!(solver.term_kind(term), TermKind::Forall) {
                    return true;
                }
                stack.extend(solver.term_children(term));
            }
            false
        })
    }

    #[test]
    fn materializes_forward_body_axiom_for_open_arithmetic_produces() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        // Register the open `produces` logic fn so its Defining body lands in the
        // ground pool under `logic_produces`.
        encoder
            .register_logic_fn(&open_produces_logic_fn(arithmetic_produces_body()))
            .expect("register open produces logic fn");

        let produces_func = declare_test_produces_func(&mut encoder, CONCRETE_PRODUCES_SYMBOL);
        let before = encoder.solver().assertions().len();
        encoder.assert_user_produces_body_definition(&produces_func);
        let after = encoder.solver().assertions().len();

        assert!(
            after > before,
            "an open arithmetic produces body should materialize a forward defining axiom"
        );
        assert!(
            has_forall_assertion(&encoder),
            "the materialized produces definition should be a quantified axiom"
        );
    }

    #[test]
    fn skips_body_axiom_for_adapter_produces() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder
            .register_logic_fn(&open_produces_logic_fn(adapter_produces_body()))
            .expect("register open adapter produces logic fn");

        let produces_func = declare_test_produces_func(&mut encoder, CONCRETE_PRODUCES_SYMBOL);
        let before = encoder.solver().assertions().len();
        encoder.assert_user_produces_body_definition(&produces_func);
        let after = encoder.solver().assertions().len();

        assert_eq!(
            after, before,
            "adapter produces bodies (existential + nested produces) must not be materialized"
        );
    }
}
