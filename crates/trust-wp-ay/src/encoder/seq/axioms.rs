// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq axiom assertions: residual axioms, sum axioms, and reverse axioms.

use ay_dpll::api::Sort;

use super::{AYEncoder, SeqFunctions};

impl AYEncoder {
    /// Assert get-specific Seq axioms lazily (8a-8b).
    pub(in crate::encoder) fn assert_seq_get_axioms(
        &mut self,
        seq_sort: &Sort,
        funcs: &SeqFunctions,
    ) {
        if self.seq_state.get_axioms_asserted() {
            return;
        }

        let seq_len = &funcs.seq_len;
        let seq_index_logic = &funcs.seq_index_logic;
        let seq_get = &funcs.seq_get;

        // Axiom 8a/8b: get(s, i) with Option semantics (#1882)
        // Creusot's Seq::get() returns Option<T>. We model:
        //   8a: 0 <= i < len(s) => get(s, i) = logic_Some(index_logic(s, i))
        //   8b: (i < 0 || i >= len(s)) => get(s, i) = logic_None()
        let some_smt = trust_wp_core::logic::logic_fn_smt_name("Some");
        let none_smt = trust_wp_core::logic::logic_fn_smt_name("None");
        let some_decl = self.get_or_declare_logic_func(&some_smt, &[Sort::Int], Sort::Int);
        let none_decl = self.get_or_declare_logic_func(&none_smt, &[], Sort::Int);

        let s8 = self.solver.fresh_var("seq_axiom_s8", seq_sort.clone());
        let i8 = self.solver.fresh_var("seq_axiom_i8", Sort::Int);
        let get_s_i = self.solver.apply(seq_get, &[s8, i8]);
        let index_s_i = self.solver.apply(seq_index_logic, &[s8, i8]);
        let len_s8 = self.solver.apply(seq_len, &[s8]);
        let zero8 = self.solver.int_const(0);

        let i_ge_zero = self.solver.ge(i8, zero8);
        let i_lt_len = self.solver.lt(i8, len_s8);
        let in_bounds = self.solver.and(i_ge_zero, i_lt_len);
        let some_of_index = self.solver.apply(&some_decl, &[index_s_i]);
        let get_eq_some = self.eq_term(get_s_i, some_of_index);
        let get_inbounds_implies = self.solver.implies(in_bounds, get_eq_some);
        let get_inbounds_axiom =
            self.solver
                .forall_with_triggers(&[s8, i8], get_inbounds_implies, &[&[get_s_i]]);
        self.solver.assert_term(get_inbounds_axiom);

        let s_oob = self.solver.fresh_var("seq_axiom_s_oob", seq_sort.clone());
        let i_oob = self.solver.fresh_var("seq_axiom_i_oob", Sort::Int);
        let get_oob = self.solver.apply(seq_get, &[s_oob, i_oob]);
        let len_oob = self.solver.apply(seq_len, &[s_oob]);
        let zero_oob = self.solver.int_const(0);
        let i_lt_zero = self.solver.lt(i_oob, zero_oob);
        let i_ge_len = self.solver.ge(i_oob, len_oob);
        let out_of_bounds = self.solver.or(i_lt_zero, i_ge_len);
        let none_val = self.solver.apply(&none_decl, &[]);
        let get_eq_none = self.eq_term(get_oob, none_val);
        let get_oob_implies = self.solver.implies(out_of_bounds, get_eq_none);
        let get_oob_axiom =
            self.solver
                .forall_with_triggers(&[s_oob, i_oob], get_oob_implies, &[&[get_oob]]);
        self.solver.assert_term(get_oob_axiom);

        self.seq_state.mark_get_axioms_asserted();
    }

    /// Assert concat-specific Seq axioms lazily (push bridges).
    ///
    /// Length additivity, associativity, and the two identity laws are emitted
    /// as finite ground instances for observed `seq_concat` terms. Index laws
    /// 16/17 are encoded as operation-local ITEs and ext-equality-local
    /// single-binder expansions. Keeping concat algebra out of global schemas
    /// avoids pathological E-matching loops while preserving each VC instance.
    #[allow(clippy::too_many_lines)]
    pub(in crate::encoder) fn assert_seq_concat_axioms(
        &mut self,
        seq_sort: &Sort,
        funcs: &SeqFunctions,
    ) {
        if self.seq_state.concat_axioms_asserted() {
            return;
        }

        // Ground finite-projector lanes materialize PB1/PF1 only for observed
        // applications in `assert_seq_ground_instances`.  Injecting the two
        // universal schemas here reintroduces quantifiers into otherwise QF
        // VCs and can make a concrete produces-preservation query incomplete.
        if self.use_seq_len_proxies() && self.quantifier_state.quantifier_depth() == 0 {
            self.seq_state.mark_concat_axioms_asserted();
            return;
        }

        let seq_push_back = &funcs.seq_push_back;
        let seq_concat = &funcs.seq_concat;

        // Axiom PF1: push_front(s, x) = concat(singleton(x), s) (#2116)
        let seq_push_front = &funcs.seq_push_front;
        let seq_singleton = &funcs.seq_singleton;
        let pf1_s = self.solver.fresh_var("seq_pf1_s", seq_sort.clone());
        let pf1_x = self.solver.fresh_var("seq_pf1_x", Sort::Int);
        let pf1_push = self.solver.apply(seq_push_front, &[pf1_s, pf1_x]);
        let pf1_single = self.solver.apply(seq_singleton, &[pf1_x]);
        let pf1_concat = self.solver.apply(seq_concat, &[pf1_single, pf1_s]);
        let pf1_eq = self.eq_term(pf1_push, pf1_concat);
        let pf1_axiom = self
            .solver
            .forall_with_triggers(&[pf1_s, pf1_x], pf1_eq, &[&[pf1_push]]);
        self.solver.assert_term(pf1_axiom);

        // Axiom PB1: push_back(s, x) = concat(s, singleton(x)) (#2116)
        let pb1_s = self.solver.fresh_var("seq_pb1_s", seq_sort.clone());
        let pb1_x = self.solver.fresh_var("seq_pb1_x", Sort::Int);
        let pb1_push = self.solver.apply(seq_push_back, &[pb1_s, pb1_x]);
        let pb1_single = self.solver.apply(seq_singleton, &[pb1_x]);
        let pb1_concat = self.solver.apply(seq_concat, &[pb1_s, pb1_single]);
        let pb1_eq = self.eq_term(pb1_push, pb1_concat);
        let pb1_axiom = self
            .solver
            .forall_with_triggers(&[pb1_s, pb1_x], pb1_eq, &[&[pb1_push]]);
        self.solver.assert_term(pb1_axiom);

        self.seq_state.mark_concat_axioms_asserted();
    }

    /// Assert contains-specific Seq axioms lazily (9-10).
    ///
    /// These axioms are recursive through `seq_contains` and can dominate
    /// unrelated Seq goals when asserted only because the Seq theory was
    /// initialized. Keep them out of queries that never use membership.
    pub(in crate::encoder) fn assert_seq_contains_axioms(
        &mut self,
        seq_sort: &Sort,
        funcs: &SeqFunctions,
    ) {
        if self.seq_state.contains_axioms_asserted() {
            return;
        }

        let seq_contains = &funcs.seq_contains;
        let seq_push_back = &funcs.seq_push_back;
        let seq_empty = funcs.seq_empty;

        // Axiom 9: contains(seq_empty, v) = false (#699)
        // Empty sequences contain no elements.
        let cv = self.solver.fresh_var("seq_axiom_cv", Sort::Int);
        let contains_empty_cv = self.solver.apply(seq_contains, &[seq_empty, cv]);
        let false_term = self.solver.bool_const(false);
        let contains_empty_eq = self.eq_term(contains_empty_cv, false_term);
        // Trigger: contains(seq_empty, v) — instantiate on contains applied to empty (#1586).
        let axiom_empty_contains =
            self.solver
                .forall_with_triggers(&[cv], contains_empty_eq, &[&[contains_empty_cv]]);
        self.solver.assert_term(axiom_empty_contains);

        // Axiom 10: contains(push_back(s, v), x) = (x == v || contains(s, x)) (#699)
        // Membership in push_back: either the element is the pushed value, or it
        // was already contained in the original sequence.
        let cs = self.solver.fresh_var("seq_axiom_cs", seq_sort.clone());
        let cpv = self.solver.fresh_var("seq_axiom_cpv", Sort::Int);
        let cx = self.solver.fresh_var("seq_axiom_cx", Sort::Int);
        let push_cs_cpv = self.solver.apply(seq_push_back, &[cs, cpv]);
        let contains_push_cx = self.solver.apply(seq_contains, &[push_cs_cpv, cx]);
        let cx_eq_cpv = self.eq_term(cx, cpv);
        let contains_cs_cx = self.solver.apply(seq_contains, &[cs, cx]);
        let cx_eq_or_prior = self.solver.or(cx_eq_cpv, contains_cs_cx);
        let contains_push_eq = self.eq_term(contains_push_cx, cx_eq_or_prior);
        // Trigger: contains(push_back(s, v), x) — instantiate on contains over push (#1586).
        let axiom_push_contains = self.solver.forall_with_triggers(
            &[cs, cpv, cx],
            contains_push_eq,
            &[&[contains_push_cx]],
        );
        self.solver.assert_term(axiom_push_contains);

        self.seq_state.mark_contains_axioms_asserted();
    }

    /// Assert sum-specific Seq axioms lazily (6-7).
    ///
    /// These axioms trigger on `push_back` terms and are only needed when
    /// `sum()` appears in the query. Asserting them eagerly causes quantifier
    /// churn in push_back-heavy goals that never reference sums (#1317).
    pub(in crate::encoder) fn assert_seq_sum_axioms(
        &mut self,
        seq_sort: &Sort,
        funcs: &SeqFunctions,
    ) {
        let seq_sum = &funcs.seq_sum;
        let seq_push_back = &funcs.seq_push_back;
        let seq_empty = funcs.seq_empty;

        // Axiom 6: sum(seq_empty) = 0 (#690)
        let sum_empty = self.solver.apply(seq_sum, &[seq_empty]);
        let zero6 = self.solver.int_const(0);
        let axiom6 = self.eq_term(sum_empty, zero6);
        self.solver.assert_term(axiom6);

        // Axiom 7: sum(push_back(s, v)) = sum(s) + v (#690)
        let s7 = self.solver.fresh_var("seq_axiom_s7", seq_sort.clone());
        let v7 = self.solver.fresh_var("seq_axiom_v7", Sort::Int);
        let push_s7v7 = self.solver.apply(seq_push_back, &[s7, v7]);
        let sum_push = self.solver.apply(seq_sum, &[push_s7v7]);
        let sum_s7 = self.solver.apply(seq_sum, &[s7]);
        let sum_s7_plus_v = self.solver.add(sum_s7, v7);
        let axiom7_body = self.eq_term(sum_push, sum_s7_plus_v);
        // Trigger: push_back(s, v) — instantiate on push_back application (#1586).
        let axiom7 = self
            .solver
            .forall_with_triggers(&[s7, v7], axiom7_body, &[&[push_s7v7]]);
        self.solver.assert_term(axiom7);
    }

    /// Assert axioms for `seq_reverse` (#1581).
    ///
    /// Five axioms:
    /// 1. `reverse(seq_empty) = seq_empty` (empty reverse identity)
    /// 2. `forall s: len(reverse(s)) = len(s)` (length preservation)
    /// 3. `forall s, i: 0 <= i < len(s) ==> index(reverse(s), i) = index(s, len(s) - 1 - i)`
    /// 4. `forall s, x: reverse(push_back(s, x)) = push_front(reverse(s), x)` (push_back distributivity)
    /// 5. `forall s, x: reverse(push_front(s, x)) = push_back(reverse(s), x)` (push_front distributivity)
    ///
    /// R4 is the critical axiom for seq_iter-style ghost loop proofs where
    /// `push_front_ghost` accumulates a reversed sequence: the invariant
    /// `result == produced.reverse()` with body effect `push_front(result, x)`
    /// and `produced' = push_back(produced, x)` requires exactly R4 to close
    /// the preservation step.
    pub(in crate::encoder) fn assert_seq_reverse_axioms(
        &mut self,
        seq_sort: &Sort,
        funcs: &SeqFunctions,
    ) {
        self.assert_seq_reverse_axioms_opts(seq_sort, funcs, true);
    }

    /// As [`Self::assert_seq_reverse_axioms`], but `include_index_axiom` controls
    /// whether R3 (the index-mirror axiom `index(reverse(s), i) = index(s, len-1-i)`)
    /// is asserted. R3's nested-arithmetic trigger is the heaviest of the family
    /// for E-matching; structural reverse-of-push proofs (the seq_iter ghost loops)
    /// only need R1/R2/R4/R5, so the production path skips R3 to avoid the
    /// instantiation blowup that turns provable goals into timeouts. Tests and any
    /// path that genuinely indexes a reversed sequence keep R3 via the default
    /// wrapper above. SOUNDNESS: omitting an axiom is completeness-only.
    pub(in crate::encoder) fn assert_seq_reverse_axioms_opts(
        &mut self,
        seq_sort: &Sort,
        funcs: &SeqFunctions,
        include_index_axiom: bool,
    ) {
        let seq_reverse = &funcs.seq_reverse;
        let seq_empty = funcs.seq_empty;
        let seq_len = &funcs.seq_len;
        let seq_index_logic = &funcs.seq_index_logic;
        let seq_push_back = &funcs.seq_push_back;
        let seq_push_front = &funcs.seq_push_front;

        // Axiom R1: reverse(seq_empty) = seq_empty
        let rev_empty = self.solver.apply(seq_reverse, &[seq_empty]);
        let axiom_r1 = self.eq_term(rev_empty, seq_empty);
        self.solver.assert_term(axiom_r1);

        // Axiom R2: forall s: len(reverse(s)) = len(s)
        let sr2 = self.solver.fresh_var("seq_rev_s2", seq_sort.clone());
        let rev_sr2 = self.solver.apply(seq_reverse, &[sr2]);
        let len_rev = self.solver.apply(seq_len, &[rev_sr2]);
        let len_s = self.solver.apply(seq_len, &[sr2]);
        let axiom_r2_body = self.eq_term(len_rev, len_s);
        let axiom_r2 = self
            .solver
            .forall_with_triggers(&[sr2], axiom_r2_body, &[&[rev_sr2]]);
        self.solver.assert_term(axiom_r2);

        // Axiom R3: forall s, i: 0 <= i < len(s) ==> index(reverse(s), i) = index(s, len(s) - 1 - i)
        if include_index_axiom {
            let sr3 = self.solver.fresh_var("seq_rev_s3", seq_sort.clone());
            let ir3 = self.solver.fresh_var("seq_rev_i3", Sort::Int);
            let zero = self.solver.int_const(0);
            let one = self.solver.int_const(1);
            let len_sr3 = self.solver.apply(seq_len, &[sr3]);
            let i_ge_0 = self.solver.ge(ir3, zero);
            let i_lt_len = self.solver.lt(ir3, len_sr3);
            let in_bounds = self.solver.and(i_ge_0, i_lt_len);
            let rev_sr3 = self.solver.apply(seq_reverse, &[sr3]);
            let rev_at_i = self.solver.apply(seq_index_logic, &[rev_sr3, ir3]);
            let len_minus_1 = self.solver.sub(len_sr3, one);
            let mirror_idx = self.solver.sub(len_minus_1, ir3);
            let s_at_mirror = self.solver.apply(seq_index_logic, &[sr3, mirror_idx]);
            let eq_body = self.eq_term(rev_at_i, s_at_mirror);
            let axiom_r3_body = self.solver.implies(in_bounds, eq_body);
            let axiom_r3 =
                self.solver
                    .forall_with_triggers(&[sr3, ir3], axiom_r3_body, &[&[rev_at_i]]);
            self.solver.assert_term(axiom_r3);
        }

        // Axiom R4: forall s, x: reverse(push_back(s, x)) = push_front(reverse(s), x)
        //
        // This is the key identity for ghost loop accumulation proofs.
        // Given invariant `result == reverse(produced)` with body effects:
        //   produced' = push_back(produced, x)
        //   result'   = push_front(result, x)
        // Preservation requires: push_front(reverse(produced), x) == reverse(push_back(produced, x))
        // which is exactly this axiom. (#1581)
        let sr4 = self.solver.fresh_var("seq_rev_s4", seq_sort.clone());
        let xr4 = self.solver.fresh_var("seq_rev_x4", Sort::Int);
        let push_back_s_x = self.solver.apply(seq_push_back, &[sr4, xr4]);
        let rev_push_back = self.solver.apply(seq_reverse, &[push_back_s_x]);
        let rev_s4 = self.solver.apply(seq_reverse, &[sr4]);
        let push_front_rev_x = self.solver.apply(seq_push_front, &[rev_s4, xr4]);
        let axiom_r4_body = self.eq_term(rev_push_back, push_front_rev_x);
        // Trigger on push_back(s, x) rather than reverse(push_back(s, x)):
        // in loop preservation, the e-graph contains `push_back(produced, x)` from
        // the body effect and `reverse(produced_prime)` from the primed invariant.
        // Congruence gives `reverse(produced_prime) == reverse(push_back(produced, x))`
        // but only if the latter term exists. Triggering on push_back ensures R4
        // fires before congruence is needed.
        // Multi-trigger (alternative trigger sets): fire on the inner `push_back(s, x)`
        // pattern OR on the OUTER `reverse(push_back(s, x))` term. The outer trigger
        // is needed when PB1/concat-associativity rewrite push_back into a concat fan
        // that dilutes inner-pattern matching, leaving R4 under-instantiated (#1581).
        // SOUNDNESS: adding an alternative trigger to an already-asserted VALID axiom
        // only increases ground instantiations; it can never create a false-UNSAT.
        let axiom_r4 = self.solver.forall_with_triggers(
            &[sr4, xr4],
            axiom_r4_body,
            &[&[push_back_s_x], &[rev_push_back]],
        );
        self.solver.assert_term(axiom_r4);

        // Axiom R5: forall s, x: reverse(push_front(s, x)) = push_back(reverse(s), x)
        //
        // Dual of R4. Ensures reverse distributes symmetrically over both
        // push_front and push_back.
        let sr5 = self.solver.fresh_var("seq_rev_s5", seq_sort.clone());
        let xr5 = self.solver.fresh_var("seq_rev_x5", Sort::Int);
        let push_front_s_x = self.solver.apply(seq_push_front, &[sr5, xr5]);
        let rev_push_front = self.solver.apply(seq_reverse, &[push_front_s_x]);
        let rev_s5 = self.solver.apply(seq_reverse, &[sr5]);
        let push_back_rev_x = self.solver.apply(seq_push_back, &[rev_s5, xr5]);
        let axiom_r5_body = self.eq_term(rev_push_front, push_back_rev_x);
        // Multi-trigger — symmetric with R4: fire on inner `push_front(s, x)` OR on the
        // OUTER `reverse(push_front(s, x))` term. SOUNDNESS: completeness-only (see R4).
        let axiom_r5 = self.solver.forall_with_triggers(
            &[sr5, xr5],
            axiom_r5_body,
            &[&[push_front_s_x], &[rev_push_front]],
        );
        self.solver.assert_term(axiom_r5);
    }
}
