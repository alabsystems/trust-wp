// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Permutation / multiset theory for `Seq` (gap: no-permutation-multiset-theory).
//!
//! Before this module `permutation_of` / `exchange` / `count` were
//! uninterpreted with only length-equality (trust-wp-std `seq::specs::{
//! PERMUTATION_OF, EXCHANGE, COUNT}`), so the sort examples (insertion_sort,
//! selection_sort_generic, gnome_sort, heapsort_generic, knuth_shuffle) could
//! not discharge their permutation invariants.
//!
//! Encoding strategy (mirrors `assert_seq_reverse_axioms` / `..._contains_..`):
//! three canonical UFs declared in `ensure_seq_theory`
//!   * `seq_permutation_of : Seq x Seq -> Bool`  — `permut(s, t)`
//!   * `seq_exchange       : Seq x Seq x Int x Int -> Bool` — `exchange(t,s,i,j)`
//!   * `seq_count          : Seq x Int -> Int`   — `count(s, x)`
//! plus a family of TRIGGERED quantified laws asserted lazily (once per query)
//! by `assert_seq_permutation_axioms`.
//!
//! ## Why a separate relation rather than only the contract `ensures`
//!
//! The table-backed contract (`PERMUTATION_OF`) can only state first-order
//! consequences of a *single* application (`result ==> len equality`); it
//! cannot state the equational laws (reflexivity / symmetry / transitivity)
//! that connect *different* applications, which is exactly what loop
//! preservation needs:
//!     invariant `permut(v@, old_v@)`
//!     body effect `exchange((^v)@, v@, i, j)`  (from the swap spec)
//!     goal `permut((^v)@, old_v@)`
//! closing this requires `exchange => permut` plus `permut` transitivity.
//!
//! ## Trigger discipline (NO matching loops)
//!
//! Every law is gated on a *ground-observable* head term:
//!   * P-REFL fires on `permut(s, s)` — its body has no `permut` head, so it
//!     cannot re-trigger itself.
//!   * P-SYM fires on `permut(s, t)` and concludes `permut(t, s)`. We assert it
//!     as a biconditional `permut(s,t) <-> permut(t,s)` with the SINGLE trigger
//!     `permut(s,t)`. A biconditional adds the reverse fact in one
//!     instantiation; the reverse term `permut(t,s)`, when itself matched,
//!     yields `permut(t,s) <-> permut(s,t)` whose right side already exists, so
//!     the e-graph reaches fixpoint after one hop (no growth).
//!   * P-TRANS fires on the PAIR `[permut(s,t), permut(t,u)]` (a multi-pattern
//!     requiring BOTH antecedent heads to already be present as ground terms);
//!     it never manufactures a fresh middle term, so it only chains over
//!     `permut` facts the solver already has. This is the standard
//!     non-looping transitivity trigger.
//!   * EX=>PERM fires on `exchange(t, s, i, j)` and concludes `permut(t, s)`
//!     (a NEW permut head) — but the trigger is the `exchange` head, never the
//!     `permut` head, so it fires at most once per distinct ground `exchange`
//!     application.
//!   * COUNT-PRES fires on the PAIR `[permut(s,t), seq_count(s,x)]`: given a
//!     permutation and an *already-present* count probe on one side, it equates
//!     the counts. Triggering on the existing `seq_count(s,x)` term (rather than
//!     synthesising `seq_count(t,x)`) means it only relates counts the query
//!     already mentions; the produced `seq_count(t,x)` is a new term but its
//!     own re-match needs a *different* `permut` fact, bounded by the finite
//!     ground permut set.
//!   * COUNT-NONNEG fires on `seq_count(s,x)` (a units law, body is `>= 0`,
//!     no recursion).
//!
//! ## Soundness
//!
//! Each law is valid in the intended multiset model (a Seq denotes the
//! multiset of its elements; `permut` is multiset equality; `count` is
//! multiplicity; `exchange(t,s,i,j)` means t and s agree everywhere except a
//! transposition of i,j, which preserves the multiset). Asserting valid
//! universally-quantified facts can only *remove* models, never add a
//! spurious one, so UNSAT remains sound. Triggers are a completeness/perf
//! concern only. (Same argument as the reverse-axiom family.)

use ay_dpll::api::Sort;

use super::{AYEncoder, SeqFunctions};

impl AYEncoder {
    /// Assert the permutation / multiset laws lazily (once per query).
    ///
    /// Idempotent: guarded by `seq_state.permutation_axioms_asserted()`. Called
    /// from the `permutation_of` / `exchange` / `count` dispatch arms in
    /// `operations.rs` before the corresponding UF application is built, and is
    /// snapshot/restored across obligation slices like the other lazy families.
    #[allow(clippy::too_many_lines)]
    pub(in crate::encoder) fn assert_seq_permutation_axioms(
        &mut self,
        seq_sort: &Sort,
        funcs: &SeqFunctions,
    ) {
        if self.seq_state.permutation_axioms_asserted() {
            return;
        }

        let seq_permutation_of = &funcs.seq_permutation_of;
        let seq_exchange = &funcs.seq_exchange;
        let seq_count = &funcs.seq_count;
        let seq_len = &funcs.seq_len;
        let seq_index_logic = &funcs.seq_index_logic;

        // ── P-REFL: forall s. permut(s, s) ─────────────────────────────
        // Trigger: permut(s, s). Body is `true`-shaped (the application
        // itself), no permut head in the body => cannot self-retrigger.
        let refl_s = self.solver.fresh_var("seq_perm_refl_s", seq_sort.clone());
        let refl_app = self.solver.apply(seq_permutation_of, &[refl_s, refl_s]);
        let refl_true = self.solver.bool_const(true);
        let refl_body = self.eq_term(refl_app, refl_true);
        let refl_axiom = self
            .solver
            .forall_with_triggers(&[refl_s], refl_body, &[&[refl_app]]);
        self.solver.assert_term(refl_axiom);

        // ── P-SYM: forall s, t. permut(s, t) <-> permut(t, s) ──────────
        // Single trigger on permut(s, t); biconditional reaches e-graph
        // fixpoint after one hop (see module docs).
        let sym_s = self.solver.fresh_var("seq_perm_sym_s", seq_sort.clone());
        let sym_t = self.solver.fresh_var("seq_perm_sym_t", seq_sort.clone());
        let sym_st = self.solver.apply(seq_permutation_of, &[sym_s, sym_t]);
        let sym_ts = self.solver.apply(seq_permutation_of, &[sym_t, sym_s]);
        let sym_body = self.solver.iff(sym_st, sym_ts);
        let sym_axiom = self
            .solver
            .forall_with_triggers(&[sym_s, sym_t], sym_body, &[&[sym_st]]);
        self.solver.assert_term(sym_axiom);

        // ── P-TRANS: forall s,t,u. permut(s,t) && permut(t,u) => permut(s,u)
        // Multi-pattern trigger [permut(s,t), permut(t,u)]: BOTH antecedents
        // must already exist as ground terms; never manufactures a middle
        // element => the canonical non-looping transitivity trigger.
        let tr_s = self.solver.fresh_var("seq_perm_tr_s", seq_sort.clone());
        let tr_t = self.solver.fresh_var("seq_perm_tr_t", seq_sort.clone());
        let tr_u = self.solver.fresh_var("seq_perm_tr_u", seq_sort.clone());
        let tr_st = self.solver.apply(seq_permutation_of, &[tr_s, tr_t]);
        let tr_tu = self.solver.apply(seq_permutation_of, &[tr_t, tr_u]);
        let tr_su = self.solver.apply(seq_permutation_of, &[tr_s, tr_u]);
        let tr_hyp = self.solver.and(tr_st, tr_tu);
        let tr_body = self.solver.implies(tr_hyp, tr_su);
        let tr_axiom =
            self.solver
                .forall_with_triggers(&[tr_s, tr_t, tr_u], tr_body, &[&[tr_st, tr_tu]]);
        self.solver.assert_term(tr_axiom);

        // ── EX=>PERM + exchange length/element shape ────────────────────
        // forall t,s,i,j. exchange(t,s,i,j) =>
        //     permut(t, s)
        //  && len(t) == len(s)
        //  && (0<=i<len(s) && 0<=j<len(s) =>
        //        index(t,i)==index(s,j) && index(t,j)==index(s,i)
        //     && forall k. (0<=k<len(s) && k!=i && k!=j) => index(t,k)==index(s,k))
        // Trigger: exchange(t,s,i,j) (the only exchange head) => fires once per
        // ground exchange. The inner forall<k> frame is a SEPARATE nested
        // quantifier triggered on index(t,k) so it only instantiates at indices
        // the query already reads (matches the SET-axiom frame pattern in
        // seq/operations.rs `set`).
        let ex_t = self.solver.fresh_var("seq_ex_t", seq_sort.clone());
        let ex_s = self.solver.fresh_var("seq_ex_s", seq_sort.clone());
        let ex_i = self.solver.fresh_var("seq_ex_i", Sort::Int);
        let ex_j = self.solver.fresh_var("seq_ex_j", Sort::Int);
        let ex_app = self.solver.apply(seq_exchange, &[ex_t, ex_s, ex_i, ex_j]);
        // exchange => permut(t, s)
        let ex_perm = self.solver.apply(seq_permutation_of, &[ex_t, ex_s]);
        // exchange => len(t) == len(s)
        let ex_len_t = self.solver.apply(seq_len, &[ex_t]);
        let ex_len_s = self.solver.apply(seq_len, &[ex_s]);
        let ex_len_eq = self.eq_term(ex_len_t, ex_len_s);
        // bounds guard for the pointwise facts
        let zero = self.solver.int_const(0);
        let i_ge0 = self.solver.ge(ex_i, zero);
        let i_lt = self.solver.lt(ex_i, ex_len_s);
        let j_ge0 = self.solver.ge(ex_j, zero);
        let j_lt = self.solver.lt(ex_j, ex_len_s);
        let i_ok = self.solver.and(i_ge0, i_lt);
        let j_ok = self.solver.and(j_ge0, j_lt);
        let ij_ok = self.solver.and(i_ok, j_ok);
        // index(t,i)==index(s,j) && index(t,j)==index(s,i)
        let t_at_i = self.solver.apply(seq_index_logic, &[ex_t, ex_i]);
        let t_at_j = self.solver.apply(seq_index_logic, &[ex_t, ex_j]);
        let s_at_i = self.solver.apply(seq_index_logic, &[ex_s, ex_i]);
        let s_at_j = self.solver.apply(seq_index_logic, &[ex_s, ex_j]);
        let swap_i = self.eq_term(t_at_i, s_at_j);
        let swap_j = self.eq_term(t_at_j, s_at_i);
        let swap_both = self.solver.and(swap_i, swap_j);
        let swap_guarded = self.solver.implies(ij_ok, swap_both);
        // nested frame: forall k. (0<=k<len(s) && k!=i && k!=j) => t[k]==s[k]
        let fr_k = self.solver.fresh_var("seq_ex_k", Sort::Int);
        let fr_k_ge0 = self.solver.ge(fr_k, zero);
        let fr_k_lt = self.solver.lt(fr_k, ex_len_s);
        let fr_k_in = self.solver.and(fr_k_ge0, fr_k_lt);
        let fr_k_ne_i = {
            let e = self.eq_term(fr_k, ex_i);
            self.solver.not(e)
        };
        let fr_k_ne_j = {
            let e = self.eq_term(fr_k, ex_j);
            self.solver.not(e)
        };
        let fr_ne = self.solver.and(fr_k_ne_i, fr_k_ne_j);
        let fr_guard = self.solver.and(fr_k_in, fr_ne);
        let t_at_k = self.solver.apply(seq_index_logic, &[ex_t, fr_k]);
        let s_at_k = self.solver.apply(seq_index_logic, &[ex_s, fr_k]);
        let fr_eq = self.eq_term(t_at_k, s_at_k);
        let fr_body = self.solver.implies(fr_guard, fr_eq);
        let fr_axiom = self
            .solver
            .forall_with_triggers(&[fr_k], fr_body, &[&[t_at_k]]);
        // assemble the exchange consequent (frame is asserted as its own
        // quantifier so its trigger is independent of the exchange trigger)
        let ex_conj1 = self.solver.and(ex_perm, ex_len_eq);
        let ex_conj2 = self.solver.and(ex_conj1, swap_guarded);
        let ex_conj = self.solver.and(ex_conj2, fr_axiom);
        let ex_body = self.solver.implies(ex_app, ex_conj);
        let ex_axiom =
            self.solver
                .forall_with_triggers(&[ex_t, ex_s, ex_i, ex_j], ex_body, &[&[ex_app]]);
        self.solver.assert_term(ex_axiom);

        // ── COUNT-NONNEG: forall s, x. count(s, x) >= 0 ────────────────
        let cn_s = self.solver.fresh_var("seq_cnt_s", seq_sort.clone());
        let cn_x = self.solver.fresh_var("seq_cnt_x", Sort::Int);
        let cn_app = self.solver.apply(seq_count, &[cn_s, cn_x]);
        let cn_zero = self.solver.int_const(0);
        let cn_body = self.solver.ge(cn_app, cn_zero);
        let cn_axiom = self
            .solver
            .forall_with_triggers(&[cn_s, cn_x], cn_body, &[&[cn_app]]);
        self.solver.assert_term(cn_axiom);

        // ── COUNT-LEN: forall s, x. count(s, x) <= len(s) ──────────────
        let cl_s = self.solver.fresh_var("seq_cntl_s", seq_sort.clone());
        let cl_x = self.solver.fresh_var("seq_cntl_x", Sort::Int);
        let cl_app = self.solver.apply(seq_count, &[cl_s, cl_x]);
        let cl_len = self.solver.apply(seq_len, &[cl_s]);
        let cl_body = self.solver.le(cl_app, cl_len);
        let cl_axiom = self
            .solver
            .forall_with_triggers(&[cl_s, cl_x], cl_body, &[&[cl_app]]);
        self.solver.assert_term(cl_axiom);

        // ── COUNT-PRES: forall s,t,x. permut(s,t) => count(s,x)==count(t,x)
        // Multi-pattern trigger [permut(s,t), count(s,x)]: only fires when both
        // a permutation fact AND a count probe on its left side already exist.
        // The produced count(t,x) is fresh, but its own re-match needs a
        // *different* permut fact, so chaining is bounded by the finite ground
        // permut set (no runaway count synthesis).
        let cp_s = self.solver.fresh_var("seq_cntp_s", seq_sort.clone());
        let cp_t = self.solver.fresh_var("seq_cntp_t", seq_sort.clone());
        let cp_x = self.solver.fresh_var("seq_cntp_x", Sort::Int);
        let cp_perm = self.solver.apply(seq_permutation_of, &[cp_s, cp_t]);
        let cp_cs = self.solver.apply(seq_count, &[cp_s, cp_x]);
        let cp_ct = self.solver.apply(seq_count, &[cp_t, cp_x]);
        let cp_eq = self.eq_term(cp_cs, cp_ct);
        let cp_body = self.solver.implies(cp_perm, cp_eq);
        let cp_axiom =
            self.solver
                .forall_with_triggers(&[cp_s, cp_t, cp_x], cp_body, &[&[cp_perm, cp_cs]]);
        self.solver.assert_term(cp_axiom);

        // ── PERM-LEN: forall s, t. permut(s, t) => len(s) == len(t) ────
        // Recovers the legacy contract consequence directly on the UF so the
        // length half of a sort invariant survives even without a count probe.
        let pl_s = self.solver.fresh_var("seq_perml_s", seq_sort.clone());
        let pl_t = self.solver.fresh_var("seq_perml_t", seq_sort.clone());
        let pl_perm = self.solver.apply(seq_permutation_of, &[pl_s, pl_t]);
        let pl_len_s = self.solver.apply(seq_len, &[pl_s]);
        let pl_len_t = self.solver.apply(seq_len, &[pl_t]);
        let pl_eq = self.eq_term(pl_len_s, pl_len_t);
        let pl_body = self.solver.implies(pl_perm, pl_eq);
        let pl_axiom = self
            .solver
            .forall_with_triggers(&[pl_s, pl_t], pl_body, &[&[pl_perm]]);
        self.solver.assert_term(pl_axiom);

        self.seq_state.mark_permutation_axioms_asserted();
    }
}
