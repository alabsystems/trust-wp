// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sorting Stage A: permutation/exchange equivalence + swap bridge axioms.
//!
//! `Seq::permutation_of` and `Seq::exchange` are encoded as monomorphized
//! uninterpreted Bool predicates (`method_permutation_of_2_...`,
//! `method_exchange_4_...`). Their defining specs (PERMUTATION_OF / EXCHANGE)
//! only relate them to `len`/index — they carry no *algebraic* structure. As a
//! result, a loop whose invariant is `v@.permutation_of(old_v@)` cannot prove
//! preservation across a `Vec::swap`, because nothing connects the per-swap
//! exchange relation to the multiset-permutation predicate, nor chains
//! successive swaps transitively.
//!
//! This module asserts a small, SOUND axiom bundle over those UFs:
//!
//! - `permut_refl`:        `forall s.        P(s, s)`
//! - `permut_sym`:         `forall a b.      P(a, b)  ==> P(b, a)`
//! - `exchange_permut`:    `forall s o i j.  E(s, o, i, j) ==> P(s, o)`
//! - `exchange_chain_r`:   `forall n o m i j. E(n,o,i,j) /\ P(o,m) ==> P(n,m)`
//! - `exchange_chain_l`:   `forall n o m i j. E(n,o,i,j) /\ P(m,o) ==> P(m,n)`
//!
//! ## Why a *bounded one-step chain* instead of general transitivity
//!
//! A general `forall a b c. P(a,b) /\ P(b,c) ==> P(a,c)`, combined with the
//! symmetry law (which DOUBLES every permutation fact), is the classic
//! E-matching matching-loop: each new `P` fact re-triggers symmetry and
//! transitivity, which manufacture more `P` facts, ad infinitum. Empirically it
//! produced hundreds of `P(_,_)` instances on a one-line function. Instead we
//! gate transitivity behind an EXCHANGE atom: the chain rules only fire when an
//! `E(n,o,i,j)` swap fact exists AND there is a permutation fact about the
//! swap's *pre-state* `o` sharing the pivot. That is exactly the loop-
//! preservation shape (`exchange(new,old) /\ permutation_of(old, base) ==>
//! permutation_of(new, base)` and its mirror), and the instantiation count is
//! bounded by (#exchange facts x #permutation facts mentioning the pre-state).
//! No standalone `P /\ P ==> P` loop is armed.
//!
//! ## Soundness (completeness-only)
//!
//! The intended model of `permutation_of` is the why3 `seq.Permut` multiset
//! theory: `P(a, b)` iff `a` and `b` are the same multiset of elements.
//! Under that model every axiom above is VALID:
//!   - refl/sym are equivalence-relation laws of multiset equality;
//!   - `exchange ==> permutation_of` holds because a transposition of two
//!     positions is a bijection, hence a permutation (same multiset);
//!   - the chain rules are instances of `exchange ==> permut` followed by
//!     transitivity of multiset equality — both valid.
//! Adding *valid* axioms over these uninterpreted predicates is a
//! completeness-only change: it adds hypotheses to a VC, which can only turn
//! `unknown`/`sat` into `unsat` (proved) — it can never make a genuinely
//! satisfiable (falsifiable) VC unsatisfiable. Hence no false-accept.

use ay_dpll::api::{Sort, Term};

use super::AYEncoder;

impl AYEncoder {
    /// Assert the permutation/exchange axiom bundle for a just-encoded
    /// `permutation_of` or `exchange` call.
    ///
    /// `method` is the source-level method name, `param_sorts` the encoded
    /// parameter sorts of the call (receiver first), `all_terms` the encoded
    /// argument terms (receiver first), and `result` the Bool term standing for
    /// this predicate application. The quantified bundle is keyed by the
    /// resolved UF symbol so each law is emitted at most once per Seq sort; a
    /// single targeted ground reflexivity seed is added per `permutation_of`
    /// call (needed for the `v == old_v` loop-entry obligation).
    pub(super) fn assert_permutation_exchange_axioms(
        &mut self,
        method: &str,
        param_sorts: &[Sort],
        all_terms: &[Term],
        result: Term,
    ) {
        let (perm_seq_sort, is_exchange) = match method {
            "permutation_of" if param_sorts.len() == 2 && all_terms.len() == 2 => {
                (param_sorts[0].clone(), false)
            }
            "exchange" if param_sorts.len() == 4 && all_terms.len() == 4 => {
                (param_sorts[0].clone(), true)
            }
            _ => return,
        };

        // The `permutation_of` UF over the same Seq sort that this call used.
        // For an `exchange(s, o, i, j)` call, `s`/`o` are the same `@`-views the
        // loop's `permutation_of(s, o)` invariant uses, so deriving the
        // permutation symbol from `param_sorts[0..2]` yields the SAME
        // monomorphized UF the invariant referenced. (#sorting-stage-a)
        let perm_param_sorts = [perm_seq_sort.clone(), perm_seq_sort.clone()];
        let perm_symbol = Self::bool_method_symbol("permutation_of", &perm_param_sorts);
        let perm_decl =
            self.get_or_declare_method_func(&perm_symbol, &perm_param_sorts, Sort::Bool);

        // --- Quantified refl + sym (once per perm UF) ---
        if self.permutation_exchange_axioms.insert(perm_symbol.clone()) {
            // permut_refl: forall s. P(s, s)   [trigger: P(s, s)]
            {
                let s = self.solver.fresh_var("perm_refl_s", perm_seq_sort.clone());
                let body = self.solver.apply(&perm_decl, &[s, s]);
                let axiom = self.solver.forall_with_triggers(&[s], body, &[&[body]]);
                self.solver.assert_term(axiom);
            }

            // permut_sym: forall a b. P(a, b) ==> P(b, a)   [trigger: P(a, b)]
            {
                let a = self.solver.fresh_var("perm_sym_a", perm_seq_sort.clone());
                let b = self.solver.fresh_var("perm_sym_b", perm_seq_sort.clone());
                let p_ab = self.solver.apply(&perm_decl, &[a, b]);
                let p_ba = self.solver.apply(&perm_decl, &[b, a]);
                let body = self.solver.implies(p_ab, p_ba);
                let axiom = self.solver.forall_with_triggers(&[a, b], body, &[&[p_ab]]);
                self.solver.assert_term(axiom);
            }
        }

        // Ground seeds reference the concrete call terms, so they must only be
        // emitted at ground level — inside a quantifier body `all_terms` are
        // bound variables not in scope at the top level. (The closed quantified
        // laws above are always safe.)
        let at_ground_level = self.quantifier_state.quantifier_depth() == 0;

        if !is_exchange {
            if at_ground_level {
                // Targeted ground reflexivity for THIS call's operands. The
                // loop-entry obligation `permutation_of(v, old_v)` holds because
                // `v == old_v` at entry. We hand the solver the guarded refl
                // instance `a == b ==> P(a, b)` over the exact operands, so the
                // entry goal is discharged by direct (dis)equality reasoning
                // rather than relying on UF-application congruence propagation,
                // and we add the bare self-application `P(a, a)` as an explicit
                // anchor for the sym/chain laws. Minimal (one pair, not the
                // whole e-graph) to avoid flooding the sym law.
                let a = all_terms[0];
                let b = all_terms[1];
                let p_aa = self.solver.apply(&perm_decl, &[a, a]);
                self.solver.assert_term(p_aa);
                if b != a {
                    let p_ab = self.solver.apply(&perm_decl, &[a, b]);
                    let a_eq_b = self.solver.eq(a, b);
                    let guarded_refl = self.solver.implies(a_eq_b, p_ab);
                    self.solver.assert_term(guarded_refl);
                }
            }
            return;
        }

        // --- exchange path: bridge + bounded one-step chain (once per E UF) ---
        let exch_param_sorts = [
            param_sorts[0].clone(),
            param_sorts[1].clone(),
            param_sorts[2].clone(),
            param_sorts[3].clone(),
        ];
        let exch_symbol = Self::bool_method_symbol("exchange", &exch_param_sorts);
        let exch_decl =
            self.get_or_declare_method_func(&exch_symbol, &exch_param_sorts, Sort::Bool);

        if self.permutation_exchange_axioms.insert(exch_symbol.clone()) {
            let i_sort = param_sorts[2].clone();
            let j_sort = param_sorts[3].clone();

            // exchange_permut: forall s o i j. E(s, o, i, j) ==> P(s, o)
            // [trigger: E(s, o, i, j)]
            {
                let s = self
                    .solver
                    .fresh_var("exch_permut_s", perm_seq_sort.clone());
                let o = self
                    .solver
                    .fresh_var("exch_permut_o", perm_seq_sort.clone());
                let i = self.solver.fresh_var("exch_permut_i", i_sort.clone());
                let j = self.solver.fresh_var("exch_permut_j", j_sort.clone());
                let e = self.solver.apply(&exch_decl, &[s, o, i, j]);
                let p = self.solver.apply(&perm_decl, &[s, o]);
                let body = self.solver.implies(e, p);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[s, o, i, j], body, &[&[e]]);
                self.solver.assert_term(axiom);
            }

            // exchange_chain_r: forall n o m i j.
            //     E(n, o, i, j) /\ P(o, m) ==> P(n, m)
            // multi-trigger {E(n, o, i, j), P(o, m)} — fires only when a swap of
            // `n` from `o` meets a permutation fact whose LEFT operand is the
            // swap pre-state `o`.
            {
                let n = self
                    .solver
                    .fresh_var("exch_chain_r_n", perm_seq_sort.clone());
                let o = self
                    .solver
                    .fresh_var("exch_chain_r_o", perm_seq_sort.clone());
                let m = self
                    .solver
                    .fresh_var("exch_chain_r_m", perm_seq_sort.clone());
                let i = self.solver.fresh_var("exch_chain_r_i", i_sort.clone());
                let j = self.solver.fresh_var("exch_chain_r_j", j_sort.clone());
                let e = self.solver.apply(&exch_decl, &[n, o, i, j]);
                let p_om = self.solver.apply(&perm_decl, &[o, m]);
                let p_nm = self.solver.apply(&perm_decl, &[n, m]);
                let hyp = self.solver.and(e, p_om);
                let body = self.solver.implies(hyp, p_nm);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[n, o, m, i, j], body, &[&[e, p_om]]);
                self.solver.assert_term(axiom);
            }

            // exchange_chain_l: forall n o m i j.
            //     E(n, o, i, j) /\ P(m, o) ==> P(m, n)
            // multi-trigger {E(n, o, i, j), P(m, o)} — mirror of the above for
            // invariants of the form `base.permutation_of(array)` (insertion
            // sort), whose RIGHT operand is the swap pre-state `o`.
            {
                let n = self
                    .solver
                    .fresh_var("exch_chain_l_n", perm_seq_sort.clone());
                let o = self
                    .solver
                    .fresh_var("exch_chain_l_o", perm_seq_sort.clone());
                let m = self
                    .solver
                    .fresh_var("exch_chain_l_m", perm_seq_sort.clone());
                let i = self.solver.fresh_var("exch_chain_l_i", i_sort);
                let j = self.solver.fresh_var("exch_chain_l_j", j_sort);
                let e = self.solver.apply(&exch_decl, &[n, o, i, j]);
                let p_mo = self.solver.apply(&perm_decl, &[m, o]);
                let p_mn = self.solver.apply(&perm_decl, &[m, n]);
                let hyp = self.solver.and(e, p_mo);
                let body = self.solver.implies(hyp, p_mn);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[n, o, m, i, j], body, &[&[e, p_mo]]);
                self.solver.assert_term(axiom);
            }
        }

        // Per-call GROUND bridge for the exact swap-site terms (`result` IS
        // `E(s, o, i, j)`): hand the solver `E(s,o,i,j) ==> P(s,o)` directly so
        // the bridge for THIS swap does not depend on the E-matcher firing.
        if at_ground_level {
            let s_term = all_terms[0];
            let o_term = all_terms[1];
            let p_so = self.solver.apply(&perm_decl, &[s_term, o_term]);
            let ground_bridge = self.solver.implies(result, p_so);
            self.solver.assert_term(ground_bridge);
        }
    }
}
