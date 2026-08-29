// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{FuncDecl, Logic, Sort, Term};

use super::super::{sort_context::sort_inference::fmap_sort, AYEncoder};

fn decl_has_signature(decl: &FuncDecl, domain: &[Sort], range: &Sort) -> bool {
    let actual_domain = decl.domain();
    actual_domain.len() == domain.len()
        && actual_domain
            .iter()
            .zip(domain.iter())
            .all(|(actual, expected)| actual == expected)
        && decl.range() == range
}

fn fmap_insert_decl_matches_legacy_int_signature(decl: &FuncDecl, fmap: &Sort) -> bool {
    decl_has_signature(decl, &[fmap.clone(), Sort::Int, Sort::Int], fmap)
}

impl AYEncoder {
    /// `Logic::All` currently routes arithmetic atoms headed by arbitrary UFs
    /// through LRA as unsupported atoms. Keep the public `fmap_len` declaration
    /// for demand detection, but encode each ground length as an Int proxy in
    /// that logic so FMap length facts remain ordinary linear arithmetic.
    pub(crate) fn use_fmap_len_proxies(&self) -> bool {
        matches!(self.logic(), Logic::All)
    }

    /// Return the arithmetic term used for `fmap_len(receiver)`.
    ///
    /// In AUFLIA/QF_AUFLIA this is the historical UF application. In `ALL`, it
    /// is a memoized Int proxy for the exact receiver term. Reusing the proxy
    /// preserves same-term functionality while avoiding unsupported UF-headed
    /// LRA atoms in mixed datatype/FMap verification queries.
    pub(crate) fn fmap_len_term(&mut self, receiver: Term) -> Term {
        let fmap = fmap_sort();
        let func = self.get_or_declare_spec_fn("fmap_len", std::slice::from_ref(&fmap), Sort::Int);

        if !self.use_fmap_len_proxies() {
            return self.solver.apply(&func, &[receiver]);
        }

        if let Some(proxy) = self.encoding_cache.fmap_len_proxy(receiver) {
            return proxy;
        }

        let proxy = self.solver.fresh_var("fmap_len_proxy", Sort::Int);
        self.encoding_cache.insert_fmap_len_proxy(receiver, proxy);
        proxy
    }

    /// Assert linking axioms for FMap (finite map) operations.
    ///
    /// Without these axioms, `fmap_insert`, `fmap_contains`, `fmap_lookup`, and
    /// `fmap_len` are pure UFs with no semantic content. The solver cannot derive
    /// that `fmap_contains(fmap_insert(m, k, v), k) == true` or that
    /// `fmap_lookup(fmap_insert(m, k, v), k) == v`.
    #[allow(clippy::too_many_lines)] // Axiom assertion with many independent clauses
    pub(crate) fn assert_fmap_axioms(&mut self) {
        let insert_decl = self.spec_func_decl_cloned("fmap_insert");
        let contains_decl = self.spec_func_decl_cloned("fmap_contains");
        let lookup_decl = self.spec_func_decl_cloned("fmap_lookup");
        let len_decl = self.spec_func_decl_cloned("fmap_len");

        // Without fmap_insert, there are no linking axioms to assert.
        let Some(insert_decl) = insert_decl else {
            return;
        };

        // Shared quantifier variables: map (FMap sort), key/value (Int sort)
        let fmap = fmap_sort();
        if !fmap_insert_decl_matches_legacy_int_signature(&insert_decl, &fmap) {
            tracing::debug!(
                domain = ?insert_decl.domain(),
                range = ?insert_decl.range(),
                "skipping legacy quantified FMap insert axioms for non-Int key/value signature; ground instances remain signature-aware"
            );
            return;
        }

        let m = self.solver.fresh_var("fmap_ax_m", fmap.clone());
        let k = self.solver.fresh_var("fmap_ax_k", Sort::Int);
        let v = self.solver.fresh_var("fmap_ax_v", Sort::Int);
        let insert_m_k_v = self.solver.apply(&insert_decl, &[m, k, v]);

        // ── Insert-contains: fmap_contains(fmap_insert(m, k, v), k) ──
        if let Some(contains_decl) = contains_decl.as_ref() {
            let contains_ins_k = self.solver.apply(contains_decl, &[insert_m_k_v, k]);
            let axiom =
                self.solver
                    .forall_with_triggers(&[m, k, v], contains_ins_k, &[&[insert_m_k_v]]);
            self.solver.assert_term(axiom);
        }

        // ── Insert-lookup: fmap_lookup(fmap_insert(m, k, v), k) = v ──
        if let Some(lookup_decl) = lookup_decl.as_ref() {
            let lookup_ins_k = self.solver.apply(lookup_decl, &[insert_m_k_v, k]);
            let _lookup_sort = lookup_decl.range().clone();
            let eq_v = self.eq_term(lookup_ins_k, v);
            let axiom = self
                .solver
                .forall_with_triggers(&[m, k, v], eq_v, &[&[insert_m_k_v]]);
            self.solver.assert_term(axiom);
        }

        // ── Frame axioms (for k1 != k2) ──
        // These use a second key variable to express "operations on key k1 do not
        // affect key k2."
        let k2 = self.solver.fresh_var("fmap_ax_k2", Sort::Int);
        let keys_equal = self.eq_term(k, k2);
        let keys_differ = self.solver.not(keys_equal);

        // Insert-frame-contains: k != k2 ==>
        //   fmap_contains(fmap_insert(m, k, v), k2) = fmap_contains(m, k2)
        if let Some(contains_decl) = contains_decl.as_ref() {
            let contains_ins_k2 = self.solver.apply(contains_decl, &[insert_m_k_v, k2]);
            let contains_m_k2 = self.solver.apply(contains_decl, &[m, k2]);
            let frame_eq = self.eq_term(contains_ins_k2, contains_m_k2);
            let frame_implies = self.solver.implies(keys_differ, frame_eq);
            let axiom = self.solver.forall_with_triggers(
                &[m, k, v, k2],
                frame_implies,
                &[&[contains_ins_k2]],
            );
            self.solver.assert_term(axiom);
        }

        // Insert-frame-lookup: k != k2 ==>
        //   fmap_lookup(fmap_insert(m, k, v), k2) = fmap_lookup(m, k2)
        if let Some(lookup_decl) = lookup_decl.as_ref() {
            let lookup_ins_k2 = self.solver.apply(lookup_decl, &[insert_m_k_v, k2]);
            let lookup_m_k2 = self.solver.apply(lookup_decl, &[m, k2]);
            let _lookup_sort = lookup_decl.range().clone();
            let frame_eq = self.eq_term(lookup_ins_k2, lookup_m_k2);
            let frame_implies = self.solver.implies(keys_differ, frame_eq);
            let axiom = self.solver.forall_with_triggers(
                &[m, k, v, k2],
                frame_implies,
                &[&[lookup_ins_k2]],
            );
            self.solver.assert_term(axiom);
        }

        // Coverage recording (CAP-80 staged retirement): the full insert
        // universal bundle (direct + frame, contains AND lookup legs) is on
        // the solver iff both decls exist at this point. Recorded for the
        // stage-2 driver A/B; no gate consults this flag yet.
        if contains_decl.is_some() && lookup_decl.is_some() {
            self.fmap_quantified_coverage.insert_semantics = true;
        }

        // ── Insert-len axioms ──
        if !self.use_fmap_len_proxies() {
            if let (Some(contains_decl), Some(len_decl)) =
                (contains_decl.as_ref(), len_decl.as_ref())
            {
                let one = self.solver.int_const(1);
                let len_ins = self.solver.apply(len_decl, &[insert_m_k_v]);
                let len_m = self.solver.apply(len_decl, &[m]);
                let contains_m_k = self.solver.apply(contains_decl, &[m, k]);

                // Case 1: key already present => len unchanged
                let len_eq = self.eq_term(len_ins, len_m);
                let case1 = self.solver.implies(contains_m_k, len_eq);
                let axiom1 =
                    self.solver
                        .forall_with_triggers(&[m, k, v], case1, &[&[insert_m_k_v]]);
                self.solver.assert_term(axiom1);

                // Case 2: key not present => len increments
                let not_contains = self.solver.not(contains_m_k);
                let len_plus_1 = self.solver.add(len_m, one);
                let len_eq_plus = self.eq_term(len_ins, len_plus_1);
                let case2 = self.solver.implies(not_contains, len_eq_plus);
                let axiom2 =
                    self.solver
                        .forall_with_triggers(&[m, k, v], case2, &[&[insert_m_k_v]]);
                self.solver.assert_term(axiom2);
            }
        }

        // ── Len non-negativity: forall m. fmap_len(m) >= 0 ──
        if !self.use_fmap_len_proxies() {
            if let Some(len_decl) = len_decl.as_ref() {
                let m2 = self.solver.fresh_var("fmap_ax_m2", fmap.clone());
                let zero = self.solver.int_const(0);
                let len_m2 = self.solver.apply(len_decl, &[m2]);
                let len_ge_0 = self.solver.ge(len_m2, zero);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[m2], len_ge_0, &[&[len_m2]]);
                self.solver.assert_term(axiom);
                // Coverage recording (CAP-80 staged retirement): the
                // binder-exact universal `forall m. fmap_len(m) >= 0` is now
                // asserted, so the ground `fmap_len_nonneg` pool family is a
                // redundant consequence and may be demoted at stage >= 1. Set
                // ONLY here — the early returns above (missing `fmap_insert`
                // decl, non-Int legacy signature) and the `Logic::All`
                // len-proxy mode skip this block and leave the flag false, so
                // the pool stays the sole semantic source exactly when needed.
                self.fmap_quantified_coverage.len_nonneg = true;
            }
        }

        // ── Into-seq witness axioms ──
        // `fmap_into_seq` is the canonical history witness for FMap -> Seq
        // materialization. Keep it one-way and small: preserved length plus
        // membership for each key/value pair.
        if let Some(into_seq_decl) = self.spec_func_decl_cloned("fmap_into_seq") {
            let seq_funcs = self.ensure_seq_theory();

            let m = self.solver.fresh_var("fmap_ax_seq_m", fmap.clone());
            let k = self.solver.fresh_var("fmap_ax_seq_k", Sort::Int);
            let seq_m = self.solver.apply(&into_seq_decl, &[m]);
            let lookup_m_k = lookup_decl
                .as_ref()
                .map(|lookup_decl| self.solver.apply(lookup_decl, &[m, k]));

            if let Some(len_decl) = len_decl.as_ref() {
                let seq_len = self.solver.apply(&seq_funcs.seq_len, &[seq_m]);
                let fmap_len = self.solver.apply(len_decl, &[m]);
                let len_eq = self.eq_term(seq_len, fmap_len);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[m], len_eq, &[&[seq_len]]);
                self.solver.assert_term(axiom);
            }

            if let (Some(contains_decl), Some(lookup_m_k)) = (contains_decl.as_ref(), lookup_m_k) {
                let contains_m_k = self.solver.apply(contains_decl, &[m, k]);
                let seq_contains = self
                    .solver
                    .apply(&seq_funcs.seq_contains_pair, &[seq_m, k, lookup_m_k]);
                let bridge_body = self.solver.implies(contains_m_k, seq_contains);
                let axiom =
                    self.solver
                        .forall_with_triggers(&[m, k], bridge_body, &[&[seq_contains]]);
                self.solver.assert_term(axiom);
            }
        }

        // ── FMap empty constant axioms (#2549) ──
        // `fmap_empty` is a canonical constant of FMap sort. These axioms
        // connect it to the contains/len UFs so the solver knows that an
        // empty map has no keys and zero length.
        {
            let fmap_empty = self.solver.declare_const("fmap_empty", fmap.clone());

            // Empty-contains: forall k. !fmap_contains(fmap_empty, k)
            if let Some(contains_decl) = contains_decl.as_ref() {
                let ek = self.solver.fresh_var("fmap_ax_ek", Sort::Int);
                let contains_empty_k = self.solver.apply(contains_decl, &[fmap_empty, ek]);
                let not_contains = self.solver.not(contains_empty_k);
                let axiom =
                    self.solver
                        .forall_with_triggers(&[ek], not_contains, &[&[contains_empty_k]]);
                self.solver.assert_term(axiom);
            }

            // Empty-len: fmap_len(fmap_empty) == 0
            if len_decl.is_some() {
                let len_empty = self.fmap_len_term(fmap_empty);
                let zero = self.solver.int_const(0);
                let len_eq_zero = self.eq_term(len_empty, zero);
                self.solver.assert_term(len_eq_zero);
            }
        }

        // ── FMap merge axioms (left-bias) (#1778) ──
        // These give `fmap_merge(m1, m2)` its semantic content. The merge
        // operation combines two maps with left-bias: m1 values win on key
        // collision, matching the Creusot `|(v1, _)| v1` resolver.
        let merge_decl = self.spec_func_decl_cloned("fmap_merge");
        if let Some(merge_decl) = merge_decl {
            let m1 = self.solver.fresh_var("fmap_mg_m1", fmap.clone());
            let m2 = self.solver.fresh_var("fmap_mg_m2", fmap);
            let k = self.solver.fresh_var("fmap_mg_k", Sort::Int);
            let merge_m1_m2 = self.solver.apply(&merge_decl, &[m1, m2]);

            // Merge-contains-forward:
            //   forall m1, m2, k. fmap_contains(m1, k) ==>
            //     fmap_contains(fmap_merge(m1, m2), k)
            // Merge-contains-forward-right:
            //   forall m1, m2, k. fmap_contains(m2, k) ==>
            //     fmap_contains(fmap_merge(m1, m2), k)
            // Merge-contains-backward:
            //   forall m1, m2, k. fmap_contains(fmap_merge(m1, m2), k) ==>
            //     fmap_contains(m1, k) || fmap_contains(m2, k)
            if let Some(contains_decl) = contains_decl.as_ref() {
                let c_m1_k = self.solver.apply(contains_decl, &[m1, k]);
                let c_m2_k = self.solver.apply(contains_decl, &[m2, k]);
                let c_merge_k = self.solver.apply(contains_decl, &[merge_m1_m2, k]);

                // Forward: m1 contains k => merge contains k
                let ax_fwd_left = self.solver.implies(c_m1_k, c_merge_k);
                let axiom =
                    self.solver
                        .forall_with_triggers(&[m1, m2, k], ax_fwd_left, &[&[c_merge_k]]);
                self.solver.assert_term(axiom);

                // Forward: m2 contains k => merge contains k
                let ax_fwd_right = self.solver.implies(c_m2_k, c_merge_k);
                let axiom =
                    self.solver
                        .forall_with_triggers(&[m1, m2, k], ax_fwd_right, &[&[c_merge_k]]);
                self.solver.assert_term(axiom);

                // Backward: merge contains k => m1 or m2 contains k
                let m1_or_m2 = self.solver.or(c_m1_k, c_m2_k);
                let ax_bwd = self.solver.implies(c_merge_k, m1_or_m2);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[m1, m2, k], ax_bwd, &[&[c_merge_k]]);
                self.solver.assert_term(axiom);
            }

            // Merge-lookup-left (left-bias):
            //   forall m1, m2, k. fmap_contains(m1, k) ==>
            //     fmap_lookup(fmap_merge(m1, m2), k) = fmap_lookup(m1, k)
            // Trigger: fmap_lookup(fmap_merge(m1, m2), k) — covers all three
            // bound variables so the solver can instantiate on ground lookup
            // terms involving a merge subexpression.
            if let (Some(contains_decl), Some(lookup_decl)) =
                (contains_decl.as_ref(), lookup_decl.as_ref())
            {
                let c_m1_k = self.solver.apply(contains_decl, &[m1, k]);
                let l_merge_k = self.solver.apply(lookup_decl, &[merge_m1_m2, k]);
                let l_m1_k = self.solver.apply(lookup_decl, &[m1, k]);
                let _lookup_sort = lookup_decl.range().clone();
                let eq = self.eq_term(l_merge_k, l_m1_k);
                let ax = self.solver.implies(c_m1_k, eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[m1, m2, k], ax, &[&[l_merge_k]]);
                self.solver.assert_term(axiom);
            }

            // Merge-lookup-right-only:
            //   forall m1, m2, k. !fmap_contains(m1, k) && fmap_contains(m2, k) ==>
            //     fmap_lookup(fmap_merge(m1, m2), k) = fmap_lookup(m2, k)
            // Trigger: fmap_lookup(fmap_merge(m1, m2), k)
            if let (Some(contains_decl), Some(lookup_decl)) =
                (contains_decl.as_ref(), lookup_decl.as_ref())
            {
                let c_m1_k = self.solver.apply(contains_decl, &[m1, k]);
                let not_c_m1_k = self.solver.not(c_m1_k);
                let c_m2_k = self.solver.apply(contains_decl, &[m2, k]);
                let premise = self.solver.and(not_c_m1_k, c_m2_k);
                let l_merge_k = self.solver.apply(lookup_decl, &[merge_m1_m2, k]);
                let l_m2_k = self.solver.apply(lookup_decl, &[m2, k]);
                let _lookup_sort = lookup_decl.range().clone();
                let eq = self.eq_term(l_merge_k, l_m2_k);
                let ax = self.solver.implies(premise, eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[m1, m2, k], ax, &[&[l_merge_k]]);
                self.solver.assert_term(axiom);
            }

            // Coverage recording (CAP-80 staged retirement): the full merge
            // universal bundle (contains forward/backward + lookup left/
            // right-only) is on the solver iff both decls exist. Recorded
            // only; no gate consults this flag yet.
            if contains_decl.is_some() && lookup_decl.is_some() {
                self.fmap_quantified_coverage.merge_semantics = true;
            }
        }
    }
}
