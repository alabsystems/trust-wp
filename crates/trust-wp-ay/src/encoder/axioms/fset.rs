// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;

use super::super::AYEncoder;

impl AYEncoder {
    /// Assert linking axioms for FSet (finite set) operations (#2115).
    ///
    /// Without these axioms, `fset_peek`, `fset_insert`, `fset_remove`,
    /// `fset_contains`, and `fset_is_empty` are pure UFs with no semantic
    /// content. The solver cannot derive that `fset_contains(s, fset_peek(s))`
    /// or that `!fset_contains(fset_remove(s, x), x)`.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn assert_fset_axioms(&mut self) {
        let contains_decl = self.spec_func_decl_cloned("fset_contains");
        let is_empty_decl = self.spec_func_decl_cloned("fset_is_empty");
        let peek_decl = self.spec_func_decl_cloned("fset_peek");
        let insert_decl = self.spec_func_decl_cloned("fset_insert");
        let remove_decl = self.spec_func_decl_cloned("fset_remove");

        // ── Insert-non-empty: !is_empty(insert(s, x)) (#2547) ──
        // Inserting always produces a non-empty set. This axiom only needs
        // is_empty and insert — it does NOT require fset_contains, so it
        // must be asserted before the contains_decl early return below.
        if let (Some(is_empty_decl), Some(insert_decl)) =
            (is_empty_decl.as_ref(), insert_decl.as_ref())
        {
            let s = self.solver.fresh_var("fset_ax_s_ine", Sort::Int);
            let x = self.solver.fresh_var("fset_ax_x_ine", Sort::Int);
            let insert_s_x = self.solver.apply(insert_decl, &[s, x]);
            let is_empty_ins = self.solver.apply(is_empty_decl, &[insert_s_x]);
            let not_empty = self.solver.not(is_empty_ins);
            let axiom = self
                .solver
                .forall_with_triggers(&[s, x], not_empty, &[&[insert_s_x]]);
            self.solver.assert_term(axiom);
        }

        let len_declared = self.spec_func_decl_cloned("fset_len").is_some();
        // The axioms below state what `peek`, `insert`, `remove` and `len` mean
        // through membership, so they need `fset_contains` whether or not the
        // query names it: `s.remove(s.peek()).len() < s.len()` (a logic
        // function's variant decrease, bug/vcgen) mentions no `contains`, and
        // without these axioms every such goal failed on a model no finite set
        // has. Declaring the symbol adds no fact of its own; each axiom holds
        // of every finite set. With none of those functions there is nothing
        // to link.
        let contains_decl = match contains_decl {
            Some(decl) => decl,
            None if peek_decl.is_some()
                || insert_decl.is_some()
                || remove_decl.is_some()
                || len_declared =>
            {
                self.get_or_declare_spec_func("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool)
            }
            None => return,
        };

        // ── Peek-contains: !is_empty(s) ==> contains(s, peek(s)) ──
        if let (Some(is_empty_decl), Some(peek_decl)) = (is_empty_decl.as_ref(), peek_decl.as_ref())
        {
            let s = self.solver.fresh_var("fset_ax_s_pk", Sort::Int);
            let is_empty_s = self.solver.apply(is_empty_decl, &[s]);
            let not_empty = self.solver.not(is_empty_s);
            let peek_s = self.solver.apply(peek_decl, &[s]);
            let contains_s_peek = self.solver.apply(&contains_decl, &[s, peek_s]);
            let axiom_body = self.solver.implies(not_empty, contains_s_peek);
            let axiom = self
                .solver
                .forall_with_triggers(&[s], axiom_body, &[&[peek_s]]);
            self.solver.assert_term(axiom);
        }

        // ── Insert-contains: contains(insert(s, x), x) ──
        if let Some(insert_decl) = insert_decl.as_ref() {
            let s = self.solver.fresh_var("fset_ax_s_ic", Sort::Int);
            let x = self.solver.fresh_var("fset_ax_x_ic", Sort::Int);
            let insert_s_x = self.solver.apply(insert_decl, &[s, x]);
            let contains_ins_x = self.solver.apply(&contains_decl, &[insert_s_x, x]);
            let axiom = self
                .solver
                .forall_with_triggers(&[s, x], contains_ins_x, &[&[insert_s_x]]);
            self.solver.assert_term(axiom);
        }

        // ── Insert-contains-frame: x != y ==>
        //      contains(insert(s, x), y) = contains(s, y) ──
        if let Some(insert_decl) = insert_decl.as_ref() {
            let s = self.solver.fresh_var("fset_ax_s_if", Sort::Int);
            let x = self.solver.fresh_var("fset_ax_x_if", Sort::Int);
            let y = self.solver.fresh_var("fset_ax_y_if", Sort::Int);
            let insert_s_x = self.solver.apply(insert_decl, &[s, x]);
            let contains_ins_y = self.solver.apply(&contains_decl, &[insert_s_x, y]);
            let contains_s_y = self.solver.apply(&contains_decl, &[s, y]);
            let elems_equal = self.eq_term(x, y);
            let elems_differ = self.solver.not(elems_equal);
            let frame_eq = self.eq_term(contains_ins_y, contains_s_y);
            let frame_implies = self.solver.implies(elems_differ, frame_eq);
            let axiom =
                self.solver
                    .forall_with_triggers(&[s, x, y], frame_implies, &[&[contains_ins_y]]);
            self.solver.assert_term(axiom);
        }

        // ── Remove-contains-self: !contains(remove(s, x), x) ──
        if let Some(remove_decl) = remove_decl.as_ref() {
            let s = self.solver.fresh_var("fset_ax_s_rc", Sort::Int);
            let x = self.solver.fresh_var("fset_ax_x_rc", Sort::Int);
            let remove_s_x = self.solver.apply(remove_decl, &[s, x]);
            let contains_rem_x = self.solver.apply(&contains_decl, &[remove_s_x, x]);
            let not_contains = self.solver.not(contains_rem_x);
            let axiom = self
                .solver
                .forall_with_triggers(&[s, x], not_contains, &[&[remove_s_x]]);
            self.solver.assert_term(axiom);
        }

        // ── Remove-contains-frame: x != y ==>
        //      contains(remove(s, x), y) = contains(s, y) ──
        if let Some(remove_decl) = remove_decl.as_ref() {
            let s = self.solver.fresh_var("fset_ax_s_rf", Sort::Int);
            let x = self.solver.fresh_var("fset_ax_x_rf", Sort::Int);
            let y = self.solver.fresh_var("fset_ax_y_rf", Sort::Int);
            let remove_s_x = self.solver.apply(remove_decl, &[s, x]);
            let contains_rem_y = self.solver.apply(&contains_decl, &[remove_s_x, y]);
            let contains_s_y = self.solver.apply(&contains_decl, &[s, y]);
            let elems_equal = self.eq_term(x, y);
            let elems_differ = self.solver.not(elems_equal);
            let frame_eq = self.eq_term(contains_rem_y, contains_s_y);
            let frame_implies = self.solver.implies(elems_differ, frame_eq);
            let axiom =
                self.solver
                    .forall_with_triggers(&[s, x, y], frame_implies, &[&[contains_rem_y]]);
            self.solver.assert_term(axiom);
        }

        // ── Contains-non-empty: contains(s, x) ==> !is_empty(s) (#2547) ──
        // A set that contains an element cannot be empty. Without this, the
        // solver can model contains(s, x) = true AND is_empty(s) = true.
        if let Some(is_empty_decl) = is_empty_decl.as_ref() {
            let s = self.solver.fresh_var("fset_ax_s_cne", Sort::Int);
            let x = self.solver.fresh_var("fset_ax_x_cne", Sort::Int);
            let contains_s_x = self.solver.apply(&contains_decl, &[s, x]);
            let is_empty_s = self.solver.apply(is_empty_decl, &[s]);
            let not_empty = self.solver.not(is_empty_s);
            let axiom_body = self.solver.implies(contains_s_x, not_empty);
            let axiom = self
                .solver
                .forall_with_triggers(&[s, x], axiom_body, &[&[contains_s_x]]);
            self.solver.assert_term(axiom);
        }

        // ── FSet len axioms (#2209) ──
        // Without these, `fset_len` is a pure UF disconnected from insert/remove.
        let len_decl = self.spec_func_decl_cloned("fset_len");
        if let Some(len_decl) = len_decl.as_ref() {
            // Non-negativity: forall s. fset_len(s) >= 0
            {
                let s = self.solver.fresh_var("fset_ax_s_ln", Sort::Int);
                let len_s = self.solver.apply(len_decl, &[s]);
                let zero = self.solver.int_const(0);
                let non_neg = self.solver.ge(len_s, zero);
                let axiom = self.solver.forall_with_triggers(&[s], non_neg, &[&[len_s]]);
                self.solver.assert_term(axiom);
            }

            // is_empty link: is_empty(s) <==> len(s) == 0
            if let Some(is_empty_decl) = is_empty_decl.as_ref() {
                let s = self.solver.fresh_var("fset_ax_s_le", Sort::Int);
                let len_s = self.solver.apply(len_decl, &[s]);
                let is_empty_s = self.solver.apply(is_empty_decl, &[s]);
                let zero = self.solver.int_const(0);
                let len_eq_zero = self.eq_term(len_s, zero);
                let iff = self.eq_term(is_empty_s, len_eq_zero);
                let axiom = self.solver.forall_with_triggers(&[s], iff, &[&[len_s]]);
                self.solver.assert_term(axiom);
            }

            // Insert-len-new: !contains(s, x) ==> len(insert(s, x)) == len(s) + 1
            if let Some(insert_decl) = insert_decl.as_ref() {
                let s = self.solver.fresh_var("fset_ax_s_il", Sort::Int);
                let x = self.solver.fresh_var("fset_ax_x_il", Sort::Int);
                let insert_s_x = self.solver.apply(insert_decl, &[s, x]);
                let contains_s_x = self.solver.apply(&contains_decl, &[s, x]);
                let not_contains = self.solver.not(contains_s_x);
                let len_ins = self.solver.apply(len_decl, &[insert_s_x]);
                let len_s = self.solver.apply(len_decl, &[s]);
                let one = self.solver.int_const(1);
                let len_plus_one = self.solver.add(len_s, one);
                let len_eq = self.eq_term(len_ins, len_plus_one);
                let axiom_body = self.solver.implies(not_contains, len_eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[s, x], axiom_body, &[&[insert_s_x]]);
                self.solver.assert_term(axiom);
            }

            // Insert-len-existing: contains(s, x) ==> len(insert(s, x)) == len(s)
            if let Some(insert_decl) = insert_decl.as_ref() {
                let s = self.solver.fresh_var("fset_ax_s_ie", Sort::Int);
                let x = self.solver.fresh_var("fset_ax_x_ie", Sort::Int);
                let insert_s_x = self.solver.apply(insert_decl, &[s, x]);
                let contains_s_x = self.solver.apply(&contains_decl, &[s, x]);
                let len_ins = self.solver.apply(len_decl, &[insert_s_x]);
                let len_s = self.solver.apply(len_decl, &[s]);
                let len_eq = self.eq_term(len_ins, len_s);
                let axiom_body = self.solver.implies(contains_s_x, len_eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[s, x], axiom_body, &[&[insert_s_x]]);
                self.solver.assert_term(axiom);
            }

            // Remove-len-existing: contains(s, x) ==> len(remove(s, x)) == len(s) - 1
            if let Some(remove_decl) = remove_decl.as_ref() {
                let s = self.solver.fresh_var("fset_ax_s_rl", Sort::Int);
                let x = self.solver.fresh_var("fset_ax_x_rl", Sort::Int);
                let remove_s_x = self.solver.apply(remove_decl, &[s, x]);
                let contains_s_x = self.solver.apply(&contains_decl, &[s, x]);
                let len_rem = self.solver.apply(len_decl, &[remove_s_x]);
                let len_s = self.solver.apply(len_decl, &[s]);
                let one = self.solver.int_const(1);
                let len_minus_one = self.solver.sub(len_s, one);
                let len_eq = self.eq_term(len_rem, len_minus_one);
                let axiom_body = self.solver.implies(contains_s_x, len_eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[s, x], axiom_body, &[&[remove_s_x]]);
                self.solver.assert_term(axiom);
            }

            // Remove-len-absent: !contains(s, x) ==> len(remove(s, x)) == len(s)
            if let Some(remove_decl) = remove_decl.as_ref() {
                let s = self.solver.fresh_var("fset_ax_s_ra", Sort::Int);
                let x = self.solver.fresh_var("fset_ax_x_ra", Sort::Int);
                let remove_s_x = self.solver.apply(remove_decl, &[s, x]);
                let contains_s_x = self.solver.apply(&contains_decl, &[s, x]);
                let not_contains = self.solver.not(contains_s_x);
                let len_rem = self.solver.apply(len_decl, &[remove_s_x]);
                let len_s = self.solver.apply(len_decl, &[s]);
                let len_eq = self.eq_term(len_rem, len_s);
                let axiom_body = self.solver.implies(not_contains, len_eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[s, x], axiom_body, &[&[remove_s_x]]);
                self.solver.assert_term(axiom);
            }

            // ── FSet empty constant: len and is_empty axioms (#2549) ──
            // These axioms need len_decl, so they stay inside the len_decl guard.
            {
                let fset_empty = self.solver.declare_const("fset_empty", Sort::Int);

                // Empty-len: fset_len(fset_empty) == 0
                let len_empty = self.solver.apply(len_decl, &[fset_empty]);
                let zero = self.solver.int_const(0);
                let len_eq_zero = self.eq_term(len_empty, zero);
                self.solver.assert_term(len_eq_zero);

                // Empty-is_empty: fset_is_empty(fset_empty) == true
                if let Some(is_empty_decl) = is_empty_decl.as_ref() {
                    let is_empty_empty = self.solver.apply(is_empty_decl, &[fset_empty]);
                    let t = self.solver.bool_const(true);
                    let is_empty_eq = self.eq_term(is_empty_empty, t);
                    self.solver.assert_term(is_empty_eq);
                }
            }
        }

        // ── FsetInt.interval: Why3 stdlib `set.mlw`, theory `FsetInt`:
        //      function interval (l r: int) : fset int
        //      axiom interval_def:
        //        forall l r x: int. mem x (interval l r) <-> l <= x < r
        //    Creusot binds `FSet::interval` to `set.FsetInt.interval`
        //    (creusot-std/src/logic/fset.rs). Encoded literally, triggered on
        //    the membership application. No cardinality fact is added.
        if let Some(interval_decl) = self.spec_func_decl_cloned("fset_interval") {
            let l = self.solver.fresh_var("fset_ax_l_iv", Sort::Int);
            let r = self.solver.fresh_var("fset_ax_r_iv", Sort::Int);
            let x = self.solver.fresh_var("fset_ax_x_iv", Sort::Int);
            let interval_lr = self.solver.apply(&interval_decl, &[l, r]);
            let mem = self.solver.apply(&contains_decl, &[interval_lr, x]);
            let lower = self.solver.le(l, x);
            let upper = self.solver.lt(x, r);
            let in_range = self.solver.and(lower, upper);
            let iff = self.eq_term(mem, in_range);
            let axiom = self.solver.forall_with_triggers(&[l, r, x], iff, &[&[mem]]);
            self.solver.assert_term(axiom);
        }

        // ── Fset.map: Why3 stdlib `set.mlw`, theory `Fset`:
        //      function map (f: 'a -> 'b) (u: fset 'a) : fset 'b
        //      axiom map_def:
        //        forall f: 'a -> 'b, u: fset 'a, y: 'b.
        //        mem y (map f u) <-> exists x: 'a. mem x u /\ y = f x
        //    Creusot's `FSet::map(self, f)` is open: `FSet::fmap(f, self)`,
        //    and `fmap` is `#[builtin("set.Fset.map")]`. `f x` is
        //    `Mapping::get` (`map.Map.get`), encoded as `mapping_get`.
        //
        //    ay declines quantifiers nested under an iff, so map_def is
        //    asserted in its Skolemized form, a conservative extension with a
        //    fresh witness symbol `fset_map_witness` that nothing else uses:
        //      (->) forall u f y. mem y (map f u) ->
        //             mem (w u f y) u /\ y = f (w u f y)
        //      (<-) forall u f x. mem x u -> mem (f x) (map f u)
        //    The (<-) half is exactly map_def's right-to-left direction
        //    (Why3 also states it as lemma `mem_map`).
        if let Some(map_decl) = self.spec_func_decl_cloned("fset_map") {
            let mapping = crate::encoder::sort_context::sort_inference::mapping_sort();
            let get_decl = self.get_or_declare_spec_fn(
                "mapping_get",
                &[mapping.clone(), Sort::Int],
                Sort::Int,
            );
            let witness_decl = self.get_or_declare_spec_fn(
                "fset_map_witness",
                &[Sort::Int, mapping.clone(), Sort::Int],
                Sort::Int,
            );
            // (->)
            {
                let u = self.solver.fresh_var("fset_ax_u_mpl", Sort::Int);
                let f = self.solver.fresh_var("fset_ax_f_mpl", mapping.clone());
                let y = self.solver.fresh_var("fset_ax_y_mpl", Sort::Int);
                let map_uf = self.solver.apply(&map_decl, &[u, f]);
                let mem_y = self.solver.apply(&contains_decl, &[map_uf, y]);
                let w = self.solver.apply(&witness_decl, &[u, f, y]);
                let mem_w = self.solver.apply(&contains_decl, &[u, w]);
                let fw = self.solver.apply(&get_decl, &[f, w]);
                let y_eq_fw = self.eq_term(y, fw);
                let rhs = self.solver.and(mem_w, y_eq_fw);
                let body = self.solver.implies(mem_y, rhs);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[u, f, y], body, &[&[mem_y]]);
                self.solver.assert_term(axiom);
            }
            // (<-)
            {
                let u = self.solver.fresh_var("fset_ax_u_mpr", Sort::Int);
                let f = self.solver.fresh_var("fset_ax_f_mpr", mapping);
                let x = self.solver.fresh_var("fset_ax_x_mpr", Sort::Int);
                let map_uf = self.solver.apply(&map_decl, &[u, f]);
                let mem_x = self.solver.apply(&contains_decl, &[u, x]);
                let fx = self.solver.apply(&get_decl, &[f, x]);
                let mem_fx = self.solver.apply(&contains_decl, &[map_uf, fx]);
                let body = self.solver.implies(mem_x, mem_fx);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[u, f, x], body, &[&[mem_x, map_uf]]);
                self.solver.assert_term(axiom);
            }
        }

        // ── Fset.filter: Why3 stdlib `set.mlw`, theory `Fset`:
        //      function filter (s: fset 'a) (p: 'a -> bool) : fset 'a
        //      axiom filter_def:
        //        forall s: fset 'a, p: 'a -> bool, x: 'a.
        //        mem x (filter s p) <-> mem x s /\ p x
        //    Creusot binds `FSet::filter` to `set.Fset.filter`. `p x` is
        //    `Mapping<T, bool>::get`; a Bool-position `get` is encoded as
        //    `mapping_get(p, x) != 0` (`coerce_bool_operand`), so the axiom
        //    reads the predicate the same way (bool embedded as 0 / non-0).
        if let Some(filter_decl) = self.spec_func_decl_cloned("fset_filter") {
            let mapping = crate::encoder::sort_context::sort_inference::mapping_sort();
            let get_decl = self.get_or_declare_spec_fn(
                "mapping_get",
                &[mapping.clone(), Sort::Int],
                Sort::Int,
            );
            let s = self.solver.fresh_var("fset_ax_s_ft", Sort::Int);
            let p = self.solver.fresh_var("fset_ax_p_ft", mapping);
            let x = self.solver.fresh_var("fset_ax_x_ft", Sort::Int);
            let filter_sp = self.solver.apply(&filter_decl, &[s, p]);
            let mem_filter = self.solver.apply(&contains_decl, &[filter_sp, x]);
            let mem_s = self.solver.apply(&contains_decl, &[s, x]);
            let px = self.solver.apply(&get_decl, &[p, x]);
            let zero = self.solver.int_const(0);
            let px_holds = self.solver.neq(px, zero);
            let rhs = self.solver.and(mem_s, px_holds);
            let iff = self.eq_term(mem_filter, rhs);
            let axiom = self
                .solver
                .forall_with_triggers(&[s, p, x], iff, &[&[mem_filter]]);
            self.solver.assert_term(axiom);
        }

        // ── FSet empty-contains axiom (#2549) ──
        // forall x. !fset_contains(fset_empty, x)
        // This axiom needs only contains_decl (not len_decl), so it must be
        // outside the len_decl guard to fire even when fset_len is undeclared.
        {
            let fset_empty = self.solver.declare_const("fset_empty", Sort::Int);
            let ex = self.solver.fresh_var("fset_ax_ex", Sort::Int);
            let contains_empty_x = self.solver.apply(&contains_decl, &[fset_empty, ex]);
            let not_contains = self.solver.not(contains_empty_x);
            let axiom =
                self.solver
                    .forall_with_triggers(&[ex], not_contains, &[&[contains_empty_x]]);
            self.solver.assert_term(axiom);
        }
    }
}
