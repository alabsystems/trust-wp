// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FSet ground instance assertions.
//!
//! Extracted from `ground_pool.rs` as part of encoder decomposition (#1988).

use ay_dpll::api::Term;

/// Per-family budget for FSet ground instances. Caps the total
/// number of FSet assertions regardless of remaining global budget.
/// FSet has insert x contains and remove x contains cross-products
/// that could dominate without a cap. (#2707)
const TRUST_WP_FSET_FAMILY_BUDGET: usize = 80;

impl super::super::AYEncoder {
    /// Ground instances for FSet axioms.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn assert_fset_ground_instances(&mut self, remaining_budget: usize) -> usize {
        let mut count = 0usize;
        let budget = remaining_budget.min(TRUST_WP_FSET_FAMILY_BUDGET);

        if budget == 0 {
            tracing::debug!(
                count,
                budget,
                remaining_budget,
                "fset ground instances: budget exhausted before assertion (#2707)"
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
                        "fset ground instances: budget exhausted (#2707)"
                    );
                    return count;
                }
            };
        }

        let contains_decl = self.spec_func_decl_cloned("fset_contains");
        let is_empty_decl = self.spec_func_decl_cloned("fset_is_empty");
        let len_decl = self.spec_func_decl_cloned("fset_len");
        let peek_decl = self.spec_func_decl_cloned("fset_peek");
        let contains_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fset_contains")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        // For each fset_insert(s, x):
        //   - contains(insert(s, x), x) = true
        let insert_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fset_insert")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        if let Some(contains_decl) = contains_decl.as_ref() {
            for (app, args) in &insert_entries {
                if args.len() != 2 {
                    continue;
                }
                let x = args[1];
                let insert_app = *app;
                budget_guard!();
                let contains_ins_x = self.solver.apply(contains_decl, &[insert_app, x]);
                self.assert_solver_term("ground/fset_insert_contains", contains_ins_x);
                count = count.saturating_add(1);
            }
        }

        // For each fset_remove(s, x):
        //   - !contains(remove(s, x), x)
        let remove_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fset_remove")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        if let Some(contains_decl) = contains_decl.as_ref() {
            for (app, args) in &remove_entries {
                if args.len() != 2 {
                    continue;
                }
                let x = args[1];
                let remove_app = *app;
                budget_guard!();
                let contains_rem_x = self.solver.apply(contains_decl, &[remove_app, x]);
                let not_contains = self.solver.not(contains_rem_x);
                self.assert_solver_term("ground/fset_remove_not_contains", not_contains);
                count = count.saturating_add(1);
            }
        }

        // For each observed contains(r, x) and intersection(s, t) of the same
        // sort:
        //   - r == intersection(s, t) =>
        //     contains(r, x) = contains(s, x) && contains(t, x)
        let intersection_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fset_intersection")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        if let Some(contains_decl) = contains_decl.as_ref() {
            for (contains_app, contains_args) in &contains_entries {
                if contains_args.len() != 2 {
                    continue;
                }
                let receiver = contains_args[0];
                let x = contains_args[1];

                for (intersection_app, intersection_args) in &intersection_entries {
                    if intersection_args.len() != 2
                        || self.solver.get_sort(receiver) != self.solver.get_sort(*intersection_app)
                    {
                        continue;
                    }
                    let s = intersection_args[0];
                    let t = intersection_args[1];
                    budget_guard!();
                    let contains_s_x = self.solver.apply(contains_decl, &[s, x]);
                    let contains_t_x = self.solver.apply(contains_decl, &[t, x]);
                    let expected = self.solver.and(contains_s_x, contains_t_x);
                    let eq = self.eq_term(*contains_app, expected);
                    let aliases = self.asserted_equality_closure(*intersection_app, 48);
                    let assertion = if receiver == *intersection_app || aliases.contains(&receiver)
                    {
                        eq
                    } else {
                        let same_receiver = self.eq_term(receiver, *intersection_app);
                        self.solver.implies(same_receiver, eq)
                    };
                    self.assert_solver_term("ground/fset_intersection_contains", assertion);
                    count = count.saturating_add(1);
                }
            }
        }

        // For each observed contains(r, x) and difference(s, t) of the same sort:
        //   - r == difference(s, t) =>
        //     contains(r, x) = contains(s, x) && !contains(t, x)
        let difference_entries: Vec<(Term, Vec<Term>)> = self
            .ground_pool
            .entries_for("fset_difference")
            .map(|es| {
                es.iter()
                    .map(|e| (e.application, e.arg_terms.clone()))
                    .collect()
            })
            .unwrap_or_default();

        if let Some(contains_decl) = contains_decl.as_ref() {
            for (contains_app, contains_args) in &contains_entries {
                if contains_args.len() != 2 {
                    continue;
                }
                let receiver = contains_args[0];
                let x = contains_args[1];

                for (difference_app, difference_args) in &difference_entries {
                    if difference_args.len() != 2
                        || self.solver.get_sort(receiver) != self.solver.get_sort(*difference_app)
                    {
                        continue;
                    }
                    let s = difference_args[0];
                    let t = difference_args[1];
                    budget_guard!();
                    let contains_s_x = self.solver.apply(contains_decl, &[s, x]);
                    let contains_t_x = self.solver.apply(contains_decl, &[t, x]);
                    let not_contains_t_x = self.solver.not(contains_t_x);
                    let expected = self.solver.and(contains_s_x, not_contains_t_x);
                    let eq = self.eq_term(*contains_app, expected);
                    let aliases = self.asserted_equality_closure(*difference_app, 48);
                    let assertion = if receiver == *difference_app || aliases.contains(&receiver) {
                        eq
                    } else {
                        let same_receiver = self.eq_term(receiver, *difference_app);
                        self.solver.implies(same_receiver, eq)
                    };
                    self.assert_solver_term("ground/fset_difference_contains", assertion);
                    count = count.saturating_add(1);
                }
            }
        }

        // fset_len non-negativity for each observed len application
        let len_entries: Vec<Vec<Term>> = self
            .ground_pool
            .entries_for("fset_len")
            .map(|es| es.iter().map(|e| e.arg_terms.clone()).collect())
            .unwrap_or_default();
        if let Some(len_decl) = len_decl.as_ref() {
            let zero = self.solver.int_const(0);
            for args in &len_entries {
                if args.len() == 1 {
                    budget_guard!();
                    let len_app = self.solver.apply(len_decl, &[args[0]]);
                    let ge_zero = self.solver.ge(len_app, zero);
                    self.assert_solver_term("ground/fset_len_nonneg", ge_zero);
                    count = count.saturating_add(1);
                }
            }

            // is_empty link: is_empty(s) <==> len(s) == 0
            if let Some(is_empty_decl) = is_empty_decl.as_ref() {
                for args in &len_entries {
                    if args.len() == 1 {
                        budget_guard!();
                        let len_app = self.solver.apply(len_decl, &[args[0]]);
                        let is_empty_app = self.solver.apply(is_empty_decl, &[args[0]]);
                        let zero = self.solver.int_const(0);
                        let len_eq_zero = self.eq_term(len_app, zero);
                        let iff = self.eq_term(is_empty_app, len_eq_zero);
                        self.assert_solver_term("ground/fset_len_empty_link", iff);
                        count = count.saturating_add(1);
                    }
                }
            }
        }

        // peek(s) membership: !is_empty(s) => contains(s, peek(s))
        let peek_entries: Vec<Vec<Term>> = self
            .ground_pool
            .entries_for("fset_peek")
            .map(|es| es.iter().map(|e| e.arg_terms.clone()).collect())
            .unwrap_or_default();
        if let (Some(peek_decl), Some(is_empty_decl), Some(contains_decl)) = (
            peek_decl.as_ref(),
            is_empty_decl.as_ref(),
            contains_decl.as_ref(),
        ) {
            for args in &peek_entries {
                if args.len() == 1 {
                    let s = args[0];
                    budget_guard!();
                    let is_empty_s = self.solver.apply(is_empty_decl, &[s]);
                    let not_empty = self.solver.not(is_empty_s);
                    let peek_s = self.solver.apply(peek_decl, &[s]);
                    let contains_s_peek = self.solver.apply(contains_decl, &[s, peek_s]);
                    let impl_term = self.solver.implies(not_empty, contains_s_peek);
                    self.assert_solver_term("ground/fset_peek_contains", impl_term);
                    count = count.saturating_add(1);
                }
            }
        }

        // fset_insert len: for each insert(s, x), assert len relationships.
        // Mirrors quantified axioms in axioms.rs: insert-len-new and insert-len-existing.
        // These ground instances help ay when the quantified axioms don't fire. (#2288)
        if let (Some(contains_decl), Some(len_decl)) = (contains_decl.as_ref(), len_decl.as_ref()) {
            for (app, args) in &insert_entries {
                if args.len() != 2 {
                    continue;
                }
                let s = args[0];
                let x = args[1];
                let insert_app = *app;
                budget_guard!();
                let contains_s_x = self.solver.apply(contains_decl, &[s, x]);
                let len_ins = self.solver.apply(len_decl, &[insert_app]);
                let len_s = self.solver.apply(len_decl, &[s]);
                let one = self.solver.int_const(1);
                let len_plus_1 = self.solver.add(len_s, one);

                // ITE formulation: len(insert(s,x)) = ite(contains(s,x), len(s), len(s)+1)
                let ite_len = self.solver.ite(contains_s_x, len_s, len_plus_1);
                let eq = self.eq_term(len_ins, ite_len);
                self.assert_solver_term("ground/fset_insert_len", eq);
                count = count.saturating_add(1);
            }
        }

        // fset_remove len: for each remove(s, x), assert len relationships.
        // Mirrors quantified axioms: remove-len-existing and remove-len-absent. (#2288)
        if let (Some(contains_decl), Some(len_decl)) = (contains_decl.as_ref(), len_decl.as_ref()) {
            for (app, args) in &remove_entries {
                if args.len() != 2 {
                    continue;
                }
                let s = args[0];
                let x = args[1];
                let remove_app = *app;
                budget_guard!();
                let contains_s_x = self.solver.apply(contains_decl, &[s, x]);
                let len_rem = self.solver.apply(len_decl, &[remove_app]);
                let len_s = self.solver.apply(len_decl, &[s]);
                let one = self.solver.int_const(1);
                let len_minus_1 = self.solver.sub(len_s, one);

                // ITE formulation: len(remove(s,x)) = ite(contains(s,x), len(s)-1, len(s))
                let ite_len = self.solver.ite(contains_s_x, len_minus_1, len_s);
                let eq = self.eq_term(len_rem, ite_len);
                self.assert_solver_term("ground/fset_remove_len", eq);
                count = count.saturating_add(1);
            }
        }

        // Insert-non-empty: for each insert(s, x), assert !is_empty(insert(s, x)).
        // Ground counterpart to the quantified axiom in axioms.rs (#2547).
        if let Some(is_empty_decl) = is_empty_decl.as_ref() {
            for (app, args) in &insert_entries {
                if args.len() != 2 {
                    continue;
                }
                let insert_app = *app;
                budget_guard!();
                let is_empty_ins = self.solver.apply(is_empty_decl, &[insert_app]);
                let not_empty = self.solver.not(is_empty_ins);
                self.assert_solver_term("ground/fset_insert_non_empty", not_empty);
                count = count.saturating_add(1);
            }
        }

        // Contains-non-empty: for each contains(s, x) ground term, assert
        // contains(s, x) ==> !is_empty(s). Ground counterpart (#2547).
        if let (Some(_contains_decl), Some(is_empty_decl)) =
            (contains_decl.as_ref(), is_empty_decl.as_ref())
        {
            for (app, args) in &contains_entries {
                if args.len() != 2 {
                    continue;
                }
                let s = args[0];
                let contains_app = *app;
                budget_guard!();
                let is_empty_s = self.solver.apply(is_empty_decl, &[s]);
                let not_empty = self.solver.not(is_empty_s);
                let impl_term = self.solver.implies(contains_app, not_empty);
                self.assert_solver_term("ground/fset_contains_non_empty", impl_term);
                count = count.saturating_add(1);
            }
        }

        // Remove-contains-frame: for each remove(s, x) and each observed
        // membership query `contains(s, y)` on the SAME base set s, assert
        //   x != y ==> contains(remove(s, x), y) == contains(s, y).
        // Ground counterpart to the quantified frame axiom in axioms.rs.
        //
        // The candidate `y` values are the second arguments of `contains(s, ·)`
        // terms — the elements already queried against the base set. Crucially
        // this INCLUDES the negated goal's Skolem (bug/vcgen's `set_max` `sk_o`
        // in `contains(s, sk_o)`, once this family runs after the goal is
        // asserted), which is exactly the witness that must be shown to survive
        // into the recursive sub-set. Materializing `contains(remove(s, x), sk_o)`
        // supplies the frame link ay-dpll's single-round E-matching cannot derive
        // from the quantified frame axiom.
        //
        // The receiver restriction (`y` drawn only from `contains(s, ·)`, never
        // from `contains(sp, ·)`) is deliberate: instantiating the frame at every
        // observed contains argument mints a fresh `contains(sp, y)` for each,
        // and each is a trigger for a recursion-IH universal of the form
        // `forall o. contains(sp, o) ==> …`, which floods the arithmetic
        // interface (observed empirically as ~130k-decision E-matching churn on
        // set_max). Keying off `contains(s, ·)` bounds the family to the goal
        // witnesses that actually need the link. Sound: each instance is a true
        // instance of the asserted universal frame axiom. (#2288 pattern, #vcgen)
        // Opt-in (default OFF): the frame family reduces the set_max-style
        // recursion obligation to a ground refutation, but the pinned ay-core
        // LRA (leg-C "simplex=Sat but unsupported", the #6167 per-atom gate)
        // returns Unknown on the resulting UF-valued arithmetic atoms
        // (`sk_o <= set_max(sp)`), so the reduction cannot yet be closed by the
        // solver. Kept behind a flag so the sound infrastructure is preserved
        // without changing default behavior; enable once ay's LRA supports the
        // UF-arithmetic atoms. (#vcgen)
        if std::env::var_os("TRUST_WP_ENABLE_FSET_FRAME_IH_GROUNDS").is_some() {
            if let Some(contains_decl) = contains_decl.as_ref() {
                for (remove_app, remove_args) in &remove_entries {
                    if remove_args.len() != 2 {
                        continue;
                    }
                    let s = remove_args[0];
                    let x = remove_args[1];
                    let remove_app = *remove_app;
                    for (_contains_app, contains_args) in &contains_entries {
                        if contains_args.len() != 2 {
                            continue;
                        }
                        // Only frame elements already queried against THIS base set s
                        // (i.e. `contains(s, y)` terms), never arbitrary contains
                        // receivers — see the churn note above.
                        if contains_args[0] != s {
                            continue;
                        }
                        let y = contains_args[1];
                        // y == x is the remove-contains-self case (already emitted as
                        // `!contains(remove(s, x), x)`); the frame law only constrains
                        // distinct elements.
                        if y == x {
                            continue;
                        }
                        budget_guard!();
                        let contains_rem_y = self.solver.apply(contains_decl, &[remove_app, y]);
                        let contains_s_y = self.solver.apply(contains_decl, &[s, y]);
                        let frame_eq = self.eq_term(contains_rem_y, contains_s_y);
                        let x_eq_y = self.eq_term(x, y);
                        let x_ne_y = self.solver.not(x_eq_y);
                        let framed = self.solver.implies(x_ne_y, frame_eq);
                        self.assert_solver_term("ground/fset_remove_contains_frame", framed);
                        count = count.saturating_add(1);
                    }
                }
            }
        }

        // Ground instances of the Why3 membership characterisations for
        // `fset_interval` (FsetInt.interval_def), `fset_filter`
        // (Fset.filter_def) and `fset_map` (Fset.map_def). Each is the
        // quantified axiom from `assert_fset_axioms` instantiated at an
        // observed `contains(r, x)` with `r == <op>(..)`.
        if let Some(contains_decl) = contains_decl.as_ref() {
            let mapping = crate::encoder::sort_context::sort_inference::mapping_sort();
            let entries = |this: &Self, name: &str| -> Vec<(Term, Vec<Term>)> {
                this.ground_pool
                    .entries_for(name)
                    .map(|es| {
                        es.iter()
                            .map(|e| (e.application, e.arg_terms.clone()))
                            .collect()
                    })
                    .unwrap_or_default()
            };
            let interval_entries = entries(self, "fset_interval");
            let filter_entries = entries(self, "fset_filter");
            let map_entries = entries(self, "fset_map");
            let get_decl = if filter_entries.is_empty() && map_entries.is_empty() {
                None
            } else {
                Some(self.get_or_declare_spec_fn(
                    "mapping_get",
                    &[mapping.clone(), ay_dpll::api::Sort::Int],
                    ay_dpll::api::Sort::Int,
                ))
            };
            for (contains_app, contains_args) in &contains_entries {
                if contains_args.len() != 2 {
                    continue;
                }
                let receiver = contains_args[0];
                let x = contains_args[1];
                if self.solver.get_sort(x) != ay_dpll::api::Sort::Int {
                    continue;
                }
                let ops = interval_entries
                    .iter()
                    .map(|e| ("interval", e))
                    .chain(filter_entries.iter().map(|e| ("filter", e)))
                    .chain(map_entries.iter().map(|e| ("map", e)))
                    .collect::<Vec<_>>();
                for (kind, (op_app, op_args)) in ops {
                    if op_args.len() != 2
                        || self.solver.get_sort(receiver) != self.solver.get_sort(*op_app)
                    {
                        continue;
                    }
                    let (a, b) = (op_args[0], op_args[1]);
                    let expected = match (kind, get_decl.as_ref()) {
                        ("interval", _) => {
                            let lower = self.solver.le(a, x);
                            let upper = self.solver.lt(x, b);
                            self.solver.and(lower, upper)
                        }
                        ("filter", Some(get_decl)) => {
                            if self.solver.get_sort(b) != mapping {
                                continue;
                            }
                            let mem_s = self.solver.apply(contains_decl, &[a, x]);
                            let px = self.solver.apply(get_decl, &[b, x]);
                            let zero = self.solver.int_const(0);
                            let px_holds = self.solver.neq(px, zero);
                            self.solver.and(mem_s, px_holds)
                        }
                        ("map", Some(get_decl)) => {
                            if self.solver.get_sort(b) != mapping {
                                continue;
                            }
                            // Skolemized map_def (see `assert_fset_axioms`):
                            //   (->) contains(r, x) -> contains(a, w) /\ x = get(b, w)
                            //        with w = fset_map_witness(a, b, x)
                            let witness_decl = self.get_or_declare_spec_fn(
                                "fset_map_witness",
                                &[
                                    ay_dpll::api::Sort::Int,
                                    mapping.clone(),
                                    ay_dpll::api::Sort::Int,
                                ],
                                ay_dpll::api::Sort::Int,
                            );
                            let w = self.solver.apply(&witness_decl, &[a, b, x]);
                            let mem_w = self.solver.apply(contains_decl, &[a, w]);
                            let fw = self.solver.apply(get_decl, &[b, w]);
                            let x_eq_fw = self.eq_term(x, fw);
                            let rhs = self.solver.and(mem_w, x_eq_fw);
                            let forward = self.solver.implies(*contains_app, rhs);
                            budget_guard!();
                            let assertion = if receiver == *op_app {
                                forward
                            } else {
                                let same_receiver = self.eq_term(receiver, *op_app);
                                self.solver.implies(same_receiver, forward)
                            };
                            self.assert_solver_term("ground/fset_map_contains_witness", assertion);
                            count += 1;
                            continue;
                        }
                        _ => continue,
                    };
                    budget_guard!();
                    let eq = self.eq_term(*contains_app, expected);
                    let assertion = if receiver == *op_app {
                        eq
                    } else {
                        let same_receiver = self.eq_term(receiver, *op_app);
                        self.solver.implies(same_receiver, eq)
                    };
                    self.assert_solver_term("ground/fset_builtin_contains", assertion);
                    count += 1;
                }
            }
        }

        count
    }
}
