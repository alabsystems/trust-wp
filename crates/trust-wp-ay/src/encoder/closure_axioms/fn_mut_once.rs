// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FnMut/FnOnce law axiom assertions: the `fn_mut_once` forward and reverse laws.
//!
//! The `fn_mut_once` law is the foundation of the Fn trait hierarchy weakening
//! chain: every `FnMut` closure is also `FnOnce` (by resolving the post-state).
//!
//! Eager instantiation and Skolemization helpers are in sibling modules:
//! - [`super::fn_mut_once_eager`]: Ground postcondition_once instantiation
//! - [`super::fn_mut_once_skolem`]: Existential Skolemization for postcondition_mut

use ay_dpll::api::Sort;
use trust_wp_core::formula::PureExpr;

use super::super::AYEncoder;

impl AYEncoder {
    pub(super) fn collect_ground_postcondition_once_calls<'a>(
        exprs: &[&'a PureExpr],
    ) -> Vec<(&'a PureExpr, &'a [PureExpr])> {
        exprs
            .iter()
            .filter_map(|expr| match expr {
                PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                } if method == "postcondition_once" => Some((receiver.as_ref(), args.as_slice())),
                _ => None,
            })
            .collect()
    }

    /// Assert the `fn_mut_once` law axiom connecting `postcondition_once` to
    /// `postcondition_mut` + `resolve`.
    ///
    /// For each compatible pair of declared closure-spec UF symbols, asserts
    /// two axioms (Skolemized biconditional):
    ///
    /// **Forward** (`FnMut` => FnOnce):
    /// ```text
    /// forall self args res_state result.
    ///   postcondition_mut(self, args, res_state, result)
    ///     ==> postcondition_once(self, args, result)
    /// ```
    ///
    /// **Reverse** (`FnOnce` => `FnMut`, Skolemized):
    /// ```text
    /// forall self args result.
    ///   postcondition_once(self, args, result)
    ///     ==> postcondition_mut(self, args, witness(self, args, result), result)
    ///         && resolve(witness(self, args, result))
    /// ```
    ///
    /// The Skolem function `witness` replaces the existential quantifier to
    /// avoid nested alternating quantifiers (`forall-exists`) which ay's
    /// E-matching handles poorly.
    ///
    /// A `postcondition_once_N_<sorts>` symbol pairs with `postcondition_mut_(N+1)_<sorts>`
    /// where the extra parameter (at position N-1, before result) is the `res_state`.
    ///
    /// This axiom is the foundation of the Fn trait hierarchy weakening chain:
    /// every `FnMut` closure is also `FnOnce` (by resolving the post-state).
    pub(crate) fn assert_fn_mut_once_law(&mut self) {
        self.assert_closure_resolve_axioms();
        // Collect postcondition_once declarations up front to avoid mutable/immutable
        // borrow conflicts while asserting axioms.
        let once_symbols: Vec<(String, ay_dpll::api::FuncDecl)> = self
            .logic_funcs_iter()
            .filter(|(name, _)| name.starts_with("closure_postcondition_once_"))
            .map(|(name, decl)| (name.clone(), decl.clone()))
            .collect();
        // Pre-collect postcondition_mut entries once instead of re-scanning all
        // logic_funcs per postcondition_once symbol (#2278 F3).
        let mut_entries = self.collect_postcondition_mut_entries();

        for (once_name, once_decl) in &once_symbols {
            let Some((once_arity, once_tags)) =
                Self::parse_closure_signature(once_name, "closure_postcondition_once_")
            else {
                continue;
            };
            if once_tags.is_empty() {
                continue;
            }
            // Use the declared UF domain sorts rather than tag-reconstructed
            // sorts — `closure_sort_from_tag("u")` returns `Sort::Int` but the
            // UF domain may contain `Sort::Uninterpreted("Unit")`. (#2151)
            let once_sorts: Vec<Sort> = once_decl.domain().to_vec();
            let sort_sig = once_tags.join("_");
            let insert_pos = once_arity - 1;
            let mut_candidates =
                Self::matching_postcondition_mut_symbols(&mut_entries, once_arity, &once_tags);
            if mut_candidates.is_empty() {
                continue;
            }
            for (_mut_name, mut_decl, mut_tags, mut_sorts) in mut_candidates {
                let res_state_sort = mut_sorts[insert_pos].clone();
                let res_state_tag = &mut_tags[insert_pos];
                let witness_name =
                    Self::fn_mut_once_witness_name(once_arity, &sort_sig, res_state_tag);
                self.assert_fn_mut_once_forward(once_decl, &mut_decl, once_arity, &mut_sorts);
                self.assert_fn_mut_once_reverse(
                    once_decl,
                    &mut_decl,
                    &once_sorts,
                    &mut_sorts,
                    &res_state_sort,
                    &witness_name,
                );
            }
        }
    }

    /// Forward axiom: `postcondition_mut(self, args, res_state, result)
    ///   ==> postcondition_once(self, args, result)`.
    fn assert_fn_mut_once_forward(
        &mut self,
        once_decl: &ay_dpll::api::FuncDecl,
        mut_decl: &ay_dpll::api::FuncDecl,
        once_arity: usize,
        mut_sorts: &[Sort],
    ) {
        let mut_arity = mut_sorts.len();
        let mut fwd_vars = Vec::with_capacity(mut_arity);
        for (i, sort) in mut_sorts.iter().enumerate() {
            let var = self.solver.fresh_var(&format!("law_fwd_{i}"), sort.clone());
            fwd_vars.push(var);
        }

        let Some(mut_term) = self.axiom_apply_tracked("fn_mut_once_fwd:mut", mut_decl, &fwd_vars)
        else {
            return;
        };

        let mut once_args = Vec::with_capacity(once_arity);
        for (i, var) in fwd_vars.iter().enumerate() {
            if i != once_arity - 1 {
                once_args.push(*var);
            }
        }
        // Fail closed when once_decl diverges from the mut_decl domain used to
        // create these variables; never fabricate a differently typed alias.
        // (#2556)
        let Some(once_term) =
            self.axiom_apply_sort_adapted("fn_mut_once_fwd:once", once_decl, &once_args)
        else {
            return;
        };

        let implication = self.solver.implies(mut_term, once_term);
        let axiom = self
            .solver
            .forall_with_triggers(&fwd_vars, implication, &[&[mut_term]]);
        self.solver.assert_term(axiom);
    }

    /// Reverse axiom (Skolemized): `postcondition_once(self, args, result)
    ///   ==> postcondition_mut(self, args, witness(...), result) && resolve(witness(...))`.
    fn assert_fn_mut_once_reverse(
        &mut self,
        once_decl: &ay_dpll::api::FuncDecl,
        mut_decl: &ay_dpll::api::FuncDecl,
        once_sorts: &[Sort],
        mut_sorts: &[Sort],
        res_state_sort: &Sort,
        witness_name: &str,
    ) {
        let mut_arity = mut_sorts.len();
        let once_arity = once_sorts.len();
        let mut rev_vars = Vec::with_capacity(once_arity);
        for (i, sort) in once_sorts.iter().enumerate() {
            let var = self.solver.fresh_var(&format!("law_rev_{i}"), sort.clone());
            rev_vars.push(var);
        }

        let Some(once_term) =
            self.axiom_apply_tracked("fn_mut_once_rev:once", once_decl, &rev_vars)
        else {
            return;
        };

        let witness_fn =
            self.get_or_declare_fn_mut_once_witness(witness_name, once_sorts, res_state_sort);
        let Some(witness_term) =
            self.axiom_apply_tracked("fn_mut_once_rev:witness", &witness_fn, &rev_vars)
        else {
            return;
        };

        let mut mut_args = Vec::with_capacity(mut_arity);
        for var in &rev_vars[..rev_vars.len() - 1] {
            mut_args.push(*var);
        }
        mut_args.push(witness_term);
        mut_args.push(rev_vars[rev_vars.len() - 1]);
        // Fail closed when mut_decl diverges from the once_decl domain used to
        // create these variables; never fabricate a differently typed alias.
        // (#2556)
        let Some(mut_term) =
            self.axiom_apply_sort_adapted("fn_mut_once_rev:mut", mut_decl, &mut_args)
        else {
            return;
        };
        let Some(resolve_witness) = self.resolve_term_for_sort(witness_term, res_state_sort) else {
            return;
        };
        let rhs = self.solver.and(mut_term, resolve_witness);

        let implication = self.solver.implies(once_term, rhs);
        let axiom = self
            .solver
            .forall_with_triggers(&rev_vars, implication, &[&[once_term]]);
        self.solver.assert_term(axiom);
    }

    pub(crate) fn get_or_declare_fn_mut_once_witness(
        &mut self,
        witness_name: &str,
        witness_sorts: &[Sort],
        res_state_sort: &Sort,
    ) -> ay_dpll::api::FuncDecl {
        let witness_fn = if let Some(existing) = self.logic_func_decl_cloned(witness_name) {
            existing
        } else {
            let declared =
                self.solver
                    .declare_fun(witness_name, witness_sorts, res_state_sort.clone());
            self.register_logic_func(witness_name.to_string(), declared.clone());
            declared
        };
        let witness_smt_name = trust_wp_core::logic::logic_fn_smt_name(witness_name);
        self.register_logic_func(witness_smt_name, witness_fn.clone());
        witness_fn
    }
}
