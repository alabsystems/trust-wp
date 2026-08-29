// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type invariant ground-axiom registration and container element invariant assertions.
//!
//! Contains:
//! - `register_type_invariant` — registers a type invariant defining axiom for ground instantiation
//! - `assert_container_element_invariant` — quantified element invariant via UF
//! - `assert_container_element_invariant_body` — quantified element invariant with inlined body

use ay_dpll::api::Sort;
use tracing::debug;
use trust_wp_core::{formula::PureExpr, logic::type_invariant_method_name};

use super::super::{AYEncoder, AssertionPhase, ContainerElementInvariantSpec};
use crate::error::EncodingError;

impl AYEncoder {
    /// Register a type invariant defining axiom (#359, Phase 2).
    ///
    /// Takes the type name, self parameter name, SMT sort, and invariant body expression.
    /// Declares `method___trust_wp_invariant_<Type>_1_<tag>` and registers the
    /// defining body with the ground pool. The encoder intentionally does not
    /// assert the global quantified axiom
    /// `forall self. invariant(self) <=> body`; observed invariant calls are
    /// handled by top-level body inlining or concrete ground-pool instances.
    ///
    /// Each type gets a unique SMT symbol via `type_invariant_method_name(type_name)`,
    /// so multiple types with invariants on the same sort do not collide (#666).
    /// Call sites must use the type-qualified method name (e.g.,
    /// `__trust_wp_invariant_NonZero`) rather than raw `"invariant"`.
    ///
    /// **Sort consistency:** `param_sort` must match what `infer_expr_sort` returns for
    /// the receiver expression at call sites. A mismatch produces different symbol names
    /// and disconnects the axiom from predicate applications.
    pub(crate) fn register_type_invariant(
        &mut self,
        type_name: &str,
        self_param: &str,
        param_sort: Sort,
        body: &PureExpr,
    ) -> Result<(), EncodingError> {
        let method_name = type_invariant_method_name(type_name);
        let smt_name = Self::bool_method_symbol(&method_name, std::slice::from_ref(&param_sort));
        self.register_type_invariant_axiom(&smt_name, self_param, param_sort, body)
    }

    fn register_type_invariant_axiom(
        &mut self,
        smt_name: &str,
        self_param: &str,
        param_sort: Sort,
        body: &PureExpr,
    ) -> Result<(), EncodingError> {
        // Skip if already registered
        if self.has_logic_fn_axiom_asserted(smt_name) {
            return Ok(());
        }

        self.increment_type_invariant_count();

        // Trivial invariant optimization (#1296): when the body is literally `true`,
        // skip the quantified axiom `forall self. inv(self) = true` which requires
        // E-matching to instantiate. Instead, record the method as trivially true
        // so call sites can inline `true` directly.
        if matches!(body, PureExpr::Bool(true)) {
            // Still declare the function so sort inference doesn't break.
            // get_or_declare_logic_func handles the idempotent declare-if-absent
            // pattern through the encoder shell. (#1584)
            self.get_or_declare_logic_func(smt_name, std::slice::from_ref(&param_sort), Sort::Bool);
            self.register_trivial_type_invariant(smt_name.to_string());
            self.mark_logic_fn_axiom_asserted(smt_name.to_string());
            return Ok(());
        }

        // Declare or get the uninterpreted invariant function
        let func_decl =
            self.get_or_declare_logic_func(smt_name, std::slice::from_ref(&param_sort), Sort::Bool);

        debug!("  registering type invariant {smt_name}: ground instances only");

        // Register the type invariant axiom with the ground-term pool for
        // ground instantiation (#1965, Lane 5). Avoiding the global quantified
        // axiom keeps otherwise ground obligations out of QuantifierUnhandled;
        // observed `inv(x)` applications still get `inv(x) <=> body[x/self]`
        // through top-level body inlining or the ground-pool flush.
        // When ground applications of `inv(x)` are collected during encoding
        // (from preconditions, postconditions, or body), the ground pool can
        // re-encode the body with concrete `x` as a ground instance.
        {
            use super::super::ground_pool::{AxiomEntry, AxiomKind};
            self.ground_pool.register_axiom(AxiomEntry {
                fn_symbol: smt_name.to_string(),
                params: vec![self_param.to_string()],
                body: body.clone(),
                requires: Vec::new(),
                func_decl: func_decl.clone(),
                return_sort: Sort::Bool,
                kind: AxiomKind::Defining,
            });
        }

        self.mark_logic_fn_axiom_asserted(smt_name.to_string());
        Ok(())
    }

    /// Materialize retry-time type invariant metadata under a new symbol (#2620).
    ///
    /// When sort drift causes the applied UF symbol (`final_symbol`) to differ
    /// from the registration symbol (`source_symbol`), this method aliases trivial
    /// markers and defining axioms so the retry UF has matching invariant metadata.
    ///
    /// This ensures:
    /// - Trivial invariant fast paths fire for the retry symbol
    /// - Quantified defining axioms have triggers matching the retry UF
    /// - Ground pool entries exist under the retry symbol
    ///
    /// Does NOT call `increment_type_invariant_count()` — aliases are not new
    /// user invariants and must not inflate the counter that
    /// `all_type_invariants_trivially_true()` relies on.
    pub(in crate::encoder) fn materialize_retry_type_invariant_symbol(
        &mut self,
        source_symbol: &str,
        final_symbol: &str,
    ) -> Result<(), EncodingError> {
        if source_symbol == final_symbol {
            return Ok(());
        }
        if self.has_logic_fn_axiom_asserted(final_symbol) {
            return Ok(());
        }

        // Trivial case: alias the trivial marker
        if self.is_trivial_type_invariant(source_symbol) {
            // The function was already declared under final_symbol by the retry
            // path in apply_method_func_with_actual_sort_retry. If not, declare
            // it from the source declaration's domain.
            if self.logic_func_decl_cloned(final_symbol).is_none() {
                if let Some(source_decl) = self.logic_func_decl_cloned(source_symbol) {
                    let domain = source_decl.domain().to_vec();
                    self.get_or_declare_logic_func(final_symbol, &domain, Sort::Bool);
                }
            }
            self.register_trivial_type_invariant(final_symbol.to_string());
            self.mark_logic_fn_axiom_asserted(final_symbol.to_string());
            return Ok(());
        }

        // Non-trivial case: find the defining axiom from the ground pool
        // and re-assert under final_symbol with the retry declaration's sorts.
        use super::super::ground_pool::AxiomKind;
        let (self_param, body) = {
            let axiom = self.ground_pool.axioms().iter().find(|a| {
                a.fn_symbol == source_symbol && a.kind == AxiomKind::Defining && a.params.len() == 1
            });
            match axiom {
                Some(a) => (a.params[0].clone(), a.body.clone()),
                None => return Ok(()),
            }
        };

        // Get the final func_decl. The retry path should have already declared it.
        let func_decl = if let Some(decl) = self.logic_func_decl_cloned(final_symbol) {
            decl
        } else {
            let domain = self
                .logic_func_decl_cloned(source_symbol)
                .map(|d| d.domain().to_vec())
                .unwrap_or_default();
            if domain.is_empty() {
                return Ok(());
            }
            self.get_or_declare_logic_func(final_symbol, &domain, Sort::Bool)
        };

        let param_sort = func_decl.domain().first().cloned().unwrap_or(Sort::Int);

        // Create bound variable and assert the defining axiom
        let qvar_id = self.next_quantifier_var_id();
        let bound_var = self
            .solver
            .fresh_var(&format!("inv_self_{qvar_id}"), param_sort);

        let old = self.insert_var(self_param.clone(), bound_var);
        let old_sort = self.insert_var_sort(self_param.clone(), self.solver.get_sort(bound_var));

        self.quantifier_state.inc_quantifier_depth();
        let body_result = self.encode_pure(&body);
        self.quantifier_state.dec_quantifier_depth();

        self.restore_var_sort(&self_param, old_sort);
        self.restore_var(&self_param, old);

        let body_term = body_result?;

        let fn_application = self.solver.apply(&func_decl, &[bound_var]);
        let defining_eq = self.eq_or_iff(fn_application, body_term, &Sort::Bool);

        debug!(
            "  materializing retry invariant {final_symbol}: \
                 forall self . {final_symbol}(self) = body (alias of {source_symbol})"
        );

        let axiom =
            self.solver
                .forall_with_triggers(&[bound_var], defining_eq, &[&[fn_application]]);
        self.assert_term(axiom);

        {
            use super::super::ground_pool::AxiomEntry;
            self.ground_pool.register_axiom(AxiomEntry {
                fn_symbol: final_symbol.to_string(),
                params: vec![self_param],
                body,
                requires: Vec::new(),
                func_decl,
                return_sort: Sort::Bool,
                kind: AxiomKind::Defining,
            });
        }

        self.mark_logic_fn_axiom_asserted(final_symbol.to_string());
        Ok(())
    }

    /// Assert quantified element invariant for a container parameter (#869).
    ///
    /// For a concrete parameter's Seq view variable, asserts:
    /// ```text
    /// forall i. 0 <= i < seq_len(param_view) =>
    ///     inv_element(seq_index_logic(param_view, i))
    /// ```
    ///
    /// This connects the container parameter to element-level invariants through
    /// the Seq encoding. Called from verify/function.rs when a `TypeInvariantDef`
    /// has `element_invariant_method` set.
    ///
    /// `param_view_name` is the Seq-sorted view variable name (e.g., "x_view").
    /// `element_invariant_method` is the qualified method name
    /// (e.g., "__trust_wp_invariant_SumTo10").
    #[cfg(test)]
    pub(crate) fn assert_container_element_invariant(
        &mut self,
        param_view_name: &str,
        element_invariant_method: &str,
    ) -> Result<(), EncodingError> {
        let element_smt = Self::bool_method_symbol(element_invariant_method, &[Sort::Int]);
        if !self.register_container_element_invariant_method_spec(
            param_view_name,
            element_invariant_method,
        )? {
            return Ok(());
        }

        // Declare or get element invariant function: inv_element : Int -> Bool
        let element_fn = self.get_or_declare_logic_func(&element_smt, &[Sort::Int], Sort::Bool);

        let seq_funcs = self.ensure_seq_theory();
        let seq_len_fn = seq_funcs.seq_len.clone();
        let seq_index_fn = seq_funcs.seq_index_logic.clone();
        let seq_sort = self.get_seq_sort();

        // Get the concrete Seq-sorted view variable for the parameter
        let param_view = self.get_or_declare_var(param_view_name, seq_sort)?;

        // Create bound variable for element index
        let i_id = self.next_quantifier_var_id();
        let i = self
            .solver
            .fresh_var(&format!("elem_inv_i_{i_id}"), Sort::Int);

        // Build: seq_len(param_view)
        let len = self.solver.apply(&seq_len_fn, &[param_view]);

        // Build: 0 <= i < seq_len(param_view)
        let zero = self.solver.int_const(0);
        let i_ge_0 = self.solver.ge(i, zero);
        let i_lt_len = self.solver.lt(i, len);
        let in_bounds = self.solver.and(i_ge_0, i_lt_len);

        // Build: seq_index_logic(param_view, i)
        let elem = self.solver.apply(&seq_index_fn, &[param_view, i]);

        // Build: inv_element(seq_index_logic(param_view, i))
        let inv_elem = self.solver.apply(&element_fn, &[elem]);

        // Build: in_bounds => inv_element(elem)
        let body = self.solver.implies(in_bounds, inv_elem);

        // Build: forall i. in_bounds => inv_element(elem)
        // Trigger on seq_index_logic(param_view, i). The needs_index_ground_terms
        // flag (set above) ensures that when encode_pure produces ground Array
        // select terms, corresponding seq_index_logic UF equalities are asserted,
        // enabling this trigger to fire (#1575).
        let axiom = self.solver.forall_with_triggers(&[i], body, &[&[elem]]);

        debug!(
            "  asserting container element invariant for {param_view_name}: \
                 forall i. 0 <= i < len => {element_smt}(index(view, i))"
        );

        self.assert_term(axiom);
        Ok(())
    }

    /// Register a container element invariant for later per-index ground
    /// instantiation without asserting the global quantified forall.
    pub(crate) fn register_container_element_invariant_method_spec(
        &mut self,
        param_view_name: &str,
        element_invariant_method: &str,
    ) -> Result<bool, EncodingError> {
        // Trivial invariant short-circuit (#1296): if element invariant is trivially
        // true, both the quantified assertion and all ground instances are tautological.
        let element_smt = Self::bool_method_symbol(element_invariant_method, &[Sort::Int]);
        if self.is_trivial_type_invariant(&element_smt) {
            return Ok(false);
        }

        // Enable ground seq_index_logic UF term emission (#1575). When
        // encode_pure produces Array select terms via seq_index_term, this flag
        // causes corresponding seq_index_logic UF equalities to be asserted as
        // ground terms and lets the registration below fire for every concrete
        // index term seen by the obligation.
        self.set_needs_seq_index_ground_terms();

        let seq_sort = self.get_seq_sort();
        let param_view = self.get_or_declare_var(param_view_name, seq_sort)?;
        self.register_container_element_invariant(
            param_view,
            ContainerElementInvariantSpec::Method {
                element_invariant_method: element_invariant_method.to_string(),
            },
        );

        Ok(true)
    }

    /// Assert quantified element invariant with inlined body (#869).
    ///
    /// Like [`assert_container_element_invariant`], but instead of calling the
    /// element invariant UF (which requires a second E-matching round to expand),
    /// this method directly encodes the invariant body with `self_param` bound to
    /// `seq_index_logic(param_view, i)`.
    ///
    /// This produces a single quantifier:
    /// ```text
    /// forall i. 0 <= i < seq_len(param_view) => body[self_param/index(param_view, i)]
    /// ```
    ///
    /// This avoids the two-step E-matching chain that ay-dpll cannot currently
    /// handle in a single check-sat round.
    #[cfg(test)]
    pub(crate) fn assert_container_element_invariant_body(
        &mut self,
        param_view_name: &str,
        self_param: &str,
        inv_body: &PureExpr,
    ) -> Result<(), EncodingError> {
        if !self.register_container_element_invariant_body_spec(
            param_view_name,
            self_param,
            inv_body,
        )? {
            return Ok(());
        }

        let seq_funcs = self.ensure_seq_theory();
        let seq_len_fn = seq_funcs.seq_len.clone();
        let seq_index_fn = seq_funcs.seq_index_logic.clone();
        let seq_sort = self.get_seq_sort();

        // Get the concrete Seq-sorted view variable for the parameter
        let param_view = self.get_or_declare_var(param_view_name, seq_sort)?;

        // Create bound variable for element index
        let i_id = self.next_quantifier_var_id();
        let i = self
            .solver
            .fresh_var(&format!("elem_inv_i_{i_id}"), Sort::Int);

        // Build: seq_len(param_view)
        let len = self.solver.apply(&seq_len_fn, &[param_view]);

        // Build: 0 <= i < seq_len(param_view)
        let zero = self.solver.int_const(0);
        let i_ge_0 = self.solver.ge(i, zero);
        let i_lt_len = self.solver.lt(i, len);
        let in_bounds = self.solver.and(i_ge_0, i_lt_len);

        // Build: seq_index_logic(param_view, i) — the element value
        let elem = self.solver.apply(&seq_index_fn, &[param_view, i]);

        // Bind self_param to the element term so encode_pure(body) references it
        let old = self.insert_var(self_param.to_string(), elem);

        // Encode the invariant body directly (e.g., get_0(self) + get_1(self) == 10
        // becomes get_0(index(view, i)) + get_1(index(view, i)) == 10).
        // Increment quantifier_depth so that inner LogicFnCall applications
        // are NOT registered with the ground pool — their arguments are bound
        // variables, not ground terms. (#1965, Lane 5)
        self.quantifier_state.inc_quantifier_depth();
        let body_result = self.encode_pure(inv_body);
        self.quantifier_state.dec_quantifier_depth();

        // Restore binding
        self.restore_var(self_param, old);

        let body_term = body_result?;

        // Build: in_bounds => body[self/elem]
        let implication = self.solver.implies(in_bounds, body_term);

        // Build: forall i. in_bounds => body[self/elem]
        // Trigger on seq_index_logic(param_view, i). The needs_index_ground_terms
        // flag (set above) ensures ground UF terms appear when encode_pure
        // produces Array select terms, enabling this trigger to fire (#1575).
        let axiom = self
            .solver
            .forall_with_triggers(&[i], implication, &[&[elem]]);

        debug!(
            "  asserting inlined container element invariant for {param_view_name}: \
                 forall i. 0 <= i < len => body[{self_param}/index(view, i)]"
        );

        self.assert_term(axiom);
        Ok(())
    }

    /// Register an inlined container element invariant body for later per-index
    /// ground instantiation without asserting the global quantified forall.
    pub(crate) fn register_container_element_invariant_body_spec(
        &mut self,
        param_view_name: &str,
        self_param: &str,
        inv_body: &PureExpr,
    ) -> Result<bool, EncodingError> {
        // Trivial invariant short-circuit (#1296): body is `true`, so every
        // ground instance would be tautological.
        if matches!(inv_body, PureExpr::Bool(true)) {
            return Ok(false);
        }

        // Enable ground seq_index_logic UF term emission (#1575), same as the
        // UF-based variant above.
        self.set_needs_seq_index_ground_terms();

        let seq_sort = self.get_seq_sort();
        let param_view = self.get_or_declare_var(param_view_name, seq_sort)?;
        self.register_container_element_invariant(
            param_view,
            ContainerElementInvariantSpec::Body {
                self_param: self_param.to_string(),
                body: inv_body.clone(),
            },
        );

        Ok(true)
    }

    pub(crate) fn assert_registered_container_element_invariants_for_index(
        &mut self,
        seq_term: ay_dpll::api::Term,
        index_term: ay_dpll::api::Term,
        element_term: ay_dpll::api::Term,
    ) -> Result<(), EncodingError> {
        let seq_term = self.coerce_to_seq(seq_term);
        let Some(specs) = self
            .seq_state
            .container_element_invariants_cloned(&seq_term)
        else {
            return Ok(());
        };

        let zero = self.solver.int_const(0);
        let len = self.seq_len_term(seq_term)?;
        let index_ge_zero = self.solver.ge(index_term, zero);
        let index_lt_len = self.solver.lt(index_term, len);
        let in_bounds = self.solver.and(index_ge_zero, index_lt_len);

        self.with_assertion_phase(AssertionPhase::GroundInstance, |encoder| {
            for spec in specs {
                let body_term = match spec {
                    ContainerElementInvariantSpec::Method {
                        element_invariant_method,
                    } => {
                        let element_smt =
                            Self::bool_method_symbol(&element_invariant_method, &[Sort::Int]);
                        let element_fn = encoder.get_or_declare_logic_func(
                            &element_smt,
                            &[Sort::Int],
                            Sort::Bool,
                        );
                        encoder.solver.apply(&element_fn, &[element_term])
                    }
                    ContainerElementInvariantSpec::Body { self_param, body } => {
                        let old = encoder.insert_var(self_param.clone(), element_term);
                        encoder.quantifier_state.inc_quantifier_depth();
                        let body_result = encoder.encode_pure(&body);
                        encoder.quantifier_state.dec_quantifier_depth();
                        encoder.restore_var(&self_param, old);
                        body_result?
                    }
                };

                let instantiated = encoder.solver.implies(in_bounds, body_term);
                encoder.assert_term(instantiated);
            }
            Ok(())
        })
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use ay_dpll::api::{SolveResult, Sort, Term, TermKind};
    use trust_wp_core::formula::{BinOp, PureExpr};

    use crate::encoder::AYEncoder;

    fn assertion_has_forall(encoder: &AYEncoder, assertion: Term) -> bool {
        let solver = encoder.solver();
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
    }

    #[test]
    fn nontrivial_type_invariant_registers_ground_axiom_without_solver_forall() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        let body = PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        );

        encoder
            .register_type_invariant("Positive", "self", Sort::Int, &body)
            .expect("type invariant registration should succeed");

        assert!(
            !encoder
                .solver()
                .assertions()
                .into_iter()
                .any(|assertion| assertion_has_forall(&encoder, assertion)),
            "nontrivial type invariant registration should not assert a global forall"
        );
        assert_eq!(
            encoder.ground_pool_for_test().axiom_count(),
            1,
            "nontrivial type invariant should still register a ground-pool axiom"
        );

        let axiom = &encoder.ground_pool_for_test().axioms()[0];
        let fn_symbol = axiom.fn_symbol.clone();
        let inv_decl = axiom.func_decl.clone();
        let one = encoder.solver.int_const(1);
        let inv_one = encoder.solver.apply(&inv_decl, &[one]);
        encoder.ground_pool_for_test_mut().register(
            &fn_symbol,
            inv_one,
            vec![one],
            vec![PureExpr::Int(1)],
        );

        let count = encoder
            .assert_ground_pool_instances()
            .expect("ground instantiation should succeed");
        assert_eq!(count, 1);

        let not_inv_one = encoder.solver.not(inv_one);
        encoder.assert_term(not_inv_one);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "ground instance should constrain observed invariant applications"
        );
    }
}
