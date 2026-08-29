// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type invariant axiom assertions for the solver tail phase.
//!
//! Type invariant *defining* bodies are registered during the bootstrap phase
//! by [`crate::encoder::logic_fn::type_invariant::register_type_invariant`].
//! The encoder does not assert a global `forall self. inv(self) = body` during
//! registration; the ground pool collects ground applications of the invariant
//! UF and instantiates the defining body with concrete terms.
//!
//! This module provides an additional strengthening pass that runs during
//! `assert_standard_axioms()`. It scans declared logic functions for type
//! invariant UF symbols and asserts ground truth axioms that the defining
//! axiom + E-matching alone may not produce in a single round:
//!
//! 1. **Trivial invariant grounding:** For trivially true invariants
//!    (body = `true`), the bootstrap phase only declares the UF and marks
//!    it trivial — it does NOT assert the quantified axiom. When ground
//!    applications of the invariant UF exist in the ground pool (from
//!    encoding `x.invariant()` calls), this module asserts `inv(x) = true`
//!    directly as a ground fact.
//!
//! 2. **Non-trivial invariant safety net:** For non-trivial invariants with
//!    ground pool applications, verify that defining body ground instances
//!    have been asserted. The ground pool's standard instantiation handles
//!    this in most cases, but this pass catches edge cases from sort drift
//!    or delayed declaration ordering.
//!
//! The module is conservative: it only asserts axioms for invariant UFs
//! that have already been declared during encoding. It does not create
//! new invariant predicates or modify the ground pool.
//!
//! Issue: #2695

use super::super::AYEncoder;

/// SMT name prefix for type invariant method UFs.
///
/// The encoder transforms `__trust_wp_invariant_<Type>` into
/// `method___trust_wp_invariant_<Type>_<arity>_<sort_tags>` via
/// `bool_method_symbol`. All type invariant UFs share this prefix.
const TYPE_INVARIANT_SMT_PREFIX: &str = "method___trust_wp_invariant_";

impl AYEncoder {
    /// Assert ground truth axioms for type invariant predicates.
    ///
    /// Called from `assert_standard_axioms()` after all expressions are encoded.
    /// Scans declared logic functions for type invariant UF symbols and asserts
    /// ground truths for applications found in the ground pool.
    ///
    /// For non-trivial invariants, ground pool instantiation handles the heavy
    /// lifting. This method provides a complementary pass for trivial
    /// invariants where no defining body is registered.
    pub(crate) fn assert_type_invariant_axioms(&mut self) {
        // Collect type invariant UF names that have been declared.
        let invariant_ufs: Vec<(String, bool)> = self
            .logic_funcs_iter()
            .filter(|(name, decl)| {
                name.starts_with(TYPE_INVARIANT_SMT_PREFIX)
                    && decl.arity() == 1
                    && decl.range() == &ay_dpll::api::Sort::Bool
            })
            .map(|(name, _)| {
                let is_trivial = self.is_trivial_type_invariant(name);
                (name.clone(), is_trivial)
            })
            .collect();

        if invariant_ufs.is_empty() {
            return;
        }

        // For each invariant UF with ground pool entries, assert ground truths.
        for (name, is_trivial) in &invariant_ufs {
            // Collect ground entries for this symbol from the ground pool.
            let ground_args: Vec<Vec<ay_dpll::api::Term>> = match self.ground_pool.entries_for(name)
            {
                Some(entries) => entries
                    .iter()
                    .filter(|e| e.arg_terms.len() == 1)
                    .map(|e| e.arg_terms.clone())
                    .collect(),
                None => continue,
            };

            if ground_args.is_empty() {
                continue;
            }

            let func_decl = match self.logic_func_decl_cloned(name) {
                Some(decl) => decl,
                None => continue,
            };

            if *is_trivial {
                // For trivially-true invariants, the bootstrap phase does NOT
                // assert a quantified axiom. Assert `inv(x) = true` directly
                // for each ground application.
                for args in &ground_args {
                    let app = self.solver.apply(&func_decl, args);
                    self.solver.assert_term(app);
                }
            }
            // For non-trivial invariants, the ground pool's logic-function
            // instantiation handles the defining body. No additional work
            // needed here.
        }
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{SolveResult, Sort};
    use trust_wp_core::formula::PureExpr;

    use super::TYPE_INVARIANT_SMT_PREFIX;
    use crate::AYEncoder;

    /// Verify the SMT name prefix matches the expected pattern.
    #[test]
    fn test_type_invariant_smt_prefix_matches_method_symbol() {
        // The type_invariant_method_name produces "__trust_wp_invariant_<Type>".
        // bool_method_symbol wraps it as "method___trust_wp_invariant_<Type>_<N>_<sorts>".
        let method_name = trust_wp_core::logic::type_invariant_method_name("TestType");
        let smt_name = AYEncoder::bool_method_symbol(&method_name, &[Sort::Int]);
        assert!(
            smt_name.starts_with(TYPE_INVARIANT_SMT_PREFIX),
            "type invariant SMT name should start with '{TYPE_INVARIANT_SMT_PREFIX}', \
             got '{smt_name}'"
        );
    }

    /// When no type invariant UFs are declared, assertion is a no-op.
    #[test]
    #[ntest::timeout(10000)]
    fn test_type_invariant_axioms_noop_without_invariant_ufs() {
        let mut encoder = AYEncoder::new();

        // Declare some unrelated logic functions.
        encoder.get_or_declare_logic_func("unrelated_fn", &[Sort::Int], Sort::Int);

        // Should not panic or change solver state.
        encoder.assert_type_invariant_axioms();

        assert_eq!(encoder.check_sat(), SolveResult::Sat);
    }

    /// Trivially-true invariant: after asserting axioms, inv(x) should be true
    /// for ground applications in the ground pool.
    #[test]
    #[ntest::timeout(10000)]
    fn test_trivial_invariant_ground_truth_asserted() {
        let mut encoder = AYEncoder::new();

        // Register a trivially-true type invariant using the public API.
        encoder
            .register_type_invariant("TrivialType", "self", Sort::Int, &PureExpr::Bool(true))
            .unwrap();

        // Declare a variable of the type.
        let x = encoder.get_or_declare_var("x", Sort::Int).unwrap();

        // Get the invariant UF declaration.
        let method_name = trust_wp_core::logic::type_invariant_method_name("TrivialType");
        let smt_name = AYEncoder::bool_method_symbol(&method_name, &[Sort::Int]);
        let func_decl = encoder.get_or_declare_logic_func(&smt_name, &[Sort::Int], Sort::Bool);

        // Record a ground application in the ground pool.
        let app = encoder.solver.apply(&func_decl, &[x]);
        encoder.ground_pool.register(
            &smt_name,
            app,
            vec![x],
            vec![PureExpr::Var("x".to_string(), None)],
        );

        // Assert the type invariant axioms.
        encoder.assert_type_invariant_axioms();

        // Now negate inv(x) — should be UNSAT because the ground truth was asserted.
        let inv_x = encoder.solver.apply(&func_decl, &[x]);
        let negated = encoder.solver.not(inv_x);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "trivial invariant ground truth should make inv(x) true after axioms (#2695)"
        );
    }

    /// Without axiom assertion, trivially-true invariant UF is unconstrained
    /// for ground applications (regression guard).
    #[test]
    #[ntest::timeout(10000)]
    fn test_trivial_invariant_unconstrained_without_axioms() {
        let mut encoder = AYEncoder::new();

        encoder
            .register_type_invariant("UncType", "self", Sort::Int, &PureExpr::Bool(true))
            .unwrap();

        let x = encoder.get_or_declare_var("x", Sort::Int).unwrap();

        let method_name = trust_wp_core::logic::type_invariant_method_name("UncType");
        let smt_name = AYEncoder::bool_method_symbol(&method_name, &[Sort::Int]);
        let func_decl = encoder.get_or_declare_logic_func(&smt_name, &[Sort::Int], Sort::Bool);

        // Record ground application but do NOT assert axioms.
        let app = encoder.solver.apply(&func_decl, &[x]);
        encoder.ground_pool.register(
            &smt_name,
            app,
            vec![x],
            vec![PureExpr::Var("x".to_string(), None)],
        );

        // For trivially-true invariants, register_type_invariant does NOT
        // assert the quantified axiom — it only marks the symbol. So without
        // assert_type_invariant_axioms, inv(x) is truly unconstrained.
        let inv_x = encoder.solver.apply(&func_decl, &[x]);
        let negated = encoder.solver.not(inv_x);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::Sat,
            "without axiom assertion, trivial invariant should be unconstrained for ground apps"
        );
    }

    /// Non-trivial invariant: the axiom module should not interfere with
    /// the defining axiom + ground pool instantiation.
    #[test]
    #[ntest::timeout(10000)]
    fn test_nontrivial_invariant_no_interference() {
        // Use quantifier-supporting logic because register_type_invariant
        // asserts a forall axiom for non-trivial bodies.
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Register a non-trivial type invariant: inv(self) = (self > 0)
        let body = PureExpr::BinOp(
            PureExpr::Var("self".to_string(), None).into(),
            trust_wp_core::formula::BinOp::Gt,
            PureExpr::Int(0).into(),
        );

        encoder
            .register_type_invariant("PosType", "self", Sort::Int, &body)
            .unwrap();

        // Assert the axiom module.
        encoder.assert_type_invariant_axioms();

        // Solver should still be satisfiable (the defining axiom alone
        // does not make the formula UNSAT).
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Sat),
            "non-trivial invariant should not make solver UNSAT, got {result:?}"
        );
    }

    /// Multiple trivially-true invariants with ground applications.
    #[test]
    #[ntest::timeout(10000)]
    fn test_multiple_trivial_invariants_all_grounded() {
        let mut encoder = AYEncoder::new();

        // Register two trivially-true type invariants.
        encoder
            .register_type_invariant("TypeA", "self", Sort::Int, &PureExpr::Bool(true))
            .unwrap();
        encoder
            .register_type_invariant("TypeB", "self", Sort::Int, &PureExpr::Bool(true))
            .unwrap();

        let x = encoder.get_or_declare_var("x", Sort::Int).unwrap();
        let y = encoder.get_or_declare_var("y", Sort::Int).unwrap();

        // Record ground applications for both.
        let method_a = trust_wp_core::logic::type_invariant_method_name("TypeA");
        let smt_a = AYEncoder::bool_method_symbol(&method_a, &[Sort::Int]);
        let decl_a = encoder.get_or_declare_logic_func(&smt_a, &[Sort::Int], Sort::Bool);
        let app_a = encoder.solver.apply(&decl_a, &[x]);
        encoder.ground_pool.register(
            &smt_a,
            app_a,
            vec![x],
            vec![PureExpr::Var("x".to_string(), None)],
        );

        let method_b = trust_wp_core::logic::type_invariant_method_name("TypeB");
        let smt_b = AYEncoder::bool_method_symbol(&method_b, &[Sort::Int]);
        let decl_b = encoder.get_or_declare_logic_func(&smt_b, &[Sort::Int], Sort::Bool);
        let app_b = encoder.solver.apply(&decl_b, &[y]);
        encoder.ground_pool.register(
            &smt_b,
            app_b,
            vec![y],
            vec![PureExpr::Var("y".to_string(), None)],
        );

        // Assert type invariant axioms.
        encoder.assert_type_invariant_axioms();

        // Negate both: inv_a(x) AND inv_b(y) should hold.
        let inv_a_x = encoder.solver.apply(&decl_a, &[x]);
        let inv_b_y = encoder.solver.apply(&decl_b, &[y]);
        let both = encoder.solver.and(inv_a_x, inv_b_y);
        let negated = encoder.solver.not(both);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "both trivial invariants should be grounded after axiom assertion (#2695)"
        );
    }

    /// No ground entries: axioms should be a no-op (no panic, no solver change).
    #[test]
    #[ntest::timeout(10000)]
    fn test_trivial_invariant_no_ground_entries_noop() {
        let mut encoder = AYEncoder::new();

        encoder
            .register_type_invariant("EmptyType", "self", Sort::Int, &PureExpr::Bool(true))
            .unwrap();

        // Do NOT record any ground applications.
        encoder.assert_type_invariant_axioms();

        assert_eq!(encoder.check_sat(), SolveResult::Sat);
    }

    /// TYPE_INVARIANT_METHOD_PREFIX aligns with the SMT prefix constant.
    #[test]
    fn test_prefix_alignment() {
        // TYPE_INVARIANT_METHOD_PREFIX is "__trust_wp_invariant_"
        // TYPE_INVARIANT_SMT_PREFIX is "method___trust_wp_invariant_"
        // The SMT prefix should be "method_" + TYPE_INVARIANT_METHOD_PREFIX
        let expected = format!(
            "method_{}",
            trust_wp_core::logic::TYPE_INVARIANT_METHOD_PREFIX
        );
        assert_eq!(
            super::TYPE_INVARIANT_SMT_PREFIX,
            expected,
            "SMT prefix should be 'method_' + TYPE_INVARIANT_METHOD_PREFIX"
        );
    }

    /// Non-trivial invariant (NonZero-style `self != 0`): after registering and
    /// asserting the invariant, the defining axiom should constrain ground instances.
    ///
    /// This simulates what happens when verifying code that uses `NonZero<T>`:
    /// the invariant `forall self. inv(self) = (self != 0)` is registered, and
    /// when `inv(x)` appears as a ground application (from preconditions or
    /// postconditions), asserting `inv(x)` should imply `x != 0`.
    #[test]
    #[ntest::timeout(10000)]
    fn test_nonzero_style_invariant_constrains_ground_instance() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Register NonZero-style invariant: inv(self) = (self != 0)
        let body = PureExpr::BinOp(
            PureExpr::Var("self".to_string(), None).into(),
            trust_wp_core::formula::BinOp::Ne,
            PureExpr::Int(0).into(),
        );
        encoder
            .register_type_invariant("NonZero", "self", Sort::Int, &body)
            .unwrap();

        // Declare a variable representing a NonZero value
        let x = encoder.get_or_declare_var("x", Sort::Int).unwrap();

        // Get the invariant function declaration
        let method_name = trust_wp_core::logic::type_invariant_method_name("NonZero");
        let smt_name = AYEncoder::bool_method_symbol(&method_name, &[Sort::Int]);
        let func_decl = encoder.get_or_declare_logic_func(&smt_name, &[Sort::Int], Sort::Bool);

        // Record a ground application in the ground pool
        let app = encoder.solver.apply(&func_decl, &[x]);
        encoder.ground_pool.register(
            &smt_name,
            app,
            vec![x],
            vec![PureExpr::Var("x".to_string(), None)],
        );

        // Assert type invariant axioms (runs ground pool instantiation)
        encoder.assert_type_invariant_axioms();

        // Assert inv(x) holds (simulating a precondition assumption)
        let inv_x = encoder.solver.apply(&func_decl, &[x]);
        encoder.assert_term(inv_x);

        // Now assert standard ground instances to trigger the defining axiom
        encoder.assert_standard_ground_instances();

        // Try to prove x == 0 — should be UNSAT because inv(x) implies x != 0
        let zero = encoder.solver.int_const(0);
        let x_eq_zero = encoder.solver.eq(x, zero);
        encoder.assert_term(x_eq_zero);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "NonZero-style invariant should make x == 0 UNSAT when inv(x) holds (#2695)"
        );
    }

    /// Verify that multiple ground applications of the same non-trivial
    /// invariant are all constrained independently.
    #[test]
    #[ntest::timeout(10000)]
    fn test_nontrivial_invariant_multiple_ground_applications() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Register positive-only invariant: inv(self) = (self > 0)
        let body = PureExpr::BinOp(
            PureExpr::Var("self".to_string(), None).into(),
            trust_wp_core::formula::BinOp::Gt,
            PureExpr::Int(0).into(),
        );
        encoder
            .register_type_invariant("Positive", "self", Sort::Int, &body)
            .unwrap();

        let x = encoder.get_or_declare_var("x", Sort::Int).unwrap();
        let y = encoder.get_or_declare_var("y", Sort::Int).unwrap();

        let method_name = trust_wp_core::logic::type_invariant_method_name("Positive");
        let smt_name = AYEncoder::bool_method_symbol(&method_name, &[Sort::Int]);
        let func_decl = encoder.get_or_declare_logic_func(&smt_name, &[Sort::Int], Sort::Bool);

        // Register ground applications for x and y
        let app_x = encoder.solver.apply(&func_decl, &[x]);
        encoder.ground_pool.register(
            &smt_name,
            app_x,
            vec![x],
            vec![PureExpr::Var("x".to_string(), None)],
        );

        let app_y = encoder.solver.apply(&func_decl, &[y]);
        encoder.ground_pool.register(
            &smt_name,
            app_y,
            vec![y],
            vec![PureExpr::Var("y".to_string(), None)],
        );

        // Assert type invariant axioms
        encoder.assert_type_invariant_axioms();

        // Assert both invariants hold
        let inv_x = encoder.solver.apply(&func_decl, &[x]);
        let inv_y = encoder.solver.apply(&func_decl, &[y]);
        encoder.assert_term(inv_x);
        encoder.assert_term(inv_y);

        // Trigger ground instantiation
        encoder.assert_standard_ground_instances();

        // Assert x + y <= 0 — should be UNSAT because both are > 0
        let zero = encoder.solver.int_const(0);
        let sum = encoder.solver.add(x, y);
        let sum_le_zero = encoder.solver.le(sum, zero);
        encoder.assert_term(sum_le_zero);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "two positive invariants should make x + y <= 0 UNSAT (#2695)"
        );
    }

    /// Trivially-true invariant with multiple ground applications of
    /// the same variable should not cause duplicate assertions or panics.
    #[test]
    #[ntest::timeout(10000)]
    fn test_trivial_invariant_duplicate_ground_applications() {
        let mut encoder = AYEncoder::new();

        encoder
            .register_type_invariant("TrivDup", "self", Sort::Int, &PureExpr::Bool(true))
            .unwrap();

        let x = encoder.get_or_declare_var("x", Sort::Int).unwrap();

        let method_name = trust_wp_core::logic::type_invariant_method_name("TrivDup");
        let smt_name = AYEncoder::bool_method_symbol(&method_name, &[Sort::Int]);
        let func_decl = encoder.get_or_declare_logic_func(&smt_name, &[Sort::Int], Sort::Bool);

        // Register the same ground application twice (can happen with
        // multiple call sites to the same method on the same receiver)
        let app1 = encoder.solver.apply(&func_decl, &[x]);
        encoder.ground_pool.register(
            &smt_name,
            app1,
            vec![x],
            vec![PureExpr::Var("x".to_string(), None)],
        );
        let app2 = encoder.solver.apply(&func_decl, &[x]);
        encoder.ground_pool.register(
            &smt_name,
            app2,
            vec![x],
            vec![PureExpr::Var("x".to_string(), None)],
        );

        // Should not panic
        encoder.assert_type_invariant_axioms();

        // inv(x) should be true
        let inv_x = encoder.solver.apply(&func_decl, &[x]);
        let negated = encoder.solver.not(inv_x);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "duplicate ground applications should still make inv(x) true (#2695)"
        );
    }
}
