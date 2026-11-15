// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trait postcondition axioms for derived trait implementations.
//!
//! When Creusot's `#[derive(Default)]` generates a postcondition like:
//! ```text
//! ensures: match result {
//!     Tuple(x0, x1) => Default::default.postcondition((), x0)
//!                    && Default::default.postcondition((), x1),
//!     _ => false
//! }
//! ```
//! the `.postcondition()` method is encoded as an uninterpreted Bool function
//! `closure_postcondition_N_sorts(receiver, args...)`. Without axioms, the
//! solver cannot determine that `Default::default.postcondition((), 0)` is
//! true for i32/i64 fields, causing the derived impl to fail verification.
//!
//! This module asserts ground truth axioms connecting the abstract
//! `.postcondition()` predicate to known concrete specs. Specifically:
//!
//! - `Default::default.postcondition((), 0) = true` for integer types
//! - `Default::default.postcondition((), false) = true` for bool
//!
//! These axioms fire only when:
//! 1. A `closure_postcondition_*` UF has been declared during encoding
//! 2. The `Default::default` logic function has also been declared
//! 3. The domain sorts are compatible (receiver=Int, unit arg, value=Int)
//!
//! Issue: #2670

use super::super::AYEncoder;

/// SMT name for `core::default::Default::default` logic function.
///
/// Computed by `logic_fn_smt_name("core::default::Default::default")`.
const DEFAULT_DEFAULT_SMT_NAME: &str = "logic_core_P__P_default_P__P_Default_P__P_default";

/// Rust path for the `Default::default` function, used as the variable name
/// when the function appears as a receiver in `.postcondition()` calls.
///
/// In the expression `Default::default.postcondition((), x0)`, the receiver
/// `Default::default` is encoded as `PureExpr::Var("core::default::Default::default", None)`
/// which becomes a AY variable with this name. The axiom must use the SAME
/// variable to ensure congruence closure connects the ground instance to the
/// actual postcondition application. (#2670)
const DEFAULT_DEFAULT_RUST_PATH: &str = "core::default::Default::default";

impl AYEncoder {
    /// Assert ground truth axioms for trait postcondition predicates.
    ///
    /// Called from `assert_standard_axioms()` after all expressions are encoded.
    /// Only asserts axioms when both the postcondition predicate and the trait
    /// method logic function have been declared.
    pub(crate) fn assert_trait_postcondition_axioms(&mut self) {
        self.assert_default_postcondition_axioms();
    }

    /// Assert `Default::default.postcondition((), v) <==> v == default_value`
    /// for primitive types whose default values are known at compile time.
    ///
    /// The postcondition predicate is encoded as:
    /// `closure_postcondition_N_sorts(default_fn_term, unit_term, value_term)`
    ///
    /// Previous approach (broken): `forall u. postcond(fn, u, 0) = true` used
    /// the concrete default value in the trigger pattern, so the axiom only
    /// fired when the value argument was literally `0`. In derived Default impls,
    /// the value is a datatype field accessor (e.g., `tuple_field_0(result)`)
    /// which evaluates to `0` but doesn't syntactically match the trigger.
    ///
    /// Fixed approach: universally quantify BOTH the unit arg AND the value arg,
    /// using a biconditional: `forall u v. postcond(fn, u, v) = (v == default)`.
    /// The trigger `[postcond(fn, u, v)]` matches any postcondition application
    /// regardless of the value argument's syntactic form, allowing the solver to
    /// simplify `postcond(fn, unit, field_accessor(result)) = (field_accessor(result) == 0)`.
    fn assert_default_postcondition_axioms(&mut self) {
        // Generated derive postconditions encode Default::default as a receiver
        // variable. Some paths do not declare a separate nullary logic function
        // for that receiver, so the variable alone must be enough to emit the
        // postcondition axioms. (#2670, #3764)
        let default_var_term = self.var_term(DEFAULT_DEFAULT_RUST_PATH);

        // Fallback for tests and encoding paths that do declare Default::default
        // as a logic function. Production declarations can carry placeholder
        // suffixes like
        // `logic_core_P__P_default_P__P_Default_P__P_default__placeholder_nullary__ret_i`.
        let default_fn_decl = self
            .logic_func_decl_cloned(DEFAULT_DEFAULT_SMT_NAME)
            .or_else(|| {
                // Search for placeholder variants with the base name prefix
                let prefix = format!("{DEFAULT_DEFAULT_SMT_NAME}__placeholder_");
                self.logic_funcs_iter()
                    .find(|(name, _)| name.starts_with(&prefix))
                    .map(|(_, decl)| decl.clone())
            });
        if default_var_term.is_none() && default_fn_decl.is_none() {
            return; // Default::default not used in this verification
        }

        // Find all closure_postcondition_* declarations that could match
        // the Default::default.postcondition((), value) pattern.
        // Expected signature: (receiver: Int, unit_arg: ?, value: Int) -> Bool
        // The closure spec encodes `.postcondition(args, result)` as a single
        // predicate with receiver as first param, then the method arguments
        // flattened. For `.postcondition((), x0)` this produces 3 params:
        // [receiver, unit_arg, x0].
        let postcond_decls: Vec<_> = self
            .logic_funcs_iter()
            .filter(|(name, decl)| {
                name.starts_with("closure_postcondition_")
                    && decl.arity() == 3
                    && decl.range() == &ay_dpll::api::Sort::Bool
            })
            .map(|(name, decl)| (name.clone(), decl.clone()))
            .collect();

        if postcond_decls.is_empty() {
            return;
        }

        if default_fn_decl
            .as_ref()
            .is_some_and(|decl| !decl.domain().is_empty())
        {
            // Unexpected arity — bail out.
            return;
        }

        // Build the default_fn term — this is the receiver for the postcondition.
        //
        // In the postcondition expression `Default::default.postcondition((), x0)`,
        // the receiver `Default::default` is encoded as a AY variable via
        // `encode_var("core::default::Default::default", ...)`, NOT as a UF
        // application of the nullary logic function. To ensure the axiom's
        // receiver term matches the actual postcondition application, we MUST
        // use the same variable.
        //
        // Primary path (production): use the variable from the var store, which
        // is the same term created during `encode_closure_spec_method` for the
        // receiver.
        //
        // Fallback (unit tests): tests declare the function under the raw SMT
        // name and manually build `apply(decl, [])` as the receiver. In this case
        // the var store has no entry for the Rust path, so we use the UF
        // application to match the test's postcondition setup. (#2670)
        let default_fn_term = if let Some(var_term) = default_var_term {
            // Production path: the receiver variable exists in the var store.
            var_term
        } else if let Some(default_fn_decl) = &default_fn_decl {
            // Fallback: use the UF application (for unit tests).
            self.solver.apply(&default_fn_decl, &[])
        } else {
            return;
        };

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        // Known default values per sort.
        let zero = self.solver.int_const(0);
        let false_term = self.solver.bool_const(false);

        // Use the canonical `__trust_wp_unit` constant for ground instances.
        // This MUST match the constant used in `assert_unit_singleton_axioms`
        // and `encode_logic_fn_call_impl`, which constrain all unit-sorted
        // variables to equal `__trust_wp_unit` via the unit singleton axiom.
        // Previously used `__trust_wp_unit_postcond` which was a separate constant
        // with no equality constraint connecting it to `__trust_wp_unit`, causing
        // congruence closure to miss the connection between ground instances and
        // actual postcondition applications (which use `__trust_wp_unit` as the
        // unit argument). This caused `<Tuple as Default>::default` to FAIL
        // verification because the solver couldn't connect the ground axiom
        // `postcond(fn, __trust_wp_unit_postcond, 0) = true` to the encoded
        // postcondition `postcond(fn, __trust_wp_unit, tuple_0(result))`. (#2670)
        let unit_ground = self
            .solver
            .declare_const("__trust_wp_unit", unit_sort.clone());

        for (_name, postcond_decl) in &postcond_decls {
            let domain = postcond_decl.domain();

            // The arity()==3 filter above guarantees these two positions, but
            // that is the filter's invariant, not this loop's — `get` proves it
            // here and skips the declaration the same way a sort mismatch does.
            let (Some(receiver_sort), Some(unit_arg_sort)) = (domain.first(), domain.get(1)) else {
                continue;
            };

            // Check if receiver sort matches the default_fn term's sort.
            let default_fn_sort = self.solver.get_sort(default_fn_term);
            if *receiver_sort != default_fn_sort {
                continue;
            }

            // Check if the second arg is Unit-sorted (represents the `()` input).
            if *unit_arg_sort != unit_sort {
                continue;
            }

            // Universally quantify over BOTH the unit argument and the value
            // argument. The biconditional connects the abstract postcondition
            // predicate to the concrete default value:
            //   forall u : Unit, v : <sort>.
            //     postcondition(default_fn, u, v) = (v == <default_value>)
            //
            // Trigger: [postcondition(default_fn, u, v)] — matches any
            // postcondition application with this receiver, regardless of
            // the syntactic form of the value argument.
            let unit_var = self.solver.fresh_var("__u_postcond", unit_sort.clone());

            // Int-valued fields: default is 0.
            if domain[2] == ay_dpll::api::Sort::Int {
                let val_var = self
                    .solver
                    .fresh_var("__v_postcond", ay_dpll::api::Sort::Int);
                let app = self
                    .solver
                    .apply(postcond_decl, &[default_fn_term, unit_var, val_var]);
                let val_eq_zero = self.eq_term(val_var, zero);
                let biconditional = self.eq_term(app, val_eq_zero);
                let axiom = self.solver.forall_with_triggers(
                    &[unit_var, val_var],
                    biconditional,
                    &[&[app]],
                );
                self.solver.assert_term(axiom);

                // Eager ground instance: directly assert postcond(default_fn, unit, 0) = true.
                // ay-dpll's single-round E-matching may not fire the quantified axiom when
                // the value argument is a datatype field accessor (e.g., tuple_0(result)).
                // The ground instance gives the solver a concrete fact it can use directly
                // in congruence closure without needing trigger matching. (#2675)
                //
                // Uses the canonical `__trust_wp_unit` constant (not a separate constant)
                // so that congruence closure connects this ground fact to actual
                // postcondition applications in the verification context. (#2670)
                let ground_app = self
                    .solver
                    .apply(postcond_decl, &[default_fn_term, unit_ground, zero]);
                self.solver.assert_term(ground_app);
            }

            // Bool-valued fields: default is false.
            if domain[2] == ay_dpll::api::Sort::Bool {
                let val_var = self
                    .solver
                    .fresh_var("__v_postcond_b", ay_dpll::api::Sort::Bool);
                let app = self
                    .solver
                    .apply(postcond_decl, &[default_fn_term, unit_var, val_var]);
                let val_eq_false = self.eq_term(val_var, false_term);
                let biconditional = self.eq_term(app, val_eq_false);
                let axiom = self.solver.forall_with_triggers(
                    &[unit_var, val_var],
                    biconditional,
                    &[&[app]],
                );
                self.solver.assert_term(axiom);

                // Eager ground instance for Bool: postcond(default_fn, unit, false) = true.
                // Same reasoning as Int case above. (#2675)
                // Uses canonical `__trust_wp_unit` for congruence closure. (#2670)
                let ground_app = self
                    .solver
                    .apply(postcond_decl, &[default_fn_term, unit_ground, false_term]);
                self.solver.assert_term(ground_app);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{SolveResult, Sort};

    use super::DEFAULT_DEFAULT_SMT_NAME;
    use crate::AYEncoder;

    /// Helper: declare `Default::default` as a nullary logic function returning `ret_sort`.
    fn declare_default_fn(encoder: &mut AYEncoder, ret_sort: Sort) {
        encoder.get_or_declare_logic_func(DEFAULT_DEFAULT_SMT_NAME, &[], ret_sort);
    }

    /// Helper: declare a `closure_postcondition_*` predicate with the given
    /// domain sorts and Bool range, and register it in the logic-func registry.
    fn declare_postcondition_predicate(encoder: &mut AYEncoder, name: &str, domain: &[Sort]) {
        encoder.get_or_declare_logic_func(name, domain, Sort::Bool);
    }

    /// Verify the SMT name constant matches the transformation from `logic_fn_smt_name`.
    #[test]
    fn test_default_smt_name_matches_transformation() {
        let computed = trust_wp_core::logic::logic_fn_smt_name("core::default::Default::default");
        assert_eq!(
            computed, DEFAULT_DEFAULT_SMT_NAME,
            "DEFAULT_DEFAULT_SMT_NAME must match logic_fn_smt_name output"
        );
    }

    /// When no `Default::default` function is declared, axiom assertion is a no-op.
    #[test]
    #[ntest::timeout(10000)]
    fn test_trait_postcondition_noop_without_default_fn() {
        let mut encoder = AYEncoder::new();

        // Only declare a postcondition predicate, no Default::default.
        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();
        declare_postcondition_predicate(
            &mut encoder,
            "closure_postcondition_1_i_u_i",
            &[Sort::Int, unit_sort, Sort::Int],
        );

        // Should not panic or change solver state.
        encoder.assert_trait_postcondition_axioms();

        // Solver should still be satisfiable (no assertions made).
        assert_eq!(encoder.check_sat(), SolveResult::Sat);
    }

    /// When no postcondition predicates are declared, axiom assertion is a no-op.
    #[test]
    #[ntest::timeout(10000)]
    fn test_trait_postcondition_noop_without_postcondition_predicate() {
        let mut encoder = AYEncoder::new();

        // Only declare Default::default, no postcondition predicates.
        declare_default_fn(&mut encoder, Sort::Int);

        // Should not panic.
        encoder.assert_trait_postcondition_axioms();

        assert_eq!(encoder.check_sat(), SolveResult::Sat);
    }

    /// After asserting axioms, `postcondition(default_fn, unit, 0)` should be true.
    /// Negating it should produce UNSAT.
    #[test]
    #[ntest::timeout(10000)]
    fn test_default_postcondition_int_zero_is_true() {
        let mut encoder = AYEncoder::new();

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        // Declare Default::default as nullary -> Int.
        let default_decl =
            encoder.get_or_declare_logic_func(DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);

        // Declare closure_postcondition_test: (Int, Unit, Int) -> Bool.
        let postcond_decl = encoder.get_or_declare_logic_func(
            "closure_postcondition_test_i_u_i",
            &[Sort::Int, unit_sort.clone(), Sort::Int],
            Sort::Bool,
        );

        // Assert the axioms.
        encoder.assert_trait_postcondition_axioms();

        // Build the same terms the axiom would produce:
        let default_fn_term = encoder.solver.apply(&default_decl, &[]);
        let unit_term = encoder.solver.declare_const("__test_unit", unit_sort);
        let zero = encoder.solver.int_const(0);
        let app = encoder
            .solver
            .apply(&postcond_decl, &[default_fn_term, unit_term, zero]);

        // Negate: postcondition(default_fn, unit, 0) = false
        let negated = encoder.solver.not(app);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "postcondition(default_fn, unit, 0) should be true after axioms (#2670)"
        );
    }

    /// After asserting axioms, `postcondition(default_fn, unit, false)` should
    /// be true for Bool-valued fields.
    #[test]
    #[ntest::timeout(10000)]
    fn test_default_postcondition_bool_false_is_true() {
        let mut encoder = AYEncoder::new();

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        // Declare Default::default as nullary -> Int.
        // (The receiver sort for the postcondition matches the default fn's range.)
        let default_decl =
            encoder.get_or_declare_logic_func(DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);

        // Declare closure_postcondition for Bool field: (Int, Unit, Bool) -> Bool.
        let postcond_decl = encoder.get_or_declare_logic_func(
            "closure_postcondition_test_i_u_b",
            &[Sort::Int, unit_sort.clone(), Sort::Bool],
            Sort::Bool,
        );

        encoder.assert_trait_postcondition_axioms();

        let default_fn_term = encoder.solver.apply(&default_decl, &[]);
        let unit_term = encoder.solver.declare_const("__test_unit_b", unit_sort);
        let false_term = encoder.solver.bool_const(false);
        let app = encoder
            .solver
            .apply(&postcond_decl, &[default_fn_term, unit_term, false_term]);

        let negated = encoder.solver.not(app);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "postcondition(default_fn, unit, false) should be true after axioms (#2670)"
        );
    }

    /// Without axioms, the postcondition predicate is unconstrained,
    /// so negating it should be satisfiable. Regression guard.
    #[test]
    #[ntest::timeout(10000)]
    fn test_without_axioms_postcondition_unconstrained() {
        let mut encoder = AYEncoder::new();

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        let default_decl =
            encoder.get_or_declare_logic_func(DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);

        let postcond_decl = encoder.get_or_declare_logic_func(
            "closure_postcondition_test_unconstrained",
            &[Sort::Int, unit_sort.clone(), Sort::Int],
            Sort::Bool,
        );

        // Do NOT call assert_trait_postcondition_axioms.

        let default_fn_term = encoder.solver.apply(&default_decl, &[]);
        let unit_term = encoder.solver.declare_const("__test_unit_unc", unit_sort);
        let zero = encoder.solver.int_const(0);
        let app = encoder
            .solver
            .apply(&postcond_decl, &[default_fn_term, unit_term, zero]);

        // Negate: should be SAT because the predicate is unconstrained.
        let negated = encoder.solver.not(app);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::Sat,
            "without axioms, postcondition is unconstrained and should be satisfiable"
        );
    }

    /// A postcondition predicate with wrong arity (2 instead of 3) should be
    /// ignored by the axiom assertion.
    #[test]
    #[ntest::timeout(10000)]
    fn test_wrong_arity_postcondition_ignored() {
        let mut encoder = AYEncoder::new();

        declare_default_fn(&mut encoder, Sort::Int);

        // Declare a postcondition with arity 2 (wrong — should be 3).
        encoder.get_or_declare_logic_func(
            "closure_postcondition_wrong_arity",
            &[Sort::Int, Sort::Int],
            Sort::Bool,
        );

        // Should not panic and should not assert any axioms.
        encoder.assert_trait_postcondition_axioms();

        assert_eq!(encoder.check_sat(), SolveResult::Sat);
    }

    /// A postcondition predicate with mismatched receiver sort should be skipped.
    #[test]
    #[ntest::timeout(10000)]
    fn test_mismatched_receiver_sort_skipped() {
        let mut encoder = AYEncoder::new();

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        // Default::default returns Int.
        declare_default_fn(&mut encoder, Sort::Int);

        // Postcondition has Bool as receiver sort (mismatch with Int).
        let postcond_decl = encoder.get_or_declare_logic_func(
            "closure_postcondition_mismatch",
            &[Sort::Bool, unit_sort.clone(), Sort::Int],
            Sort::Bool,
        );

        encoder.assert_trait_postcondition_axioms();

        // Build terms and negate — should be SAT because no axiom was asserted.
        // (default_fn_term not needed — the postcondition uses Bool receiver.)

        // The postcondition uses Bool receiver, so we need a Bool-sorted term.
        let bool_receiver = encoder.solver.bool_const(true);
        let unit_term = encoder.solver.declare_const("__test_unit_mm", unit_sort);
        let zero = encoder.solver.int_const(0);
        let app = encoder
            .solver
            .apply(&postcond_decl, &[bool_receiver, unit_term, zero]);
        let negated = encoder.solver.not(app);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::Sat,
            "mismatched receiver sort should leave postcondition unconstrained"
        );
    }

    /// Simulates the derived Default pattern for `Tuple(i32, i64)` where the
    /// postcondition value argument is a datatype field accessor, not the
    /// literal `0`. This is the exact pattern that was broken before the
    /// biconditional axiom fix: the trigger only matched literal `0`, not
    /// `tuple_field_0(result)` which evaluates to `0`.
    ///
    /// Scenario:
    ///   declare-datatype Tuple (mk_tuple (tuple_0 Int) (tuple_1 Int))
    ///   assert: result = mk_tuple(0, 0)
    ///   assert: NOT(postcond(default_fn, unit, tuple_0(result))
    ///              AND postcond(default_fn, unit, tuple_1(result)))
    /// Expected: UNSAT (both field accessors evaluate to 0, postcond should be true)
    #[test]
    #[ntest::timeout(10000)]
    fn test_default_postcondition_datatype_field_accessor() {
        let mut encoder = AYEncoder::new();

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        // Declare Default::default as nullary -> Int.
        let default_decl =
            encoder.get_or_declare_logic_func(DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);

        // Declare closure_postcondition: (Int, Unit, Int) -> Bool.
        let postcond_decl = encoder.get_or_declare_logic_func(
            "closure_postcondition_dt_i_u_i",
            &[Sort::Int, unit_sort.clone(), Sort::Int],
            Sort::Bool,
        );

        encoder.assert_trait_postcondition_axioms();

        // Declare a Tuple datatype with two Int fields.
        let tuple_dt = ay_dpll::api::DatatypeSort {
            name: "Tuple".to_string(),
            constructors: vec![ay_dpll::api::DatatypeConstructor {
                name: "mk_tuple".to_string(),
                fields: vec![
                    ay_dpll::api::DatatypeField {
                        name: "tuple_0".to_string(),
                        sort: Sort::Int,
                    },
                    ay_dpll::api::DatatypeField {
                        name: "tuple_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        };
        encoder.solver.declare_datatype(&tuple_dt);

        // Build: result = mk_tuple(0, 0)
        let zero = encoder.solver.int_const(0);
        let tuple_sort = Sort::Datatype(tuple_dt.clone());
        let result = encoder.solver.declare_const("__result", tuple_sort);
        let mk_tuple_0_0 =
            encoder
                .solver
                .datatype_constructor(&tuple_dt, "mk_tuple", &[zero, zero]);
        let result_eq = encoder.solver.eq(result, mk_tuple_0_0);
        encoder.assert_term(result_eq);

        // Build field accessors: tuple_0(result) and tuple_1(result)
        let field0 = encoder
            .solver
            .datatype_selector("tuple_0", result, Sort::Int);
        let field1 = encoder
            .solver
            .datatype_selector("tuple_1", result, Sort::Int);

        // Build postcondition applications with field accessors as value args.
        let default_fn_term = encoder.solver.apply(&default_decl, &[]);
        let unit_term = encoder.solver.declare_const("__test_unit_dt", unit_sort);
        let postcond_field0 = encoder
            .solver
            .apply(&postcond_decl, &[default_fn_term, unit_term, field0]);
        let postcond_field1 = encoder
            .solver
            .apply(&postcond_decl, &[default_fn_term, unit_term, field1]);

        // Negate: NOT(postcond(fn, unit, tuple_0(result)) AND postcond(fn, unit, tuple_1(result)))
        let both = encoder.solver.and(postcond_field0, postcond_field1);
        let negated = encoder.solver.not(both);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "postcondition should fire for datatype field accessors evaluating to 0 (#2670)"
        );
    }

    /// Regression test: the canonical `__trust_wp_unit` constant must be used
    /// in the ground instance so that congruence closure connects the ground
    /// axiom to actual postcondition applications that also use `__trust_wp_unit`.
    ///
    /// This test simulates the exact pattern that caused `<Tuple as Default>::default`
    /// to FAIL: the postcondition application uses `__trust_wp_unit` as the unit
    /// argument, and the ground instance must use the SAME constant. Previously
    /// the ground instance used `__trust_wp_unit_postcond`, a separate constant with
    /// no equality constraint to `__trust_wp_unit`, causing the solver to assign
    /// `postcond(fn, __trust_wp_unit, 0) = false` as a counterexample.
    ///
    /// Scenario:
    ///   postcond application: postcond(default_fn, __trust_wp_unit, 0)
    ///   ground instance:      postcond(default_fn, __trust_wp_unit, 0) = true
    ///   negate:               NOT(postcond(default_fn, __trust_wp_unit, 0))
    /// Expected: UNSAT (ground instance directly contradicts negation)
    #[test]
    #[ntest::timeout(10000)]
    fn test_canonical_unit_constant_ground_instance_connects() {
        let mut encoder = AYEncoder::new();

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        // Declare Default::default as nullary -> Int.
        let default_decl =
            encoder.get_or_declare_logic_func(DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);

        // Declare closure_postcondition: (Int, Unit, Int) -> Bool.
        let postcond_decl = encoder.get_or_declare_logic_func(
            "closure_postcondition_canon_i_u_i",
            &[Sort::Int, unit_sort.clone(), Sort::Int],
            Sort::Bool,
        );

        // Assert axioms — this will declare `__trust_wp_unit` and assert the
        // ground instance using it.
        encoder.assert_trait_postcondition_axioms();

        // Build the postcondition application using the SAME `__trust_wp_unit`
        // constant that the axiom module uses. This mirrors the production
        // encoding path where the driver uses `__trust_wp_unit` as the unit term.
        let default_fn_term = encoder.solver.apply(&default_decl, &[]);
        let unit_term = encoder.solver.declare_const("__trust_wp_unit", unit_sort);
        let zero = encoder.solver.int_const(0);
        let app = encoder
            .solver
            .apply(&postcond_decl, &[default_fn_term, unit_term, zero]);

        // Negate: NOT(postcond(default_fn, __trust_wp_unit, 0))
        // The ground instance asserts postcond(default_fn, __trust_wp_unit, 0) = true,
        // so this should be UNSAT. If the ground instance used a different unit
        // constant, this would be SAT (the bug we're fixing).
        let negated = encoder.solver.not(app);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "ground instance with canonical __trust_wp_unit must connect to postcondition application (#2670)"
        );
    }

    /// Verify the biconditional: postcond(default_fn, unit, 1) should be FALSE
    /// (since 1 != 0 for Int default). This tests the iff direction:
    /// postcond(fn, u, v) = false when v != default_value.
    #[test]
    #[ntest::timeout(10000)]
    fn test_default_postcondition_nonzero_int_is_false() {
        let mut encoder = AYEncoder::new();

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        let default_decl =
            encoder.get_or_declare_logic_func(DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);

        let postcond_decl = encoder.get_or_declare_logic_func(
            "closure_postcondition_nonzero_i_u_i",
            &[Sort::Int, unit_sort.clone(), Sort::Int],
            Sort::Bool,
        );

        encoder.assert_trait_postcondition_axioms();

        let default_fn_term = encoder.solver.apply(&default_decl, &[]);
        let unit_term = encoder.solver.declare_const("__test_unit_nz", unit_sort);
        let one = encoder.solver.int_const(1);
        let app = encoder
            .solver
            .apply(&postcond_decl, &[default_fn_term, unit_term, one]);

        // Assert: postcondition(default_fn, unit, 1) = true
        encoder.assert_term(app);

        // Should be UNSAT because the biconditional says postcond(fn, u, 1) = (1 == 0) = false.
        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "postcondition(default_fn, unit, 1) should be false — only 0 is the default (#2670)"
        );
    }

    /// Simulates the PRODUCTION encoding path where:
    /// 1. `Default::default` is declared under a placeholder name (not raw SMT name)
    /// 2. The receiver in the postcondition is a AY variable (from encode_var), not
    ///    a UF application
    ///
    /// This test validates the two-part fix for #2670:
    /// - Demand detection uses prefix matching to find placeholder declarations
    /// - Axiom assertion uses the variable from the var store (matching production encoding)
    ///
    /// Scenario (mirrors `<Tuple as Default>::default` encoding):
    ///   var: core::default::Default::default = <unconstrained Int>
    ///   declare-datatype Tuple (mk_tuple (tuple_0 Int) (tuple_1 Int))
    ///   assert: result = mk_tuple(0, 0)
    ///   postcondition: postcond(default_var, unit, tuple_0(result)) AND
    ///                  postcond(default_var, unit, tuple_1(result))
    /// Expected: UNSAT (axiom connects postcondition predicate to v == 0)
    #[test]
    #[ntest::timeout(10000)]
    fn test_production_path_placeholder_with_var_receiver() {
        let mut encoder = AYEncoder::new();

        let unit_sort = crate::encoder::sort_context::sort_inference::unit_sort();

        // 1. Declare Default::default under a PLACEHOLDER name (production path).
        let placeholder_name = format!("{}__placeholder_nullary__ret_i", DEFAULT_DEFAULT_SMT_NAME);
        encoder.get_or_declare_logic_func(&placeholder_name, &[], Sort::Int);

        // 2. Declare the postcondition predicate.
        let postcond_decl = encoder.get_or_declare_logic_func(
            "closure_postcondition_prod_i_u_i",
            &[Sort::Int, unit_sort.clone(), Sort::Int],
            Sort::Bool,
        );

        // 3. Create the receiver as a VARIABLE (what encode_var produces in production).
        // This is the critical difference: production uses a variable, not apply(decl, []).
        let default_var = encoder
            .get_or_declare_var(super::DEFAULT_DEFAULT_RUST_PATH, Sort::Int)
            .unwrap();

        // 4. Assert the axioms — should find the placeholder and use the variable.
        encoder.assert_trait_postcondition_axioms();

        // 5. Declare Tuple datatype and construct result = mk_tuple(0, 0).
        let tuple_dt = ay_dpll::api::DatatypeSort {
            name: "TupleProd".to_string(),
            constructors: vec![ay_dpll::api::DatatypeConstructor {
                name: "mk_tuple_prod".to_string(),
                fields: vec![
                    ay_dpll::api::DatatypeField {
                        name: "prod_tuple_0".to_string(),
                        sort: Sort::Int,
                    },
                    ay_dpll::api::DatatypeField {
                        name: "prod_tuple_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        };
        encoder.solver.declare_datatype(&tuple_dt);

        let zero = encoder.solver.int_const(0);
        let tuple_sort = Sort::Datatype(tuple_dt.clone());
        let result = encoder.solver.declare_const("__result_prod", tuple_sort);
        let mk_tuple_0_0 =
            encoder
                .solver
                .datatype_constructor(&tuple_dt, "mk_tuple_prod", &[zero, zero]);
        let result_eq = encoder.solver.eq(result, mk_tuple_0_0);
        encoder.assert_term(result_eq);

        // 6. Build postcondition applications using the VARIABLE as receiver.
        let field0 = encoder
            .solver
            .datatype_selector("prod_tuple_0", result, Sort::Int);
        let field1 = encoder
            .solver
            .datatype_selector("prod_tuple_1", result, Sort::Int);

        let unit_term = encoder.solver.declare_const("__trust_wp_unit", unit_sort);
        let postcond_field0 = encoder
            .solver
            .apply(&postcond_decl, &[default_var, unit_term, field0]);
        let postcond_field1 = encoder
            .solver
            .apply(&postcond_decl, &[default_var, unit_term, field1]);

        // 7. Negate: NOT(postcond AND postcond) — should be UNSAT.
        let both = encoder.solver.and(postcond_field0, postcond_field1);
        let negated = encoder.solver.not(both);
        encoder.assert_term(negated);

        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "production path: placeholder + var receiver should prove Default postcondition (#2670)"
        );
    }
}
