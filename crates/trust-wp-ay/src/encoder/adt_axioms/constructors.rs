// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Qualified (user-defined enum) constructor axioms + individual constructor helpers.
//!
//! When user-defined enums like `OwnResult` have constructors `Ok` and `Err`,
//! the UF path encodes them as `logic_OwnResult_P__P_Ok` (using `_P__P_` for `::`).
//! The standard axiom path only handles unqualified names (`logic_Ok` etc.),
//! so these qualified constructors need dedicated axiom generation. (#1766)

use std::collections::HashMap;

use ay_dpll::api::{FuncDecl, Sort};

use super::super::AYEncoder;

impl AYEncoder {
    /// Assert axioms for qualified (user-defined enum) constructor names (#1766).
    ///
    /// Scans `logic_funcs` for qualified constructor families such as
    /// `logic_OwnResult_P__P_Ok` or `logic_OwnResult_P__P_Ok__placeholder_i__ret_i`
    /// and generates the same axioms using the shared testers (`is_ok`, `is_some`)
    /// and accessors (`spec_unwrap`, `result_err_error`).
    pub(super) fn assert_qualified_constructor_axioms(&mut self) {
        // Suffixes that identify qualified constructors (from `::` encoding).
        const OK_SUFFIX: &str = "_P__P_Ok";
        const ERR_SUFFIX: &str = "_P__P_Err";
        const SOME_SUFFIX: &str = "_P__P_Some";
        const NONE_SUFFIX: &str = "_P__P_None";

        // Also skip the standard (unqualified) names — they were already handled.
        let std_ok = trust_wp_core::logic::logic_fn_smt_name("Ok");
        let std_err = trust_wp_core::logic::logic_fn_smt_name("Err");
        let std_some = trust_wp_core::logic::logic_fn_smt_name("Some");
        let std_none = trust_wp_core::logic::logic_fn_smt_name("None");

        // Collect qualified Int-model constructor declarations from logic_funcs.
        // Placeholder-backed names now look like
        // `logic_OwnResult_P__P_Ok__placeholder_i__ret_i`, so normalize them back
        // to the constructor family before the suffix check. Keep only one Int
        // declaration per family because the qualified axiom helpers still model
        // the legacy Int carrier. (#1766, #2274)
        let mut qualified_ok: HashMap<String, FuncDecl> = HashMap::new();
        let mut qualified_err: HashMap<String, FuncDecl> = HashMap::new();
        let mut qualified_some: HashMap<String, FuncDecl> = HashMap::new();
        let mut qualified_none: HashMap<String, FuncDecl> = HashMap::new();

        for (name, decl) in self.logic_funcs_iter() {
            let family_name = Self::logic_fn_family_name(name);

            if family_name == std_ok
                || family_name == std_err
                || family_name == std_some
                || family_name == std_none
            {
                continue;
            }

            if family_name.ends_with(OK_SUFFIX) && Self::is_int_model_constructor_decl(decl, 1) {
                Self::record_qualified_constructor(&mut qualified_ok, name, family_name, decl);
            } else if family_name.ends_with(ERR_SUFFIX)
                && Self::is_int_model_constructor_decl(decl, 1)
            {
                Self::record_qualified_constructor(&mut qualified_err, name, family_name, decl);
            } else if family_name.ends_with(SOME_SUFFIX)
                && Self::is_int_model_constructor_decl(decl, 1)
            {
                Self::record_qualified_constructor(&mut qualified_some, name, family_name, decl);
            } else if family_name.ends_with(NONE_SUFFIX)
                && Self::is_int_model_constructor_decl(decl, 0)
            {
                Self::record_qualified_constructor(&mut qualified_none, name, family_name, decl);
            }
        }

        // Check whether standard (unqualified) Ok/Err constructors exist.
        // When no standard constructor is present AND exactly one qualified
        // constructor of the same variant exists, it is safe to assert the
        // reconstruction axiom for the qualified constructor.  Without
        // reconstruction the solver cannot prove postconditions of the form
        // `OwnResult::Ok(result) == self`, which is critical for unwrap/expect
        // patterns. (#1296)
        let has_std_ok = self.find_standard_int_constructor_decl("Ok", 1).is_some();
        let has_std_err = self.find_standard_int_constructor_decl("Err", 1).is_some();

        // Safe to assert Ok reconstruction when there is no standard logic_Ok
        // AND at most one qualified Ok family (avoiding mutual collapse between
        // multiple user-defined Ok-like types).
        let ok_reconstruction_safe = !has_std_ok && qualified_ok.len() <= 1;
        let err_reconstruction_safe = !has_std_err && qualified_err.len() <= 1;

        // Qualified Ok constructors: same axioms as standard Ok
        for ok_decl in qualified_ok.values() {
            let range_sort = ok_decl.range().clone();
            let is_ok_decl = self.get_or_declare_constructor_tester_for_sort("is_ok", &range_sort);
            let unwrap_decl =
                self.get_or_declare_accessor_for_sorts("spec_unwrap", &range_sort, &Sort::Int);
            let is_some_decl =
                self.get_or_declare_constructor_tester_for_sort("is_some", &range_sort);
            self.assert_ok_constructor_axioms(
                ok_decl,
                Some(&is_ok_decl),
                Some(&unwrap_decl),
                Some(&is_some_decl),
            );
            // Reconstruction: safe when no competing Ok constructor exists.
            if ok_reconstruction_safe {
                self.assert_ok_reconstruction(ok_decl, &is_ok_decl, &unwrap_decl);
            }
        }

        // Qualified Err constructors: same axioms as standard Err
        for err_decl in qualified_err.values() {
            let range_sort = err_decl.range().clone();
            let is_ok_decl = self.get_or_declare_constructor_tester_for_sort("is_ok", &range_sort);
            let err_acc_decl =
                self.get_or_declare_accessor_for_sorts("result_err_error", &range_sort, &Sort::Int);
            let is_some_decl =
                self.get_or_declare_constructor_tester_for_sort("is_some", &range_sort);
            self.assert_err_constructor_axioms(
                err_decl,
                Some(&is_ok_decl),
                Some(&err_acc_decl),
                Some(&is_some_decl),
            );
            // Reconstruction: safe when no competing Err constructor exists.
            if err_reconstruction_safe {
                self.assert_err_reconstruction(err_decl, &is_ok_decl, &err_acc_decl);
            }
        }

        // Qualified Some constructors: same axioms as standard Some
        for some_decl in qualified_some.values() {
            let range_sort = some_decl.range().clone();
            let is_some_decl =
                self.get_or_declare_constructor_tester_for_sort("is_some", &range_sort);
            let unwrap_decl =
                self.get_or_declare_accessor_for_sorts("spec_unwrap", &range_sort, &Sort::Int);
            let is_ok_decl = self.get_or_declare_constructor_tester_for_sort("is_ok", &range_sort);
            let is_option_decl = (range_sort == Sort::Int).then(|| {
                self.get_or_declare_spec_fn("__trust_wp_is_option", &[Sort::Int], Sort::Bool)
            });
            self.assert_some_constructor_axioms(
                some_decl,
                Some(&is_some_decl),
                Some(&unwrap_decl),
                is_option_decl.as_ref(),
                Some(&is_ok_decl),
            );
        }

        // Qualified None constructors: same axioms as standard None
        for none_decl in qualified_none.values() {
            let range_sort = none_decl.range().clone();
            let is_some_decl =
                self.get_or_declare_constructor_tester_for_sort("is_some", &range_sort);
            let is_ok_decl = self.get_or_declare_constructor_tester_for_sort("is_ok", &range_sort);
            let is_option_decl = (range_sort == Sort::Int).then(|| {
                self.get_or_declare_spec_fn("__trust_wp_is_option", &[Sort::Int], Sort::Bool)
            });
            self.assert_none_constructor_axioms(
                none_decl,
                Some(&is_some_decl),
                is_option_decl.as_ref(),
                Some(&is_ok_decl),
            );
        }
    }

    /// Assert axioms for an Ok-like constructor (standard or qualified).
    ///
    /// Axioms:
    /// - `forall v. is_ok(ctor(v))` (tester)
    /// - `forall v. spec_unwrap(ctor(v)) = v` (accessor)
    /// - `forall x. is_ok(x) ==> ctor(spec_unwrap(x)) = x` (reconstruction)
    /// - `forall v. !is_some(ctor(v))` (cross-type disjointness)
    fn assert_ok_constructor_axioms(
        &mut self,
        ok_decl: &FuncDecl,
        is_ok_decl: Option<&FuncDecl>,
        unwrap_decl: Option<&FuncDecl>,
        is_some_decl: Option<&FuncDecl>,
    ) {
        if is_ok_decl.is_none() && unwrap_decl.is_none() {
            return;
        }
        let v = self.solver.fresh_var("q_res_ax_v", Sort::Int);
        let ok_v = self.solver.apply(ok_decl, &[v]);

        if let Some(is_ok_decl) = is_ok_decl {
            // forall v. is_ok(ctor(v))
            let is_ok_of_ok = self.solver.apply(is_ok_decl, &[ok_v]);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], is_ok_of_ok, &[&[ok_v]]);
            self.solver.assert_term(axiom);
        }

        if let Some(unwrap_decl) = unwrap_decl.as_ref() {
            // forall v. spec_unwrap(ctor(v)) = v
            let unwrap_of_ok = self.solver.apply(unwrap_decl, &[ok_v]);
            let eq = self.eq_term(unwrap_of_ok, v);
            let axiom = self.solver.forall_with_triggers(&[v], eq, &[&[ok_v]]);
            self.solver.assert_term(axiom);

            // Reconstruction: forall x. is_ok(x) ==> ctor(spec_unwrap(x)) = x
            // Note: We do NOT assert reconstruction for qualified constructors because
            // reconstruction axioms assume a single constructor per variant. With multiple
            // Ok-like constructors (e.g., logic_Ok and logic_OwnResult_P__P_Ok), asserting
            // reconstruction for each would lead to conflicting equalities:
            //   is_ok(x) ==> logic_Ok(spec_unwrap(x)) = x
            //   is_ok(x) ==> logic_OwnResult_P__P_Ok(spec_unwrap(x)) = x
            // This would collapse distinct types. Injectivity and tester axioms are safe.
        }

        // Cross-type disjointness: forall v. !is_some(ctor(v))
        if let Some(is_some_decl) = is_some_decl.as_ref() {
            let is_some_ok = self.solver.apply(is_some_decl, &[ok_v]);
            let not_is_some_ok = self.solver.not(is_some_ok);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], not_is_some_ok, &[&[ok_v]]);
            self.solver.assert_term(axiom);
        }
    }

    /// Assert axioms for an Err-like constructor (standard or qualified).
    ///
    /// Axioms:
    /// - `forall v. !is_ok(ctor(v))` (tester)
    /// - `forall v. result_err_error(ctor(v)) = v` (accessor)
    /// - `forall v. !is_some(ctor(v))` (cross-type disjointness)
    fn assert_err_constructor_axioms(
        &mut self,
        err_decl: &FuncDecl,
        is_ok_decl: Option<&FuncDecl>,
        err_acc_decl: Option<&FuncDecl>,
        is_some_decl: Option<&FuncDecl>,
    ) {
        if is_ok_decl.is_none() && err_acc_decl.is_none() {
            return;
        }
        let v = self.solver.fresh_var("q_res_ax_ev", Sort::Int);
        let err_v = self.solver.apply(err_decl, &[v]);

        if let Some(is_ok_decl) = is_ok_decl {
            // forall v. !is_ok(ctor(v))
            let is_ok_of_err = self.solver.apply(is_ok_decl, &[err_v]);
            let not_ok = self.solver.not(is_ok_of_err);
            let axiom = self.solver.forall_with_triggers(&[v], not_ok, &[&[err_v]]);
            self.solver.assert_term(axiom);
        }

        if let Some(err_acc_decl) = err_acc_decl {
            // forall v. result_err_error(ctor(v)) = v
            let err_acc_of_err = self.solver.apply(err_acc_decl, &[err_v]);
            let eq = self.eq_term(err_acc_of_err, v);
            let axiom = self.solver.forall_with_triggers(&[v], eq, &[&[err_v]]);
            self.solver.assert_term(axiom);
            // Reconstruction omitted for qualified constructors — see Ok comment.
        }

        // Cross-type disjointness: forall v. !is_some(ctor(v))
        if let Some(is_some_decl) = is_some_decl {
            let is_some_err = self.solver.apply(is_some_decl, &[err_v]);
            let not_is_some_err = self.solver.not(is_some_err);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], not_is_some_err, &[&[err_v]]);
            self.solver.assert_term(axiom);
        }
    }

    /// Assert the Ok reconstruction axiom for a qualified constructor (#1296).
    ///
    /// ```text
    /// forall x. is_ok(x) ==> ctor(spec_unwrap(x)) = x
    /// ```
    ///
    /// This is only safe when no other Ok-like constructor shares the same
    /// tester/accessor UFs. The caller must verify uniqueness before invoking.
    fn assert_ok_reconstruction(
        &mut self,
        ok_decl: &FuncDecl,
        is_ok_decl: &FuncDecl,
        unwrap_decl: &FuncDecl,
    ) {
        let x = self.solver.fresh_var("q_res_recon_x", Sort::Int);
        let is_ok_x = self.solver.apply(is_ok_decl, &[x]);
        let unwrap_x = self.solver.apply(unwrap_decl, &[x]);
        let ok_unwrap_x = self.solver.apply(ok_decl, &[unwrap_x]);
        let eq = self.eq_term(ok_unwrap_x, x);
        let implies = self.solver.implies(is_ok_x, eq);
        let axiom = self
            .solver
            .forall_with_triggers(&[x], implies, &[&[unwrap_x]]);
        self.solver.assert_term(axiom);
    }

    /// Assert the Err reconstruction axiom for a qualified constructor (#1296).
    ///
    /// ```text
    /// forall x. !is_ok(x) ==> ctor(result_err_error(x)) = x
    /// ```
    ///
    /// This is only safe when no other Err-like constructor shares the same
    /// tester/accessor UFs. The caller must verify uniqueness before invoking.
    fn assert_err_reconstruction(
        &mut self,
        err_decl: &FuncDecl,
        is_ok_decl: &FuncDecl,
        err_acc_decl: &FuncDecl,
    ) {
        let x = self.solver.fresh_var("q_res_recon_ex", Sort::Int);
        let is_ok_x = self.solver.apply(is_ok_decl, &[x]);
        let not_ok_x = self.solver.not(is_ok_x);
        let err_acc_x = self.solver.apply(err_acc_decl, &[x]);
        let err_of_err_acc_x = self.solver.apply(err_decl, &[err_acc_x]);
        let eq = self.eq_term(err_of_err_acc_x, x);
        let implies = self.solver.implies(not_ok_x, eq);
        let axiom = self
            .solver
            .forall_with_triggers(&[x], implies, &[&[err_acc_x]]);
        self.solver.assert_term(axiom);
    }

    /// Assert axioms for a Some-like constructor (standard or qualified).
    ///
    /// Axioms:
    /// - `forall v. is_some(ctor(v))` (tester)
    /// - `forall v. is_option(ctor(v))` (type predicate)
    /// - `forall v. spec_unwrap(ctor(v)) = v` (accessor)
    /// - `forall v. !is_ok(ctor(v))` (cross-type disjointness)
    fn assert_some_constructor_axioms(
        &mut self,
        some_decl: &FuncDecl,
        is_some_decl: Option<&FuncDecl>,
        unwrap_decl: Option<&FuncDecl>,
        is_option_decl: Option<&FuncDecl>,
        is_ok_decl: Option<&FuncDecl>,
    ) {
        if is_some_decl.is_none() && unwrap_decl.is_none() && is_option_decl.is_none() {
            return;
        }
        let v = self.solver.fresh_var("q_opt_ax_v", Sort::Int);
        let some_v = self.solver.apply(some_decl, &[v]);

        if let Some(is_some_decl) = is_some_decl {
            // forall v. is_some(ctor(v))
            let is_some_of_some = self.solver.apply(is_some_decl, &[some_v]);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], is_some_of_some, &[&[some_v]]);
            self.solver.assert_term(axiom);
        }

        if let Some(is_option_decl) = is_option_decl {
            // forall v. is_option(ctor(v))
            let is_option_some = self.solver.apply(is_option_decl, &[some_v]);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], is_option_some, &[&[some_v]]);
            self.solver.assert_term(axiom);
        }

        if let Some(unwrap_decl) = unwrap_decl {
            // forall v. spec_unwrap(ctor(v)) = v
            let unwrap_of_some = self.solver.apply(unwrap_decl, &[some_v]);
            let eq = self.eq_term(unwrap_of_some, v);
            let axiom = self.solver.forall_with_triggers(&[v], eq, &[&[some_v]]);
            self.solver.assert_term(axiom);
            // Reconstruction omitted for qualified constructors — see Ok comment.
        }

        // Cross-type disjointness: forall v. !is_ok(ctor(v))
        if let Some(is_ok_decl) = is_ok_decl {
            let is_ok_some = self.solver.apply(is_ok_decl, &[some_v]);
            let not_is_ok_some = self.solver.not(is_ok_some);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], not_is_ok_some, &[&[some_v]]);
            self.solver.assert_term(axiom);
        }
    }

    /// Assert axioms for a None-like constructor (standard or qualified).
    ///
    /// Axioms:
    /// - `!is_some(ctor())` (tester)
    /// - `is_option(ctor())` (type predicate)
    /// - `!is_ok(ctor())` (cross-type disjointness)
    fn assert_none_constructor_axioms(
        &mut self,
        none_decl: &FuncDecl,
        is_some_decl: Option<&FuncDecl>,
        is_option_decl: Option<&FuncDecl>,
        is_ok_decl: Option<&FuncDecl>,
    ) {
        let none = self.solver.apply(none_decl, &[]);

        if let Some(is_some_decl) = is_some_decl {
            // !is_some(ctor())
            let is_some_of_none = self.solver.apply(is_some_decl, &[none]);
            let axiom = self.solver.not(is_some_of_none);
            self.solver.assert_term(axiom);
        }

        if let Some(is_option_decl) = is_option_decl {
            // is_option(ctor())
            let is_option_none = self.solver.apply(is_option_decl, &[none]);
            self.solver.assert_term(is_option_none);
        }

        // Cross-type disjointness: !is_ok(ctor())
        if let Some(is_ok_decl) = is_ok_decl {
            let is_ok_none = self.solver.apply(is_ok_decl, &[none]);
            let not_is_ok_none = self.solver.not(is_ok_none);
            self.solver.assert_term(not_is_ok_none);
        }
    }
}
