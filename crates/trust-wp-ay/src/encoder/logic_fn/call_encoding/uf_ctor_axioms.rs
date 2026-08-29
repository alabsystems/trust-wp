// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! UF constructor axiom helpers for logic function call encoding.

use ay_dpll::api::{FuncDecl, Sort, Term};
use tracing::debug;

use crate::encoder::{
    match_enc::{datatype_constructor_matches, datatype_constructor_name, short_constructor_name},
    AYEncoder,
};

impl AYEncoder {
    pub(super) fn assert_ground_some_not_none(
        &mut self,
        ctor_name: &str,
        ctor_term: Term,
        arg_terms: &[Term],
    ) {
        if self.quantifier_state.quantifier_depth() != 0
            || short_constructor_name(ctor_name) != "Some"
            || arg_terms.len() != 1
        {
            return;
        }

        let term_sort = self.solver.get_sort(ctor_term);
        let datatype = match &term_sort {
            Sort::Datatype(dt) => Some(dt.clone()),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
            _ => None,
        };
        let Some(datatype) = datatype else {
            return;
        };
        let has_some = datatype
            .constructors
            .iter()
            .any(|ctor| datatype_constructor_matches(&datatype, &ctor.name, "Some"));
        let has_none = datatype.constructors.iter().any(|ctor| {
            datatype_constructor_matches(&datatype, &ctor.name, "None") && ctor.fields.is_empty()
        });
        if !has_some || !has_none {
            return;
        }

        let Some(none) =
            self.axiom_datatype_constructor("ground_some_not_none", &datatype, "None", &[])
        else {
            return;
        };
        let eq = self.eq_term(ctor_term, none);
        let distinct = self.solver.not(eq);
        self.assert_solver_term("ground_some_not_none", distinct);
    }

    /// Assert native datatype tester axioms for UF constructor placeholder terms.
    ///
    /// When a constructor (Ok, Err, Some) falls through to the UF placeholder
    /// path (because its argument sort doesn't match the native datatype field
    /// sort), the resulting UF term has the correct datatype sort but is NOT
    /// connected to the native datatype theory. The solver doesn't know that
    /// `UF_Ok(x)` should satisfy `is-Ok(...)`, or that `UF_Some(x)` should
    /// satisfy `is-Some(...)`.
    ///
    /// This method asserts the native tester for each ground UF constructor
    /// call: `is-Ctor(UF_Ctor(x)) = true`. This bridges the gap between UF
    /// constructor terms and the native datatype theory used by match pattern
    /// conditions and postcondition encoding. (#1296)
    ///
    /// Only fires at ground level (quantifier_depth == 0), for recognized
    /// constructor names, when the result sort is a declared datatype.
    pub(super) fn assert_ground_uf_constructor_tester(&mut self, ctor_name: &str, ctor_term: Term) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }
        let short = short_constructor_name(ctor_name);
        // Only fire for recognized constructor names.
        if !matches!(short, "Some" | "None" | "Ok" | "Err") {
            return;
        }
        let term_sort = self.solver.get_sort(ctor_term);
        let datatype = match &term_sort {
            Sort::Datatype(dt) => Some(dt.clone()),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
            _ => None,
        };
        let Some(datatype) = datatype else {
            return;
        };
        // Assert the native tester: is-Ctor(UF_Ctor(x)) = true.
        let actual = datatype_constructor_name(&datatype, short);
        if let Ok(tester) = self.solver.try_datatype_tester(&actual, ctor_term) {
            self.assert_solver_term("ground_uf_ctor_tester", tester);
        }
    }

    /// Assert quantified tester and selector axioms for a newly declared UF
    /// constructor placeholder.
    ///
    /// **Tester axiom:** `forall x. is-Ctor(UF_Ctor(x))`
    /// **Selector axioms:** `forall x. selector_i(UF_Ctor(x)) = x_i` (one per field)
    ///
    /// This is the universal version of `assert_ground_uf_constructor_tester`.
    /// Called once when a UF constructor placeholder is first declared, it
    /// ensures the tester and selectors hold for ALL applications of the UF,
    /// including those inside quantified postconditions that the ground-only
    /// version cannot reach. (#1296)
    ///
    /// The trigger `UF_Ctor(x)` enables E-matching so ay-dpll can instantiate
    /// the axioms when the UF constructor appears in quantified contexts.
    ///
    /// Selector axioms are critical for verification of functions like
    /// `Result<Option<T>, E>::transpose`, where the postcondition uses UF
    /// constructors (e.g., `UF_Ok(t)`) but the body encoding uses native
    /// datatype constructors. Without selector axioms, the solver cannot
    /// extract the payload from `UF_Ok(t)` to compare with the native
    /// constructor's payload, causing spurious counterexamples. (#1296)
    pub(super) fn assert_uf_constructor_tester_axiom(
        &mut self,
        ctor_name: &str,
        func_decl: &FuncDecl,
        return_sort: &Sort,
    ) {
        let short = short_constructor_name(ctor_name);

        debug!(
            "  [uf-ctor-axiom] name={ctor_name} short={short} \
                 return_sort={return_sort:?} domain={:?}",
            func_decl.domain()
        );

        if !matches!(short, "Some" | "None" | "Ok" | "Err") {
            return;
        }
        // Resolve the datatype from the return sort.
        let datatype = match return_sort {
            Sort::Datatype(dt) => Some(dt.clone()),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
            _ => None,
        };
        let Some(datatype) = datatype else {
            debug!("  [uf-ctor-axiom] no datatype found for return_sort={return_sort:?}");

            return;
        };
        let actual_short = datatype_constructor_name(&datatype, short);

        debug!(
            "  [uf-ctor-axiom] datatype={} ctors={:?}",
            datatype.name,
            datatype
                .constructors
                .iter()
                .map(|c| &c.name)
                .collect::<Vec<_>>()
        );

        let domain = func_decl.domain();
        if domain.is_empty() {
            // Nullary constructor (e.g., None): just assert the tester directly
            // on the constant term. No quantifier needed.
            let ctor_const = self.solver.apply(func_decl, &[]);
            if let Ok(tester) = self.solver.try_datatype_tester(&actual_short, ctor_const) {
                self.assert_solver_term("uf_ctor_tester_axiom/nullary", tester);
            }
            return;
        }
        // Unary+ constructor: create bound variables matching the UF domain.
        let bound_vars: Vec<Term> = domain
            .iter()
            .enumerate()
            .map(|(i, sort)| {
                self.solver
                    .fresh_var(&format!("uf_ctor_ax_{i}"), sort.clone())
            })
            .collect();
        let uf_app = self.solver.apply(func_decl, &bound_vars);

        // Tester axiom: `forall x. is-Ctor(UF_Ctor(x))`.
        if let Ok(tester) = self.solver.try_datatype_tester(&actual_short, uf_app) {
            let axiom = self
                .solver
                .forall_with_triggers(&bound_vars, tester, &[&[uf_app]]);
            self.assert_solver_term("uf_ctor_tester_axiom", axiom);
        }

        // Selector axioms bridge the native datatype selectors to UF constructor
        // arguments.
        //
        // Case 1: Sorts match — direct axiom: `forall x. selector(UF_Ctor(x)) = x`
        //
        // Case 2: Sorts differ (e.g., UF param is OwnResult-sorted but the
        // native OptionInt field is Int-sorted). Previously skipped entirely,
        // relying on nested constructor equality elimination in
        // quantifier_ctor_elim.rs. However, that only works inside quantifier
        // bodies. The body encoding path compares result bindings using native
        // selectors, and without a selector axiom the solver cannot extract
        // the payload from `UF_Some(OwnResult::Err(e))`, causing timeouts
        // from multi-round E-matching chains. (#1296)
        //
        // Fix: declare a coercion UF `__trust_wp_uf_ctor_coerce_N: A -> B` and
        // assert `forall x. selector(UF_Ctor(x)) = coerce(x)`. This gives the
        // solver a direct one-step path from UF constructors to native selectors.
        // The coercion UF is unconstrained (conservative — cannot cause false
        // proofs), but enables the solver to propagate equalities through the
        // UF/native datatype bridge without requiring Skolemization. (#1296)
        let ctor_decl = datatype
            .constructors
            .iter()
            .find(|c| datatype_constructor_matches(&datatype, &c.name, short));
        if let Some(ctor_decl) = ctor_decl {
            for (i, field) in ctor_decl.fields.iter().enumerate() {
                let Some(uf_param_sort) = domain.get(i) else {
                    continue;
                };
                let field_term_sort = field.sort.as_term_sort();
                if *uf_param_sort == field_term_sort {
                    // Case 1: Sorts match — direct selector axiom:
                    // `forall x. selector(UF_Ctor(x)) = x`
                    if let Ok(selector_term) =
                        self.solver
                            .try_datatype_selector(&field.name, uf_app, field.sort.clone())
                    {
                        let eq = self.eq_term(selector_term, bound_vars[i]);
                        let axiom = self
                            .solver
                            .forall_with_triggers(&bound_vars, eq, &[&[uf_app]]);
                        self.assert_solver_term("uf_ctor_selector_axiom", axiom);
                    }
                } else {
                    // Case 2: Cross-sort bridge via coercion UF.
                    // Declare `__trust_wp_uf_ctor_coerce_N: uf_param_sort -> field_sort`
                    // and assert `forall x. selector(UF_Ctor(x)) = coerce(x)`.
                    if let Ok(selector_term) =
                        self.solver
                            .try_datatype_selector(&field.name, uf_app, field.sort.clone())
                    {
                        // Mangle the coercion UF name with its instantiated
                        // domain/range sorts (#result_own / #transpose). The
                        // bare `__trust_wp_uf_ctor_coerce_{short}_{i}` name
                        // collides across monomorphizations that share a
                        // constructor short-name but differ in payload sort —
                        // e.g. `OwnResult<Option<T>,E>::transpose` declares
                        // `Ok.0` at both an `OwnResult`-payload and a `T`-payload
                        // sort, and the second `declare_fun` panicked with
                        // "already in use with a different native signature".
                        // Sort-tagging gives each signature a distinct name.
                        let coerce_name = format!(
                            "__trust_wp_uf_ctor_coerce_{short}_{i}_{}_{}",
                            Self::placeholder_sort_tag(uf_param_sort),
                            Self::placeholder_sort_tag(&field_term_sort),
                        );
                        // Non-panicking declare: on any residual signature clash
                        // skip this cross-sort bridge instead of aborting the
                        // whole function's verification. The selector axiom is a
                        // completeness aid (a one-step UF→native path), not a
                        // soundness obligation, so omitting it can at worst cost a
                        // recoverable timeout.
                        let Ok(coerce_decl) = self.solver.try_declare_fun(
                            &coerce_name,
                            &[uf_param_sort.clone()],
                            field_term_sort.clone(),
                        ) else {
                            continue;
                        };
                        let coerced = self.solver.apply(&coerce_decl, &[bound_vars[i]]);
                        let eq = self.eq_term(selector_term, coerced);
                        let axiom = self
                            .solver
                            .forall_with_triggers(&bound_vars, eq, &[&[uf_app]]);
                        self.assert_solver_term("uf_ctor_selector_axiom/cross_sort", axiom);

                        debug!(
                            "  [uf-ctor-axiom] cross-sort selector bridge: \
                                 {coerce_name}: {:?} -> {:?} for {short}.{}",
                            uf_param_sort, field_term_sort, field.name
                        );
                    }
                }
            }
        }
    }
}
