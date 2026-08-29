// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;

use super::super::AYEncoder;

impl AYEncoder {
    /// Assert deep_model identity axioms for integer-sorted receivers (#2117).
    ///
    /// Asserts ground identity instances for integer-sorted receivers:
    ///
    /// 1. **Ground instances (eager):** For each recorded `deep_model(t)` call
    ///    where `t` has Int sort, directly asserts `deep_model(t) = t`.
    ///    This bypasses ay-dpll's single-round E-matching limitation where the
    ///    quantified form may not fire on ground terms. Without these ground
    ///    instances, the solver finds spurious counterexamples where
    ///    `deep_model(v)` is unconstrained despite the quantified axiom.
    ///
    /// 2. **Quantified fallback:** If no concrete Int receiver was recorded,
    ///    keep the historical `forall x : Int. deep_model(x) = x` axiom for
    ///    callers that intentionally depend on a universal identity.
    pub(crate) fn assert_deep_model_axioms(&mut self) {
        // The Int-receiver deep_model UF is named "method_deep_model_1_i"
        // (1 parameter, sort tag "i" for Int). Only assert when it was declared.
        let Some(deep_model_decl) = self.logic_func_decl_cloned("method_deep_model_1_i") else {
            return;
        };

        // ── Ground instances: deep_model(t) = t for each recorded call ──
        // ay-dpll E-matching is single-round and may not instantiate the
        // quantified axiom on all ground terms. Assert ground equalities
        // directly so the solver can use them without E-matching (#2117).
        let ground_terms = self.take_deep_model_ground_terms();
        let has_int_ground_term = ground_terms
            .iter()
            .any(|(smt_name, _)| smt_name == "method_deep_model_1_i");
        if !has_int_ground_term {
            let x = self.solver.fresh_var("dm_ax_x", Sort::Int);
            let dm_x = self.solver.apply(&deep_model_decl, &[x]);
            let eq = self.eq_term(dm_x, x);
            let axiom = self.solver.forall_with_triggers(&[x], eq, &[&[dm_x]]);
            self.solver.assert_term(axiom);
        }
        for (smt_name, receiver_term) in &ground_terms {
            // Only instantiate for Int-sorted receivers (sort tag "i")
            if smt_name == "method_deep_model_1_i" {
                let dm_t = self.solver.apply(&deep_model_decl, &[*receiver_term]);
                let ground_eq = self.eq_term(dm_t, *receiver_term);
                self.solver.assert_term(ground_eq);
            }
        }
        // Restore for potential re-use (though axioms are asserted once)
        self.restore_deep_model_ground_terms(ground_terms);
    }
}
