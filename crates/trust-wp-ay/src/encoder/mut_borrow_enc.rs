// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mutable borrow encoding using RustHorn-style prophecy variables.
//!
//! This is the **production** encoding for `Formula::MutBorrow`. It creates
//! `{var}_current`, `{var}_final`, and `{var}_id` SMT variables and constrains
//! them equal to the supplied expressions. Rust's ownership guarantees make
//! this purely first-order — no heap arrays or separation logic primitives are
//! needed.
//!
//! The experimental separation-logic primitives (PointsTo, SepConj, MagicWand)
//! are reserved for future unsafe Rust support and live outside this module,
//! so the production encoding never depends on them (#2214).

use ay_dpll::api::Term;
use trust_wp_core::formula::PureExpr;

use super::{AYEncoder, MutRefVarNames};
use crate::error::EncodingError;

impl AYEncoder {
    /// Encode a mutable borrow using RustHorn-style prophecy encoding.
    ///
    /// # `RustHorn` Encoding
    ///
    /// Mutable borrows are represented as (current, final) pairs:
    /// - `{var}_current`: Value at borrow creation (corresponds to `*v`)
    /// - `{var}_final`: Prophecy of value when borrow ends (corresponds to `^v`)
    ///
    /// This encoding leverages Rust's ownership guarantees - mutable borrows have
    /// exclusive access, so we don't need to track heap disjointness explicitly.
    ///
    /// # Benefits over Separation Logic
    ///
    /// - Uses only `QF_LIA` (linear integer arithmetic) - no arrays needed
    /// - No quantifiers required
    /// - Better SMT solver performance
    /// - Matches Creusot's approach
    #[allow(clippy::similar_names)] // final_var/final_expr are meaningfully different
    pub(super) fn encode_mut_borrow(
        &mut self,
        var: &str,
        current: &PureExpr,
        final_expr: &PureExpr,
        id: &PureExpr,
    ) -> Result<Term, EncodingError> {
        // Create variables for current and final values with inferred sorts (#546)
        let names = MutRefVarNames::new(var);
        // Context-aware inference for initial var declarations. (#1965)
        let current_sort = self.infer_expr_sort_with_context(current, None);
        let final_sort = self.infer_expr_sort_with_context(final_expr, None);
        // Pre-declare variables so they exist before encode_pure resolves names.
        self.get_or_declare_var(&names.current, current_sort)?;
        self.get_or_declare_var(&names.final_val, final_sort)?;
        self.get_or_declare_var(&names.id, ay_dpll::api::Sort::Int)?;

        // Encode the expressions — this may trigger sort upgrades on the
        // variables we just declared (Int→non-Int via resolve_decl_sort).
        let current_term = self.encode_pure(current)?;
        let final_term = self.encode_pure(final_expr)?;
        let id_term = self.encode_pure(id)?;

        // Re-fetch variable terms AFTER encode_pure to pick up any sort
        // upgrades. Using pre-cached terms would bind the phantom Int-sorted
        // variable instead of the upgraded one (#1965 soundness fix).
        let current_var = self.var_term(&names.current).ok_or_else(|| {
            EncodingError::solver_error(format!("lost variable '{}'", names.current))
        })?;
        let final_var = self.var_term(&names.final_val).ok_or_else(|| {
            EncodingError::solver_error(format!("lost variable '{}'", names.final_val))
        })?;
        let id_var = self
            .var_term(&names.id)
            .ok_or_else(|| EncodingError::solver_error(format!("lost variable '{}'", names.id)))?;
        // Derive sorts from the solver terms directly. This picks up any sort
        // upgrades from encode_pure (Int→Datatype, Int→Bool) and avoids a
        // SortFallbackToInt demotion when var_sorts is stale. (#994, #2155)
        let current_sort = self.solver.get_sort(current_var);
        let final_sort = self.solver.get_sort(final_var);

        // Keep the user-facing mut-borrow current/final equalities on the
        // compatibility wrapper: complex Bool bodies like `x > 0` still prove
        // more reliably through `iff` here even though lower-level equality
        // sites use native Bool equality. (#1179, #2141)
        let c1 = self.eq_or_iff(current_var, current_term, &current_sort);
        let c2 = self.eq_or_iff(final_var, final_term, &final_sort);
        let c3 = self.eq_term(id_var, id_term);

        let current_and_final = self.solver.and(c1, c2);
        Ok(self.solver.and(current_and_final, c3))
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{SolveResult, Sort};
    use ntest::timeout;

    use super::*;
    use crate::encoder::AYEncoder;

    #[test]
    #[timeout(30000)]
    fn mut_borrow_constrains_current_and_final() {
        let mut encoder = AYEncoder::new();
        let current = PureExpr::Var("x".to_string(), None);
        let final_expr = PureExpr::Var("x_final_placeholder".to_string(), None);
        let id = PureExpr::Int(3);

        let constraint = encoder
            .encode_mut_borrow("x", &current, &final_expr, &id)
            .expect("encode_mut_borrow should succeed for simple vars");
        encoder.assert_term(constraint);

        // Assert x = 5, then x_current should also be 5
        let five = encoder.solver_mut().int_const(5);
        let x_var = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("x should be declared");
        let eq_x = encoder.solver_mut().eq(x_var, five);
        encoder.assert_term(eq_x);

        // x_current != 5 should be UNSAT (because x_current = x via encode_mut_borrow)
        let x_current = encoder
            .get_or_declare_var("x_current", Sort::Int)
            .expect("x_current should be declared by encode_mut_borrow");
        let five2 = encoder.solver_mut().int_const(5);
        let neq = encoder.solver_mut().eq(x_current, five2);
        let neg = encoder.solver_mut().not(neq);
        encoder.assert_term(neg);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "x_current should be constrained equal to x after encode_mut_borrow"
        );
    }

    #[test]
    #[timeout(30000)]
    fn mut_borrow_bool_sort_uses_iff_encoding() {
        let mut encoder = AYEncoder::new();
        let current = PureExpr::Bool(true);
        let final_expr = PureExpr::Bool(false);
        let id = PureExpr::Int(0);

        let constraint = encoder
            .encode_mut_borrow("b", &current, &final_expr, &id)
            .expect("encode_mut_borrow should succeed for Bool sort");
        encoder.assert_term(constraint);

        // b_current should be true (iff with true literal)
        let b_current = encoder
            .get_or_declare_var("b_current", Sort::Bool)
            .expect("b_current should be declared");
        let neg = encoder.solver_mut().not(b_current);
        encoder.assert_term(neg);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "b_current should be true (iff-encoded with Bool literal true)"
        );
    }
}
