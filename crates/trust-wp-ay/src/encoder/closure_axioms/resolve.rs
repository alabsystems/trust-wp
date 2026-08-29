// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure resolve axioms — structural decomposition of `resolve(env)`.
//!
//! The closure resolve axiom decomposes `resolve(env)` into a conjunction of
//! per-capture resolve constraints:
//!
//!   `resolve(env) ⟺ resolve(cap_0) ∧ resolve(cap_1) ∧ …`
//!
//! Each capture's contribution depends on its capture kind:
//! - `ByRef`: trivially `true` (shared references have no borrow to resolve)
//! - `ByValue` / `ByMutRef`: delegates to sort-level resolve (recurses for
//!   nested closure sorts, returns `true` for flat value sorts)
//!
//! Reference: Creusot `backend/resolve.rs:164-177`.
//!
//! Extracted from `closure_axioms/mod.rs` as part of #1988 decomposition.

use ay_dpll::api::{FuncDecl, Sort, Term};

use super::super::{closure_sorts::closure_env_sort_name, AYEncoder};
use crate::shared_types::CaptureKind;

impl AYEncoder {
    fn closure_selector_tracked(
        &mut self,
        context: &str,
        selector_name: &str,
        env: Term,
        sort: Sort,
    ) -> Option<Term> {
        let term = self
            .solver
            .try_datatype_selector(selector_name, env, sort)
            .ok();
        if term.is_none() {
            Self::note_closure_axiom_skipped(context);
        }
        term
    }

    fn closure_resolve_name_for_sort(sort: &Sort) -> Option<String> {
        let sort_name = closure_env_sort_name(sort)?;
        let suffix = sort_name.strip_prefix("ClosureEnv_")?;
        Some(format!("closure_resolve_{suffix}"))
    }

    fn ensure_closure_resolve_axiom_for_sort(&mut self, sort: &Sort) -> Option<FuncDecl> {
        let resolve_name = Self::closure_resolve_name_for_sort(sort)?;
        let resolve_decl =
            self.get_or_declare_logic_func(&resolve_name, std::slice::from_ref(sort), Sort::Bool);

        // Reuse logic_fn_axioms as an idempotence guard so nested closure sorts
        // can request resolve declarations without re-emitting the same axiom.
        let axiom_guard = format!("{resolve_name}::axiom");
        if !self.mark_logic_fn_axiom_asserted(axiom_guard) {
            return Some(resolve_decl);
        }

        // Compare by normalized sort name to handle both Sort::Uninterpreted
        // (from closure_sort_from_tag) and Sort::Datatype (from registration) (#2151).
        let registered = self.find_closure_struct_by_sort(sort)?;
        let sort_name = closure_env_sort_name(sort)?;
        let suffix = sort_name.strip_prefix("ClosureEnv_")?;

        let env = self
            .solver
            .fresh_var(&format!("closure_resolve_{suffix}_env"), sort.clone());
        let Some(lhs) = self.axiom_apply_tracked("closure_resolve:lhs", &resolve_decl, &[env])
        else {
            return Some(resolve_decl);
        };

        let Some(resolve_parts) = registered
            .captures
            .iter()
            .enumerate()
            .map(|(index, (_, capture_sort, capture_kind))| {
                let selector_name = format!("closure_capture_{suffix}_{index}");
                let selector_context = format!("closure_resolve:selector:{suffix}:{index}");
                let capture_term = self.closure_selector_tracked(
                    &selector_context,
                    &selector_name,
                    env,
                    capture_sort.clone(),
                )?;
                self.resolve_term_for_capture(capture_term, capture_sort, *capture_kind)
            })
            .collect::<Option<Vec<_>>>()
        else {
            return Some(resolve_decl);
        };
        let rhs = resolve_parts
            .into_iter()
            .reduce(|acc, term| self.solver.and(acc, term))
            .unwrap_or_else(|| self.solver.bool_const(true));

        let body = self.eq_term(lhs, rhs);
        let axiom = self.solver.forall_with_triggers(&[env], body, &[&[lhs]]);
        self.solver.assert_term(axiom);
        Some(resolve_decl)
    }

    /// Resolve a term at the sort level: returns the resolve predicate applied
    /// to the given term for closure sorts, or `true` for non-closure sorts.
    pub(super) fn resolve_term_for_sort(&mut self, term: Term, sort: &Sort) -> Option<Term> {
        if let Some(resolve_decl) = self.ensure_closure_resolve_axiom_for_sort(sort) {
            self.axiom_apply_tracked("resolve_term_for_sort", &resolve_decl, &[term])
        } else {
            // Non-closure sorts are value-like in the current encoding, so resolve
            // is trivially true for those terms.
            Some(self.solver.bool_const(true))
        }
    }

    /// Build a resolve term for a single capture field, sensitive to capture kind (#758).
    ///
    /// - `ByRef`: trivially `true` (shared references have no borrow to resolve)
    /// - `ByValue` / `ByMutRef`: delegates to `resolve_term_for_sort` which recurses
    ///   for nested closure sorts and returns `true` for flat value sorts. Creusot
    ///   resolves ALL captures structurally regardless of capture kind
    ///   (backend/resolve.rs:164-177). (#2151 Phase 4)
    ///
    /// The structural resolve decomposition at the closure-env level handles the
    /// `resolve(env) = resolve(cap_0) && ...` pattern; the per-capture kind here
    /// controls whether a non-closure capture contributes `true` (shared-ref only)
    /// or a real resolve constraint (value/mutable-ref). For flat sorts,
    /// `resolve_term_for_sort` returns `Some(true)` because the final-prophecy
    /// equality (`*x == ^x`) is encoded separately in the caller's borrow model.
    /// Returns `None` when the supporting closure axiom had to be skipped.
    fn resolve_term_for_capture(
        &mut self,
        term: Term,
        sort: &Sort,
        kind: CaptureKind,
    ) -> Option<Term> {
        match kind {
            CaptureKind::ByRef => {
                // Shared-ref captures have no borrow to resolve.
                Some(self.solver.bool_const(true))
            }
            CaptureKind::ByValue | CaptureKind::ByMutRef => {
                // Value and mutable-ref captures: delegate to sort-level resolve.
                // Creusot resolves ALL captures structurally regardless of capture
                // kind (backend/resolve.rs:164-177). ByValue captures of closure
                // sorts must recursively decompose; for flat sorts resolve_term_for_sort
                // returns `Some(true)` (the borrow-model handles `*x == ^x` externally).
                // (#2151 Phase 4)
                self.resolve_term_for_sort(term, sort)
            }
            _ => self.resolve_term_for_sort(term, sort),
        }
    }

    pub(crate) fn assert_closure_resolve_axioms(&mut self) {
        let closure_sorts = self.collect_closure_struct_sorts();
        for sort in closure_sorts {
            let _ = self.ensure_closure_resolve_axiom_for_sort(&sort);
        }
    }
}
