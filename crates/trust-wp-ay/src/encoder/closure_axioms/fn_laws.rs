// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fn closure laws connecting `postcondition` to `postcondition_mut`,
//! `postcondition_once`, and `hist_inv`.
//!
//! These axioms establish the Fn trait hierarchy weakening chain:
//! - `fn_mut` law: Fn => FnMut biconditional
//! - `fn_once` law: Fn => FnOnce biconditional
//! - `fn_hist_inv`: per-capture identity constraints
//! - `postcondition_mut_hist_inv`: FnMut => hist_inv implication
//!
//! Reference: Creusot `FnExt` trait laws in `creusot-std/src/std/ops.rs:65-80`.

use std::sync::Arc;

use ay_dpll::api::{FuncDecl, Sort, Term};
use tracing::debug;
use trust_wp_core::formula::PureExpr;

use super::super::{
    closure_sorts::{closure_env_sort_name, RegisteredClosureStructSort},
    sort_context::{resolve_nameable_expr, DerivedKind},
    AYEncoder,
};
use crate::{error::EncodingError, shared_types::CaptureKind};

fn final_name_at_depth(base: &str, depth: usize) -> String {
    (0..depth).fold(base.to_string(), |name, _| {
        DerivedKind::Final.format_name(&name)
    })
}

fn receiver_depth_for_param(
    receiver: &PureExpr,
    param_name: &str,
    max_depth: usize,
) -> Option<usize> {
    let receiver_name = resolve_nameable_expr(receiver, None)?;
    let mut expected = param_name.to_string();
    for depth in 0..=max_depth {
        if receiver_name == expected {
            return Some(depth);
        }
        expected = DerivedKind::Final.format_name(&expected);
    }
    None
}

impl AYEncoder {
    /// Assert a ground instance of the `fn_mut` law for a specific
    /// `postcondition_mut(...)` expression.
    ///
    /// This bypasses ay-dpll's single-round E-matching gap when the only
    /// occurrence of `postcondition_mut` is the current negated goal. The
    /// asserted formula is a direct ground instance of the quantified law and
    /// is therefore sound. (#2556)
    pub(crate) fn assert_eager_fn_mut_ground_instantiation(
        &mut self,
        ensure: &PureExpr,
    ) -> Result<(), EncodingError> {
        let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = ensure
        else {
            debug!("[TRUST_WP_DEBUG] eager fn_mut skipped: non-method-call ensure={ensure:?}");
            return Ok(());
        };
        if method != "postcondition_mut" {
            debug!("[TRUST_WP_DEBUG] eager fn_mut skipped: method={method:?} ensure={ensure:?}");
            return Ok(());
        }
        if args.len() < 2 {
            debug!(
                "[TRUST_WP_DEBUG] eager fn_mut skipped: insufficient args ({}) for ensure={ensure:?}",
                args.len()
            );
            return Ok(());
        }
        if !self.closure_postcondition_flags().has_fn {
            debug!(
                "[TRUST_WP_DEBUG] eager fn_mut skipped: missing Fn postcondition symbol for ensure={ensure:?}"
            );
            return Ok(());
        }

        let normalized_receiver = super::normalize_closure_receiver(receiver.as_ref());
        let res_state = &args[args.len() - 2];
        let result = args.last().expect("postcondition_mut has >= 2 args");
        let mut post_args = args[..args.len() - 2].to_vec();
        post_args.push(result.clone());
        let post_expr = PureExpr::MethodCall {
            receiver: Arc::new(normalized_receiver.clone()),
            method: "postcondition".to_string(),
            args: post_args,
        };

        let mut_term = self.encode_pure(ensure)?;
        let post_term = self.encode_pure(&post_expr)?;
        let self_term = self.encode_pure(normalized_receiver)?;
        let res_state_term = self.encode_pure(res_state)?;
        let self_eq_res = self.eq_term(self_term, res_state_term);
        let rhs = self.solver.and(post_term, self_eq_res);
        let iff = self.eq_term(mut_term, rhs);

        debug!("[TRUST_WP_DEBUG] asserted eager ground fn_mut instantiation for {ensure:?}");

        self.assert_term(iff);
        Ok(())
    }

    /// Assert a ground instance of the `fn_once` law for a specific
    /// `postcondition_once(...)` expression.
    ///
    /// This bypasses ay-dpll's single-round E-matching gap when the only
    /// occurrence of `postcondition_once` is the current negated goal. The
    /// asserted formula is a direct ground instance of the quantified law and
    /// is therefore sound. (#2566)
    pub(crate) fn assert_eager_fn_once_ground_instantiation(
        &mut self,
        ensure: &PureExpr,
    ) -> Result<(), EncodingError> {
        let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = ensure
        else {
            return Ok(());
        };
        if method != "postcondition_once" || args.is_empty() {
            return Ok(());
        }
        if !self.closure_postcondition_flags().has_fn {
            return Ok(());
        }

        let normalized_receiver = super::normalize_closure_receiver(receiver.as_ref());
        let post_expr = PureExpr::MethodCall {
            receiver: Arc::new(normalized_receiver.clone()),
            method: "postcondition".to_string(),
            args: args.clone(),
        };

        let once_term = self.encode_pure(ensure)?;
        let post_term = self.encode_pure(&post_expr)?;
        let self_term = self.encode_pure(normalized_receiver)?;
        let self_sort = self.solver.get_sort(self_term);
        // Mirror the quantified fn_once law (assert_fn_once_law): skip the
        // entire eager axiom when the resolve term cannot be constructed.
        // The previous `.unwrap_or_else(|| true)` fabricated `resolve(self) = true`,
        // collapsing postcondition_once to postcondition — unsound. (#2566)
        let Some(resolve) = self.resolve_term_for_sort(self_term, &self_sort) else {
            return Ok(());
        };
        let rhs = self.solver.and(post_term, resolve);
        let iff = self.eq_term(once_term, rhs);

        debug!("[TRUST_WP_DEBUG] asserted eager ground fn_once instantiation for {ensure:?}");

        self.assert_term(iff);
        Ok(())
    }

    /// Resolve the term used to seed `result_view` from a closure body.
    ///
    /// Transparent adapters like `Copied` / `Cloned` should seed
    /// `result_view` from the adapter's inner body term when the body itself
    /// is an adapter wrapper. This keeps copied set adapters visible as their
    /// inner iterator relation.
    pub(crate) fn result_view_binding_term(
        &mut self,
        fallback: Term,
        body_expr: Option<&PureExpr>,
    ) -> Term {
        body_expr
            .and_then(|expr| {
                self.body_inner_term_for_transparent_adapter(expr)
                    .ok()
                    .flatten()
            })
            .unwrap_or(fallback)
    }

    /// Assert Fn closure laws connecting `postcondition` to `postcondition_mut`,
    /// `postcondition_once`, and `hist_inv`.
    ///
    /// When the Fn-trait `postcondition` predicate is used alongside `postcondition_mut`
    /// and/or `postcondition_once`, these laws establish the weakening chain:
    ///
    /// **`fn_mut` law** (Fn => FnMut):
    /// ```text
    /// forall self args res_state result.
    ///   postcondition_mut(self, args, res_state, result)
    ///     = (postcondition(self, args, result) && self == res_state)
    /// ```
    ///
    /// **`fn_once` law** (Fn => FnOnce):
    /// ```text
    /// forall self args result.
    ///   postcondition_once(self, args, result)
    ///     = (postcondition(self, args, result) && resolve(self))
    /// ```
    ///
    /// **`fn_hist_inv` law** (Fn identity invariant):
    /// ```text
    /// forall self res_state.
    ///   hist_inv(self, res_state) = (self == res_state)
    /// ```
    ///
    /// **`postcondition_mut_hist_inv`** (`FnMut` => `hist_inv)`:
    /// ```text
    /// forall self args res_state result.
    ///   postcondition_mut(self, args, res_state, result) ==> hist_inv(self, res_state)
    /// ```
    ///
    /// These axioms are only asserted when a `postcondition` (Fn-trait) symbol is
    /// declared alongside the corresponding `postcondition_mut`/`postcondition_once`
    /// symbols, indicating Fn-trait usage in the contract.
    ///
    /// Reference: Creusot `FnExt` trait laws in `creusot-std/src/std/ops.rs:65-80`.
    pub(crate) fn assert_fn_closure_laws(&mut self) {
        self.assert_closure_resolve_axioms();

        // Find all Fn-trait postcondition symbols: closure_postcondition_N_<sorts>
        let post_symbols: Vec<(String, FuncDecl)> = self
            .logic_funcs_iter()
            .filter(|(name, _)| {
                name.starts_with("closure_postcondition_")
                    && !name.starts_with("closure_postcondition_once_")
                    && !name.starts_with("closure_postcondition_mut_")
            })
            .map(|(name, decl)| (name.clone(), decl.clone()))
            .collect();

        for (post_name, post_decl) in &post_symbols {
            // Parse arity from: closure_postcondition_N_<sort_sig>
            let Some(suffix) = post_name.strip_prefix("closure_postcondition_") else {
                continue;
            };
            let parts: Vec<&str> = suffix.splitn(2, '_').collect();
            if parts.len() < 2 {
                continue;
            }
            let Ok(post_arity) = parts[0].parse::<usize>() else {
                continue;
            };
            let sort_sig = parts[1]; // e.g., "i_i_i"
            let sort_tags: Vec<&str> = sort_sig.split('_').collect();

            debug!(
                "[TRUST_WP_DEBUG] assert_fn_closure_laws considering {post_name} \
                     with post_arity={post_arity} sort_sig={sort_sig}"
            );

            self.assert_fn_mut_law_and_hist_inv(post_decl, post_arity, &sort_tags);
            self.assert_fn_once_law(post_decl, post_arity, sort_sig);
        }
    }

    /// Assert the `fn_mut` law, `postcondition_mut_hist_inv`, and `fn_hist_inv` axioms.
    ///
    /// Given a `postcondition` symbol (Fn-trait), connects it to the matching
    /// `postcondition_mut` symbol via biconditional, and establishes `hist_inv`.
    #[allow(clippy::too_many_lines)]
    fn assert_fn_mut_law_and_hist_inv(
        &mut self,
        post_decl: &FuncDecl,
        post_arity: usize,
        sort_tags: &[&str],
    ) {
        // Sort-tag validation removed (#2151 Phase 4): the `closure_sort_from_tag`
        // round-trip was lossy ("u" → Sort::Int, losing Datatype/Uninterpreted info)
        // and unnecessary — `post_decl.domain()` provides the actual UF domain sorts.
        // Callers already validated that the symbol was parseable by `parse_closure_signature`.

        let mut mut_sort_tags = sort_tags.to_vec();
        let insert_pos = mut_sort_tags.len() - 1; // before result
        mut_sort_tags.insert(insert_pos, sort_tags[0]); // res_state has closure self sort
        let mut_sort_sig = mut_sort_tags.join("_");
        let mut_arity = post_arity + 1;
        let mut_name = format!("closure_postcondition_mut_{mut_arity}_{mut_sort_sig}");

        let mut_domain: Vec<Sort> = {
            let mut domain = post_decl.domain().to_vec();
            let res_state_idx = post_arity - 1;
            domain.insert(res_state_idx, post_decl.domain()[0].clone());
            domain
        };
        let mut_decl = if let Some(existing) = self.logic_func_decl_cloned(&mut_name) {
            existing
        } else if self
            .var_names()
            .iter()
            .any(|name| name.ends_with("_current") || name.ends_with("_final"))
        {
            debug!("[TRUST_WP_DEBUG] fn_mut law: synthesizing missing mut decl {mut_name}");
            self.get_or_declare_logic_func(&mut_name, &mut_domain, Sort::Bool)
        } else {
            debug!("[TRUST_WP_DEBUG] fn_mut law skipped: missing mut decl {mut_name}");

            return;
        };

        // Use the declared UF domain sorts rather than tag-reconstructed sorts.
        // `closure_sort_from_tag("u")` returns `Sort::Int` but the UF domain
        // may contain `Sort::Uninterpreted("Unit")` — using the actual domain
        // sorts prevents sort mismatch panics in `solver.apply()`. (#2151)
        let mut_domain = mut_decl.domain();

        // fn_mut law: postcondition_mut(self, args, res_state, result)
        //   = (postcondition(self, args, result) && self == res_state)
        let mut vars = Vec::with_capacity(mut_arity);
        for (i, sort) in mut_domain.iter().enumerate() {
            let var = self
                .solver
                .fresh_var(&format!("fn_mut_law_{i}"), sort.clone());
            vars.push(var);
        }
        let Some(mut_term) = self.axiom_apply_tracked("fn_mut_law:mut", &mut_decl, &vars) else {
            debug!("[TRUST_WP_DEBUG] fn_mut law skipped: mut term apply failed for {mut_name}");

            return;
        };

        let res_state_idx = post_arity - 1;
        let mut post_args = Vec::with_capacity(post_arity);
        for (i, var) in vars.iter().enumerate() {
            if i != res_state_idx {
                post_args.push(*var);
            }
        }
        // The compatibility entry point admits only the authenticated
        // declaration's exact domain. If hybrid sort resolution made
        // post_decl diverge from mut_decl, omit this optional premise axiom and
        // record the conservative skip rather than minting an alias. (#2556)
        let Some(post_term) =
            self.axiom_apply_sort_adapted("fn_mut_law:post", post_decl, &post_args)
        else {
            debug!(
                "[TRUST_WP_DEBUG] fn_mut law skipped: post term apply failed; \
                     post_domain={:?} mut_domain={:?}",
                post_decl.domain(),
                mut_domain
            );

            return;
        };
        let self_sort = &mut_domain[0];
        let self_eq_res = self.eq_term(vars[0], vars[res_state_idx]);
        let rhs = self.solver.and(post_term, self_eq_res);
        // Both mut_term and rhs are Bool-sorted postcondition predicates.
        // Native solver equality now handles that case in the current ay pin.
        let iff = self.eq_term(mut_term, rhs);
        let axiom = self.solver.forall_with_triggers(&vars, iff, &[&[mut_term]]);
        self.solver.assert_term(axiom);

        debug!("[TRUST_WP_DEBUG] asserted fn_mut law for {mut_name}");

        // Declare hist_inv UF: uses self_sort for both params
        let self_tag = sort_tags[0];
        let hist_inv_name = format!("closure_hist_inv_2_{self_tag}_{self_tag}");
        let hist_inv_decl = if let Some(existing) = self.logic_func_decl_cloned(&hist_inv_name) {
            existing
        } else {
            let decl = self.solver.declare_fun(
                &hist_inv_name,
                &[self_sort.clone(), self_sort.clone()],
                Sort::Bool,
            );
            self.register_logic_func(hist_inv_name.clone(), decl.clone());
            decl
        };

        // postcondition_mut_hist_inv: postcondition_mut ==> hist_inv(self, res_state)
        let mut hist_vars = Vec::with_capacity(mut_arity);
        for (i, sort) in mut_domain.iter().enumerate() {
            let var = self
                .solver
                .fresh_var(&format!("hist_inv_law_{i}"), sort.clone());
            hist_vars.push(var);
        }
        let Some(mut_term2) = self.axiom_apply_tracked("hist_inv_law:mut", &mut_decl, &hist_vars)
        else {
            return;
        };
        let Some(hist_term) = self.axiom_apply_tracked(
            "hist_inv_law:hist",
            &hist_inv_decl,
            &[hist_vars[0], hist_vars[res_state_idx]],
        ) else {
            return;
        };
        let impl_term = self.solver.implies(mut_term2, hist_term);
        let axiom = self
            .solver
            .forall_with_triggers(&hist_vars, impl_term, &[&[mut_term2]]);
        self.solver.assert_term(axiom);

        // fn_hist_inv law (#758): per-capture decomposition for registered closure
        // sorts, identity fallback for opaque sorts.
        //
        // For registered closure sorts with capture-kind metadata:
        //   hist_inv(self, res_state) <=>
        //     (conjunction for each ByRef capture i: capture_i(res_state) == capture_i(self))
        //     (ByValue captures: unconstrained — omitted from conjunction)
        //     (ByMutRef captures: unconstrained — final prophecy preserved externally)
        //
        // For opaque sorts (no registered capture info):
        //   hist_inv(self, res_state) <=> (self == res_state)
        let hi_self = self.solver.fresh_var("fn_hist_inv_self", self_sort.clone());
        let hi_res = self.solver.fresh_var("fn_hist_inv_res", self_sort.clone());
        let hi_vars = vec![hi_self, hi_res];
        let Some(hi_term) = self.axiom_apply_tracked("fn_hist_inv:hist", &hist_inv_decl, &hi_vars)
        else {
            return;
        };

        let rhs = self.build_hist_inv_rhs(self_sort, hi_self, hi_res);

        let iff_hi = self.eq_term(hi_term, rhs);
        let axiom = self
            .solver
            .forall_with_triggers(&hi_vars, iff_hi, &[&[hi_term]]);
        self.solver.assert_term(axiom);
    }

    /// Build the right-hand side of the hist_inv axiom for a given closure sort (#758).
    ///
    /// If the sort is a registered closure struct with capture-kind metadata, produces
    /// a per-capture conjunction. Otherwise falls back to identity (`self == res_state`).
    fn build_hist_inv_rhs(&mut self, sort: &Sort, hi_self: Term, hi_res: Term) -> Term {
        // Compare by normalized sort name to handle both Sort::Uninterpreted
        // (from closure_sort_from_tag) and Sort::Datatype (from registration) (#2151).
        let Some(registered) = self.find_closure_struct_by_sort(sort) else {
            return self.eq_term(hi_self, hi_res);
        };

        let captures = registered.captures;
        if !captures
            .iter()
            .any(|(_, _, kind)| *kind != CaptureKind::ByValue)
        {
            // All captures are by-value: hist_inv is unconstrained.
            return self.solver.bool_const(true);
        }

        // Recover the sort's symbol suffix for selector lookup (#2151).
        let Some(sort_name) = closure_env_sort_name(sort) else {
            return self.eq_term(hi_self, hi_res);
        };
        let Some(suffix) = sort_name.strip_prefix("ClosureEnv_") else {
            return self.eq_term(hi_self, hi_res);
        };

        let mut conjuncts = Vec::new();
        for (index, (_, capture_sort, kind)) in captures.iter().enumerate() {
            if *kind != CaptureKind::ByRef {
                // ByValue/ByMutRef: unconstrained in hist_inv.
                continue;
            }
            // ByRef: shared reference — value must not change.
            let selector_name = format!("closure_capture_{suffix}_{index}");
            let Ok(self_field) =
                self.solver
                    .try_datatype_selector(&selector_name, hi_self, capture_sort.clone())
            else {
                return self.eq_term(hi_self, hi_res);
            };
            let Ok(res_field) =
                self.solver
                    .try_datatype_selector(&selector_name, hi_res, capture_sort.clone())
            else {
                return self.eq_term(hi_self, hi_res);
            };
            conjuncts.push(self.eq_term(self_field, res_field));
        }

        if conjuncts.is_empty() {
            self.solver.bool_const(true)
        } else {
            conjuncts
                .into_iter()
                .reduce(|acc, term| self.solver.and(acc, term))
                .unwrap_or_else(|| self.solver.bool_const(true))
        }
    }

    /// Assert standalone `postcondition_once` resolve laws for FnOnce-only closures (#2668).
    ///
    /// When `postcondition_once` is declared but NO `postcondition` (Fn-trait) symbol
    /// exists, the standard `fn_once` law (`postcondition_once = postcondition && resolve`)
    /// cannot fire — there is no `postcondition` to bridge through. This leaves the
    /// `postcondition_once` predicate unconstrained in the UF encoding, causing
    /// verification to fail or timeout.
    ///
    /// For each such standalone `postcondition_once` symbol, assert:
    /// ```text
    /// forall self args result.
    ///   postcondition_once(self, args, result) ==> resolve(self)
    /// ```
    ///
    /// This is weaker than the full `fn_once` law (which also conjoins postcondition),
    /// but it provides the critical resolve constraint that FnOnce call sites need
    /// to verify that the closure environment is properly resolved after consumption.
    ///
    /// Reference: Creusot `FnOnceExt::postcondition_once` law in
    /// `creusot-std/src/std/ops.rs:45-50`.
    pub(crate) fn assert_standalone_postcondition_once_laws(&mut self) {
        self.assert_closure_resolve_axioms();

        // Collect all postcondition_once symbols
        let once_symbols: Vec<(String, FuncDecl)> = self
            .logic_funcs_iter()
            .filter(|(name, _)| name.starts_with("closure_postcondition_once_"))
            .map(|(name, decl)| (name.clone(), decl.clone()))
            .collect();

        // Collect Fn-trait postcondition symbols for exclusion
        let fn_post_sort_sigs: Vec<String> = self
            .logic_func_names_iter()
            .filter(|name| {
                name.starts_with("closure_postcondition_")
                    && !name.starts_with("closure_postcondition_once_")
                    && !name.starts_with("closure_postcondition_mut_")
            })
            .filter_map(|name| {
                let suffix = name.strip_prefix("closure_postcondition_")?;
                let (_, sort_sig) = suffix.split_once('_')?;
                Some(sort_sig.to_string())
            })
            .collect();

        for (once_name, once_decl) in &once_symbols {
            let Some(suffix) = once_name.strip_prefix("closure_postcondition_once_") else {
                continue;
            };
            let Some((_, sort_sig)) = suffix.split_once('_') else {
                continue;
            };

            // Skip if a matching Fn-trait postcondition exists — the full fn_once
            // law (asserted by assert_fn_once_law) is strictly stronger.
            if fn_post_sort_sigs.iter().any(|sig| sig == sort_sig) {
                continue;
            }

            let once_domain = once_decl.domain();
            let once_arity = once_domain.len();
            if once_arity == 0 {
                continue;
            }

            let mut vars = Vec::with_capacity(once_arity);
            for (i, sort) in once_domain.iter().enumerate() {
                let var = self
                    .solver
                    .fresh_var(&format!("fn_once_standalone_{i}"), sort.clone());
                vars.push(var);
            }

            let Some(once_term) =
                self.axiom_apply_tracked("fn_once_standalone:once", once_decl, &vars)
            else {
                continue;
            };

            let Some(resolve_self) = self.resolve_term_for_sort(vars[0], &once_domain[0]) else {
                continue;
            };

            // postcondition_once(self, args, result) ==> resolve(self)
            let implication = self.solver.implies(once_term, resolve_self);
            let axiom = self
                .solver
                .forall_with_triggers(&vars, implication, &[&[once_term]]);
            self.solver.assert_term(axiom);

            debug!(
                "[TRUST_WP_DEBUG] asserted standalone postcondition_once resolve law for \
                     {once_name}: once_domain={:?}",
                once_domain
            );
        }
    }

    /// Assert the `fn_once` law connecting `postcondition` to `postcondition_once`.
    ///
    /// `postcondition_once(self, args, result) = (postcondition(self, args, result) && resolve(self))`
    fn assert_fn_once_law(&mut self, post_decl: &FuncDecl, post_arity: usize, sort_sig: &str) {
        let once_name = format!("closure_postcondition_once_{post_arity}_{sort_sig}");

        let Some(once_decl) = self.logic_func_decl_cloned(&once_name) else {
            debug!(
                "[TRUST_WP_DEBUG] fn_once law skipped: missing once decl {once_name}; \
                     registered logic_funcs: {:?}",
                self.logic_func_names_iter()
                    .filter(|n| n.contains("postcondition"))
                    .collect::<Vec<_>>()
            );

            return;
        };

        // Use the declared UF domain sorts rather than tag-reconstructed sorts.
        // `closure_sort_from_tag("u")` returns `Sort::Int` but the UF domain
        // may contain `Sort::Uninterpreted("Unit")` — using the actual domain
        // sorts prevents sort mismatch panics in `solver.apply()`. (#2151)
        let post_domain = post_decl.domain();

        let mut vars = Vec::with_capacity(post_arity);
        for (i, sort) in post_domain.iter().enumerate() {
            let var = self
                .solver
                .fresh_var(&format!("fn_once_law_{i}"), sort.clone());
            vars.push(var);
        }

        // The compatibility entry point fails closed when once_decl diverges
        // from the post_decl domain used to create these variables. (#2556)
        let Some(once_term) = self.axiom_apply_sort_adapted("fn_once_law:once", &once_decl, &vars)
        else {
            return;
        };
        let Some(post_term) = self.axiom_apply_tracked("fn_once_law:post", post_decl, &vars) else {
            return;
        };

        // For closure-structured self sorts, resolve(self) is decomposed
        // structurally via `closure_resolve_<suffix>` axioms.
        let Some(resolve_self) = self.resolve_term_for_sort(vars[0], &post_domain[0]) else {
            return;
        };
        let rhs = self.solver.and(post_term, resolve_self);

        // Both once_term (postcondition_once predicate) and rhs are Bool, and
        // native solver equality now handles that case in the current ay pin.
        let iff = self.eq_term(once_term, rhs);
        let axiom = self
            .solver
            .forall_with_triggers(&vars, iff, &[&[once_term]]);
        self.solver.assert_term(axiom);

        debug!(
            "[TRUST_WP_DEBUG] asserted fn_once law for {once_name}: \
                 post_domain={:?} once_domain={:?}",
            post_decl.domain(),
            once_decl.domain()
        );
    }

    /// Eagerly assert ground `fn_once` law instances for postcondition_once terms
    /// found in requires/ensures (#2668).
    ///
    /// When ay-dpll's single-round E-matching cannot chain the quantified fn_once
    /// law with a ground `postcondition_once(f, args, r)` call, the postcondition
    /// assumption (`postcondition(f, args, r)`) remains disconnected. This method
    /// pre-asserts the biconditional for ground postcondition_once calls found in
    /// the contract expressions, bridging `postcondition_once` to `postcondition`
    /// + `resolve(self)` directly.
    pub(crate) fn assert_eager_fn_once_for_ensures(
        &mut self,
        requires: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let exprs: Vec<&PureExpr> = requires.iter().collect();
        self.assert_eager_fn_once_for_ensures_exprs(&exprs)
    }

    /// Eagerly assert ground `fn_once` law instances for expressions (#2668).
    pub(crate) fn assert_eager_fn_once_for_ensures_exprs(
        &mut self,
        exprs: &[&PureExpr],
    ) -> Result<(), EncodingError> {
        // Collect ground postcondition_once calls
        let once_calls: Vec<(&PureExpr, &[PureExpr])> = exprs
            .iter()
            .filter_map(|expr| match expr {
                PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                } if method == "postcondition_once" => Some((receiver.as_ref(), args.as_slice())),
                _ => None,
            })
            .collect();

        if once_calls.is_empty() {
            return Ok(());
        }

        for (receiver, args) in once_calls {
            self.assert_eager_fn_once_ground_instantiation(&PureExpr::MethodCall {
                receiver: Arc::new(receiver.clone()),
                method: "postcondition_once".to_string(),
                args: args.to_vec(),
            })?;
        }

        Ok(())
    }

    /// Assert quantified postcondition_mut ensures axioms for closures with
    /// registered ensures expressions and struct sorts (#2668).
    ///
    /// For each closure that has both a registered body (with ensures) and a
    /// registered struct sort (with capture selectors), assert:
    ///
    /// ```text
    /// forall env args res_state result.
    ///   postcondition_mut(env, args, res_state, result)
    ///     ==> ensures[old(cap) := selector(env), cap := selector(res_state), result := result]
    /// ```
    ///
    /// This connects the abstract `postcondition_mut` UF predicate to concrete
    /// capture-level effects, mirroring Creusot's per-closure `postcondition_mut`
    /// definitions (e.g., `postcondition_mut_closure1` in `.coma` output).
    ///
    /// Without this axiom, the solver sees `postcondition_mut(f, args, f2, r)`
    /// as a pure UF symbol with no connection to what the closure actually does
    /// to its captures. The fn_mut_once law can chain `postcondition_once` to
    /// `postcondition_mut`, but without the ensures bridge, the mut-level effects
    /// remain opaque.
    pub(crate) fn assert_postcondition_mut_ensures_axioms(&mut self) {
        // Collect closure bodies that have ensures expressions.
        let candidates: Vec<(String, Vec<String>, Vec<PureExpr>)> = self
            .closure_state
            .bodies_with_def_ids()
            .filter_map(|(def_id, body_info)| {
                let ensures = body_info.ensures_exprs.as_ref()?;
                if ensures.is_empty() {
                    return None;
                }
                Some((
                    def_id.to_string(),
                    body_info.capture_names.clone(),
                    ensures.clone(),
                ))
            })
            .collect();

        if candidates.is_empty() {
            return;
        }

        for (def_id, capture_names, ensures_exprs) in candidates {
            if let Err(e) = self.assert_single_postcondition_mut_ensures_axiom(
                &def_id,
                &capture_names,
                &ensures_exprs,
            ) {
                debug!(
                    "[TRUST_WP_DEBUG] postcondition_mut ensures axiom failed for \
                         {def_id}: {e}"
                );
            }
        }
    }

    /// Assert quantified postcondition_once ensures axioms for FnOnce-only closures (#2668).
    ///
    /// When `postcondition_once` is declared but NO `postcondition` (Fn-trait) symbol
    /// exists, the closure effects are disconnected from the call site. This method
    /// bridges the gap by asserting:
    ///
    /// ```text
    /// forall env args result.
    ///   postcondition_once(env, args, result)
    ///     ==> ensures[old(cap) := selector(env), cap := selector(env), result := result]
    /// ```
    ///
    /// Unlike `postcondition_mut` ensures axioms, FnOnce has no separate `res_state`:
    /// the closure is consumed, so both `old(cap)` and `cap` bind to `selector(env)`.
    /// The final value of mutable captures is constrained by the ensures expressions
    /// themselves (e.g., `(^x)@ == old(x)@ + 1`).
    pub(crate) fn assert_postcondition_once_ensures_axioms(&mut self) {
        let candidates: Vec<(String, Vec<String>, Vec<PureExpr>)> = self
            .closure_state
            .bodies_with_def_ids()
            .filter_map(|(def_id, body_info)| {
                let ensures = body_info.ensures_exprs.as_ref()?;
                if ensures.is_empty() {
                    return None;
                }
                Some((
                    def_id.to_string(),
                    body_info.capture_names.clone(),
                    ensures.clone(),
                ))
            })
            .collect();

        if candidates.is_empty() {
            return;
        }

        for (def_id, capture_names, ensures_exprs) in candidates {
            if let Err(e) = self.assert_single_postcondition_once_ensures_axiom(
                &def_id,
                &capture_names,
                &ensures_exprs,
            ) {
                debug!(
                    "[TRUST_WP_DEBUG] postcondition_once ensures axiom failed for \
                         {def_id}: {e}"
                );
            }
        }
    }

    /// Assert a single postcondition_once ensures axiom for one closure.
    fn assert_single_postcondition_once_ensures_axiom(
        &mut self,
        def_id: &str,
        capture_names: &[String],
        ensures_exprs: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let registered = match self.closure_struct_sort_cloned(def_id) {
            Some(r) => r,
            None => return Ok(()),
        };
        let closure_sort = registered.sort.clone();

        let closure_sort_name = closure_env_sort_name(&closure_sort);
        let once_decl = self
            .logic_funcs_iter()
            .filter(|(name, _)| name.starts_with("closure_postcondition_once_"))
            .find(|(_, decl)| {
                let domain = decl.domain();
                if domain.is_empty() {
                    return false;
                }
                let decl_sort_name = closure_env_sort_name(&domain[0]);
                decl_sort_name == closure_sort_name && closure_sort_name.is_some()
            })
            .map(|(name, decl)| (name.clone(), decl.clone()));

        // Single-declaration fallback (#2668): when closures pass through generic
        // functions (e.g., call_fnonce<F: FnOnce()>), the receiver sort becomes Int
        // and closure_env_sort_name returns None, causing the sort-name match above
        // to fail. If there is exactly one postcondition_once UF declaration, use it
        // unconditionally — analogous to find_body_for_receiver's single_body shortcut.
        let once_decl = once_decl.or_else(|| {
            if closure_sort_name.is_some() {
                return None; // Sort-name was available; match genuinely failed.
            }
            let candidates: Vec<_> = self
                .logic_funcs_iter()
                .filter(|(name, _)| name.starts_with("closure_postcondition_once_"))
                .filter(|(_, decl)| !decl.domain().is_empty())
                .map(|(name, decl)| (name.clone(), decl.clone()))
                .collect();
            if candidates.len() == 1 {
                debug!(
                    "[TRUST_WP_DEBUG] postcondition_once ensures axiom: \
                         sort-name match failed (Int-sorted receiver), \
                         using single-declaration fallback: {}",
                    candidates[0].0
                );

                Some(candidates.into_iter().next().unwrap())
            } else {
                None
            }
        });

        let Some((once_name, once_decl)) = once_decl else {
            return Ok(());
        };

        let once_domain = once_decl.domain();
        let once_arity = once_domain.len();
        if once_arity < 2 {
            return Ok(()); // Need at least env, result.
        }

        let mut vars = Vec::with_capacity(once_arity);
        for (i, sort) in once_domain.iter().enumerate() {
            let var = self
                .solver
                .fresh_var(&format!("once_ensures_{i}"), sort.clone());
            vars.push(var);
        }

        let env_var = vars[0];
        let result_idx = once_arity - 1;
        let result_var = vars[result_idx];

        let Some(once_term) = self.axiom_apply_tracked("once_ensures:once", &once_decl, &vars)
        else {
            return Ok(());
        };

        // Bind captures to selector terms for ensures encoding.
        //
        // For truly consumed FnOnce closures (ByValue/ByRef captures), both old_
        // and bare names bind to selector(env) — there is no separate post-state.
        //
        // For ByMutRef captures (#2668 fix): the bare capture name must NOT bind
        // to selector(env), because the ensures expression uses bare names for the
        // post-call state (e.g., `x == old(x) + 1`). Binding both to selector(env)
        // creates `selector(env) == selector(env) + 1` — always false, making the
        // axiom vacuously satisfied and disconnecting postcondition_once from the
        // closure's actual mutation effects.
        //
        // Fix: use a Skolem FUNCTION `once_post_cap(env, args, result)` for each
        // ByMutRef capture's post-state, applied to the forall-bound variables.
        // This produces:
        //   forall env, result. postcondition_once(env, result) ==>
        //     once_post_x(env, result) == selector(env) + 1
        //
        // This is logically equivalent to the existential:
        //   forall env, result. postcondition_once(env, result) ==>
        //     exists sk_x. sk_x == selector(env) + 1
        //
        // IMPORTANT: the Skolem must NOT be a universally quantified variable in
        // the forall scope. A universally quantified Skolem would create:
        //   forall env, result, sk_x. postcondition_once(env, result) ==> sk_x == ...
        // which forces postcondition_once to be false (contradictory). (#2668)
        let suffix = super::super::closure_sorts::closure_symbol_suffix(def_id);
        let mut saved_bindings: Vec<(String, Option<Term>, Option<Sort>)> = Vec::new();

        for (index, cap_name) in capture_names.iter().enumerate() {
            if index >= registered.captures.len() {
                break;
            }
            let (_, ref capture_sort, ref capture_kind) = registered.captures[index];
            let selector_name = format!("closure_capture_{suffix}_{index}");

            let selector =
                self.solver
                    .try_datatype_selector(&selector_name, env_var, capture_sort.clone());
            if let Ok(cap_term) = selector {
                // old_{cap_name} → selector(env) (pre-call state for Old() refs)
                let old_name = format!("old_{cap_name}");
                let prev_term = self.insert_var(old_name.clone(), cap_term);
                let prev_sort = self.insert_var_sort(old_name.clone(), capture_sort.clone());
                saved_bindings.push((old_name.clone(), prev_term, prev_sort));

                let old_view_name = format!("{old_name}_view");
                let prev_view_term = self.insert_var(old_view_name.clone(), cap_term);
                let prev_view_sort =
                    self.insert_var_sort(old_view_name.clone(), capture_sort.clone());
                saved_bindings.push((old_view_name, prev_view_term, prev_view_sort));

                // For ByMutRef captures, introduce a Skolem FUNCTION for the
                // post-state. The function takes the forall-bound variables as
                // arguments so the ensures expression correctly constrains its
                // return value (e.g., `once_post_x(env, result) == selector(env) + 1`).
                // For non-mut captures, bind to selector(env) as before.
                let post_term = if matches!(capture_kind, CaptureKind::ByMutRef) {
                    // Declare a Skolem function: once_post_{cap_name}(once_domain) -> capture_sort
                    let skolem_fn_name = format!("once_post_{}_{suffix}_{index}", cap_name);
                    let skolem_domain: Vec<Sort> = once_domain.to_vec();
                    let skolem_fn = self.solver.declare_fun(
                        &skolem_fn_name,
                        &skolem_domain,
                        capture_sort.clone(),
                    );
                    self.register_logic_func(skolem_fn_name, skolem_fn.clone());
                    // Apply the Skolem function to the forall-bound variables
                    // (the original `vars` before any Skolem additions).
                    // vars[0..once_arity] are the original forall-bound vars.
                    let skolem_term = self.solver.apply(&skolem_fn, &vars[..once_arity]);
                    skolem_term
                } else {
                    cap_term
                };

                let prev_cap_term = self.insert_var(cap_name.clone(), post_term);
                let prev_cap_sort = self.insert_var_sort(cap_name.clone(), capture_sort.clone());
                saved_bindings.push((cap_name.clone(), prev_cap_term, prev_cap_sort));

                let cap_view_name = format!("{cap_name}_view");
                let prev_cap_view_term = self.insert_var(cap_view_name.clone(), post_term);
                let prev_cap_view_sort =
                    self.insert_var_sort(cap_view_name.clone(), capture_sort.clone());
                saved_bindings.push((cap_view_name, prev_cap_view_term, prev_cap_view_sort));
            }
        }

        let body_expr = self
            .closure_state
            .get_body(def_id)
            .and_then(|body_info| body_info.body.clone());

        // Bind result → result_var
        let result_sort = once_domain[result_idx].clone();
        let prev_result_term = self.insert_var("result".to_string(), result_var);
        let prev_result_sort = self.insert_var_sort("result".to_string(), result_sort.clone());
        saved_bindings.push(("result".to_string(), prev_result_term, prev_result_sort));

        let result_view_term =
            self.result_view_binding_term(result_var.clone(), body_expr.as_ref());
        let prev_result_view_term = self.insert_var("result_view".to_string(), result_view_term);
        let prev_result_view_sort =
            self.insert_var_sort("result_view".to_string(), result_sort.clone());
        saved_bindings.push((
            "result_view".to_string(),
            prev_result_view_term,
            prev_result_view_sort,
        ));

        // Encode ensures expressions
        let mut ensures_terms: Vec<Term> = Vec::new();
        if let Some(body_expr) = body_expr {
            if let Ok(body_term) = self.encode_pure(&body_expr) {
                ensures_terms.push(self.eq_term(result_var, body_term));
            }
        }
        let mut encode_failed = false;
        for ensure in ensures_exprs {
            match self.encode_pure(ensure) {
                Ok(term) => ensures_terms.push(term),
                Err(e) => {
                    debug!(
                        "[TRUST_WP_DEBUG] postcondition_once ensures axiom: \
                             encode failed for {ensure:?}: {e}"
                    );

                    encode_failed = true;
                    break;
                }
            }
        }

        // Restore all saved bindings
        for (name, prev_term, prev_sort) in saved_bindings {
            self.restore_var(&name, prev_term);
            self.restore_var_sort(&name, prev_sort);
        }

        if encode_failed || ensures_terms.is_empty() {
            return Ok(());
        }

        let ensures_conj = ensures_terms
            .into_iter()
            .reduce(|acc, term| self.solver.and(acc, term))
            .expect("ensures_terms is non-empty");

        // forall vars. postcondition_once(vars) ==> ensures_conjunction
        let implication = self.solver.implies(once_term, ensures_conj);
        let axiom = self
            .solver
            .forall_with_triggers(&vars, implication, &[&[once_term]]);
        self.solver.assert_term(axiom);

        debug!(
            "[TRUST_WP_DEBUG] asserted postcondition_once ensures axiom for \
                 {once_name} (def_id={def_id}, captures={:?})",
            capture_names
        );

        Ok(())
    }

    /// Assert a single postcondition_mut ensures axiom for one closure.
    fn assert_single_postcondition_mut_ensures_axiom(
        &mut self,
        def_id: &str,
        capture_names: &[String],
        ensures_exprs: &[PureExpr],
    ) -> Result<(), EncodingError> {
        // Step 1: Look up the registered closure struct sort for this def_id.
        let registered = match self.closure_struct_sort_cloned(def_id) {
            Some(r) => r,
            None => return Ok(()), // No struct sort registered — skip.
        };
        let closure_sort = registered.sort.clone();

        // Step 2: Find the matching postcondition_mut UF symbol whose domain[0]
        // matches this closure sort by normalized name comparison.
        let closure_sort_name = closure_env_sort_name(&closure_sort);
        let mut_decl = self
            .logic_funcs_iter()
            .filter(|(name, _)| name.starts_with("closure_postcondition_mut_"))
            .find(|(_, decl)| {
                let domain = decl.domain();
                if domain.is_empty() {
                    return false;
                }
                let decl_sort_name = closure_env_sort_name(&domain[0]);
                decl_sort_name == closure_sort_name && closure_sort_name.is_some()
            })
            .map(|(name, decl)| (name.clone(), decl.clone()));

        // Single-declaration fallback (#2668): when closures pass through generic
        // functions, the receiver sort becomes Int and closure_env_sort_name returns
        // None. If there is exactly one postcondition_mut UF declaration, use it.
        let mut_decl = mut_decl.or_else(|| {
            if closure_sort_name.is_some() {
                return None;
            }
            let candidates: Vec<_> = self
                .logic_funcs_iter()
                .filter(|(name, _)| name.starts_with("closure_postcondition_mut_"))
                .filter(|(_, decl)| !decl.domain().is_empty())
                .map(|(name, decl)| (name.clone(), decl.clone()))
                .collect();
            if candidates.len() == 1 {
                debug!(
                    "[TRUST_WP_DEBUG] postcondition_mut ensures axiom: \
                         sort-name match failed (Int-sorted receiver), \
                         using single-declaration fallback: {}",
                    candidates[0].0
                );

                Some(candidates.into_iter().next().unwrap())
            } else {
                None
            }
        });

        let Some((mut_name, mut_decl)) = mut_decl else {
            debug!(
                "[TRUST_WP_DEBUG] postcondition_mut ensures axiom: no matching mut \
                     decl for closure sort {:?} (def_id={def_id})",
                closure_sort_name
            );

            return Ok(());
        };

        let mut_domain = mut_decl.domain();
        let mut_arity = mut_domain.len();
        if mut_arity < 3 {
            return Ok(()); // Need at least env, res_state, result.
        }

        // Step 3: Create quantifier variables matching the postcondition_mut domain.
        // Layout: [env, param_0, ..., param_N-1, res_state, result]
        let mut vars = Vec::with_capacity(mut_arity);
        for (i, sort) in mut_domain.iter().enumerate() {
            let var = self
                .solver
                .fresh_var(&format!("mut_ensures_{i}"), sort.clone());
            vars.push(var);
        }

        let env_var = vars[0];
        let res_state_idx = mut_arity - 2;
        let result_idx = mut_arity - 1;
        let res_state_var = vars[res_state_idx];
        let result_var = vars[result_idx];

        // Step 4: Build postcondition_mut(env, args, res_state, result) application.
        let Some(mut_term) = self.axiom_apply_tracked("mut_ensures:mut", &mut_decl, &vars) else {
            return Ok(());
        };

        // Step 5: Temporarily bind capture names to selector terms and encode ensures.
        //
        // For each capture `i` with name `cap_name`:
        //   - `"old_{cap_name}"` → selector_i(env_var) (pre-call state, for Old() refs)
        //   - `"{cap_name}"` → selector_i(res_state_var) (post-call state)
        // Also bind `"result"` → result_var.
        //
        // Save/restore pattern: saves existing bindings, sets temporary ones,
        // encodes, then restores originals.
        let suffix = super::super::closure_sorts::closure_symbol_suffix(def_id);

        let mut saved_bindings: Vec<(String, Option<Term>, Option<Sort>)> = Vec::new();

        // Bind capture selectors
        for (index, cap_name) in capture_names.iter().enumerate() {
            if index >= registered.captures.len() {
                break;
            }
            let (_, ref capture_sort, _) = registered.captures[index];
            let selector_name = format!("closure_capture_{suffix}_{index}");

            // Bind old_{cap_name} → selector(env_var) for Old() references
            let old_name = format!("old_{cap_name}");
            let old_selector =
                self.solver
                    .try_datatype_selector(&selector_name, env_var, capture_sort.clone());
            if let Ok(old_term) = old_selector {
                let prev_term = self.insert_var(old_name.clone(), old_term);
                let prev_sort = self.insert_var_sort(old_name.clone(), capture_sort.clone());
                saved_bindings.push((old_name.clone(), prev_term, prev_sort));

                // Also bind old_{cap_name}_view → same term (#2668).
                //
                // Ensures expressions use `@` (View) on captures: `x@ == old(x)@ + 1`.
                // View(Old(Var("x"))) resolves to "old_x_view" via resolve_nameable_expr,
                // but the axiom only bound "old_x". For scalar captures (Int/Bool),
                // View is identity so the same selector term is correct.
                let old_view_name = format!("{old_name}_view");
                let prev_view_term = self.insert_var(old_view_name.clone(), old_term);
                let prev_view_sort =
                    self.insert_var_sort(old_view_name.clone(), capture_sort.clone());
                saved_bindings.push((old_view_name, prev_view_term, prev_view_sort));
            }

            // Bind cap_name → selector(res_state_var) for bare references (post-state)
            let res_selector = self.solver.try_datatype_selector(
                &selector_name,
                res_state_var,
                capture_sort.clone(),
            );
            if let Ok(res_term) = res_selector {
                let prev_term = self.insert_var(cap_name.clone(), res_term);
                let prev_sort = self.insert_var_sort(cap_name.clone(), capture_sort.clone());
                saved_bindings.push((cap_name.clone(), prev_term, prev_sort));

                // Also bind {cap_name}_view → same term (#2668).
                //
                // View(Var("x")) resolves to "x_view" via resolve_nameable_expr +
                // DerivedKind::View. For scalar captures, View is identity.
                let cap_view_name = format!("{cap_name}_view");
                let prev_view_term = self.insert_var(cap_view_name.clone(), res_term);
                let prev_view_sort =
                    self.insert_var_sort(cap_view_name.clone(), capture_sort.clone());
                saved_bindings.push((cap_view_name, prev_view_term, prev_view_sort));
            }
        }

        // Bind result → result_var
        let result_sort = mut_domain[result_idx].clone();
        let prev_result_term = self.insert_var("result".to_string(), result_var);
        let prev_result_sort = self.insert_var_sort("result".to_string(), result_sort.clone());
        saved_bindings.push(("result".to_string(), prev_result_term, prev_result_sort));

        let body_expr = self
            .closure_state
            .get_body(def_id)
            .and_then(|body_info| body_info.body.clone());

        // Also bind result_view → result_var (#2668).
        // Ensures may reference `result@` which resolves to "result_view".
        let result_view_term =
            self.result_view_binding_term(result_var.clone(), body_expr.as_ref());
        let prev_result_view_term = self.insert_var("result_view".to_string(), result_view_term);
        let prev_result_view_sort =
            self.insert_var_sort("result_view".to_string(), result_sort.clone());
        saved_bindings.push((
            "result_view".to_string(),
            prev_result_view_term,
            prev_result_view_sort,
        ));

        // Step 6: Encode ensures expressions and build conjunction.
        let mut ensures_terms: Vec<Term> = Vec::new();
        if let Some(body_expr) = body_expr {
            if let Ok(body_term) = self.encode_pure(&body_expr) {
                ensures_terms.push(self.eq_term(result_var, body_term));
            }
        }
        let mut encode_failed = false;
        for ensure in ensures_exprs {
            match self.encode_pure(ensure) {
                Ok(term) => ensures_terms.push(term),
                Err(e) => {
                    debug!(
                        "[TRUST_WP_DEBUG] postcondition_mut ensures axiom: \
                             encode failed for {ensure:?}: {e}"
                    );

                    encode_failed = true;
                    break;
                }
            }
        }

        // Step 7: Restore all saved bindings.
        for (name, prev_term, prev_sort) in saved_bindings {
            self.restore_var(&name, prev_term);
            self.restore_var_sort(&name, prev_sort);
        }

        if encode_failed || ensures_terms.is_empty() {
            return Ok(());
        }

        // Step 8: Build the conjunction of all ensures terms.
        let ensures_conj = ensures_terms
            .into_iter()
            .reduce(|acc, term| self.solver.and(acc, term))
            .expect("ensures_terms is non-empty");

        // Step 9: Assert the quantified axiom:
        // forall vars. postcondition_mut(vars) ==> ensures_conjunction
        let implication = self.solver.implies(mut_term, ensures_conj);
        let axiom = self
            .solver
            .forall_with_triggers(&vars, implication, &[&[mut_term]]);
        self.solver.assert_term(axiom);

        debug!(
            "[TRUST_WP_DEBUG] asserted postcondition_mut ensures axiom for \
                 {mut_name} (def_id={def_id}, captures={:?})",
            capture_names
        );

        Ok(())
    }

    /// Eagerly assert ground ensures effects for each ground `postcondition_once`
    /// call found in preconditions (#2668).
    ///
    /// The quantified `postcondition_once ==> ensures` axiom relies on ay-dpll's
    /// single-round E-matching, which may fire for one ground call but miss others
    /// when multiple sequential calls exist (e.g., `test_fnmut3` pattern: two
    /// `postcondition_once(tuple1(^^x), (), call_4)` and
    /// `postcondition_once(tuple1(^^^x), (), call_6)` calls).
    ///
    /// This method pre-instantiates the ensures effects for each ground call:
    ///   `postcondition_once(env, args, result)` is assumed as a precondition
    ///     ==> assert `ensures[captures := selectors(env), result := result]`
    ///
    /// This is sound because the ground assertion is a logical consequence of
    /// the quantified axiom applied to the specific ground terms.
    pub(crate) fn assert_eager_ground_postcondition_once_ensures(
        &mut self,
        requires: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let exprs: Vec<&PureExpr> = requires.iter().collect();
        self.assert_eager_ground_postcondition_once_ensures_for_exprs(&exprs)
    }

    /// Eagerly assert ground ensures effects for postcondition_once calls in
    /// arbitrary expression slices (body assumptions, etc.) (#2668).
    pub(crate) fn assert_eager_ground_postcondition_once_ensures_for_exprs(
        &mut self,
        exprs: &[&PureExpr],
    ) -> Result<(), EncodingError> {
        let once_calls = Self::collect_ground_postcondition_once_calls(exprs);
        if once_calls.is_empty() {
            return Ok(());
        }

        // Collect all closure bodies that have ensures.
        let candidates: Vec<(String, Option<String>, Vec<String>, Vec<PureExpr>)> = self
            .closure_state
            .bodies_with_def_ids()
            .filter_map(|(def_id, body_info)| {
                let ensures = body_info.ensures_exprs.as_ref()?;
                if ensures.is_empty() {
                    return None;
                }
                Some((
                    def_id.to_string(),
                    body_info.param_name.clone(),
                    body_info.capture_names.clone(),
                    ensures.clone(),
                ))
            })
            .collect();
        if candidates.is_empty() {
            return Ok(());
        }

        for (receiver, args) in once_calls {
            let direct_matches: Vec<_> = candidates
                .iter()
                .filter(|(_, param_name, _, _)| {
                    param_name.as_deref().is_some_and(|param_name| {
                        receiver_depth_for_param(receiver, param_name, 8).is_some()
                    })
                })
                .collect();
            let selected_candidates: Vec<_> = if direct_matches.is_empty() {
                if candidates.len() == 1 {
                    candidates.iter().collect()
                } else {
                    debug!(
                        "[TRUST_WP_DEBUG] eager ground once ensures skipped: \
                         receiver={receiver:?} did not uniquely match {} closure bodies",
                        candidates.len()
                    );
                    Vec::new()
                }
            } else {
                direct_matches
            };

            // For each ground postcondition_once call, assert effects only for
            // the closure body that matches the receiver. Falling back to every
            // registered body is unsound when multiple closures have ensures.
            for (def_id, param_name, capture_names, ensures_exprs) in selected_candidates {
                self.assert_eager_ground_once_ensures_for_call(
                    receiver,
                    args,
                    def_id,
                    param_name.as_deref(),
                    capture_names,
                    ensures_exprs,
                )?;
            }
        }
        Ok(())
    }

    /// Assert ground ensures effects for a single postcondition_once call.
    ///
    /// Given `postcondition_once(env_expr, arg_exprs..., result_expr)`:
    /// 1. Encode env_expr and result_expr as SMT terms
    /// 2. Bind capture selectors to env_expr
    /// 3. Encode ensures with those bindings
    /// 4. Assert `postcondition_once_term ==> ensures_conjunction`
    fn assert_eager_ground_once_ensures_for_call(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        def_id: &str,
        param_name: Option<&str>,
        capture_names: &[String],
        ensures_exprs: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let registered = match self.closure_struct_sort_cloned(def_id) {
            Some(r) => r,
            None => return Ok(()),
        };

        if args.is_empty() {
            return Ok(());
        }

        if self.assert_direct_ground_once_ensures_for_call(
            receiver,
            args,
            def_id,
            param_name,
            capture_names,
            ensures_exprs,
            &registered,
        )? {
            return Ok(());
        }

        // Encode the postcondition_once call as an assumption fact.
        // We encode it as a method call and assert the implication.
        let normalized_receiver = super::normalize_closure_receiver(receiver);
        let env_term = self.encode_pure(normalized_receiver)?;
        let result_expr = args
            .last()
            .expect("postcondition_once has at least result arg");
        let result_term = self.encode_pure(result_expr)?;

        let suffix = super::super::closure_sorts::closure_symbol_suffix(def_id);
        let mut saved_bindings: Vec<(
            String,
            Option<ay_dpll::api::Term>,
            Option<ay_dpll::api::Sort>,
        )> = Vec::new();

        // Bind captures to selector terms applied to the concrete env term.
        for (index, cap_name) in capture_names.iter().enumerate() {
            if index >= registered.captures.len() {
                break;
            }
            let (_, ref capture_sort, ref capture_kind) = registered.captures[index];
            let selector_name = format!("closure_capture_{suffix}_{index}");

            let selector =
                self.solver
                    .try_datatype_selector(&selector_name, env_term, capture_sort.clone());
            if let Ok(cap_term) = selector {
                // old_{cap_name} → selector(env) (pre-call state)
                let old_name = format!("old_{cap_name}");
                let prev_term = self.insert_var(old_name.clone(), cap_term);
                let prev_sort = self.insert_var_sort(old_name.clone(), capture_sort.clone());
                saved_bindings.push((old_name.clone(), prev_term, prev_sort));

                let old_view_name = format!("{old_name}_view");
                let prev_view_term = self.insert_var(old_view_name.clone(), cap_term);
                let prev_view_sort =
                    self.insert_var_sort(old_view_name.clone(), capture_sort.clone());
                saved_bindings.push((old_view_name, prev_view_term, prev_view_sort));

                // For ByMutRef captures, we need a fresh Skolem constant for the
                // post-state (not bound to selector(env)). For non-mut captures,
                // bind to selector(env) as the post-state is unchanged.
                let post_term = if matches!(capture_kind, CaptureKind::ByMutRef) {
                    // Use a ground Skolem constant for this specific call.
                    // We can't use a Skolem function here (as in the quantified axiom)
                    // because this is a ground instantiation. `fresh_var` generates
                    // a uniquely-named variable.
                    let skolem_name = format!("eager_once_post_{}_{suffix}_{index}", cap_name);
                    let skolem_var = self.solver.fresh_var(&skolem_name, capture_sort.clone());
                    skolem_var
                } else {
                    cap_term
                };

                let prev_cap_term = self.insert_var(cap_name.clone(), post_term);
                let prev_cap_sort = self.insert_var_sort(cap_name.clone(), capture_sort.clone());
                saved_bindings.push((cap_name.clone(), prev_cap_term, prev_cap_sort));

                let cap_view_name = format!("{cap_name}_view");
                let prev_cap_view_term = self.insert_var(cap_view_name.clone(), post_term);
                let prev_cap_view_sort =
                    self.insert_var_sort(cap_view_name.clone(), capture_sort.clone());
                saved_bindings.push((cap_view_name, prev_cap_view_term, prev_cap_view_sort));
            }
        }

        // Bind result
        let result_sort = self.solver.get_sort(result_term);
        let prev_result_term = self.insert_var("result".to_string(), result_term);
        let prev_result_sort = self.insert_var_sort("result".to_string(), result_sort.clone());
        saved_bindings.push(("result".to_string(), prev_result_term, prev_result_sort));

        let prev_result_view_term = self.insert_var("result_view".to_string(), result_term);
        let prev_result_view_sort =
            self.insert_var_sort("result_view".to_string(), result_sort.clone());
        saved_bindings.push((
            "result_view".to_string(),
            prev_result_view_term,
            prev_result_view_sort,
        ));

        // Encode ensures expressions
        let mut ensures_terms = Vec::new();
        let mut encode_failed = false;
        for ensure in ensures_exprs {
            match self.encode_pure(ensure) {
                Ok(term) => ensures_terms.push(term),
                Err(e) => {
                    debug!(
                            "[TRUST_WP_DEBUG] eager ground once ensures: encode failed for {ensure:?}: {e}"
                        );

                    encode_failed = true;
                    break;
                }
            }
        }

        // Restore all saved bindings
        for (name, prev_term, prev_sort) in saved_bindings {
            self.restore_var(&name, prev_term);
            self.restore_var_sort(&name, prev_sort);
        }

        if encode_failed || ensures_terms.is_empty() {
            return Ok(());
        }

        let ensures_conj = ensures_terms
            .into_iter()
            .reduce(|acc, term| self.solver.and(acc, term))
            .expect("ensures_terms is non-empty");

        // Encode the postcondition_once call as a term for the implication guard.
        let once_call = PureExpr::MethodCall {
            receiver: std::sync::Arc::new(receiver.clone()),
            method: "postcondition_once".to_string(),
            args: args.to_vec(),
        };
        let once_term = self.encode_pure(&once_call)?;

        // Assert: postcondition_once(env, args, result) ==> ensures_conjunction
        let implication = self.solver.implies(once_term, ensures_conj);
        self.solver.assert_term(implication);

        debug!(
            "[TRUST_WP_DEBUG] asserted eager ground postcondition_once ensures for \
                 def_id={def_id}, receiver={receiver:?}"
        );

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn assert_direct_ground_once_ensures_for_call(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        def_id: &str,
        param_name: Option<&str>,
        capture_names: &[String],
        ensures_exprs: &[PureExpr],
        registered: &RegisteredClosureStructSort,
    ) -> Result<bool, EncodingError> {
        const MAX_DIRECT_ONCE_DEPTH: usize = 8;

        let Some(param_name) = param_name else {
            return Ok(false);
        };
        let Some(depth) = receiver_depth_for_param(receiver, param_name, MAX_DIRECT_ONCE_DEPTH)
        else {
            return Ok(false);
        };

        let result_expr = args
            .last()
            .expect("postcondition_once has at least result arg");
        let result_term = self.encode_pure(result_expr)?;

        let mut saved_bindings: Vec<(
            String,
            Option<ay_dpll::api::Term>,
            Option<ay_dpll::api::Sort>,
        )> = Vec::new();

        for (index, cap_name) in capture_names.iter().enumerate() {
            if index >= registered.captures.len() {
                break;
            }

            let (_, ref capture_sort, ref capture_kind) = registered.captures[index];
            let pre_name = final_name_at_depth(cap_name, depth);
            let post_name = if matches!(capture_kind, CaptureKind::ByMutRef) {
                final_name_at_depth(cap_name, depth + 1)
            } else {
                pre_name.clone()
            };

            let pre_term = self.get_or_declare_var(&pre_name, capture_sort.clone())?;
            let post_term = self.get_or_declare_var(&post_name, capture_sort.clone())?;

            let old_name = format!("old_{cap_name}");
            let prev_term = self.insert_var(old_name.clone(), pre_term);
            let prev_sort = self.insert_var_sort(old_name.clone(), capture_sort.clone());
            saved_bindings.push((old_name.clone(), prev_term, prev_sort));

            let old_view_name = format!("{old_name}_view");
            let prev_view_term = self.insert_var(old_view_name.clone(), pre_term);
            let prev_view_sort = self.insert_var_sort(old_view_name.clone(), capture_sort.clone());
            saved_bindings.push((old_view_name, prev_view_term, prev_view_sort));

            let prev_cap_term = self.insert_var(cap_name.clone(), post_term);
            let prev_cap_sort = self.insert_var_sort(cap_name.clone(), capture_sort.clone());
            saved_bindings.push((cap_name.clone(), prev_cap_term, prev_cap_sort));

            let cap_view_name = format!("{cap_name}_view");
            let prev_cap_view_term = self.insert_var(cap_view_name.clone(), post_term);
            let prev_cap_view_sort =
                self.insert_var_sort(cap_view_name.clone(), capture_sort.clone());
            saved_bindings.push((cap_view_name, prev_cap_view_term, prev_cap_view_sort));
        }

        let result_sort = self.solver.get_sort(result_term);
        let prev_result_term = self.insert_var("result".to_string(), result_term);
        let prev_result_sort = self.insert_var_sort("result".to_string(), result_sort.clone());
        saved_bindings.push(("result".to_string(), prev_result_term, prev_result_sort));

        let prev_result_view_term = self.insert_var("result_view".to_string(), result_term);
        let prev_result_view_sort = self.insert_var_sort("result_view".to_string(), result_sort);
        saved_bindings.push((
            "result_view".to_string(),
            prev_result_view_term,
            prev_result_view_sort,
        ));

        let mut ensures_terms = Vec::new();
        if let Some(body_expr) = self
            .closure_state
            .get_body(def_id)
            .and_then(|body_info| body_info.body.clone())
        {
            if let Ok(body_term) = self.encode_pure(&body_expr) {
                ensures_terms.push(self.eq_term(result_term, body_term));
            }
        }

        let mut encode_failed = false;
        for ensure in ensures_exprs {
            match self.encode_pure(ensure) {
                Ok(term) => ensures_terms.push(term),
                Err(e) => {
                    debug!(
                        "[TRUST_WP_DEBUG] direct ground once ensures: encode failed for {ensure:?}: {e}"
                    );
                    encode_failed = true;
                    break;
                }
            }
        }

        for (name, prev_term, prev_sort) in saved_bindings {
            self.restore_var(&name, prev_term);
            self.restore_var_sort(&name, prev_sort);
        }

        if encode_failed || ensures_terms.is_empty() {
            return Ok(false);
        }

        let ensures_conj = ensures_terms
            .into_iter()
            .reduce(|acc, term| self.solver.and(acc, term))
            .expect("ensures_terms is non-empty");

        // The collector returns top-level positive postcondition_once facts from
        // already-asserted requires/body-assumption slices. Assert the directly
        // projected consequence eagerly so sequential ByMutRef calls do not rely
        // on mixed datatype-selector/arithmetic reasoning.
        self.solver.assert_term(ensures_conj);
        debug!(
            "[TRUST_WP_DEBUG] asserted direct ground postcondition_once ensures for \
                 def_id={def_id}, receiver={receiver:?}, depth={depth}"
        );

        Ok(true)
    }

    /// Eagerly assert ground ensures effects for each ground `postcondition_mut`
    /// call found in preconditions (#2668).
    ///
    /// Mirrors `assert_eager_ground_postcondition_once_ensures` but for
    /// postcondition_mut calls. The postcondition_mut layout is:
    /// `postcondition_mut(env, args..., res_state, result)`.
    ///
    /// For each ground call, asserts:
    ///   `postcondition_mut(env, args, res_state, result)` ==>
    ///     ensures[old_cap := selector(env), cap := selector(res_state), result := result]
    pub(crate) fn assert_eager_ground_postcondition_mut_ensures(
        &mut self,
        requires: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let exprs: Vec<&PureExpr> = requires.iter().collect();
        self.assert_eager_ground_postcondition_mut_ensures_for_exprs(&exprs)
    }

    /// Eagerly assert ground ensures effects for postcondition_mut calls.
    pub(crate) fn assert_eager_ground_postcondition_mut_ensures_for_exprs(
        &mut self,
        exprs: &[&PureExpr],
    ) -> Result<(), EncodingError> {
        let mut_calls: Vec<(&PureExpr, &[PureExpr])> = exprs
            .iter()
            .filter_map(|expr| match expr {
                PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                } if method == "postcondition_mut" => Some((receiver.as_ref(), args.as_slice())),
                _ => None,
            })
            .collect();

        if mut_calls.is_empty() {
            return Ok(());
        }

        let candidates: Vec<(String, Vec<String>, Vec<PureExpr>)> = self
            .closure_state
            .bodies_with_def_ids()
            .filter_map(|(def_id, body_info)| {
                let ensures = body_info.ensures_exprs.as_ref()?;
                if ensures.is_empty() {
                    return None;
                }
                Some((
                    def_id.to_string(),
                    body_info.capture_names.clone(),
                    ensures.clone(),
                ))
            })
            .collect();
        if candidates.is_empty() {
            return Ok(());
        }

        for (receiver, args) in mut_calls {
            for (def_id, capture_names, ensures_exprs) in &candidates {
                self.assert_eager_ground_mut_ensures_for_call(
                    receiver,
                    args,
                    def_id,
                    capture_names,
                    ensures_exprs,
                )?;
            }
        }
        Ok(())
    }

    /// Assert ground ensures effects for a single postcondition_mut call.
    fn assert_eager_ground_mut_ensures_for_call(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        def_id: &str,
        capture_names: &[String],
        ensures_exprs: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let registered = match self.closure_struct_sort_cloned(def_id) {
            Some(r) => r,
            None => return Ok(()),
        };

        // postcondition_mut args: [param_args..., res_state, result]
        if args.len() < 2 {
            return Ok(());
        }

        let normalized_receiver = super::normalize_closure_receiver(receiver);
        let env_term = self.encode_pure(normalized_receiver)?;
        let res_state_idx = args.len() - 2;
        let result_idx = args.len() - 1;
        let res_state_expr = &args[res_state_idx];
        let result_expr = &args[result_idx];
        let res_state_term = self.encode_pure(res_state_expr)?;
        let result_term = self.encode_pure(result_expr)?;

        let suffix = super::super::closure_sorts::closure_symbol_suffix(def_id);
        let mut saved_bindings: Vec<(
            String,
            Option<ay_dpll::api::Term>,
            Option<ay_dpll::api::Sort>,
        )> = Vec::new();

        for (index, cap_name) in capture_names.iter().enumerate() {
            if index >= registered.captures.len() {
                break;
            }
            let (_, ref capture_sort, _) = registered.captures[index];
            let selector_name = format!("closure_capture_{suffix}_{index}");

            // old_{cap_name} → selector(env) (pre-call state)
            let old_selector =
                self.solver
                    .try_datatype_selector(&selector_name, env_term, capture_sort.clone());
            if let Ok(old_term) = old_selector {
                let old_name = format!("old_{cap_name}");
                let prev_term = self.insert_var(old_name.clone(), old_term);
                let prev_sort = self.insert_var_sort(old_name.clone(), capture_sort.clone());
                saved_bindings.push((old_name.clone(), prev_term, prev_sort));

                let old_view_name = format!("{old_name}_view");
                let prev_view_term = self.insert_var(old_view_name.clone(), old_term);
                let prev_view_sort =
                    self.insert_var_sort(old_view_name.clone(), capture_sort.clone());
                saved_bindings.push((old_view_name, prev_view_term, prev_view_sort));
            }

            // cap_name → selector(res_state) (post-call state)
            let res_selector = self.solver.try_datatype_selector(
                &selector_name,
                res_state_term,
                capture_sort.clone(),
            );
            if let Ok(res_term) = res_selector {
                let prev_term = self.insert_var(cap_name.clone(), res_term);
                let prev_sort = self.insert_var_sort(cap_name.clone(), capture_sort.clone());
                saved_bindings.push((cap_name.clone(), prev_term, prev_sort));

                let cap_view_name = format!("{cap_name}_view");
                let prev_cap_view_term = self.insert_var(cap_view_name.clone(), res_term);
                let prev_cap_view_sort =
                    self.insert_var_sort(cap_view_name.clone(), capture_sort.clone());
                saved_bindings.push((cap_view_name, prev_cap_view_term, prev_cap_view_sort));
            }
        }

        // Bind result
        let result_sort = self.solver.get_sort(result_term);
        let prev_result_term = self.insert_var("result".to_string(), result_term);
        let prev_result_sort = self.insert_var_sort("result".to_string(), result_sort.clone());
        saved_bindings.push(("result".to_string(), prev_result_term, prev_result_sort));

        let prev_result_view_term = self.insert_var("result_view".to_string(), result_term);
        let prev_result_view_sort =
            self.insert_var_sort("result_view".to_string(), result_sort.clone());
        saved_bindings.push((
            "result_view".to_string(),
            prev_result_view_term,
            prev_result_view_sort,
        ));

        // Encode ensures
        let mut ensures_terms = Vec::new();
        let mut encode_failed = false;
        for ensure in ensures_exprs {
            match self.encode_pure(ensure) {
                Ok(term) => ensures_terms.push(term),
                Err(e) => {
                    debug!(
                            "[TRUST_WP_DEBUG] eager ground mut ensures: encode failed for {ensure:?}: {e}"
                        );

                    encode_failed = true;
                    break;
                }
            }
        }

        // Restore bindings
        for (name, prev_term, prev_sort) in saved_bindings {
            self.restore_var(&name, prev_term);
            self.restore_var_sort(&name, prev_sort);
        }

        if encode_failed || ensures_terms.is_empty() {
            return Ok(());
        }

        let ensures_conj = ensures_terms
            .into_iter()
            .reduce(|acc, term| self.solver.and(acc, term))
            .expect("ensures_terms is non-empty");

        // Encode the postcondition_mut call as a term
        let mut_call = PureExpr::MethodCall {
            receiver: std::sync::Arc::new(receiver.clone()),
            method: "postcondition_mut".to_string(),
            args: args.to_vec(),
        };
        let mut_term = self.encode_pure(&mut_call)?;

        let implication = self.solver.implies(mut_term, ensures_conj);
        self.solver.assert_term(implication);

        debug!(
            "[TRUST_WP_DEBUG] asserted eager ground postcondition_mut ensures for \
                 def_id={def_id}, receiver={receiver:?}"
        );

        Ok(())
    }
}
