// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Eager instantiation of fn_mut_once reverse axiom for ground postcondition_once calls,
//! and synthetic ground postcondition_mut call generation from postcondition_once requires.

use ay_dpll::api::Sort;
use tracing::debug;
use trust_wp_core::formula::PureExpr;

use super::super::AYEncoder;
use crate::error::EncodingError;

impl AYEncoder {
    /// Eagerly instantiate the reverse fn_mut_once axiom for ground postcondition_once
    /// terms found in the preconditions.
    ///
    /// ay's E-matching performs one round per check-sat, so axiom chains requiring
    /// two steps (reverse axiom fires -> universal postcondition instantiates) cannot
    /// converge in a single pass. This method pre-instantiates the reverse axiom's
    /// conclusion for known ground postcondition_once calls, making the ground
    /// `postcondition_mut(self, args, witness(...), result)` term available for the
    /// first E-matching round (#970).
    ///
    /// Must be called after preconditions have been encoded. This path declares
    /// the Skolem witness functions it needs, so the quantified FnMut/FnOnce
    /// bridge can remain opt-in on hot verification paths.
    pub(crate) fn assert_eager_fn_mut_once_instantiations(
        &mut self,
        requires: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let exprs: Vec<&PureExpr> = requires.iter().collect();
        self.assert_eager_fn_mut_once_instantiations_for_exprs(&exprs)
    }

    /// Eagerly instantiate the reverse fn_mut_once axiom for ground
    /// `postcondition_once` terms found in arbitrary expressions that are
    /// already asserted in the current VC (for example body `LetAssume`
    /// assumptions). (#2556)
    pub(crate) fn assert_eager_fn_mut_once_instantiations_for_exprs(
        &mut self,
        exprs: &[&PureExpr],
    ) -> Result<(), EncodingError> {
        let once_calls = Self::collect_ground_postcondition_once_calls(exprs);
        if once_calls.is_empty() {
            debug!("[TRUST_WP_DEBUG] eager fn_mut_once skipped: no ground once calls");

            return Ok(());
        }
        // Pre-collect postcondition_mut entries once (#2278 F3).
        let mut_entries = self.collect_postcondition_mut_entries();

        for (receiver, args) in once_calls {
            // Build the sort signature to find the corresponding witness function
            let normalized_receiver = super::normalize_closure_receiver(receiver);
            let param_sorts: Vec<Sort> = std::iter::once(normalized_receiver)
                .chain(args.iter())
                .map(|expr| self.infer_expr_sort_with_context(expr, None))
                .collect();
            let once_arity = param_sorts.len();
            let once_tags = param_sorts
                .iter()
                .map(Self::closure_sort_tag)
                .collect::<Vec<_>>();
            let sort_sig = once_tags.join("_");
            let once_name = format!("closure_postcondition_once_{once_arity}_{sort_sig}");
            let witness_sorts = self
                .logic_func_decl_cloned(&once_name)
                .map(|decl| decl.domain().to_vec())
                .unwrap_or_else(|| param_sorts.clone());
            let insert_pos = once_arity - 1;
            let mut_candidates =
                Self::matching_postcondition_mut_symbols(&mut_entries, once_arity, &once_tags);
            if mut_candidates.is_empty() {
                debug!(
                        "[TRUST_WP_DEBUG] eager fn_mut_once: no mut candidates for once_tags={once_tags:?}"
                    );

                continue;
            }

            // Encode the ground arguments
            let receiver_term = self.encode_pure_impl(normalized_receiver, None)?;
            let arg_terms: Vec<ay_dpll::api::Term> = args
                .iter()
                .map(|a| self.encode_pure_impl(a, None))
                .collect::<Result<Vec<_>, _>>()?;

            for (_mut_name, mut_decl, mut_tags, mut_sorts) in mut_candidates {
                let res_state_tag = &mut_tags[insert_pos];
                let res_state_sort = mut_sorts[insert_pos].clone();
                let preferred_witness_name =
                    Self::fn_mut_once_witness_name(once_arity, &sort_sig, res_state_tag);
                let legacy_witness_name = format!("fn_mut_once_witness_{once_arity}_{sort_sig}");
                let witness_name = if self
                    .logic_func_decl_cloned(&preferred_witness_name)
                    .is_some()
                {
                    preferred_witness_name
                } else if self.logic_func_decl_cloned(&legacy_witness_name).is_some() {
                    legacy_witness_name
                } else {
                    preferred_witness_name
                };
                let witness_fn = self.get_or_declare_fn_mut_once_witness(
                    &witness_name,
                    &witness_sorts,
                    &res_state_sort,
                );

                // Build witness(receiver, args...) term
                let mut witness_args: Vec<ay_dpll::api::Term> = vec![receiver_term];
                witness_args.extend(arg_terms.iter().copied());
                let Some(witness_term) = self.axiom_apply_tracked(
                    "eager_fn_mut_once:witness",
                    &witness_fn,
                    &witness_args,
                ) else {
                    debug!("[TRUST_WP_DEBUG] eager fn_mut_once: witness apply failed");

                    continue;
                };

                // Build postcondition_mut(receiver, args..., witness(...), result) term
                // The result is the last arg, the witness is inserted before it.
                // split_last: "the leading args, and the result". Indexing
                // `len() - 1` underflows on an empty arg vector; this fails
                // closed the way the rest of this loop does.
                let Some((result_term, leading_terms)) = arg_terms.split_last() else {
                    continue;
                };
                let mut mut_args: Vec<ay_dpll::api::Term> = vec![receiver_term];
                mut_args.extend_from_slice(leading_terms);
                mut_args.push(witness_term);
                mut_args.push(*result_term); // result
                let Some(mut_term) =
                    self.axiom_apply_tracked("eager_fn_mut_once:mut", &mut_decl, &mut_args)
                else {
                    debug!("[TRUST_WP_DEBUG] eager fn_mut_once: mut apply failed");

                    continue;
                };

                // `once_calls` are collected from `requires`, so each call is already a
                // ground assumption in this VC. Assert the Skolemized reverse-law
                // conclusion directly:
                //   postcondition_mut(self, args, witness(...), result)
                //   resolve(witness(...))
                // This avoids relying on one more implication instantiation step and
                // preserves Creusot's fn_mut_once witness-resolve contract for eager
                // instantiation paths (#970, closures/07_mutable_capture).
                self.solver.assert_term(mut_term);
                if let Some(resolve_term) =
                    self.resolve_term_for_sort(witness_term, &res_state_sort)
                {
                    self.solver.assert_term(resolve_term);
                }

                debug!(
                        "[TRUST_WP_DEBUG] eager fn_mut_once asserted mut witness for once_tags={once_tags:?}"
                    );
            }
        }

        Ok(())
    }

    /// Eagerly instantiate the forward fn_mut_once axiom for ground
    /// `postcondition_mut` terms found in preconditions.
    ///
    /// ay v0.2.0 E-matching may fail to instantiate the quantified forward law
    /// `forall vars. postcondition_mut(vars) => postcondition_once(vars)`.
    /// This pre-asserts the conclusion for known ground postcondition_mut calls,
    /// making the `postcondition_once(self, args, result)` fact directly available.
    pub(crate) fn assert_eager_fn_mut_once_forward_instantiations(
        &mut self,
        requires: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let exprs: Vec<&PureExpr> = requires.iter().collect();
        self.assert_eager_fn_mut_once_forward_instantiations_for_exprs(&exprs)
    }

    pub(crate) fn assert_eager_fn_mut_once_forward_instantiations_for_exprs(
        &mut self,
        exprs: &[&PureExpr],
    ) -> Result<(), EncodingError> {
        let mut_calls = Self::collect_ground_postcondition_mut_calls(exprs);
        if mut_calls.is_empty() {
            return Ok(());
        }

        let once_entries: Vec<(String, ay_dpll::api::FuncDecl)> = self
            .logic_funcs_iter()
            .filter(|(name, _)| name.starts_with("closure_postcondition_once_"))
            .map(|(name, decl)| (name.clone(), decl.clone()))
            .collect();
        if once_entries.is_empty() {
            return Ok(());
        }

        for (receiver, args) in mut_calls {
            let normalized_receiver = super::normalize_closure_receiver(receiver);
            // postcondition_mut args: [arg1, ..., argN, res_state, result]
            // postcondition_once args: [arg1, ..., argN, result]
            // We need to drop res_state (second-to-last) to form the once call.
            if args.len() < 2 {
                continue;
            }
            let once_args_exprs: Vec<&PureExpr> = args[..args.len() - 2]
                .iter()
                .chain(std::iter::once(args.last().unwrap()))
                .collect();
            let param_sorts: Vec<Sort> = std::iter::once(normalized_receiver)
                .chain(once_args_exprs.iter().copied())
                .map(|expr| self.infer_expr_sort_with_context(expr, None))
                .collect();
            let once_tags: Vec<String> = param_sorts.iter().map(Self::closure_sort_tag).collect();
            let once_arity = param_sorts.len();
            let expected_name = format!(
                "closure_postcondition_once_{once_arity}_{}",
                once_tags.join("_")
            );
            let Some(once_decl) = once_entries
                .iter()
                .find(|(name, _)| *name == expected_name)
                .map(|(_, decl)| decl.clone())
            else {
                continue;
            };

            let receiver_term = self.encode_pure_impl(normalized_receiver, None)?;
            let mut once_term_args: Vec<ay_dpll::api::Term> = vec![receiver_term];
            for arg_expr in &once_args_exprs {
                once_term_args.push(self.encode_pure_impl(arg_expr, None)?);
            }
            let Some(once_term) =
                self.axiom_apply_tracked("eager_fwd_fn_mut_once:once", &once_decl, &once_term_args)
            else {
                continue;
            };
            self.solver.assert_term(once_term);

            debug!(
                "[TRUST_WP_DEBUG] eager fn_mut_once forward: asserted once for mut_args={:?}",
                args.len()
            );
        }

        Ok(())
    }

    fn collect_ground_postcondition_mut_calls<'a>(
        exprs: &[&'a PureExpr],
    ) -> Vec<(&'a PureExpr, &'a [PureExpr])> {
        exprs
            .iter()
            .filter_map(|expr| match expr {
                PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                } if method == "postcondition_mut" => Some((receiver.as_ref(), args.as_slice())),
                _ => None,
            })
            .collect()
    }

    /// Synthesize ground `postcondition_mut` calls implied by ground
    /// `postcondition_once` requires.
    ///
    /// This mirrors `assert_eager_fn_mut_once_instantiations` but returns the
    /// witness-instantiated call expressions instead of asserting SMT terms.
    /// The eager negated-existential instantiator uses these synthetic calls
    /// as additional witness sources when the only available ground fact is a
    /// `postcondition_once` precondition. (#2556)
    pub(crate) fn synthetic_ground_postcondition_mut_calls_from_once_requires(
        &mut self,
        requires: &[PureExpr],
    ) -> Vec<(PureExpr, Vec<PureExpr>)> {
        let exprs: Vec<&PureExpr> = requires.iter().collect();
        self.synthetic_ground_postcondition_mut_calls_from_once_exprs(&exprs)
    }

    pub(crate) fn synthetic_ground_postcondition_mut_calls_from_once_exprs(
        &mut self,
        exprs: &[&PureExpr],
    ) -> Vec<(PureExpr, Vec<PureExpr>)> {
        let once_calls = Self::collect_ground_postcondition_once_calls(exprs);
        if once_calls.is_empty() {
            return Vec::new();
        }

        let mut_entries = self.collect_postcondition_mut_entries();
        let mut calls = Vec::new();

        for (receiver, args) in once_calls {
            let normalized_receiver = super::normalize_closure_receiver(receiver);
            let param_sorts: Vec<Sort> = std::iter::once(normalized_receiver)
                .chain(args.iter())
                .map(|expr| self.infer_expr_sort_with_context(expr, None))
                .collect();
            let once_arity = param_sorts.len();
            let once_tags = param_sorts
                .iter()
                .map(Self::closure_sort_tag)
                .collect::<Vec<_>>();
            let sort_sig = once_tags.join("_");
            let once_name = format!("closure_postcondition_once_{once_arity}_{sort_sig}");
            let witness_sorts = self
                .logic_func_decl_cloned(&once_name)
                .map(|decl| decl.domain().to_vec())
                .unwrap_or_else(|| param_sorts.clone());
            let insert_pos = once_arity - 1;
            let mut_candidates =
                Self::matching_postcondition_mut_symbols(&mut_entries, once_arity, &once_tags);
            if mut_candidates.is_empty() {
                continue;
            }

            for (_mut_name, _mut_decl, mut_tags, mut_sorts) in mut_candidates {
                let res_state_tag = &mut_tags[insert_pos];
                let res_state_sort = mut_sorts[insert_pos].clone();
                let preferred_witness_name =
                    Self::fn_mut_once_witness_name(once_arity, &sort_sig, res_state_tag);
                let legacy_witness_name = format!("fn_mut_once_witness_{once_arity}_{sort_sig}");
                let witness_name = if self
                    .logic_func_decl_cloned(&preferred_witness_name)
                    .is_some()
                {
                    preferred_witness_name
                } else if self.logic_func_decl_cloned(&legacy_witness_name).is_some() {
                    legacy_witness_name
                } else {
                    preferred_witness_name
                };
                self.get_or_declare_fn_mut_once_witness(
                    &witness_name,
                    &witness_sorts,
                    &res_state_sort,
                );

                let mut witness_args = Vec::with_capacity(args.len() + 1);
                witness_args.push(normalized_receiver.clone());
                witness_args.extend(args.iter().cloned());
                let witness_expr = PureExpr::LogicFnCall {
                    name: witness_name,
                    args: witness_args,
                };

                let Some((result_arg, leading_args)) = args.split_last() else {
                    continue;
                };
                let mut mut_args = Vec::with_capacity(args.len().saturating_add(1));
                mut_args.extend(leading_args.iter().cloned());
                mut_args.push(witness_expr);
                mut_args.push(result_arg.clone());
                calls.push((normalized_receiver.clone(), mut_args));
            }
        }

        calls
    }
}
