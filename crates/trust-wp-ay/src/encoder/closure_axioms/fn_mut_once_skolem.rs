// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Existential Skolemization for postcondition_mut assumptions and sort inference.
//!
//! ay-dpll does not implement Skolemization for existential quantifiers (ay#813).
//! This module provides eager Skolemization that introduces fresh constants for
//! existentially bound variables in postcondition_mut-containing assumptions,
//! creating ground terms for E-matching.

use ay_dpll::api::Sort;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::{AYEncoder, MAX_ENCODING_DEPTH};
use crate::{error::EncodingError, expr::expr_mentions_var};

impl AYEncoder {
    /// Infer the ay sort for an existentially bound variable used in
    /// `postcondition_mut` Skolemization.
    ///
    /// Sort resolution priority:
    /// 1. `ExprSort` annotation on the `Exists` node (if populated by the driver)
    /// 2. Receiver sort from a `postcondition_mut` call where the variable appears
    ///    as the state argument (position index N-2 for an N-arg `postcondition_mut`
    ///    call: `f.postcondition_mut(args, state, result)`)
    /// 3. Receiver sort when the variable IS the receiver of `postcondition_mut`
    ///    (e.g., `st1.postcondition_mut((), st2, result)` — `st1` should have
    ///    the same sort as the outer closure `f`)
    /// 4. Fallback: `Sort::Int`
    pub(super) fn infer_existential_var_sort(
        &mut self,
        var_sort: Option<&ExprSort>,
        var: &str,
        body: &PureExpr,
    ) -> Sort {
        // Priority 1: explicit annotation
        if let Some(es) = var_sort {
            return self.sort_from_expr_sort(es.clone());
        }

        // Priority 2-3: find the receiver sort from a postcondition_mut call
        // where var appears as state arg or as receiver
        if let Some(sort) = self.find_postcondition_mut_receiver_sort(var, body) {
            return sort;
        }

        Sort::Int
    }

    /// Walk the expression body to find a `postcondition_mut` method call where
    /// `var` appears as the state argument. If found, return the ay sort of the
    /// receiver (which should be the closure environment sort).
    ///
    /// Handles the pattern:
    ///   `f.postcondition_mut((), st1, r)` — if var == "st1", returns sort of `f`
    ///   `st1.postcondition_mut((), st2, result)` — if var == "st1", returns sort
    ///   of the first reference found for the receiver
    pub(crate) fn find_postcondition_mut_receiver_sort(
        &self,
        var: &str,
        body: &PureExpr,
    ) -> Option<Sort> {
        self.find_postcondition_mut_receiver_sort_impl(var, body, 0)
    }

    fn find_postcondition_mut_receiver_sort_impl(
        &self,
        var: &str,
        body: &PureExpr,
        depth: usize,
    ) -> Option<Sort> {
        if depth > MAX_ENCODING_DEPTH {
            return None;
        }
        let next = depth + 1;
        let recurse =
            |expr: &PureExpr| self.find_postcondition_mut_receiver_sort_impl(var, expr, next);
        match body {
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if method == "postcondition_mut" => {
                // In postcondition_mut(args, state, result), state is at args[len-2]
                // (second-to-last position). The variable could also be the receiver.
                let is_state_arg = args.len() >= 2
                    && matches!(&args[args.len() - 2], PureExpr::Var(name, _) if name == var);
                // Use normalize_closure_receiver to strip arbitrary-depth deref
                // chains (e.g., Deref(Deref(Var("st1")))) so the is_receiver check
                // correctly handles Box-wrapped closure receivers. (#2668)
                let normalized = super::normalize_closure_receiver(receiver);
                let is_receiver = matches!(normalized, PureExpr::Var(name, _) if name == var);

                if is_state_arg {
                    // var is the state arg — use the receiver's sort
                    return self.resolve_receiver_sort(receiver);
                }
                if is_receiver {
                    // var IS the receiver — find another postcondition_mut call in the
                    // sibling context to determine the sort. For now, check if any
                    // existing closure env variable in scope has a non-Int sort.
                    return self.resolve_receiver_sort(receiver);
                }
                None
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                recurse(receiver).or_else(|| args.iter().find_map(recurse))
            }
            PureExpr::BinOp(l, _, r) => recurse(l).or_else(|| recurse(r)),
            PureExpr::UnOp(_, inner)
            | PureExpr::Deref(inner)
            | PureExpr::Old(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => recurse(inner),
            PureExpr::Ite(c, t, e) => recurse(c).or_else(|| recurse(t)).or_else(|| recurse(e)),
            PureExpr::Exists {
                var: bound, body, ..
            }
            | PureExpr::Forall {
                var: bound, body, ..
            } => {
                if bound == var {
                    None
                } else {
                    recurse(body)
                }
            }
            PureExpr::Match { scrutinee, arms } => recurse(scrutinee).or_else(|| {
                arms.iter().find_map(|arm| {
                    if arm.pattern.binds_name(var) {
                        None
                    } else {
                        recurse(&arm.body)
                    }
                })
            }),
            PureExpr::Let {
                var: bound,
                value,
                body,
            } => recurse(value).or_else(|| if bound == var { None } else { recurse(body) }),
            PureExpr::LetAssume { assumption, body } => {
                recurse(assumption).or_else(|| recurse(body))
            }
            PureExpr::LetObligation { obligation, body } => {
                recurse(obligation).or_else(|| recurse(body))
            }
            PureExpr::LogicFnCall { args, .. } => args.iter().find_map(recurse),
            PureExpr::Closure { params, body } => {
                if params.iter().any(|(name, _)| name == var) {
                    None
                } else {
                    recurse(body)
                }
            }
            _ => None,
        }
    }

    /// Resolve the ay sort of a receiver expression. First tries runtime
    /// variable lookup, then falls back to declared `postcondition_mut` UFs
    /// to find the expected closure environment sort.
    fn resolve_receiver_sort(&self, receiver: &PureExpr) -> Option<Sort> {
        match receiver {
            PureExpr::Var(name, _) => {
                if let Some(term) = self.var_term(name) {
                    let sort = self.solver.get_sort(term);
                    // Only return non-Int sorts — Int is the uninformative default
                    if sort != Sort::Int {
                        return Some(sort);
                    }
                }
                // Fall back to declared postcondition_mut UF domain sorts.
                // When `f` is a generic parameter, its runtime sort is Int,
                // but the declared UFs encode the actual closure env sort.
                self.infer_closure_env_sort_from_declared_ufs()
            }
            PureExpr::Deref(inner) => self.resolve_receiver_sort(inner),
            _ => None,
        }
    }

    /// Look at declared `closure_postcondition_mut_*` UFs and return the
    /// first non-Int sort found in the first (receiver) domain position.
    /// This recovers the closure environment sort when the receiver variable
    /// has only `Sort::Int` from generic parameter encoding.
    fn infer_closure_env_sort_from_declared_ufs(&self) -> Option<Sort> {
        for (name, decl) in self.logic_funcs_iter() {
            if name.starts_with("closure_postcondition_mut_") {
                // The first domain sort is the receiver (closure env) sort
                if let Some(first_sort) = decl.domain().first() {
                    if *first_sort != Sort::Int {
                        return Some(first_sort.clone());
                    }
                }
            }
        }
        None
    }

    /// Example:
    /// ```text
    /// Input:  exists<f2: F> f.postcondition_mut(a, f2, result) && resolve(f2)
    /// Output: assert f.postcondition_mut(a, sk_f2, result) && resolve(sk_f2)
    /// ```
    /// where `sk_f2` is a fresh constant with the same sort as `f`.
    ///
    /// This creates ground `postcondition_mut(...)` and `resolve(...)` terms
    /// in the E-graph, enabling the fn_mut law's trigger to fire and derive
    /// `postcondition(f, a, result)` in a single E-matching round (#970).
    ///
    /// Must be called after preconditions have been encoded.
    pub(crate) fn assert_eager_existential_skolemizations(
        &mut self,
        requires: &[PureExpr],
    ) -> Result<(), EncodingError> {
        let exprs: Vec<&PureExpr> = requires.iter().collect();
        self.assert_eager_existential_skolemizations_for_exprs(&exprs)
    }

    pub(crate) fn assert_eager_existential_skolemizations_for_exprs(
        &mut self,
        exprs: &[&PureExpr],
    ) -> Result<(), EncodingError> {
        for &expr in exprs {
            let PureExpr::Exists { var, body, .. } = expr else {
                continue;
            };
            if !Self::body_has_postcondition_mut_with_var(body, var) {
                continue;
            }
            let term = self.encode_with_recursive_existential_skolemization(expr)?;
            self.solver.assert_term(term);
        }

        Ok(())
    }

    pub(crate) fn encode_with_recursive_existential_skolemization(
        &mut self,
        expr: &PureExpr,
    ) -> Result<ay_dpll::api::Term, EncodingError> {
        let PureExpr::Exists {
            var,
            var_sort,
            body,
            ..
        } = expr
        else {
            return self.encode_pure(expr);
        };
        // Skolemize if:
        // (a) the bound var appears in a postcondition_mut arg (direct reference), OR
        // (b) the body transitively contains postcondition_mut in deeper
        //     existentials (we need to "punch through" unused wrapper layers
        //     so inner existentials can also be Skolemized).
        if !Self::body_has_postcondition_mut_with_var(body, var)
            && !Self::body_has_any_postcondition_mut(body)
        {
            return self.encode_pure(expr);
        }

        // Replace existential witnesses in positive assumptions with fresh
        // constants. Recursing through nested existentials yields fully-ground
        // postcondition_mut chain facts when possible.
        let sk_counter = self.next_quantifier_var_id();
        let sk_name = format!("sk_exists_{var}_{sk_counter}");
        // Infer sort from (1) ExprSort annotation, (2) postcondition_mut receiver
        // context, (3) fallback to Int. Using Int for generic state params causes
        // sort mismatches when postcondition_mut was declared with a closure env
        // sort from axiom paths. (#2151)
        let sk_sort = self.infer_existential_var_sort(var_sort.as_ref(), var, body);
        let witness_term = self.solver.fresh_var(&sk_name, sk_sort);

        let old_binding = self.insert_var(var.clone(), witness_term);
        // Keep Deref/Final semantics consistent with quantifier-bound variables
        // while encoding the Skolemized body (notably for resolve(var)).
        self.bind_quantifier_var(var.clone());
        let encoded = self.encode_with_recursive_existential_skolemization(body);
        if Self::body_has_postcondition_mut_with_var(body, var) {
            self.assert_eager_fn_mut_ground_instantiations_for_var(body, var)?;
        }
        self.unbind_quantifier_var(var);
        self.restore_var(var, old_binding);

        encoded
    }

    fn assert_eager_fn_mut_ground_instantiations_for_var(
        &mut self,
        expr: &PureExpr,
        var: &str,
    ) -> Result<(), EncodingError> {
        self.assert_eager_fn_mut_ground_instantiations_for_var_inner(expr, var, 0)
    }

    fn assert_eager_fn_mut_ground_instantiations_for_var_inner(
        &mut self,
        expr: &PureExpr,
        var: &str,
        depth: usize,
    ) -> Result<(), EncodingError> {
        if depth > MAX_ENCODING_DEPTH {
            return Ok(());
        }
        let next = depth + 1;
        match expr {
            PureExpr::MethodCall { method, .. }
                if method == "postcondition_mut" && expr_mentions_var(expr, var) =>
            {
                self.assert_eager_fn_mut_ground_instantiation(expr)?;
                Ok(())
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(receiver, var, next)?;
                for arg in args {
                    self.assert_eager_fn_mut_ground_instantiations_for_var_inner(arg, var, next)?;
                }
                Ok(())
            }
            PureExpr::BinOp(lhs, _, rhs) => {
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(lhs, var, next)?;
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(rhs, var, next)
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Deref(inner)
            | PureExpr::Old(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => {
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(inner, var, next)
            }
            PureExpr::Ite(cond, then_expr, else_expr) => {
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(cond, var, next)?;
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(then_expr, var, next)?;
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(else_expr, var, next)
            }
            PureExpr::Exists {
                var: bound, body, ..
            }
            | PureExpr::Forall {
                var: bound, body, ..
            } => {
                if bound == var {
                    Ok(())
                } else {
                    self.assert_eager_fn_mut_ground_instantiations_for_var_inner(body, var, next)
                }
            }
            PureExpr::Match { scrutinee, arms } => {
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(scrutinee, var, next)?;
                for arm in arms {
                    if !arm.pattern.binds_name(var) {
                        self.assert_eager_fn_mut_ground_instantiations_for_var_inner(
                            &arm.body, var, next,
                        )?;
                    }
                }
                Ok(())
            }
            PureExpr::Let {
                var: bound,
                value,
                body,
            } => {
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(value, var, next)?;
                if bound == var {
                    Ok(())
                } else {
                    self.assert_eager_fn_mut_ground_instantiations_for_var_inner(body, var, next)
                }
            }
            PureExpr::LetAssume { assumption, body } => {
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(
                    assumption, var, next,
                )?;
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(body, var, next)
            }
            PureExpr::LetObligation { obligation, body } => {
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(
                    obligation, var, next,
                )?;
                self.assert_eager_fn_mut_ground_instantiations_for_var_inner(body, var, next)
            }
            PureExpr::LogicFnCall { args, .. } => {
                for arg in args {
                    self.assert_eager_fn_mut_ground_instantiations_for_var_inner(arg, var, next)?;
                }
                Ok(())
            }
            PureExpr::Closure { params, body } => {
                if params.iter().any(|(name, _)| name == var) {
                    Ok(())
                } else {
                    self.assert_eager_fn_mut_ground_instantiations_for_var_inner(body, var, next)
                }
            }
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(..) => Ok(()),
            #[allow(unreachable_patterns)]
            _ => Ok(()),
        }
    }
}
