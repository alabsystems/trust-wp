// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pure expression encoding for the AY encoder.
//!
//! This module implements the core `encode_pure_impl` method: a dispatcher that
//! matches on `PureExpr` variants and delegates to specialized encoding helpers.
//!
//! Submodule layout:
//! - `mod.rs` — `encode_pure_impl` dispatcher, `Ite`/`Old` handling, path guard
//! - `vars` — `Var` encoding
//! - `bindings` — `LetAssume` / `LetObligation`
//! - `binop` — `BinOp` expression encoding
//! - `wrapper` — `Deref` / `Final` wrapper rewriting
//! - sibling `operators` module — binary/unary operator terms and bitwise axioms
//!
//! Extracted from `mod.rs` as part of the encoder decomposition (#907).

mod bindings;
mod binop;
mod vars;
mod wrapper;

use std::{collections::HashMap, sync::Arc};

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};

use self::wrapper::WrapperKind;
use super::{sort_context::DerivedKind, AYEncoder, DepthGuard, MAX_ENCODING_DEPTH};
use crate::error::EncodingError;

const SINGLE_BIT_PROOF_BV_WIDTH: i64 = 64;

impl AYEncoder {
    fn int_literal(expr: &PureExpr) -> Option<i64> {
        match expr {
            PureExpr::Int(value) => Some(*value),
            _ => None,
        }
    }

    fn is_one_shift_mask(expr: &PureExpr) -> bool {
        let PureExpr::BinOp(left, BinOp::Shl, _) = expr else {
            return false;
        };
        Self::int_literal(left) == Some(1)
    }

    fn is_single_bit_test_body(expr: &PureExpr) -> bool {
        let PureExpr::BinOp(left, BinOp::Ne, right) = expr else {
            return false;
        };
        let masked = if Self::int_literal(right) == Some(0) {
            left.as_ref()
        } else if Self::int_literal(left) == Some(0) {
            right.as_ref()
        } else {
            return false;
        };
        let PureExpr::BinOp(mask_left, BinOp::BitAnd, mask_right) = masked else {
            return false;
        };
        Self::is_one_shift_mask(mask_left) || Self::is_one_shift_mask(mask_right)
    }

    fn shl_one_shift(expr: &PureExpr) -> Option<&PureExpr> {
        let PureExpr::BinOp(left, BinOp::Shl, shift) = expr else {
            return None;
        };
        (Self::int_literal(left) == Some(1)).then_some(shift.as_ref())
    }

    fn bitnot_shl_one_shift(expr: &PureExpr) -> Option<&PureExpr> {
        let PureExpr::UnOp(UnOp::BitNot | UnOp::Not, inner) = expr else {
            return None;
        };
        Self::shl_one_shift(inner)
    }

    fn inline_single_bit_alias_context(expr: &PureExpr) -> PureExpr {
        match expr {
            PureExpr::Let { var, value, body } => {
                let mut substitutions = HashMap::new();
                substitutions.insert(var.clone(), Self::inline_single_bit_alias_context(value));
                Self::inline_single_bit_alias_context(&body.substitute(&substitutions))
            }
            PureExpr::LetAssume { body, .. } | PureExpr::LetObligation { body, .. } => {
                Self::inline_single_bit_alias_context(body)
            }
            _ => expr.clone(),
        }
    }

    fn clear_bit_value_parts(expr: &PureExpr) -> Option<(PureExpr, PureExpr)> {
        let expr = Self::inline_single_bit_alias_context(expr);
        let PureExpr::BinOp(left, BinOp::BitAnd, right) = expr else {
            return None;
        };
        if let Some(bit) = Self::bitnot_shl_one_shift(&right) {
            return Some((left.as_ref().clone(), bit.clone()));
        }
        Self::bitnot_shl_one_shift(&left).map(|bit| (right.as_ref().clone(), bit.clone()))
    }

    fn single_bit_test_parts(expr: &PureExpr) -> Option<(PureExpr, PureExpr)> {
        let PureExpr::BinOp(left, BinOp::Ne, right) = expr else {
            return None;
        };
        let masked = if Self::int_literal(right) == Some(0) {
            left.as_ref()
        } else if Self::int_literal(left) == Some(0) {
            right.as_ref()
        } else {
            return None;
        };
        let PureExpr::BinOp(mask_left, BinOp::BitAnd, mask_right) = masked else {
            return None;
        };
        if let Some(bit) = Self::shl_one_shift(mask_right) {
            return Some((mask_left.as_ref().clone(), bit.clone()));
        }
        Self::shl_one_shift(mask_left).map(|bit| (mask_right.as_ref().clone(), bit.clone()))
    }

    fn single_bit_test_expr(value: PureExpr, bit: PureExpr) -> PureExpr {
        let mask = PureExpr::BinOp(Arc::new(PureExpr::Int(1)), BinOp::Shl, Arc::new(bit));
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(value),
                BinOp::BitAnd,
                Arc::new(mask),
            )),
            BinOp::Ne,
            Arc::new(PureExpr::Int(0)),
        )
    }

    fn try_expand_clear_bit_alias_single_bit_test(&self, expanded: &PureExpr) -> Option<PureExpr> {
        let (tested_value, query_bit) = Self::single_bit_test_parts(expanded)?;
        let tested_alias = match &tested_value {
            PureExpr::Var(name, _) => self.var_expr_alias(name).cloned()?,
            _ => return None,
        };
        let (base_value, cleared_bit) = Self::clear_bit_value_parts(&tested_alias)?;

        let preserved_bit = Self::single_bit_test_expr(base_value, query_bit.clone());
        let different_bit = PureExpr::BinOp(
            Arc::new(query_bit.clone()),
            BinOp::Ne,
            Arc::new(cleared_bit.clone()),
        );
        let simplified =
            PureExpr::BinOp(Arc::new(preserved_bit), BinOp::And, Arc::new(different_bit));

        let nonnegative = PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            BinOp::Le,
            Arc::new(cleared_bit.clone()),
        );
        let below_width = PureExpr::BinOp(
            Arc::new(cleared_bit),
            BinOp::Lt,
            Arc::new(PureExpr::Int(SINGLE_BIT_PROOF_BV_WIDTH)),
        );
        let in_range = PureExpr::BinOp(Arc::new(nonnegative), BinOp::And, Arc::new(below_width));

        Some(PureExpr::Ite(
            Arc::new(in_range),
            Arc::new(simplified),
            Arc::new(expanded.clone()),
        ))
    }

    fn try_expand_single_bit_test_logic_call(
        &self,
        name: &str,
        args: &[PureExpr],
    ) -> Option<PureExpr> {
        if !self.arithmetic_mode.bitwise_proof_mode() {
            return None;
        }

        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        let axiom = self.ground_pool.axioms().iter().find(|axiom| {
            axiom.fn_symbol == smt_name
                && axiom.kind == crate::encoder::ground_pool::AxiomKind::Defining
                && axiom.requires.is_empty()
                && axiom.params.len() == args.len()
                && Self::is_single_bit_test_body(&axiom.body)
        })?;

        let substitutions: HashMap<String, PureExpr> = axiom
            .params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        let expanded = axiom.body.substitute(&substitutions);
        Some(
            self.try_expand_clear_bit_alias_single_bit_test(&expanded)
                .unwrap_or(expanded),
        )
    }

    fn expand_logic_fn_proof_call_let(
        &self,
        var: &str,
        value: &PureExpr,
        body: &PureExpr,
    ) -> Option<PureExpr> {
        use crate::encoder::ground_pool::AxiomKind;

        let PureExpr::LogicFnCall { name, args } = value else {
            return None;
        };
        if body.free_vars().contains(var) {
            return None;
        }

        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        let spec_axioms: Vec<_> = self
            .ground_pool
            .axioms()
            .iter()
            .filter(|axiom| axiom.kind == AxiomKind::Spec && axiom.fn_symbol == smt_name)
            .collect();
        let first_spec = spec_axioms.first()?;
        if first_spec.params.len() != args.len() {
            return None;
        }
        let requires = first_spec.requires.clone();

        let mut substitutions: HashMap<String, PureExpr> = first_spec
            .params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        substitutions.insert("result".to_string(), value.clone());

        let mut expanded = body.clone();
        for axiom in spec_axioms.iter().rev() {
            let assumption = axiom.body.substitute(&substitutions);
            expanded = PureExpr::LetAssume {
                assumption: Arc::new(assumption),
                body: Arc::new(expanded),
            };
        }
        for requirement in requires.iter().rev() {
            let obligation = requirement.substitute(&substitutions);
            expanded = PureExpr::LetObligation {
                obligation: Arc::new(obligation),
                body: Arc::new(expanded),
            };
        }

        Some(expanded)
    }

    fn predeclare_stdlib_option_datatypes_from_some(
        &mut self,
        expr: &PureExpr,
        prefix: Option<DerivedKind>,
    ) {
        use crate::encoder::match_enc::{
            short_constructor_name, stdlib_constructor_target, SwitchTarget,
        };

        match expr {
            PureExpr::BinOp(left, _, right) => {
                self.predeclare_stdlib_option_datatypes_from_some(left, prefix);
                self.predeclare_stdlib_option_datatypes_from_some(right, prefix);
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => {
                self.predeclare_stdlib_option_datatypes_from_some(inner, prefix);
            }
            PureExpr::Ite(cond, then_expr, else_expr) => {
                self.predeclare_stdlib_option_datatypes_from_some(cond, prefix);
                self.predeclare_stdlib_option_datatypes_from_some(then_expr, prefix);
                self.predeclare_stdlib_option_datatypes_from_some(else_expr, prefix);
            }
            PureExpr::MethodCall { receiver, args, .. } => {
                self.predeclare_stdlib_option_datatypes_from_some(receiver, prefix);
                for arg in args {
                    self.predeclare_stdlib_option_datatypes_from_some(arg, prefix);
                }
            }
            PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
                self.predeclare_stdlib_option_datatypes_from_some(body, prefix);
                for trigger_group in triggers {
                    for trigger in trigger_group {
                        self.predeclare_stdlib_option_datatypes_from_some(trigger, prefix);
                    }
                }
            }
            PureExpr::Match { scrutinee, arms } => {
                self.predeclare_stdlib_option_datatypes_from_some(scrutinee, prefix);
                for arm in arms {
                    self.predeclare_stdlib_option_datatypes_from_some(&arm.body, prefix);
                }
            }
            PureExpr::LogicFnCall { name, args } => {
                if matches!(
                    stdlib_constructor_target(name),
                    Some(SwitchTarget::OptionInt)
                ) && short_constructor_name(name) == "Some"
                {
                    if let Some(payload) = args.first() {
                        let payload_sort = self.infer_expr_sort_with_context(payload, prefix);
                        let datatype = self.stdlib_option_datatype_for_payload_sort(payload_sort);
                        self.ensure_datatype_declared(&datatype);
                    }
                }
                for arg in args {
                    self.predeclare_stdlib_option_datatypes_from_some(arg, prefix);
                }
            }
            PureExpr::Let { value, body, .. } => {
                self.predeclare_stdlib_option_datatypes_from_some(value, prefix);
                self.predeclare_stdlib_option_datatypes_from_some(body, prefix);
            }
            PureExpr::LetAssume { assumption, body }
            | PureExpr::LetObligation {
                obligation: assumption,
                body,
            } => {
                self.predeclare_stdlib_option_datatypes_from_some(assumption, prefix);
                self.predeclare_stdlib_option_datatypes_from_some(body, prefix);
            }
            PureExpr::Closure { body, .. } => {
                self.predeclare_stdlib_option_datatypes_from_some(body, prefix);
            }
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
            #[allow(unreachable_patterns)]
            _ => {}
        }
    }

    fn assert_ffs_zero_ite_then_branch(
        &mut self,
        cond_expr: &PureExpr,
        then_expr: &PureExpr,
        aux: Term,
        then_term: Term,
        prefix: Option<DerivedKind>,
    ) {
        if self.quantifier_state.quantifier_depth() != 0
            || Self::int_literal(then_expr) != Some(0)
            || self.solver.get_sort(aux) != Sort::Int
            || self.solver.get_sort(then_term) != Sort::Int
        {
            return;
        }

        let Some((logic_name, arg_expr)) = ffs_zero_condition(cond_expr) else {
            return;
        };
        if !matches!(arg_expr, PureExpr::Var(_, _)) {
            return;
        }
        if self.leading_zeros_logic_axiom(logic_name).is_none() {
            return;
        }

        let dedup_key = format!("ite_int_aux/ffs_zero_then::{logic_name}::{arg_expr:?}::{aux:?}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        let Ok(arg_term) = self.encode_pure_impl(arg_expr, prefix) else {
            return;
        };
        if self.solver.get_sort(arg_term) != Sort::Int {
            return;
        }

        let zero = self.solver.int_const(0);
        let arg_eq_zero = self.eq_term(arg_term, zero);
        let aux_eq_then = self.eq_term(aux, then_term);
        let implication = self.solver.implies(arg_eq_zero, aux_eq_then);
        self.assert_solver_term("ite_int_aux/ffs_zero_then", implication);
    }

    /// Internal implementation of pure expression encoding with optional
    /// derived-name context.
    ///
    /// When `prefix` is `Some(DerivedKind::Old)`, variable names are resolved in
    /// the `old(...)` context. When `None`, no extra derivation is applied.
    #[allow(clippy::too_many_lines)]
    pub(super) fn encode_pure_impl(
        &mut self,
        expr: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        self.traversal.recursion_depth += 1;
        if self.traversal.recursion_depth > MAX_ENCODING_DEPTH {
            self.traversal.recursion_depth -= 1;
            return Err(EncodingError::unsupported(
                "expression nesting exceeds maximum depth",
            ));
        }
        let _guard = DepthGuard(&raw mut self.traversal.recursion_depth);
        match expr {
            PureExpr::Bool(b) => Ok(self.solver.bool_const(*b)),
            PureExpr::Int(n) => Ok(self.solver.int_const(*n)),
            PureExpr::Float(v) => self
                .solver
                .try_real_const(v.to_f64())
                .map_err(|e| EncodingError::unsupported(format!("float constant: {e}"))),
            PureExpr::Var(name, sort_ann) => self.encode_var(name, sort_ann.as_ref(), prefix),
            PureExpr::BinOp(l, op, r) => self.encode_binop_expr(l, *op, r, prefix),
            PureExpr::UnOp(op, inner) => {
                if matches!(op, UnOp::Not) {
                    self.seed_bool_context_hints(inner);
                }
                let t = self.encode_pure_impl(inner, prefix)?;
                self.encode_unop(*op, t)
            }
            PureExpr::Ite(cond, then_expr, else_expr) => {
                self.seed_bool_context_hints(cond);
                self.predeclare_stdlib_option_datatypes_from_some(then_expr, prefix);
                self.predeclare_stdlib_option_datatypes_from_some(else_expr, prefix);
                let c_raw = self.encode_pure_impl(cond, prefix)?;
                // Ite condition must be Bool-sorted; coerce Int fallbacks. (#994)
                let c = self.coerce_bool_operand(c_raw);

                let then_result = {
                    let _guard = self.push_path_condition(c);
                    // The condition is a fact only in the selected arm.  Seed
                    // its sequence refinements under that same path guard;
                    // doing so before the guard leaks `len(s) == 0` globally
                    // and can collapse an arbitrary ITE onto its then arm.
                    self.try_synthesize_len_zero_seq_value(cond, prefix)?;
                    self.try_synthesize_index_mut_seq_value(cond, prefix)?;
                    self.encode_pure_impl(then_expr, prefix)
                };
                let t = then_result?;

                let not_c = self.solver.not(c);
                let else_result = {
                    let _guard = self.push_path_condition(not_c);
                    self.encode_pure_impl(else_expr, prefix)
                };
                let e = else_result?;
                // Bool-valued conditionals are encoded without SMT ite to avoid
                // ay-dpll clause-reconstruction panics in mixed matcher/Seq
                // obligations. `(ite c t e)` is equivalent to `(c => t) /\ (!c => e)`.
                // Use context-aware inference so LogicFnCall nodes
                // returning Bool are not misclassified as Int. (#1965)
                if self.infer_expr_sort_with_context(then_expr, prefix) == Sort::Bool
                    && self.infer_expr_sort_with_context(else_expr, prefix) == Sort::Bool
                {
                    // Coerce branches to Bool: inference may disagree with
                    // actual encoded sort for complex expressions. (#994)
                    let t = self.coerce_bool_operand(t);
                    let e = self.coerce_bool_operand(e);
                    let c_implies_t = self.solver.implies(c, t);
                    let not_c_implies_e = self.solver.implies(not_c, e);
                    Ok(self.solver.and(c_implies_t, not_c_implies_e))
                } else if self.solver.get_sort(t) == Sort::Int
                    && self.solver.get_sort(e) == Sort::Int
                {
                    // Inside a quantifier body, we MUST emit a real `ite` term
                    // instead of a fresh global auxiliary constant. The aux pattern
                    // declares a top-level constant and asserts `c => aux=t` and
                    // `!c => aux=e` globally — but `c`, `t`, `e` reference bound
                    // variables in scope only under the quantifier, so the global
                    // assertions silently pin the aux to a single arbitrary value,
                    // making the quantified body equivalent to a constant function
                    // and the resulting VC `Unknown` (e.g., bug/181_ident). (#5)
                    if self.quantifier_state.quantifier_depth() != 0 {
                        Ok(self.safe_ite(c, t, e))
                    } else {
                        let aux_id = self.next_quantifier_var_id();
                        let aux = self
                            .solver
                            .declare_const(&format!("__trust_wp_ite_int_aux_{aux_id}"), Sort::Int);
                        let then_eq = self.eq_term(aux, t);
                        let else_eq = self.eq_term(aux, e);
                        let then_guard = self.solver.implies(c, then_eq);
                        let else_guard = self.solver.implies(not_c, else_eq);
                        self.assert_solver_term("ite_int_aux/then", then_guard);
                        self.assert_solver_term("ite_int_aux/else", else_guard);
                        self.assert_ffs_zero_ite_then_branch(cond, then_expr, aux, t, prefix);
                        Ok(aux)
                    }
                } else {
                    // Use safe_ite for sort-safe ITE construction with panic
                    // isolation. Handles heterogeneous sorts (e.g., Tuple2 vs
                    // Int, OptionInt vs Option) via harmonization. (#2077, #2699)
                    Ok(self.safe_ite(c, t, e))
                }
            }
            PureExpr::Old(inner) => {
                // For mutable borrow contracts: old(*v) is the same as *v (both are v_current)
                // because *v already represents the entry-state value in RustHorn encoding.
                // For other expressions: old(x) uses "old_" prefix.
                if matches!(inner.as_ref(), PureExpr::Deref(_)) {
                    // old(*v) = *v = v_current
                    self.encode_pure_impl(inner, prefix)
                } else {
                    // old(x) = old_x (nested old() just keeps using old_ prefix)
                    self.encode_pure_impl(inner, Some(DerivedKind::Old))
                }
            }
            PureExpr::Deref(inner) => {
                self.encode_deref_or_final(expr, inner, WrapperKind::Deref, prefix)
            }
            PureExpr::Final(inner) => {
                self.encode_deref_or_final(expr, inner, WrapperKind::Final, prefix)
            }
            PureExpr::View(inner) => self.encode_view_expr(inner, prefix),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                // Use receiver-qualified hint key to prevent cross-receiver
                // sort hint pollution (#2245). A Bool hint from one mapping's
                // `.get()` must not poison a different mapping's `.get()`.
                let qualified_key = crate::encoder::sort_context::hint_collection::receiver_qualified_method_hint_key(receiver, method);
                if self.sort_hint_matches(&qualified_key, &ExprSort::Bool)
                    && matches!(method.as_str(), "get" | "index" | "index_logic" | "lookup")
                {
                    return self.encode_bool_context_operand(expr, prefix);
                }
                // Method calls on logical views - handle Seq operations
                self.encode_method_call_impl(receiver, method, args, prefix)
            }
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                // Universal quantifier in pure expressions
                self.encode_pure_forall_impl(var, var_sort.clone(), body, triggers, prefix)
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => {
                // Existential quantifier in pure expressions
                self.encode_pure_exists_impl(var, var_sort.clone(), body, triggers, prefix)
            }
            PureExpr::Match { scrutinee, arms } => {
                // Encode match as nested ITE (if-then-else) chain
                self.predeclare_stdlib_option_datatypes_from_some(scrutinee, prefix);
                for arm in arms {
                    self.predeclare_stdlib_option_datatypes_from_some(&arm.body, prefix);
                }
                self.encode_match_impl(scrutinee, arms, prefix)
            }
            PureExpr::LogicFnCall { name, args } => {
                // Integer narrowing cast via BV truncation (#2666, #938).
                // The driver emits `__trust_wp_int_truncate_{s|u}{bits}(value)`
                // for narrowing IntToInt casts. Intercept here to call
                // `encode_int_truncation_bv` which gives exact modular semantics.
                if let Some(bits) = parse_unsigned_to_signed_same_width_cast_name(name) {
                    if let Some(operand) = args.first() {
                        let value_term = self.encode_pure_impl(operand, prefix)?;
                        return Ok(self.encode_unsigned_to_signed_same_width(value_term, bits));
                    }
                }

                if let Some((target_bits, signed)) = parse_int_truncate_name(name) {
                    if let Some(operand) = args.first() {
                        if let PureExpr::Int(value) = operand {
                            if let Some(folded) =
                                fold_int_truncate_const(*value, target_bits, signed)
                            {
                                return Ok(self.solver.int_const(folded));
                            }
                        }
                        let value_term = self.encode_pure_impl(operand, prefix)?;
                        return Ok(self.encode_int_truncation_bv(value_term, target_bits, signed));
                    }
                }

                // Shift-amount-in-range marker (ledger int-shift-full): the
                // driver wraps the amount operand of a machine-int `<<`/`>>`
                // in `__trust_wp_shift_amount_in_range_{bits}(amount)`.
                // Value-wise it is the identity; encoding it collects the
                // path-guarded proof obligation `0 <= amount && amount < bits`
                // through the same channel as the `divisor != 0` obligations
                // (`assert_nonzero_divisor`), so the verification layer proves
                // it alongside the negated postconditions.
                if let Some(bits) = parse_shift_amount_in_range_name(name) {
                    if let Some(operand) = args.first() {
                        let amount_term = self.encode_pure_impl(operand, prefix)?;
                        return Ok(self.collect_shift_amount_range_obligation(amount_term, bits));
                    }
                }

                // Normalize turbofish wrappers for layout intrinsics into the
                // specialized function name. proof_assert expressions bypass the
                // driver's contract rewriting, so turbofish wrappers like
                // `size_of_logic(__trust_wp_turbofish_arg(bool))` arrive here
                // un-normalized. Convert to `size_of_logic__bool()` so layout
                // axioms can assert concrete values.
                if let Some((specialized_name, stripped_args)) =
                    normalize_layout_turbofish(name, args)
                {
                    return self.encode_logic_fn_call_impl(
                        &specialized_name,
                        &stripped_args,
                        prefix,
                    );
                }
                if let Some(expanded) = self.try_expand_single_bit_test_logic_call(name, args) {
                    return self.encode_pure_impl(&expanded, prefix);
                }
                // Logic function call: encode as uninterpreted function application
                self.encode_logic_fn_call_impl(name, args, prefix)
            }
            PureExpr::Let { var, value, body } => {
                if let Some(expanded) = self.expand_logic_fn_proof_call_let(var, value, body) {
                    return self.encode_pure_impl(&expanded, prefix);
                }
                // Encode let-binding as ay let: (let ((var value)) body)
                let value_term = self.encode_pure_impl(value, prefix)?;
                let old_binding = self.insert_var(var.clone(), value_term);
                let body_result = self.encode_pure_impl(body, prefix);
                self.restore_var(var, old_binding);
                body_result
            }
            PureExpr::LetAssume { assumption, body } => {
                self.encode_let_assume(assumption, body, prefix)
            }
            PureExpr::LetObligation { obligation, body } => {
                self.encode_let_obligation(obligation, body, prefix)
            }
            PureExpr::Closure { params, body } => {
                // Closure expressions in logic context (#985).
                //
                // Full higher-order encoding (lambda terms) is not supported.
                // Instead, create a fresh uninterpreted function symbol for
                // the closure and assert a defining axiom:
                //   forall params. closure_fn(params) == body
                //
                // When the closure has no parameters (thunk), encode just
                // the body directly as the closure's value.
                //
                // This handles the common pattern `c@ == |z: u32| z@ % 2 == 0`
                // in PredCell contracts: the closure predicate becomes a
                // concrete function whose axiom constrains call results.
                self.encode_closure_in_logic(params, body, prefix)
            }
            // PureExpr is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns)]
            _ => Err(EncodingError::unsupported(format!(
                "unhandled PureExpr variant: {expr:?}"
            ))),
        }
    }

    /// Encode a closure expression in logic context (#985, #2683).
    ///
    /// Full higher-order closure encoding requires lambda terms which SMT
    /// does not natively support. This method provides two strategies:
    ///
    /// - **Zero-parameter closures** (thunks): encode the body directly.
    /// - **Single-parameter closures**: encode as a Mapping-sorted constant
    ///   with a defining axiom `forall x. mapping_get(closure_map, x) == body`.
    ///   This handles the common Creusot pattern where closures are used as
    ///   `Mapping` values (e.g., `let map = |x| ...; map.get(x)`).
    /// - **Multi-parameter closures** (2+): fall back to an unconstrained
    ///   constant since Mapping only supports single-argument total functions.
    fn encode_closure_in_logic(
        &mut self,
        params: &[(String, Option<ExprSort>)],
        body: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        use super::unsoundness;
        use crate::encoder::sort_context::sort_inference::mapping_sort;

        if params.is_empty() {
            // Zero-parameter closure (thunk): encode the body directly
            return self.encode_pure_impl(body, prefix);
        }

        if params.len() == 1 && self.closure_state.mapping_context() {
            // Single-parameter closure in Mapping context: encode as
            // Mapping-sorted constant with a defining axiom.
            //
            // Strategy: create a fresh Mapping-sorted constant, then assert
            //   forall param. mapping_get(closure_map, param) == body
            // This allows `map.get(x)` to resolve through the mapping_get UF
            // to the closure body.
            //
            // Guard: only when `closure_mapping_context` is set. This flag
            // is activated during logic function body encoding when the
            // function's return sort is Mapping, so closures used as Mapping
            // values (e.g., `#[logic] fn g() -> Mapping<Int, bool> { |x| ... }`)
            // are correctly encoded. In all other contexts (LetAssume,
            // quantifier bodies, etc.), closures fall through to the
            // unconstrained Bool constant below. (#2683)
            let uid = self.next_quantifier_var_id();
            let closure_map = self
                .solver
                .declare_const(&format!("__closure_mapping_{uid}"), mapping_sort());

            // Create a bound variable for the closure parameter
            let (param_name, param_sort_hint) = &params[0];
            let param_sort = match param_sort_hint {
                Some(ExprSort::Bool) => Sort::Bool,
                Some(ExprSort::Seq) => Sort::Seq(Box::new(Sort::Int)),
                _ => Sort::Int, // Default to Int for unspecified sorts
            };
            let bound_var = self
                .solver
                .fresh_var(&format!("__closure_param_{uid}"), param_sort.clone());

            // Save old binding, install the bound variable
            let old_binding = self.insert_var(param_name.clone(), bound_var);
            let old_sort = self.insert_var_sort(param_name.clone(), param_sort.clone());
            self.bind_quantifier_var(param_name.clone());

            // Increment quantifier depth so inner calls are not grounded
            self.quantifier_state.inc_quantifier_depth();
            let body_result = self.encode_pure_impl(body, prefix);
            self.quantifier_state.dec_quantifier_depth();

            // Restore binding
            self.unbind_quantifier_var(param_name);
            self.restore_var_sort(param_name, old_sort);
            self.restore_var(param_name, old_binding);

            let body_term = body_result?;

            // Build: mapping_get(closure_map, param)
            let mapping = mapping_sort();
            let mg_func = self.get_or_declare_spec_fn(
                "mapping_get",
                &[mapping, param_sort.clone()],
                Sort::Int,
            );
            let mg_app =
                self.safe_apply("closure_mapping_axiom", &mg_func, &[closure_map, bound_var])?;

            // Assert: forall param. mapping_get(closure_map, param) == body
            //
            // When the closure body is Bool-sorted (predicate closures like
            // `|z: u32| z@ % 2 == 0`), coerce it to Int via `ite(body, 1, 0)`
            // before the equality. mapping_get returns Int (the carrier sort),
            // so a direct `eq(Int, Bool)` would produce a sort mismatch that
            // `harmonize_eq_or_ite_terms` handles via an unconstrained
            // placeholder — breaking the defining axiom. (#2316)
            let body_sort = self.solver.get_sort(body_term);
            let body_for_eq = if body_sort == Sort::Bool {
                let one = self.solver.int_const(1);
                let zero = self.solver.int_const(0);
                self.solver.ite(body_term, one, zero)
            } else {
                body_term
            };
            let eq = self.eq_term(mg_app, body_for_eq);
            let axiom = self
                .solver
                .forall_with_triggers(&[bound_var], eq, &[&[mg_app]]);
            self.solver.assert_term(axiom);

            // Record the closure mapping so the Mapping ground-instance flush can
            // re-materialize `mapping_get(closure_map, k) == body_for_eq[z := k]`
            // for each observed obligation key `k`. The quantified axiom above
            // already pins the closure semantics, but ay-dpll's single-round
            // E-matching frequently fails to instantiate it at the concrete keys
            // (e.g. `v` and `v + 2` in PredCell `adds_two`), stranding an
            // otherwise-provable goal at `quantifier-unhandled`. Each ground
            // instance is a logical consequence of the universal just asserted,
            // so it can never change satisfiability. (#985, #2316)
            self.closure_mapping_axioms
                .push((closure_map, bound_var, body_for_eq));

            return Ok(closure_map);
        }

        // Last-resort opaque closure VALUE (multi-parameter closures, and
        // single-parameter closures outside Mapping context): fall back to a
        // fresh unconstrained constant. Multi-arg closures cannot be
        // represented as single-key Mapping values, so we use an opaque
        // fallback. Bool is chosen because closures in logic context typically
        // appear as predicates inside quantifier bodies, which require
        // Bool-sorted terms.
        //
        // FA-CRITICAL (vacfix): the constant is unconstrained, but its Bool
        // sort is ARBITRARY and it propagates — applying the closure yields a
        // Bool-returning UF, and any arithmetic use of that application is
        // promoted through `bool_to_int`'s `ite(b, 1, 0)`, FABRICATING the
        // premise "value in {0,1}" for a closure whose real return type is
        // unbounded. On `lang/unsized_quant` (`let len = |x: [i32]| x@.len()`)
        // that makes the flatly false `forall<x> len[x] <= 1` valid; live
        // trust-wp is saved only by ay declining the nested-quantifier shape,
        // and ay is actively removing that masking. So this site books the
        // DEMOTING `OpaqueClosureValueFallback` rather than the LOW,
        // non-demoting `UnsupportedConstructSkip` it used to share with the
        // `EncodingError` factories: no obligation encoded on top of a
        // fabricated closure value may be reported `Verified`.
        unsoundness::increment(unsoundness::UnsoundnessCategory::OpaqueClosureValueFallback);
        let uid = self.next_quantifier_var_id();
        let fallback = self
            .solver
            .declare_const(&format!("__closure_logic_{uid}"), Sort::Bool);
        Ok(fallback)
    }
}

/// Layout intrinsic names that should have turbofish type args folded into
/// the function name for concrete axiom matching.
const LAYOUT_INTRINSICS: &[&str] = &["size_of_logic", "align_of_logic"];

/// Turbofish wrapper function name used by the contract parser.
const TURBOFISH_WRAPPER: &str = "__trust_wp_turbofish_arg";

/// Prefix for integer truncation synthetic names emitted by the driver (#2666).
const INT_TRUNCATE_PREFIX: &str = "__trust_wp_int_truncate_";

/// Parse an integer truncation synthetic name into `(target_bits, signed)`.
///
/// The driver emits names like `__trust_wp_int_truncate_u8` (unsigned 8-bit) or
/// `__trust_wp_int_truncate_s16` (signed 16-bit). Returns `Some((bits, signed))`
/// if the name matches, `None` otherwise.
pub(crate) fn parse_int_truncate_name(name: &str) -> Option<(u32, bool)> {
    let suffix = name.strip_prefix(INT_TRUNCATE_PREFIX)?;
    let (signed, bits_str) = if let Some(rest) = suffix.strip_prefix('s') {
        (true, rest)
    } else if let Some(rest) = suffix.strip_prefix('u') {
        (false, rest)
    } else {
        return None;
    };
    let bits: u32 = bits_str.parse().ok()?;
    Some((bits, signed))
}

/// Prefix for the shift-amount-in-range marker emitted by the driver for
/// machine-int `<<`/`>>` amounts (ledger int-shift-full).
const SHIFT_AMOUNT_IN_RANGE_PREFIX: &str = "__trust_wp_shift_amount_in_range_";

/// Parse a shift-amount-in-range marker name into the bit width of the
/// SHIFTED operand's type.
///
/// The driver emits names like `__trust_wp_shift_amount_in_range_8` (for a
/// shift of an 8-bit integer). Value-wise the marker is the identity on its
/// single argument; pure encoding intercepts it to collect the path-guarded
/// proof obligation `0 <= amount && amount < bits` alongside the division
/// obligations. Returns `Some(bits)` if the name matches, `None` otherwise.
pub(crate) fn parse_shift_amount_in_range_name(name: &str) -> Option<u32> {
    let suffix = name.strip_prefix(SHIFT_AMOUNT_IN_RANGE_PREFIX)?;
    suffix.parse().ok().filter(|bits| *bits > 0)
}

pub(crate) fn fold_int_truncate_const(value: i64, target_bits: u32, signed: bool) -> Option<i64> {
    if target_bits == 0 || target_bits > 64 {
        return None;
    }

    let modulus = 1_i128.checked_shl(target_bits)?;
    let unsigned = i128::from(value).rem_euclid(modulus);
    let folded = if signed {
        let sign_bit = 1_i128.checked_shl(target_bits - 1)?;
        if unsigned >= sign_bit {
            unsigned - modulus
        } else {
            unsigned
        }
    } else {
        unsigned
    };
    i64::try_from(folded).ok()
}

fn ffs_zero_condition(cond: &PureExpr) -> Option<(&str, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = cond else {
        return None;
    };
    ffs_logic_zero_side(left, right).or_else(|| ffs_logic_zero_side(right, left))
}

fn ffs_logic_zero_side<'a>(
    candidate: &'a PureExpr,
    zero_side: &PureExpr,
) -> Option<(&'a str, &'a PureExpr)> {
    if AYEncoder::int_literal(zero_side) != Some(0) {
        return None;
    }
    let PureExpr::LogicFnCall { name, args } = candidate else {
        return None;
    };
    (args.len() == 1).then_some((name.as_str(), &args[0]))
}

const INT_CAST_PREFIX: &str = "__trust_wp_int_cast_";

/// Parse same-width unsigned-to-signed cast names emitted by the driver.
///
/// `__trust_wp_int_cast_u64_to_s64` returns `Some(64)`. Other cast families keep
/// using the generic BV truncation path.
pub(crate) fn parse_unsigned_to_signed_same_width_cast_name(name: &str) -> Option<u32> {
    let suffix = name.strip_prefix(INT_CAST_PREFIX)?;
    let (source_bits, target) = suffix.strip_prefix('u')?.split_once("_to_s")?;
    let source_bits: u32 = source_bits.parse().ok()?;
    let target_bits: u32 = target.parse().ok()?;
    (source_bits == target_bits).then_some(target_bits)
}

/// Normalize layout intrinsic turbofish wrappers at the encoder level.
///
/// Converts `size_of_logic(__trust_wp_turbofish_arg(bool))` to
/// `size_of_logic__bool()` so that `assert_layout_axioms()` can match
/// the type-specialized SMT name and assert concrete values.
///
/// Returns `Some((specialized_name, remaining_args))` if normalization
/// applied, `None` otherwise.
fn normalize_layout_turbofish(name: &str, args: &[PureExpr]) -> Option<(String, Vec<PureExpr>)> {
    if !LAYOUT_INTRINSICS.contains(&name) || args.is_empty() {
        return None;
    }
    // Check if the first arg is a turbofish wrapper with a Var type name.
    if let PureExpr::LogicFnCall {
        name: wrapper_name,
        args: wrapper_args,
    } = &args[0]
    {
        if wrapper_name == TURBOFISH_WRAPPER && wrapper_args.len() == 1 {
            if let PureExpr::Var(type_name, _) = &wrapper_args[0] {
                let specialized = format!("{name}__{type_name}");
                let remaining = args[1..].to_vec();
                return Some((specialized, remaining));
            }
            // Handle `__trust_wp_tuple0()` (unit type `()`) as a turbofish arg.
            // The unit type arrives as a LogicFnCall rather than a Var, so
            // the Var check above misses it. Fold it into the name as `()`
            // so that layout axioms can assert `size_of_logic__()() == 0`.
            if let PureExpr::LogicFnCall {
                name: inner_name,
                args: inner_args,
            } = &wrapper_args[0]
            {
                if inner_name == "__trust_wp_tuple0" && inner_args.is_empty() {
                    let specialized = format!("{name}__()");
                    let remaining = args[1..].to_vec();
                    return Some((specialized, remaining));
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use trust_wp_core::formula::PureExpr;

    use super::*;

    fn turbofish_var(layout_fn: &str, type_name: &str) -> (String, Vec<PureExpr>) {
        let args = vec![PureExpr::LogicFnCall {
            name: TURBOFISH_WRAPPER.to_string(),
            args: vec![PureExpr::Var(type_name.to_string(), None)],
        }];
        (layout_fn.to_string(), args)
    }

    #[test]
    fn test_normalize_layout_turbofish_var_type() {
        let (name, args) = turbofish_var("size_of_logic", "bool");
        let result = normalize_layout_turbofish(&name, &args);
        assert!(result.is_some());
        let (specialized, remaining) = result.unwrap();
        assert_eq!(specialized, "size_of_logic__bool");
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_normalize_layout_turbofish_unit_type() {
        // size_of_logic(__trust_wp_turbofish_arg(__trust_wp_tuple0()))
        let args = vec![PureExpr::LogicFnCall {
            name: TURBOFISH_WRAPPER.to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "__trust_wp_tuple0".to_string(),
                args: vec![],
            }],
        }];
        let result = normalize_layout_turbofish("size_of_logic", &args);
        assert!(result.is_some());
        let (specialized, remaining) = result.unwrap();
        assert_eq!(specialized, "size_of_logic__()");
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_normalize_layout_turbofish_align_unit_type() {
        let args = vec![PureExpr::LogicFnCall {
            name: TURBOFISH_WRAPPER.to_string(),
            args: vec![PureExpr::LogicFnCall {
                name: "__trust_wp_tuple0".to_string(),
                args: vec![],
            }],
        }];
        let result = normalize_layout_turbofish("align_of_logic", &args);
        assert!(result.is_some());
        let (specialized, _) = result.unwrap();
        assert_eq!(specialized, "align_of_logic__()");
    }

    #[test]
    fn test_normalize_layout_turbofish_non_layout_fn_returns_none() {
        let (_, args) = turbofish_var("some_other_fn", "bool");
        let result = normalize_layout_turbofish("some_other_fn", &args);
        assert!(result.is_none());
    }

    #[test]
    fn test_normalize_layout_turbofish_no_args_returns_none() {
        let result = normalize_layout_turbofish("size_of_logic", &[]);
        assert!(result.is_none());
    }
}
