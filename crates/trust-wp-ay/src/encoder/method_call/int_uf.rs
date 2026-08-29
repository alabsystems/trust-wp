// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Int-returning UF patterns: method encoding, pow2 with axiom set,
//! deep_model with ground tracking, and auxiliary Int bridge.
//!
//! Contains `encode_int_method_uf`, `encode_pow2_method`, and
//! `encode_deep_model_uf` — the Int-returning counterparts to the Bool
//! patterns in `bool_uf.rs`.

use ay_dpll::api::{FuncDecl, Sort, Term};
use num_bigint::BigInt;
use trust_wp_core::formula::{int_bounds::pow2_expr, PureExpr};

use super::super::{recursive_eval::simplify_ground, AYEncoder};
use crate::error::EncodingError;

impl AYEncoder {
    fn method_call_mentions_bound_vars(&self, receiver: &PureExpr, args: &[PureExpr]) -> bool {
        self.quantifier_state.has_bound_vars()
            && std::iter::once(receiver)
                .chain(args.iter())
                .any(|expr| expr.any_free_var(|name, _sort| self.quantifier_state.is_bound(name)))
    }

    /// Encode a method call as an Int-returning uninterpreted function (#737).
    ///
    /// Used for methods like `deep_model()`, `capacity()`, `set()`, `namespace()`,
    /// `id()` that return integer values but whose semantics we don't model.
    ///
    /// Returns an auxiliary Int variable bridged to the UF application via an
    /// asserted equality, so that downstream arithmetic uses a pure Int term
    /// instead of a UF application. This works around ay-dpll's theory
    /// combination limitation (#2323).
    pub(in crate::encoder) fn encode_int_method_uf(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let arg_terms: Vec<Term> = args
            .iter()
            .map(|arg| self.encode_pure_impl(arg, prefix))
            .collect::<Result<Vec<_>, _>>()?;

        let param_sorts: Vec<Sort> = std::iter::once((receiver, receiver_term))
            .chain(args.iter().zip(arg_terms.iter().copied()))
            .map(|(expr, term)| self.method_param_sort(expr, term, prefix))
            .collect();
        let sort_signature = param_sorts
            .iter()
            .map(Self::method_sort_tag)
            .collect::<Vec<_>>()
            .join("_");
        let smt_name = format!("method_{method}_{}_{sort_signature}", param_sorts.len());

        let mut all_terms = Vec::with_capacity(1 + arg_terms.len());
        all_terms.push(receiver_term);
        all_terms.extend(arg_terms.iter().copied());

        let (uf_app, _final_symbol) = self.apply_method_func_with_actual_sort_retry(
            &format!("method_call::int_uf::{method}"),
            &smt_name,
            &param_sorts,
            Sort::Int,
            &all_terms,
        )?;

        // `capacity()` is a pure model accessor in stdlib specs. Feeding its
        // raw UF application into arithmetic VCs can force ay's arithmetic
        // parser down an unsupported-function path, so keep a cached opaque Int
        // carrier without asserting a global aux-to-UF equality.
        if method == "capacity" {
            if let Some(aux) = self.seq_state.get_uf_int_aux(&uf_app) {
                return Ok(aux);
            }
            let aux_name = format!("__uf_int_aux_{}", self.seq_state.next_fresh_seq_lit_id());
            let aux_var = self.solver.declare_const(&aux_name, Sort::Int);
            self.seq_state.insert_uf_int_aux(uf_app, aux_var);
            return Ok(aux_var);
        }

        // Inside quantifier scopes, return raw UF applications only when the
        // call actually mentions a bound variable. Ground calls can still use
        // the normal aux bridge without introducing free bound variables.
        if self.quantifier_state.quantifier_depth() > 0
            && self.method_call_mentions_bound_vars(receiver, args)
        {
            return Ok(uf_app);
        }
        // Return cached auxiliary if we've already bridged this UF application.
        if let Some(aux) = self.seq_state.get_uf_int_aux(&uf_app) {
            return Ok(aux);
        }
        // Bridge: auxiliary Int variable so downstream arithmetic uses a pure
        // Int term instead of a UF application (#2323).
        let aux_name = format!("__uf_int_aux_{}", self.seq_state.next_fresh_seq_lit_id());
        let aux_var = self.solver.declare_const(&aux_name, Sort::Int);
        // For bit-count methods (`leading_zeros_logic`, `trailing_zeros_logic`,
        // `leading_ones_logic`, `trailing_ones_logic`) the bridge equality
        // `aux_var == uf_app` is the source of LRA "unsupported atom" downgrades
        // when the VC only consumes the aux in arithmetic contexts: LRA parses
        // the UF application as an unknown function, marks the atom unsupported,
        // and downgrades subsequent SAT results to Unknown. Replace the global
        // bridge equality with self-contained Int range axioms on `aux_var`
        // (`0 <= aux_var <= width`) so LRA sees only pure-arithmetic atoms.
        // The cached `aux_var` still ties multiple occurrences of the same UF
        // application together (congruence via cache), and the range matches
        // the actual semantics of bit-count methods on primitive integers.
        // (#994, Phase 4)
        let bit_count_method = matches!(
            method,
            "leading_zeros_logic"
                | "trailing_zeros_logic"
                | "leading_ones_logic"
                | "trailing_ones_logic"
        );
        if !bit_count_method {
            let bridge_eq = self.eq_term(aux_var, uf_app);
            self.solver.assert_term(bridge_eq);
        }
        self.seq_state.insert_uf_int_aux(uf_app, aux_var);
        self.assert_bit_count_range(method, aux_var);
        self.assert_leading_zeros_nonzero_range(method, receiver_term, aux_var);

        // Collection-cardinality non-negativity for std iterator carriers.
        //
        // `iter@.len()` on an FMap/Seq iterator collapses view∘len into this
        // composite UF whenever the carrier's encoded sort is not the
        // collection sort itself (encode_fmap_method's len fallback). The
        // result still denotes a std collection cardinality, so the LEN law's
        // non-negativity clause applies: trust-wp-std/src/logic/fmap.rs
        // `FMap::LEN` — `ensures: result >= 0` ("the standard cardinality
        // non-negativity fact required by loop variants like `iter@.len()`");
        // Seq lengths carry the same ground law (`seq_len_nonnegative_ground`).
        // Name-gated to trust-wp-std/driver-owned iterator carrier sorts so
        // user-defined `len` methods are never touched. (ce-census 2026-08-20,
        // ghost/fmap_iter merge_fmaps loop_variant_nonneg)
        if matches!(method, "len" | "len_ghost") {
            let receiver_sort_leaf = match param_sorts.first() {
                Some(Sort::Datatype(dt)) => Some(dt.name.as_str()),
                Some(Sort::Uninterpreted(name)) => Some(name.as_str()),
                _ => None,
            }
            .map(|name| name.rsplit("::").next().unwrap_or(name));
            if matches!(
                receiver_sort_leaf,
                Some("FMapIter" | "SeqIter" | "IntoIter")
            ) {
                let zero = self.solver.int_const(0);
                let nonnegative = self.solver.ge(aux_var, zero);
                self.assert_solver_term("std_iterator_len_nonnegative_ground", nonnegative);
            }
        }

        // Driver-shaped enum bodies often branch on `discriminant(self)` after
        // the constructor-equality precondition has already been reduced to a
        // native tester. Add the exact ground implication on the observed
        // receiver so the solver does not need quantified tester-to-tag
        // matching just to collapse the body ITE. (#1296)
        if method == "discriminant" && self.quantifier_state.quantifier_depth() == 0 {
            if let Some(Sort::Datatype(datatype)) = param_sorts.first() {
                // Look up actual discriminant values from the AdtDecl (#2631).
                let adt_decl = self.adt_decl_for_name(&datatype.name).cloned();
                for (variant_idx, constructor) in datatype.constructors.iter().enumerate() {
                    let Ok(tester) = self
                        .solver
                        .try_datatype_tester(&constructor.name, receiver_term)
                    else {
                        continue;
                    };
                    let discr_val = Self::datatype_discriminant_value(
                        adt_decl.as_ref(),
                        &constructor.name,
                        variant_idx,
                    );
                    let tag = self.solver.int_const_bigint(&discr_val);
                    let discr_eq_tag = self.eq_term(aux_var, tag);
                    let implication = self.solver.implies(tester, discr_eq_tag);
                    self.assert_solver_term("datatype_discriminant/ground_tester", implication);
                }
            }
        }

        Ok(aux_var)
    }

    /// Self-contained Int range axiom for bit-count UF results.
    ///
    /// For `leading_zeros_logic` / `trailing_zeros_logic` / `leading_ones_logic`
    /// / `trailing_ones_logic`, the result is always in `[0, 64]` on any
    /// primitive integer up to 64 bits wide. Asserting this directly on the
    /// auxiliary Int variable avoids the LRA "unsupported atom" downgrade that
    /// the `aux_var == uf_app` bridge equality would otherwise introduce, while
    /// still giving the solver enough information for downstream arithmetic
    /// reasoning. (#994, Phase 4)
    fn assert_bit_count_range(&mut self, method: &str, result: Term) {
        if !matches!(
            method,
            "leading_zeros_logic"
                | "trailing_zeros_logic"
                | "leading_ones_logic"
                | "trailing_ones_logic"
        ) {
            return;
        }
        if self.solver.get_sort(result) != Sort::Int {
            return;
        }

        let dedup_key = format!("bit_count_range::{method}::{result:?}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        let zero = self.solver.int_const(0);
        let width = self.solver.int_const(64);
        let ge_zero = self.solver.ge(result, zero);
        let le_width = self.solver.le(result, width);
        self.assert_solver_term("bit_count_range/ge_zero", ge_zero);
        self.assert_solver_term("bit_count_range/le_width", le_width);
    }

    fn assert_leading_zeros_nonzero_range(&mut self, method: &str, receiver: Term, result: Term) {
        if method != "leading_zeros_logic"
            || self.solver.get_sort(receiver) != Sort::Int
            || self.solver.get_sort(result) != Sort::Int
        {
            return;
        }

        let guard_key = self.active_path_condition_key();
        let dedup_key =
            format!("leading_zeros_nonzero_range::{receiver:?}::{result:?}::{guard_key}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        let zero = self.solver.int_const(0);
        let width = self.solver.int_const(64);
        let max = (BigInt::from(1u8) << 64) - BigInt::from(1u8);
        let max_term = self.solver.int_const_bigint(&max);
        let ge_zero = self.solver.ge(receiver, zero);
        let le_max = self.solver.le(receiver, max_term);
        let nonzero = self.solver.neq(receiver, zero);
        let unsigned_domain = self.solver.and(ge_zero, le_max);
        let premise = self.solver.and(unsigned_domain, nonzero);

        let result_ge_zero = self.solver.ge(result, zero);
        let result_lt_width = self.solver.lt(result, width);
        let result_in_range = self.solver.and(result_ge_zero, result_lt_width);
        let implication = self.solver.implies(premise, result_in_range);
        self.assert_solver_term("leading_zeros_logic/nonzero_range", implication);
    }

    /// Encode `pow2()` with exact folding for ground receivers.
    ///
    /// When the receiver simplifies to a non-negative integer literal that fits
    /// in `u32`, encode the exact repeated-squaring arithmetic tree so
    /// `pow2(4) == 16` does not depend on an uninterpreted function. Symbolic
    /// receivers use a UF with a small symbolic axiom set:
    ///
    /// - ground base facts for `pow2(0)` and `pow2(1)`
    /// - a guarded lower-bound axiom `pow2(i) >= pow2(i - 1) + pow2(i - 2)`
    ///   for `i >= 2` (Fibonacci sum bound — used by `lemma_fib_bound`)
    /// - the semantic doubling axiom `pow2(n + 1) == 2 * pow2(n)` for `n >= 0`
    ///   (Phase 3/4: gives `pow2` its actual `2^n` definitional semantics;
    ///   previously only the Fibonacci lower bound was axiomatized)
    /// - the non-negativity bound `pow2(n) >= 1` for `n >= 0`
    ///
    /// The inductive lower-bound axiom uses a 3-term multi-trigger so it only
    /// fires when all three ground calls are already present (for example from
    /// the `lemma_fib_bound` induction step), which avoids the recursive
    /// E-matching floods that a single-pattern recursive axiom would cause.
    /// The doubling axiom uses a 2-term multi-trigger `{pow2(n+1), pow2(n)}`
    /// so it only fires when both ground terms are already present, keeping
    /// E-matching bounded. (#994; Phase 3/4)
    pub(super) fn encode_pow2_method(
        &mut self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let simplified_receiver = simplify_ground(receiver);
        if let PureExpr::Int(exp) = simplified_receiver {
            if let Ok(exp) = u32::try_from(exp) {
                return self.encode_pure_impl(&pow2_expr(exp), prefix);
            }
        }

        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let param_sort = self.method_param_sort(receiver, receiver_term, prefix);
        let smt_name = format!("method_pow2_1_{}", Self::method_sort_tag(&param_sort));
        let func_decl = self.get_or_declare_method_func(&smt_name, &[param_sort], Sort::Int);

        let (final_decl, pow_term) =
            match self.safe_apply("method_call::pow2", &func_decl, &[receiver_term]) {
                Ok(term) => (func_decl, term),
                Err(original_err) => {
                    let actual_sort = self.solver.get_sort(receiver_term);
                    if actual_sort == func_decl.domain()[0] {
                        return Err(original_err);
                    }
                    let retry_name =
                        format!("method_pow2_1_{}", Self::method_sort_tag(&actual_sort));
                    let retry_decl =
                        self.get_or_declare_method_func(&retry_name, &[actual_sort], Sort::Int);
                    let term =
                        self.safe_apply("method_call::pow2", &retry_decl, &[receiver_term])?;
                    (retry_decl, term)
                }
            };

        self.assert_pow2_axioms(&final_decl);
        self.assert_pow2_ground_instances(&final_decl, receiver_term, pow_term);
        Ok(pow_term)
    }

    fn assert_pow2_axioms(&mut self, pow2_func: &FuncDecl) {
        let func_name = pow2_func.name().to_string();
        let dedup_key = format!("pow2_axioms::{func_name}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        let domain = pow2_func.domain();
        if !matches!(domain, [Sort::Int]) {
            return;
        }

        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);
        let two = self.solver.int_const(2);

        let pow_zero = self.solver.apply(pow2_func, &[zero]);
        let pow_one = self.solver.apply(pow2_func, &[one]);
        let pow_zero_eq = self.eq_term(pow_zero, one);
        let pow_one_eq = self.eq_term(pow_one, two);
        self.assert_solver_term("pow2_axiom/base0", pow_zero_eq);
        self.assert_solver_term("pow2_axiom/base1", pow_one_eq);

        // Proof-call and universal-postcondition lanes bootstrap logic
        // functions in finite ground-only mode. Keep `pow2` aligned with that
        // contract: every observed receiver gets the exact guarded instances
        // below, while the recursive quantified family would only add an
        // unbounded E-matching/model-validation burden. Omitting those global
        // foralls is completeness-only; no unsupported consequence is added.
        if self.encoding_cache.logic_fn_defining_axioms_ground_only() {
            return;
        }

        let x = self.solver.fresh_var("pow2_x", Sort::Int);
        let x_ge_two = self.solver.ge(x, two);
        let x_minus_1 = self.solver.sub(x, one);
        let x_minus_2 = self.solver.sub(x, two);
        let pow_x = self.solver.apply(pow2_func, &[x]);
        let pow_x_minus_1 = self.solver.apply(pow2_func, &[x_minus_1]);
        let pow_x_minus_2 = self.solver.apply(pow2_func, &[x_minus_2]);
        let rhs = self.solver.add(pow_x_minus_1, pow_x_minus_2);
        let lower_bound = self.solver.ge(pow_x, rhs);
        let body = self.solver.implies(x_ge_two, lower_bound);
        let inductive_axiom =
            self.solver
                .forall_with_triggers(&[x], body, &[&[pow_x, pow_x_minus_1, pow_x_minus_2]]);
        self.assert_solver_term("pow2_axiom/lower_bound", inductive_axiom);

        // Semantic doubling axiom: forall n. n >= 0 ==> pow2(n + 1) == 2 * pow2(n).
        //
        // This is the standard inductive definition of pow2 (=2^n) and is what
        // ties the UF to its intended `2^n` semantics. Without it, the solver
        // only knows the Fibonacci-style lower bound above, which is not strong
        // enough for recurrence proofs that need the exact doubling property
        // (e.g., closing `lemma_fib_bound` followed by usize-overflow reasoning
        // in `fib_memo`).
        //
        // Multi-trigger {pow2(n+1), pow2(n)} keeps E-matching bounded: the
        // axiom only fires when both ground terms are already present, so it
        // does not recursively instantiate to arbitrary depths. (Phase 3/4)
        let n = self.solver.fresh_var("pow2_n", Sort::Int);
        let n_ge_zero = self.solver.ge(n, zero);
        let n_plus_one = self.solver.add(n, one);
        let pow_n = self.solver.apply(pow2_func, &[n]);
        let pow_n_plus_one = self.solver.apply(pow2_func, &[n_plus_one]);
        let two_pow_n = self.solver.mul(two, pow_n);
        let doubling_eq = self.eq_term(pow_n_plus_one, two_pow_n);
        let doubling_body = self.solver.implies(n_ge_zero, doubling_eq);
        let doubling_axiom =
            self.solver
                .forall_with_triggers(&[n], doubling_body, &[&[pow_n_plus_one, pow_n]]);
        self.assert_solver_term("pow2_axiom/doubling", doubling_axiom);

        // Non-negativity: forall n. n >= 0 ==> pow2(n) >= 1.
        //
        // The doubling axiom alone does not pin down a sign; combined with
        // `pow2(0) = 1`, it implies `pow2(n) >= 1` for all `n >= 0`, but the
        // solver cannot always derive this by induction within timeout. The
        // explicit lower bound supports overflow reasoning chains like
        // `fib(i) <= pow2(i)` plus `pow2(63) <= usize::MAX`.
        let m = self.solver.fresh_var("pow2_m", Sort::Int);
        let m_ge_zero = self.solver.ge(m, zero);
        let pow_m = self.solver.apply(pow2_func, &[m]);
        let pow_m_ge_one = self.solver.ge(pow_m, one);
        let nonneg_body = self.solver.implies(m_ge_zero, pow_m_ge_one);
        let nonneg_axiom = self
            .solver
            .forall_with_triggers(&[m], nonneg_body, &[&[pow_m]]);
        self.assert_solver_term("pow2_axiom/nonneg", nonneg_axiom);
    }

    fn assert_pow2_ground_instances(&mut self, pow2_func: &FuncDecl, receiver: Term, pow: Term) {
        let domain = pow2_func.domain();
        if !matches!(domain, [Sort::Int]) || self.solver.get_sort(receiver) != Sort::Int {
            return;
        }

        let guard_key = self.active_path_condition_key();
        let dedup_key = format!(
            "pow2_ground_lower_bound::{}::{receiver:?}::{guard_key}",
            pow2_func.name()
        );
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);
        let two = self.solver.int_const(2);

        let receiver_eq_zero = self.eq_term(receiver, zero);
        let base_zero = self.eq_term(pow, one);
        let base_zero_implication = self.solver.implies(receiver_eq_zero, base_zero);
        let base_zero_guarded = self.guard_with_active_path(base_zero_implication);
        self.assert_solver_term("pow2_axiom/base0_ground", base_zero_guarded);

        let receiver_eq_one = self.eq_term(receiver, one);
        let base_one = self.eq_term(pow, two);
        let base_one_implication = self.solver.implies(receiver_eq_one, base_one);
        let base_one_guarded = self.guard_with_active_path(base_one_implication);
        self.assert_solver_term("pow2_axiom/base1_ground", base_one_guarded);

        let receiver_ge_two = self.solver.ge(receiver, two);
        let receiver_minus_1 = self.solver.sub(receiver, one);
        let receiver_minus_2 = self.solver.sub(receiver, two);
        let pow_minus_1 = self.solver.apply(pow2_func, &[receiver_minus_1]);
        let pow_minus_2 = self.solver.apply(pow2_func, &[receiver_minus_2]);
        let rhs = self.solver.add(pow_minus_1, pow_minus_2);
        let lower_bound = self.solver.ge(pow, rhs);
        let ground_axiom = self.solver.implies(receiver_ge_two, lower_bound);
        let guarded = self.guard_with_active_path(ground_axiom);
        self.assert_solver_term("pow2_axiom/lower_bound_ground", guarded);

        // Ground doubling instance: receiver >= 1 ==> pow(receiver) == 2 * pow(receiver - 1).
        //
        // Per-call instance of the quantified doubling axiom in
        // `assert_pow2_axioms`. Emitting it here as a guarded ground assertion
        // helps the solver when the quantified trigger cannot find both
        // `pow2(receiver)` and `pow2(receiver-1)` simultaneously (the
        // multi-trigger requires both ground terms to be present, which is
        // not always the case in a single VC). (Phase 3/4)
        let receiver_ge_one = self.solver.ge(receiver, one);
        let pow_minus_1_for_double = self.solver.apply(pow2_func, &[receiver_minus_1]);
        let two_times_prev = self.solver.mul(two, pow_minus_1_for_double);
        let doubling_eq = self.eq_term(pow, two_times_prev);
        let doubling_implication = self.solver.implies(receiver_ge_one, doubling_eq);
        let doubling_guarded = self.guard_with_active_path(doubling_implication);
        self.assert_solver_term("pow2_axiom/doubling_ground", doubling_guarded);

        // Ground non-negativity: receiver >= 0 ==> pow >= 1.
        let receiver_ge_zero = self.solver.ge(receiver, zero);
        let pow_ge_one = self.solver.ge(pow, one);
        let nonneg_implication = self.solver.implies(receiver_ge_zero, pow_ge_one);
        let nonneg_guarded = self.guard_with_active_path(nonneg_implication);
        self.assert_solver_term("pow2_axiom/nonneg_ground", nonneg_guarded);
    }

    /// Encode `deep_model()` as an Int-returning UF with ground term tracking (#2117).
    ///
    /// Replicates the UF declaration pattern from `encode_int_method_uf`,
    /// then records the `(smt_name, receiver_term)` pair so that
    /// `assert_deep_model_axioms` can eagerly instantiate the identity axiom
    /// as ground equalities (`deep_model(t) = t`) in addition to the quantified
    /// axiom. This bypasses ay-dpll's single-round E-matching limitation where
    /// the quantified axiom `forall x. deep_model(x) = x` may not fire on
    /// ground `deep_model(t)` terms.
    pub(super) fn encode_deep_model_uf(
        &mut self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Encode receiver first to get the concrete term and inferred sort
        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let param_sort = self.method_param_sort(receiver, receiver_term, prefix);
        let sort_tag = Self::method_sort_tag(&param_sort);
        let smt_name = format!("method_deep_model_1_{sort_tag}");
        let (result, final_symbol) = self.apply_method_func_with_actual_sort_retry(
            "method_call::deep_model",
            &smt_name,
            &[param_sort],
            Sort::Int,
            &[receiver_term],
        )?;

        // Track for eager ground instantiation
        self.record_deep_model_ground_term(final_symbol, receiver_term);

        Ok(result)
    }
}
