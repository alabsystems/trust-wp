// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bool-returning UF patterns: produces predicate, invariant inlining,
//! sort-drift retry for Bool method calls.
//!
//! Contains `encode_produces_predicate`, `encode_bool_method_predicate`,
//! and invariant body inlining helpers used by the method-call encoder.

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::{sort_context::resolve_nameable_expr, unsoundness, AYEncoder};
use crate::error::EncodingError;

impl AYEncoder {
    fn is_hashmap_list_invariant_body(expr: &PureExpr) -> bool {
        Self::expr_contains_logic_call(expr, "good_bucket")
            && Self::expr_contains_logic_call(expr, "no_double_binding")
    }

    fn expr_contains_logic_call(expr: &PureExpr, expected: &str) -> bool {
        let expected = Self::normalize_logic_name(expected);
        let mut found = false;
        expr.for_each_recursive(|node| {
            if found {
                return;
            }
            match node {
                PureExpr::LogicFnCall { name, .. }
                    if Self::normalize_logic_name(name).ends_with(&expected) =>
                {
                    found = true;
                }
                PureExpr::MethodCall { method, .. }
                    if Self::normalize_logic_name(method).ends_with(&expected) =>
                {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    fn normalize_logic_name(name: &str) -> String {
        name.chars().filter(|ch| *ch != '_').collect()
    }

    fn hashmap_list_predicate_list_sort(&self) -> Sort {
        self.get_datatype_decl("List")
            .cloned()
            .map(Sort::Datatype)
            .unwrap_or_else(|| Sort::Uninterpreted("List".to_string()))
    }

    fn restore_hashmap_list_predicate_arg(
        &mut self,
        term: &mut Term,
        param_sort: &mut Sort,
        list_sort: &Sort,
    ) {
        if *param_sort != Sort::Int {
            return;
        }
        let target_sort = list_sort.as_term_sort();
        if let Some(restored) = self.try_restore_seq_element_from_int(*term, &target_sort) {
            *term = restored;
            *param_sort = list_sort.clone();
        }
    }

    fn restore_hashmap_list_predicate_args(
        &mut self,
        method: &str,
        all_terms: &mut [Term],
        param_sorts: &mut [Sort],
    ) {
        let list_sort = self.hashmap_list_predicate_list_sort();
        match method {
            "no_double_binding" if all_terms.len() == 1 && param_sorts.len() == 1 => {
                self.restore_hashmap_list_predicate_arg(
                    &mut all_terms[0],
                    &mut param_sorts[0],
                    &list_sort,
                );
            }
            "good_bucket" if all_terms.len() == 3 && param_sorts.len() == 3 => {
                self.restore_hashmap_list_predicate_arg(
                    &mut all_terms[1],
                    &mut param_sorts[1],
                    &list_sort,
                );
            }
            _ => {}
        }
    }

    /// Encode `produces(visited, o)` as a Bool-returning uninterpreted function
    /// with explicit Seq sort for the `visited` parameter (#379).
    ///
    /// `produces` is the IteratorSpec relational predicate: given an iterator state
    /// `self`, a visited sequence, and a successor state `o`, it returns whether
    /// `self` transitions to `o` having produced `visited`. The `visited` parameter
    /// is always a `Seq`, but syntactic sort inference (`infer_expr_sort`) would
    /// return `Int` for bare variables. This method overrides that.
    ///
    /// Uses the same actual-sort retry mechanism as `encode_bool_method_predicate`
    /// and `encode_int_method_uf`: when `method_param_sort` infers richer sorts
    /// than the actual encoded term sorts (e.g., IterMut vs Int for iterator
    /// state variables), the first `safe_apply` fails on sort mismatch. The retry
    /// re-declares the UF with the actual term sorts and re-applies. (#994 RC2)
    pub(super) fn encode_produces_predicate(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if args.len() != 2 {
            return Err(EncodingError::unsupported(format!(
                "produces expects 2 arguments (visited, o), got {}",
                args.len()
            )));
        }

        // Ensure the Seq sort exists for the visited parameter without forcing
        // theory setup on the sort-only path.
        let seq_sort = self.get_seq_sort();

        // Register Seq sort hint for the visited parameter BEFORE encoding it,
        // so that `encode_pure_impl` declares the variable with Seq sort rather
        // than defaulting to Int. Without this, ay's `apply` panics on sort mismatch.
        let visited_is_nameable = resolve_nameable_expr(&args[0], prefix).is_some();
        if let Some(name) = resolve_nameable_expr(&args[0], prefix) {
            self.record_sort_hint(name, ExprSort::Seq);
        }

        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let visited_term = self.encode_pure_impl(&args[0], prefix)?;
        let visited_term = if visited_is_nameable {
            let bridged = self.bridge_int_to_seq_carrier(visited_term);
            self.coerce_to_seq(bridged)
        } else {
            self.coerce_to_seq(visited_term)
        };
        let o_term = self.encode_pure_impl(&args[1], prefix)?;

        let all_terms = vec![receiver_term, visited_term, o_term];

        // Sort signature: receiver=inferred, visited=Seq, o=inferred
        // Context-aware inference for produces predicate sorts. (#1965)
        let receiver_sort = self.method_param_sort(receiver, receiver_term, prefix);
        let o_sort = self.method_param_sort(&args[1], o_term, prefix);
        let param_sorts = vec![receiver_sort, seq_sort.clone(), o_sort];

        let smt_name = Self::bool_method_symbol("produces", &param_sorts);
        let func_decl = self.get_or_declare_method_func(&smt_name, &param_sorts, Sort::Bool);

        // Try with inferred sorts first, retry with actual term sorts on
        // mismatch. Recovery handles sort drift between inference and actual
        // encoding (e.g., IterMut inferred but Int encoded for iterator
        // state variables in quantifier-bound contexts). (#994 RC2)
        let (final_decl, term) =
            match self.safe_apply("method_call::produces", &func_decl, &all_terms) {
                Ok(term) => (func_decl, term),
                Err(original_err) => {
                    // `visited` is semantically Seq even when the encoded carrier
                    // term has fallen back to Int, so only retry the receiver and
                    // successor-state slots with their actual encoded sorts.
                    let mut retry_param_sorts: Vec<Sort> =
                        all_terms.iter().map(|t| self.solver.get_sort(*t)).collect();
                    retry_param_sorts[1] = seq_sort;
                    if retry_param_sorts == param_sorts {
                        return Err(original_err);
                    }
                    let retry_name = Self::bool_method_symbol("produces", &retry_param_sorts);
                    let retry_decl = self.get_or_declare_method_func(
                        &retry_name,
                        &retry_param_sorts,
                        Sort::Bool,
                    );
                    let term = self.safe_apply("method_call::produces", &retry_decl, &all_terms)?;
                    (retry_decl, term)
                }
            };

        // Materialize the user's open `produces` body in the invariant symbol's
        // argument frame so the loop invariant `iter_old.produces(produced, it)`
        // gains its index-property semantics. Completeness-only: the body is the
        // exact open `produces` definition (reused verbatim from the ground
        // pool), and a no-op when produces is opaque or driver-rewritten. (#produces-body)
        self.assert_user_produces_body_definition(&final_decl);

        self.assert_logical_fmap_iter_produces_decomposition(receiver, &final_decl)?;
        self.assert_logical_fmap_iter_view_bridge(receiver, receiver_term, prefix)?;
        self.assert_logical_fmap_iter_view_bridge(&args[1], o_term, prefix)?;
        // Ground-level length partition for FMapIter produces calls (#2116).
        // Asserted as a direct implication instead of relying on the full
        // transparent predicate decomposition (which contains nested quantifiers
        // that ay-dpll struggles to instantiate).
        let logical_fmap_iter_ground_length = self
            .assert_logical_fmap_iter_ground_length_partition(
                receiver, term, &args[0], &args[1], prefix,
            )?;
        // IterMut produces decomposition — snapshot-aware content-equality (#2238).
        // Fires the quantified axiom (with view projector for both Seq and
        // uninterpreted IterMut state sorts), ground-level length partition,
        // ground content equality, and view bridges for IterMut receivers.
        self.assert_iter_mut_produces_decomposition(receiver, &final_decl)?;
        self.assert_iter_mut_view_bridge(receiver, receiver_term, prefix)?;
        self.assert_iter_mut_view_bridge(&args[1], o_term, prefix)?;
        self.assert_iter_mut_ground_length_partition(receiver, term, &args[0], &args[1], prefix)?;
        self.assert_iter_mut_ground_content_equality(receiver, term, &args[0], prefix)?;
        self.assert_iter_mut_ground_remainder_equality(receiver, term, &args[0], &args[1], prefix)?;
        // Assert observed produces consequences on the successful decl. The
        // quantified produces axioms are intentionally not asserted here: SAT
        // precondition checks with independent produces calls can otherwise time
        // out in ay. Ground reflexivity/transitivity below is conservative and
        // sufficient for current VC proof paths.
        self.assert_produces_ground_transitivity(&final_decl, receiver_term, visited_term, o_term);

        Ok(
            logical_fmap_iter_ground_length.map_or(term, |length_partition| {
                self.solver.and(term, length_partition)
            }),
        )
    }

    pub(in crate::encoder) fn encode_bool_method_predicate(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Compute SMT name early to check for trivial invariant optimization (#1296)
        let pre_param_sorts: Vec<Sort> = std::iter::once(receiver)
            .chain(args.iter())
            .map(|e| self.infer_encoded_sort(e, prefix))
            .collect();
        let pre_smt_name = Self::bool_method_symbol(method, &pre_param_sorts);

        // Trivial invariant short-circuit (#1296): if this method was registered
        // with body `true`, return `true` directly instead of an uninterpreted
        // function application that would require E-matching to resolve.
        if self.is_trivial_type_invariant(&pre_smt_name) {
            unsoundness::increment(unsoundness::UnsoundnessCategory::InvariantTrueShortCircuit);
            return Ok(self.solver.bool_const(true));
        }
        // Fallback for un-rewritten "invariant" method calls (#1296): when a
        // quantifier-bound variable calls `.invariant()`, the driver cannot
        // resolve the type-qualified method name (no type info on bound vars).
        // If ALL registered type invariant axioms are trivially-true, then any
        // un-qualified `.invariant()` call must also be trivially true. This is
        // sound because un-qualified "invariant" only appears in quantifier
        // bodies where the receiver type is unknown.
        if method == "invariant" && self.all_type_invariants_trivially_true() {
            unsoundness::increment(unsoundness::UnsoundnessCategory::InvariantTrueShortCircuit);
            return Ok(self.solver.bool_const(true));
        }

        // Eager invariant body inlining (#726, #1296): inline the defining
        // axiom's body directly instead of creating a UF application. This
        // avoids the E-matching chain problem where ay cannot compose the body
        // axiom `forall self. inv(self) <=> body(self)` with the enclosing
        // formula.
        //
        // Fires at the top level (quantifier_depth == 0) and inside existential
        // scopes (exists_quantifier_depth > 0). Does NOT fire inside
        // forall-only scopes: ay-dpll handles forall via Skolemization +
        // E-matching, which requires UF applications to remain as triggers for
        // the body axiom. Inlining inside forall would remove the UF trigger,
        // causing the body axiom to go unresolved → ay-dpll returns Unknown.
        //
        // Top-level inlining (#1296): ay-dpll's model builder can fail to
        // respect the body axiom for ground UF calls, returning an invalid
        // model that triggers "model validation failed" → Unknown. Inlining
        // bypasses this ay limitation for ground invariant calls.
        if self.quantifier_state.exists_quantifier_depth() > 0
            || self.quantifier_state.quantifier_depth() == 0
        {
            if let Some(result) = self.try_inline_invariant_body(&pre_smt_name, receiver, prefix) {
                return result;
            }
        }

        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let arg_terms: Vec<Term> = args
            .iter()
            .map(|arg| self.encode_pure_impl(arg, prefix))
            .collect::<Result<Vec<_>, _>>()?;

        // Recompute param sorts after term encoding so wrapper-induced declarations
        // (`View(_)`, `Deref(_)`) are reflected in `var_sorts` before declaring the UF.
        // This prevents declaration/apply sort drift on first use. (#1805)
        let mut all_terms = Vec::with_capacity(1 + arg_terms.len());
        all_terms.push(receiver_term);
        all_terms.extend(arg_terms.iter().copied());

        let mut param_sorts: Vec<Sort> = std::iter::once((receiver, receiver_term))
            .chain(args.iter().zip(arg_terms.iter().copied()))
            .map(|(expr, term)| self.method_param_sort(expr, term, prefix))
            .collect();
        self.restore_hashmap_list_predicate_args(method, &mut all_terms, &mut param_sorts);
        let smt_name = Self::bool_method_symbol(method, &param_sorts);

        // Post-encoding invariant fast paths (#2620): when sort drift causes
        // pre_smt_name ≠ smt_name, the pre-encoding fast paths above may have
        // missed a trivial invariant or inline-eligible axiom registered under
        // the post-encoding symbol. Re-check with the corrected name.
        //
        // Also saves the normalized registration symbol (`invariant_source_symbol`)
        // for post-retry materialization: if the fast paths don't fire (e.g.,
        // forall-only scopes with non-trivial invariants), the retry UF needs a
        // matching quantified axiom asserted under `final_symbol`.
        let invariant_source_symbol = if smt_name == pre_smt_name {
            None
        } else {
            // ay-dpll exposes Datatype carriers as Uninterpreted sorts on
            // term reads (#2257), so method_param_sort may return
            // Uninterpreted("X") while type invariant registration used
            // Datatype(X). Normalize Uninterpreted→Datatype for known
            // registered datatypes so the lookup matches the axiom
            // registration symbol.
            let normalized_sorts: Vec<Sort> = param_sorts
                .iter()
                .map(|s| match s {
                    Sort::Uninterpreted(name) => {
                        if let Some(dt) = self.get_datatype_decl(name) {
                            Sort::Datatype(dt.clone())
                        } else {
                            s.clone()
                        }
                    }
                    other => other.clone(),
                })
                .collect();
            let lookup_name = Self::bool_method_symbol(method, &normalized_sorts);
            if self.is_trivial_type_invariant(&lookup_name) {
                unsoundness::increment(unsoundness::UnsoundnessCategory::InvariantTrueShortCircuit);
                return Ok(self.solver.bool_const(true));
            }
            if self.quantifier_state.exists_quantifier_depth() > 0
                || self.quantifier_state.quantifier_depth() == 0
            {
                if let Some(result) = self.try_inline_invariant_body_with_term(
                    &lookup_name,
                    receiver,
                    receiver_term,
                    prefix,
                ) {
                    return result;
                }
            }
            Some(lookup_name)
        };

        let (result, final_symbol) = self.apply_method_func_with_actual_sort_retry(
            &format!("method_call::bool_predicate::{method}"),
            &smt_name,
            &param_sorts,
            Sort::Bool,
            &all_terms,
        )?;

        // Materialize retry-time invariant metadata (#2620): when sort drift
        // was detected above but fast paths didn't fire (e.g., forall-only
        // scopes with non-trivial invariants), alias the invariant's trivial
        // marker and defining axiom from the registration symbol onto
        // final_symbol so E-matching can fire on the retry UF.
        if let Some(ref source_symbol) = invariant_source_symbol {
            self.materialize_retry_type_invariant_symbol(source_symbol, &final_symbol)?;
        }

        // Sorting Stage A (#sorting-stage-a): for `permutation_of` / `exchange`
        // predicates, assert the SOUND permutation/exchange equivalence + swap
        // bridge axiom bundle (completeness-only; see permutation_axioms.rs).
        // Done before the `all_terms` move below; the helper internally gates
        // its per-call ground seeds on quantifier depth.
        if method == "permutation_of" || method == "exchange" {
            self.assert_permutation_exchange_axioms(method, &param_sorts, &all_terms, result);
        }

        // nth_bit defining axiom (cc/arithmetic). In `#[bitwise_proof]` mode
        // `nth_bit` is otherwise an opaque bool UF with zero constraints, so
        // any obligation over it is trivially SAT. For a concrete bit index
        // `n`, the bit is fully determined: for every non-negative integer `x`,
        //   nth_bit(x, n) <=> ((x div 2^n) mod 2 == 1)
        // This div/mod identity matches Why3's `UIntNBW.nth` / `IntNBW.nth` on
        // the value's two's-complement bitvector for every non-negative `x`
        // (a non-negative value has identical bits under the signed and
        // unsigned interpretations, and out-of-width indices read 0 under
        // both). The `x >= 0` guard keeps the axiom sound for a symbolic signed
        // receiver — it constrains nothing about negative values. The general
        // symbolic bit index needs QF_BV lowering (future work). Ground only:
        // inside a quantifier the arguments are bound variables, not concrete
        // literals. (#bitwise nth_bit)
        if method == "nth_bit" && self.quantifier_state.quantifier_depth() == 0 {
            self.assert_nth_bit_defining_axiom(receiver_term, arg_terms.first().copied(), result);
        }

        // Register ground pool entry for type invariant method calls so that
        // `assert_ground_pool_instances` can produce ground instances of the
        // defining axiom. Without this, ay-dpll E-matching may not fire on
        // `inv(result)` in the two-phase axiom solving pipeline, causing the
        // axiom-free probe to find SAT and the rescue path to return Failed.
        // Only register at ground level (not inside quantifier bodies where
        // arguments are bound variables, not ground terms). (#994, #1965)
        if self.quantifier_state.quantifier_depth() == 0 {
            let mut all_exprs = Vec::with_capacity(1 + args.len());
            all_exprs.push(receiver.clone());
            all_exprs.extend(args.iter().cloned());
            self.ground_pool.register_with_path_conditions(
                &final_symbol,
                result,
                all_terms,
                all_exprs,
                self.active_path_conditions_cloned(),
            );
            self.assert_hashmap_list_invariant_len_consequence(
                &final_symbol,
                result,
                receiver_term,
            )?;
        }

        Ok(result)
    }

    /// Emit the `nth_bit` defining axiom for a ground bit index.
    ///
    /// See the call site in `encode_bool_method_predicate` for the soundness
    /// argument. Fires only when the bit index `n` is a concrete non-negative
    /// integer literal (so `2^n` is a computable constant) and the receiver is
    /// Int-sorted; otherwise it is a no-op and the opaque UF is left in place
    /// (no regression relative to today's behaviour).
    fn assert_nth_bit_defining_axiom(
        &mut self,
        receiver_term: Term,
        arg_term: Option<Term>,
        result: Term,
    ) {
        use num_traits::ToPrimitive;

        let Some(arg_term) = arg_term else {
            return;
        };
        if self.solver.get_sort(receiver_term) != Sort::Int {
            return;
        }
        // The bit index must be a concrete non-negative integer literal for the
        // ground div/mod instance to be materialisable.
        let Some(n) = self.term_int_literal(arg_term) else {
            return;
        };
        // `to_u32` rejects negative and pathologically large indices in one
        // step; real bit indices are far below the machine width.
        let Some(n_u32) = n.to_u32() else {
            return;
        };
        if n_u32 > 4096 {
            return;
        }
        // 2^n as an arbitrary-precision constant (n can exceed i64 bit width for
        // wide machine ints such as u128).
        let two_pow_n = num_bigint::BigInt::from(1u32) << (n_u32 as usize);
        let two_pow_n = self.solver.int_const_bigint(&two_pow_n);
        let x_div = self.solver.int_div(receiver_term, two_pow_n);
        let two = self.solver.int_const(2);
        let x_mod = self.solver.modulo(x_div, two);
        let one = self.solver.int_const(1);
        let bit_set = self.solver.eq(x_mod, one);
        let iff = self.solver.iff(result, bit_set);
        let zero = self.solver.int_const(0);
        let x_nonneg = self.solver.ge(receiver_term, zero);
        let guarded = self.solver.implies(x_nonneg, iff);
        self.solver.assert_term(guarded);
    }

    /// Try to inline a type invariant body when inside a quantifier scope (#726).
    ///
    /// Searches the ground pool's registered axioms for a defining axiom matching
    /// `smt_name`. If found, encodes the receiver, binds the self parameter to the
    /// receiver term, and encodes the axiom body directly. This produces the
    /// semantically equivalent expression without requiring E-matching to chain
    /// the body axiom with the enclosing quantifier.
    ///
    /// Returns `None` if no matching axiom is found, falling through to normal
    /// UF encoding.
    fn try_inline_invariant_body(
        &mut self,
        smt_name: &str,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<Result<Term, EncodingError>> {
        use super::super::ground_pool::AxiomKind;

        // Find the defining axiom for this invariant method
        let (self_param, body) = {
            let axiom = self.ground_pool.axioms().iter().find(|a| {
                a.fn_symbol == smt_name && a.kind == AxiomKind::Defining && a.params.len() == 1
            })?;
            (axiom.params[0].clone(), axiom.body.clone())
        };
        if Self::is_hashmap_list_invariant_body(&body) {
            return None;
        }

        // Encode the receiver expression
        let receiver_term = match self.encode_pure_impl(receiver, prefix) {
            Ok(t) => t,
            Err(e) => return Some(Err(e)),
        };
        if let Err(err) = self.register_inlined_invariant_ground_application(
            smt_name,
            receiver,
            receiver_term,
            prefix,
        ) {
            return Some(Err(err));
        }

        // Bind self parameter to the encoded receiver, encode the body
        let old = self.insert_var(self_param.clone(), receiver_term);
        let result = self.encode_pure_impl(&body, prefix);

        // Restore previous binding
        self.restore_var(&self_param, old);

        Some(result)
    }

    /// Try to inline a type invariant body using a pre-encoded receiver term (#2620).
    ///
    /// Same as [`try_inline_invariant_body`] but skips receiver encoding — used
    /// in the post-encoding fast path when sort drift causes a symbol name change
    /// and the receiver has already been encoded.
    fn try_inline_invariant_body_with_term(
        &mut self,
        smt_name: &str,
        receiver: &PureExpr,
        receiver_term: ay_dpll::api::Term,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<Result<Term, EncodingError>> {
        use super::super::ground_pool::AxiomKind;

        let (self_param, body) = {
            let axiom = self.ground_pool.axioms().iter().find(|a| {
                a.fn_symbol == smt_name && a.kind == AxiomKind::Defining && a.params.len() == 1
            })?;
            (axiom.params[0].clone(), axiom.body.clone())
        };
        if Self::is_hashmap_list_invariant_body(&body) {
            return None;
        }

        if let Err(err) = self.register_inlined_invariant_ground_application(
            smt_name,
            receiver,
            receiver_term,
            prefix,
        ) {
            return Some(Err(err));
        }

        let old = self.insert_var(self_param.clone(), receiver_term);
        let result = self.encode_pure_impl(&body, prefix);
        self.restore_var(&self_param, old);

        Some(result)
    }

    fn register_inlined_invariant_ground_application(
        &mut self,
        smt_name: &str,
        receiver: &PureExpr,
        receiver_term: Term,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        if self.quantifier_state.quantifier_depth() != 0 {
            return Ok(());
        }

        let receiver_sort = self.method_param_sort(receiver, receiver_term, prefix);
        let (application, _) = self.apply_method_func_with_actual_sort_retry(
            "method_call::inline_invariant",
            smt_name,
            &[receiver_sort],
            Sort::Bool,
            &[receiver_term],
        )?;
        self.ground_pool.register_with_path_conditions(
            smt_name,
            application,
            vec![receiver_term],
            vec![receiver.clone()],
            self.active_path_conditions_cloned(),
        );
        Ok(())
    }

    fn assert_hashmap_list_invariant_len_consequence(
        &mut self,
        smt_name: &str,
        inv_app: Term,
        receiver_term: Term,
    ) -> Result<(), EncodingError> {
        use super::super::ground_pool::AxiomKind;

        let Some(body) = self.ground_pool.axioms().iter().find_map(|axiom| {
            (axiom.fn_symbol == smt_name
                && axiom.kind == AxiomKind::Defining
                && axiom.params.len() == 1)
                .then(|| axiom.body.clone())
        }) else {
            return Ok(());
        };
        if !Self::is_hashmap_list_invariant_body(&body)
            || !Self::hashmap_list_invariant_body_has_len_positive(&body)
        {
            return Ok(());
        }

        let receiver_sort = self.solver.get_sort(receiver_term);
        let seq_sort = self.get_seq_sort();
        let buckets_decl =
            self.get_or_declare_logic_func("myhashmap_buckets", &[receiver_sort], seq_sort);
        let buckets = self.safe_apply(
            "method_call/hashmap_list_invariant_len::myhashmap_buckets",
            &buckets_decl,
            &[receiver_term],
        )?;
        let buckets_len = self.seq_len_term(buckets)?;
        let zero = self.solver.int_const(0);
        let len_positive = self.solver.lt(zero, buckets_len);

        let mut guards = self.active_path_conditions_cloned();
        guards.push(inv_app);
        let guard = guards
            .into_iter()
            .reduce(|acc, term| self.solver.and(acc, term))
            .unwrap_or_else(|| self.solver.bool_const(true));
        let fact = self.solver.implies(guard, len_positive);
        self.assert_solver_term("method_call/hashmap_list_invariant_len", fact);
        Ok(())
    }

    fn hashmap_list_invariant_body_has_len_positive(expr: &PureExpr) -> bool {
        let mut found = false;
        expr.for_each_recursive(|node| {
            if found {
                return;
            }
            let PureExpr::BinOp(left, trust_wp_core::formula::BinOp::Lt, right) = node else {
                return;
            };
            if matches!(left.as_ref(), PureExpr::Int(0))
                && (Self::expr_contains_logic_call(right, "seq_len")
                    || Self::expr_contains_logic_call(right, "len"))
            {
                found = true;
            }
        });
        found
    }
}
