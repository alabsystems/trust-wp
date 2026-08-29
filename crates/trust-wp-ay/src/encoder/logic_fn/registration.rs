// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{FuncDecl, Sort, Term};
use tracing::debug;
use trust_wp_core::{
    formula::{ExprSort, PureExpr},
    logic::{LogicFnDef, LogicMode},
};

use crate::{
    encoder::{require_domain_sort, sort_context::is_seq_family_sort, unsoundness, AYEncoder},
    error::EncodingError,
};

/// True iff `expr` contains a (possibly nested) call to the logic function
/// named `fn_name`. Uses the complete depth-limited traversal so no PureExpr
/// variant is missed — important because a missed recursive call would let a
/// recursive branch be emitted as a "base case" and drive the solver into
/// non-terminating unfolding.
fn pure_expr_mentions_logic_call(expr: &PureExpr, fn_name: &str) -> bool {
    use trust_wp_core::formula::PureExprDepthLimitedTraversalExt as _;
    let mut found = false;
    expr.for_each_recursive_with_depth_limit(crate::encoder::MAX_ENCODING_DEPTH, |node| {
        if let PureExpr::LogicFnCall { name, .. } = node {
            if name == fn_name {
                found = true;
            }
        }
    });
    found
}

/// If `logic_fn`'s body is `Ite(cond, then, else)` with exactly one branch that
/// makes no recursive call to the function, return `(cond, base_branch,
/// guard_is_positive)`: the guard under which the function provably equals that
/// non-recursive base branch (`guard_is_positive` = the `then` branch is the
/// base, so the guard is `cond`; otherwise the `else` branch is the base and the
/// guard is `!cond`).
///
/// This recognises the `if base_guard { base } else { ..recurse.. }` shape (e.g.
/// `num_of_pos(i,j,t) = if i>=j { 0 } else { num_of_pos(i,j-1,t) + .. }`). Only a
/// clean base/step split qualifies — bodies where both or neither branch recurse
/// are left to the bounded-ground-instance path.
fn recursive_ite_base_case(logic_fn: &LogicFnDef) -> Option<(PureExpr, PureExpr, bool)> {
    let PureExpr::Ite(cond, then_b, else_b) = logic_fn.body() else {
        return None;
    };
    let name = logic_fn.name();
    let then_rec = pure_expr_mentions_logic_call(then_b, name);
    let else_rec = pure_expr_mentions_logic_call(else_b, name);
    match (then_rec, else_rec) {
        (false, true) => Some(((**cond).clone(), (**then_b).clone(), true)),
        (true, false) => Some(((**cond).clone(), (**else_b).clone(), false)),
        _ => None,
    }
}

fn skip_global_quantified_axioms_for_datatype_logic(
    logic_fn: &LogicFnDef,
    param_sorts: &[Sort],
) -> bool {
    // Datatype-match definitions/specs are still registered with the ground
    // pool. The global forall form can make satisfiable counterexample queries
    // depend on incomplete datatype matching/model validation and fail closed
    // to Unknown.
    has_datatype_param(param_sorts)
        && (logic_fn.is_recursive() || logic_body_contains_match(logic_fn.body()))
}

fn has_datatype_param(param_sorts: &[Sort]) -> bool {
    param_sorts
        .iter()
        .any(|sort| matches!(sort, Sort::Datatype(_)))
}

fn logic_fn_requires_contains_quantifier(logic_fn: &LogicFnDef) -> bool {
    logic_fn.requires().iter().any(|req| {
        req.any_recursive(|node| matches!(node, PureExpr::Forall { .. } | PureExpr::Exists { .. }))
    })
}

fn skip_global_defining_axiom_for_bit_count_logic(logic_fn: &LogicFnDef) -> bool {
    !logic_fn.is_recursive()
        && logic_fn.requires().is_empty()
        && logic_fn.ensures().is_empty()
        && logic_body_contains_bit_count_method(logic_fn.body())
}

fn skip_global_defining_axiom_for_hashmap_list_good_bucket(logic_fn: &LogicFnDef) -> bool {
    logic_fn.params().len() == 3
        && logic_fn.requires().is_empty()
        && logic_fn.ensures().is_empty()
        && trust_wp_core::logic::logic_fn_smt_name(logic_fn.name()) == "logic_good__bucket"
        && matches!(logic_fn.body(), PureExpr::Forall { .. })
}

fn skip_global_defining_axiom_for_hashmap_list_bucket_ix(logic_fn: &LogicFnDef) -> bool {
    logic_fn.params().len() == 2
        && logic_fn.requires().is_empty()
        && logic_fn.ensures().is_empty()
        && trust_wp_core::logic::logic_fn_smt_name(logic_fn.name()) == "logic_bucket__ix"
}

fn skip_global_defining_axiom_for_hashmap_list_bucket(logic_fn: &LogicFnDef) -> bool {
    logic_fn.params().len() == 2
        && logic_fn.requires().is_empty()
        && logic_fn.ensures().is_empty()
        && trust_wp_core::logic::logic_fn_smt_name(logic_fn.name()) == "logic_bucket"
}

fn logic_body_contains_match(expr: &PureExpr) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        if matches!(node, PureExpr::Match { .. }) {
            found = true;
        }
    });
    found
}

fn skip_global_quantified_logic_axioms(logic_fn: &LogicFnDef) -> bool {
    // Guarded definitions are registered in the ground pool and instantiated
    // only when their requires can be checked for a concrete call. Keeping the
    // global `forall args. requires(args) => f(args) = body(args)` visible makes
    // satisfiable counterexample queries depend on quantified model synthesis.
    !logic_fn.requires().is_empty()
}

fn skip_global_quantified_spec_axioms(
    logic_fn: &LogicFnDef,
    _param_sorts: &[Sort],
    encoder: &AYEncoder,
) -> bool {
    (logic_fn.is_recursive() && logic_fn_requires_contains_quantifier(logic_fn))
        || (encoder
            .encoding_cache
            .logic_fn_defining_axioms_ground_only()
            && !logic_fn.requires().is_empty())
}

fn logic_body_contains_bit_count_method(expr: &PureExpr) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        if matches!(
            node,
            PureExpr::MethodCall { method, args, .. }
                if args.is_empty()
                    && matches!(
                        method.as_str(),
                        "leading_zeros_logic"
                            | "trailing_zeros_logic"
                            | "leading_ones_logic"
                            | "trailing_ones_logic"
                    )
        ) {
            found = true;
        }
    });
    found
}

fn unsupported_wrapper_body(expr: &PureExpr) -> Option<&'static str> {
    let mut unsupported = None;
    expr.for_each_recursive(|node| {
        if unsupported.is_some() {
            return;
        }
        let (kind, inner) = match node {
            PureExpr::Deref(inner) => ("deref", inner.as_ref()),
            PureExpr::Final(inner) => ("final", inner.as_ref()),
            _ => return,
        };
        if !wrapper_base_supported(inner) {
            unsupported = Some(kind);
        }
    });
    unsupported
}

fn wrapper_base_supported(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Var(_, _)
            | PureExpr::MethodCall { .. }
            | PureExpr::LogicFnCall { .. }
            | PureExpr::BinOp(_, _, _)
            | PureExpr::UnOp(_, _)
            | PureExpr::Old(_)
            | PureExpr::Deref(_)
            | PureExpr::Final(_)
            | PureExpr::Int(_)
            | PureExpr::Bool(_)
            | PureExpr::Float(_)
            | PureExpr::Ite(_, _, _)
    )
}

impl AYEncoder {
    /// Register a logic function with its defining axiom.
    ///
    /// # Contracts
    ///
    /// ```text
    /// REQUIRES: logic_fn.name is a valid identifier.
    /// REQUIRES: logic_fn.params are distinct parameter names.
    /// REQUIRES: logic_fn.body is a well-formed PureExpr referencing only params.
    ///
    /// ENSURES (Soundness): After registration, the solver assumes:
    ///     forall params: logic_fn(params) = body[params]
    ///     This axiom is triggered by E-matching on logic_fn applications.
    ///
    /// ENSURES (Idempotence): Repeated registration is safe (no-op if already registered).
    ///
    /// ENSURES (Error): Err only if body contains unsupported constructs.
    /// ```
    ///
    /// This declares the function as an uninterpreted SMT function and asserts
    /// a defining axiom that relates the function to its body.
    ///
    /// For a logic function:
    /// ```text
    /// #[logic]
    /// fn max(a: Int, b: Int) -> Int {
    ///     if a >= b { a } else { b }
    /// }
    /// ```
    ///
    /// This generates (with trigger pattern for E-matching):
    /// ```smt2
    /// (declare-fun logic_max (Int Int) Int)
    /// (assert (forall ((a Int) (b Int))
    ///   (! (= (logic_max a b) (ite (>= a b) a b))
    ///      :pattern ((logic_max a b)))))
    /// ```
    ///
    /// # Arguments
    /// * `logic_fn` - The logic function definition to register
    ///
    /// # Errors
    /// Returns `EncodingError::Unsupported` if the function body contains
    /// expressions that cannot be encoded (e.g., unsupported method calls
    /// or complex deref expressions).
    pub(crate) fn register_logic_fn(&mut self, logic_fn: &LogicFnDef) -> Result<(), EncodingError> {
        self.register_logic_fn_with_mode(logic_fn, logic_fn.mode())
    }

    /// Register a logic function with an explicit effective mode.
    ///
    /// This allows the driver to pass mode overrides (from module-level
    /// scoping) without deep-cloning `LogicFnDef` structs. (#564)
    #[allow(clippy::too_many_lines)]
    pub(super) fn register_logic_fn_with_mode(
        &mut self,
        logic_fn: &LogicFnDef,
        effective_mode: LogicMode,
    ) -> Result<(), EncodingError> {
        self.register_view_return_sort_if_supported(logic_fn);
        if self.register_direct_view_fn_if_supported(logic_fn, effective_mode) {
            return Ok(());
        }
        self.preseed_logic_fn_return_sort_hint(logic_fn);

        let smt_name = trust_wp_core::logic::logic_fn_smt_name(logic_fn.name());

        // Skip if already registered with its axiom
        if self.has_logic_fn_axiom_asserted(&smt_name) {
            return Ok(());
        }

        let func_decl = self.declare_logic_fn_signature(logic_fn);

        // Suppress the defining axiom for opaque logic functions.
        // A function is opaque when:
        // - Explicitly marked `is_opaque`, OR
        // - Mode is `Default` (opaque by default, matching Creusot semantics)
        //
        // Open/OpenSelf/Prophetic modes emit the axiom (body is visible).
        // OpenSelf scoping is handled by the driver (scope_logic_fn_modes
        // in callbacks.rs), which computes effective modes per-caller and
        // passes them as overrides to avoid deep-cloning LogicFnDef structs.
        //
        // IMPORTANT: Even when the defining axiom is suppressed, spec axioms
        // from `ensures` clauses are still emitted. In Creusot, spec_axioms
        // are emitted as module-level axioms visible to all proofs in scope,
        // regardless of function opacity. The ensures clause represents a
        // user-proven property that callers should be able to rely on. (#1296)
        if logic_fn.is_opaque() || effective_mode == LogicMode::Default {
            let skip_global_spec_axioms =
                skip_global_quantified_spec_axioms(logic_fn, func_decl.domain(), self);
            if !logic_fn.ensures().is_empty() {
                self.emit_spec_axioms(logic_fn, &func_decl, &smt_name, !skip_global_spec_axioms)?;
            }
            self.mark_logic_fn_axiom_asserted(smt_name);
            return Ok(());
        }

        // Create bound variables for each parameter with correct sorts.
        // Use the FuncDecl's domain sorts (from declare_logic_fn_signature) which
        // incorporate both param_sorts hints AND infer_seq_like_params fallback.
        // Previously used resolve_logic_param_sort which only checks param_sorts,
        // causing Int sort for params detected as Seq via body inference. (#1572)
        let domain = func_decl.domain();
        let param_sorts: Vec<Sort> = logic_fn
            .params()
            .iter()
            .enumerate()
            .map(|(i, _)| {
                require_domain_sort(domain, i, &format!("register_logic_fn:{}", logic_fn.name()))
            })
            .collect::<Result<_, _>>()?;
        let mut bound_vars: Vec<Term> = Vec::new();
        let mut old_bindings: Vec<(String, Option<Term>)> = Vec::new();
        let mut old_sorts: Vec<(String, Option<Sort>)> = Vec::new();

        for (param, param_sort) in logic_fn.params().iter().zip(param_sorts.iter()) {
            let qvar_id = self.next_quantifier_var_id();
            let bound_var = self.solver.fresh_var(
                &format!("logic_param_{param}_{qvar_id}"),
                param_sort.clone(),
            );
            bound_vars.push(bound_var);

            // Record Seq sort hints so is_seq_receiver dispatches correctly
            // during body encoding. Without this, method calls like `t.index(j)`
            // on Seq-sorted bound vars route to FMap encoding instead of Seq
            // encoding, causing sort mismatches. (#1572)
            if is_seq_family_sort(param_sort) {
                self.record_sort_hint(param.clone(), ExprSort::Seq);
            }
            let old_sort = self.insert_var_sort(param.clone(), param_sort.clone());
            old_sorts.push((param.clone(), old_sort));

            // Save old binding and install new one
            let old = self.insert_var(param.clone(), bound_var);
            old_bindings.push((param.clone(), old));
            // Logic-function params are pure logical values, so wrapper/view
            // encoding must collapse to the bound term instead of synthesizing
            // fresh `{param}_view` variables. (#1635)
            self.bind_quantifier_var(param.clone());
        }

        // Encode the body and requires with parameters in scope.
        // Increment quantifier_depth so that inner LogicFnCall applications
        // are NOT registered with the ground pool — their arguments are bound
        // variables, not ground terms. (#1965, Lane 5)
        //
        // When the function's return sort is Mapping, enable closure_mapping_context
        // so that single-parameter closures in the body are encoded as
        // Mapping-sorted constants with defining axioms. This handles the
        // Creusot pattern: `#[logic] fn g() -> Mapping<Int, bool> { |x| ... }`.
        // (#2683)
        let return_sort = func_decl.range().clone();

        let skip_global_defining_axiom = (!bound_vars.is_empty()
            && self.encoding_cache.logic_fn_defining_axioms_ground_only())
            || logic_fn.is_recursive()
            || skip_global_quantified_logic_axioms(logic_fn)
            || skip_global_quantified_axioms_for_datatype_logic(logic_fn, &param_sorts)
            || skip_global_defining_axiom_for_bit_count_logic(logic_fn)
            || skip_global_defining_axiom_for_hashmap_list_good_bucket(logic_fn)
            || skip_global_defining_axiom_for_hashmap_list_bucket_ix(logic_fn)
            || skip_global_defining_axiom_for_hashmap_list_bucket(logic_fn);
        if skip_global_defining_axiom {
            debug!("  registering {}: skipping global defining axiom", smt_name);

            if let Some(kind) = unsupported_wrapper_body(logic_fn.body()) {
                for param in logic_fn.params().iter().rev() {
                    self.unbind_quantifier_var(param);
                }
                for (name, old_sort) in old_sorts {
                    self.restore_var_sort(&name, old_sort);
                }
                for (name, old) in old_bindings {
                    self.restore_var(&name, old);
                }
                return Err(EncodingError::unsupported(format!(
                    "complex {kind} expression in logic function body: {:?}",
                    logic_fn.body()
                )));
            }

            if !bound_vars.is_empty() {
                use crate::encoder::ground_pool::{AxiomEntry, AxiomKind};

                self.ground_pool.register_axiom(AxiomEntry {
                    fn_symbol: smt_name.clone(),
                    params: logic_fn.params().to_vec(),
                    body: logic_fn.body().clone(),
                    requires: logic_fn.requires().to_vec(),
                    func_decl: func_decl.clone(),
                    return_sort: return_sort.clone(),
                    kind: AxiomKind::Defining,
                });

                // Recursive logic fns skip the global defining-forall (it would
                // drive the solver into infinite unfolding), relying on bounded
                // GROUND instances — but those only fire when EVERY argument is
                // ground. A base-case branch that makes no recursive call is safe
                // to assert as a guarded global forall, which lets the solver
                // discharge e.g. `num_of_pos(0, j, t) == 0` when `0 >= j` even
                // with a symbolic Seq `t` (the base value doesn't depend on `t`).
                // This is exactly the fact filter_positive's loop_initialization
                // needs. SOUND: `cond ==> f(params) == then` is a literal
                // consequence of the body `Ite(cond, then, else)`. TERMINATING:
                // the chosen branch is recursion-free, so the axiom's `f(params)`
                // trigger introduces no new `f`-applications. Best-effort: a
                // base-case encoding error just skips the optimization.
                if logic_fn.is_recursive() {
                    if let Some((cond_expr, base_expr, guard_positive)) =
                        recursive_ite_base_case(logic_fn)
                    {
                        self.quantifier_state.inc_quantifier_depth();
                        let emitted: Result<(), EncodingError> = (|| {
                            let cond_term = self.encode_pure(&cond_expr)?;
                            let base_term = self.encode_pure(&base_expr)?;
                            let app = self.safe_apply(
                                &format!("recursive_base_case:{}", logic_fn.name()),
                                &func_decl,
                                &bound_vars,
                            )?;
                            let mut guard = if guard_positive {
                                cond_term
                            } else {
                                self.solver.not(cond_term)
                            };
                            // SOUNDNESS: the defining axiom is REQUIRES-guarded
                            // (`guard_with_requires` on the normal path), so
                            // `f(params) == base` only holds where the precondition
                            // holds. Fold the fn's `requires` into the base-case
                            // guard; an unguarded axiom over-constrains `f` outside
                            // its domain for any recursive fn with a `#[requires]`
                            // (e.g. `id`/`set_max`) and could manufacture a spurious
                            // UNSAT (false-accept). Empty requires leaves the guard
                            // unchanged, so num_of_pos and friends are unaffected.
                            for req in logic_fn.requires() {
                                let req_term = self.encode_pure(req)?;
                                guard = self.solver.and(req_term, guard);
                            }
                            let eq = self.eq_term(app, base_term);
                            let implied = self.solver.implies(guard, eq);
                            let axiom =
                                self.solver
                                    .forall_with_triggers(&bound_vars, implied, &[&[app]]);
                            self.assert_solver_term("recursive_base_case_axiom", axiom);
                            Ok(())
                        })();
                        self.quantifier_state.dec_quantifier_depth();
                        let _ = emitted;
                    }
                }
            }

            for param in logic_fn.params().iter().rev() {
                self.unbind_quantifier_var(param);
            }
            for (name, old_sort) in old_sorts {
                self.restore_var_sort(&name, old_sort);
            }
            for (name, old) in old_bindings {
                self.restore_var(&name, old);
            }

            if !logic_fn.ensures().is_empty() {
                self.emit_spec_axioms(
                    logic_fn,
                    &func_decl,
                    &smt_name,
                    !skip_global_quantified_spec_axioms(logic_fn, &param_sorts, self),
                )?;
            }

            self.mark_logic_fn_axiom_asserted(smt_name);
            return Ok(());
        }

        let mapping_return =
            return_sort == crate::encoder::sort_context::sort_inference::mapping_sort();
        let old_closure_mapping = if mapping_return {
            self.closure_state.set_mapping_context(true)
        } else {
            self.closure_state.mapping_context()
        };
        self.quantifier_state.inc_quantifier_depth();
        let body_result = self.encode_pure(logic_fn.body());
        let requires_result: Result<Vec<Term>, EncodingError> = if logic_fn.requires().is_empty() {
            Ok(Vec::new())
        } else {
            logic_fn
                .requires()
                .iter()
                .map(|req| self.encode_pure(req))
                .collect()
        };
        self.quantifier_state.dec_quantifier_depth();
        self.closure_state.set_mapping_context(old_closure_mapping);

        // Restore all bindings (always, even on error)
        for param in logic_fn.params().iter().rev() {
            self.unbind_quantifier_var(param);
        }
        for (name, old_sort) in old_sorts {
            self.restore_var_sort(&name, old_sort);
        }
        for (name, old) in old_bindings {
            self.restore_var(&name, old);
        }

        // Propagate any encoding error
        let body_term = body_result?;
        let requires_terms = requires_result?;

        // Create the function application: logic_fn(param1, param2, ...)
        // Use safe_apply to catch ay sort mismatches that can occur when
        // DatatypeSort naming diverges between registration and encoding
        // contexts (e.g., "List" vs "Adt_Cons_Nil"). (#1965, #2002)
        let fn_application = self.safe_apply(
            &format!("register_logic_fn:{}", logic_fn.name()),
            &func_decl,
            &bound_vars,
        )?;

        // Create the equality: logic_fn(params...) = body.
        // Bool-returning logic functions now rely on the native equality
        // helper because the current ay pin includes the #1179 fix.
        // (return_sort already computed above for closure_mapping_context.)

        // Helper: build requires guard around a term.
        let guard_with_requires = |solver: &mut ay_dpll::api::Solver, term: Term| -> Term {
            match requires_terms.as_slice() {
                [] => term,
                [single] => solver.implies(*single, term),
                [first, rest @ ..] => {
                    let requires_term = rest.iter().fold(*first, |acc, &req| solver.and(acc, req));
                    solver.implies(requires_term, term)
                }
            }
        };

        // Helper: wrap axiom body in a quantifier with trigger (or assert directly).
        let assert_axiom =
            |solver: &mut ay_dpll::api::Solver, body: Term, bound_vars: &[Term], trigger: Term| {
                if bound_vars.is_empty() {
                    solver.assert_term(body);
                } else {
                    let axiom = solver.forall_with_triggers(bound_vars, body, &[&[trigger]]);
                    solver.assert_term(axiom);
                }
            };

        // Emit the defining axiom: forall params. f(params) = body
        let defining_eq = self.eq_term(fn_application, body_term);
        let axiom_body = guard_with_requires(&mut self.solver, defining_eq);

        debug!(
            "  registering {}: forall {:?} . {} = body",
            smt_name,
            bound_vars
                .iter()
                .map(|v| format!("{v:?}"))
                .collect::<Vec<_>>(),
            smt_name
        );

        assert_axiom(&mut self.solver, axiom_body, &bound_vars, fn_application);

        // NOTE: The HKMS12 limited encoding (`f_lim`) was previously declared
        // here for recursive logic functions (#1305), following Heule, Kassios,
        // Mueller, Summers (VMCAI 2012). However, the `f_lim` functions were
        // never referenced in spec axioms, call encoding, or VCs — making them
        // dead code in the SMT encoding. trust-wp handles recursive functions via
        // direct ground evaluation (`assert_recursive_logic_fn_ground_instances`)
        // and one-step unfolding (`assert_recursive_fn_unfoldings`) instead,
        // which sidestep E-matching entirely. Removed in #2646.

        // Register the defining axiom with the ground-term pool for Phase 2
        // ground instantiation (#994). When ground calls to this function are
        // observed during encoding, the verification layer can re-encode the
        // body with concrete arguments to produce ground instances.
        if !bound_vars.is_empty() {
            use crate::encoder::ground_pool::{AxiomEntry, AxiomKind};

            self.ground_pool.register_axiom(AxiomEntry {
                fn_symbol: smt_name.clone(),
                params: logic_fn.params().to_vec(),
                body: logic_fn.body().clone(),
                requires: logic_fn.requires().to_vec(),
                func_decl: func_decl.clone(),
                return_sort: return_sort.clone(),
                kind: AxiomKind::Defining,
            });
        }

        // Emit spec axioms for ensures clauses (#1296).
        if !logic_fn.ensures().is_empty() {
            self.emit_spec_axioms(
                logic_fn,
                &func_decl,
                &smt_name,
                !skip_global_quantified_spec_axioms(logic_fn, &param_sorts, self),
            )?;
        }

        self.mark_logic_fn_axiom_asserted(smt_name);
        Ok(())
    }

    /// Emit spec axioms for a logic function's `#[ensures(...)]` clauses (#1296).
    ///
    /// Spec axioms make the postcondition available to callers, independently of
    /// whether the defining axiom (body) is visible.
    ///
    /// The axiom is ALWAYS guarded by the function's `requires` clauses: the
    /// `ensures` of a guarded logic fn is only proven UNDER its precondition,
    /// so the sound module-level fact is `∀p. requires(p) ⇒ ensures(p)`.
    /// Asserting the unguarded `∀p. ensures(p)` states a strictly stronger —
    /// generally FALSE — fact (e.g. filter_positive's
    /// `lemma_num_of_pos_increasing` with `requires(j <= k)` would yield the
    /// false axiom `∀i,j,k,t. num_of_pos(i,j,t) <= num_of_pos(i,k,t)`), and a
    /// false global axiom makes every obligation provable (false-accept).
    /// The defining-axiom path (`guard_with_requires`) and the ground pool
    /// (`AxiomEntry::requires`) already guard; this path must match them.
    ///
    /// For a function `fn foo(x: Int) -> Int` with `#[requires(x >= 0)]` and
    /// `#[ensures(result > x)]`:
    ///   `forall x. x >= 0 => foo(x) > x`  (with trigger on `foo(x)`)
    ///
    /// For a zero-param lemma `fn id_mono()` with `#[ensures(forall<i,j> ...)]`:
    ///   the ensures is asserted directly (no outer quantifier), still guarded
    ///   by any (closed) `requires`.
    ///
    /// If a `requires` clause fails to encode, the global spec axioms for this
    /// function are DROPPED (never asserted unguarded or under a partial
    /// guard): fewer axioms is sound, a weaker guard is not. Ground-pool
    /// registration is unaffected — ground instances re-encode and re-check
    /// the requires at each ground argument point.
    #[allow(clippy::too_many_lines)]
    fn emit_spec_axioms(
        &mut self,
        logic_fn: &LogicFnDef,
        func_decl: &FuncDecl,
        smt_name: &str,
        assert_global_axioms: bool,
    ) -> Result<(), EncodingError> {
        // Create bound variables for each parameter.
        // Use the FuncDecl's domain sorts (from declare_logic_fn_signature) which
        // incorporate both param_sorts hints AND infer_seq_like_params fallback.
        // Previously used resolve_logic_param_sort which only checks param_sorts,
        // causing Int sort for params detected as Seq via body inference. (#1572)
        let domain = func_decl.domain();
        let param_sorts: Vec<Sort> = logic_fn
            .params()
            .iter()
            .enumerate()
            .map(|(i, _)| {
                require_domain_sort(domain, i, &format!("emit_spec_axioms:{}", logic_fn.name()))
            })
            .collect::<Result<_, _>>()?;
        let mut bound_vars: Vec<Term> = Vec::new();
        let mut old_bindings: Vec<(String, Option<Term>)> = Vec::new();
        let mut old_sorts: Vec<(String, Option<Sort>)> =
            Vec::with_capacity(logic_fn.params().len() + 1);
        let mut logical_bindings: Vec<String> = Vec::with_capacity(logic_fn.params().len() + 1);

        for (param, param_sort) in logic_fn.params().iter().zip(param_sorts.iter()) {
            let qvar_id = self.next_quantifier_var_id();
            let bound_var = self
                .solver
                .fresh_var(&format!("spec_param_{param}_{qvar_id}"), param_sort.clone());
            bound_vars.push(bound_var);
            // Record Seq sort hints for is_seq_receiver dispatch (#1572)
            if is_seq_family_sort(param_sort) {
                self.record_sort_hint(param.clone(), ExprSort::Seq);
            }
            let old_sort = self.insert_var_sort(param.clone(), param_sort.clone());
            old_sorts.push((param.clone(), old_sort));
            let old = self.insert_var(param.clone(), bound_var);
            old_bindings.push((param.clone(), old));
            self.bind_quantifier_var(param.clone());
            logical_bindings.push(param.clone());
        }

        // Bind "result" to the function application f(params...).
        let fn_app_for_result =
            self.safe_apply("emit_spec_axioms/result_binding", func_decl, &bound_vars)?;
        let result_old = self.insert_var("result".to_string(), fn_app_for_result);
        old_bindings.push(("result".to_string(), result_old));
        let result_old_sort = self.insert_var_sort(
            "result".to_string(),
            self.solver.get_sort(fn_app_for_result),
        );
        old_sorts.push(("result".to_string(), result_old_sort));
        self.bind_quantifier_var("result".to_string());
        logical_bindings.push("result".to_string());

        // Increment quantifier_depth so that inner LogicFnCall applications
        // are NOT registered with the ground pool — their arguments are bound
        // variables, not ground terms. (#1965, Lane 5)
        //
        // Before encoding, filter out trivially-true ensures clauses (#2696).
        // A spec axiom like `forall a. a.0@ == a.0@` (from u2's ensures in
        // bug/206.rs) is vacuous but creates a quantifier ay-dpll cannot
        // decide, causing quantifier-unhandled. The postcondition path already
        // has `is_trivially_true_postcondition`; this applies the same check
        // to spec axioms.
        let non_trivial_ensures: Vec<(usize, &trust_wp_core::formula::PureExpr)> = logic_fn
            .ensures()
            .iter()
            .enumerate()
            .filter(|(_, ens)| !crate::verify::is_trivially_true_postcondition(ens))
            .collect();
        self.quantifier_state.inc_quantifier_depth();
        let spec_results: Vec<(usize, Result<Term, EncodingError>)> = non_trivial_ensures
            .iter()
            .map(|&(idx, ens)| (idx, self.encode_pure(ens)))
            .collect();
        // Encode the `requires` clauses under the SAME parameter bindings so
        // they can guard the asserted spec axioms below (see the method docs:
        // an unguarded ensures-axiom from a fn with a requires is unsound).
        let requires_results: Result<Vec<Term>, EncodingError> = logic_fn
            .requires()
            .iter()
            .map(|req| self.encode_pure(req))
            .collect();
        self.quantifier_state.dec_quantifier_depth();

        // Restore all bindings.
        for name in logical_bindings.iter().rev() {
            self.unbind_quantifier_var(name);
        }
        for (name, old_sort) in old_sorts {
            self.restore_var_sort(&name, old_sort);
        }
        for (name, old) in old_bindings {
            self.restore_var(&name, old);
        }

        // Fold the requires clauses into a single guard term. `None` means the
        // guard could not be encoded, in which case every global spec axiom
        // for this function is dropped (sound fallback — fewer facts). A
        // partial guard would be UNSOUND (weaker antecedent than proven), so
        // it is all-or-nothing.
        let requires_guard: Option<Option<Term>> = match requires_results {
            Ok(terms) => {
                let coerced: Vec<Term> = terms
                    .into_iter()
                    .map(|t| self.coerce_bool_operand(t))
                    .collect();
                Some(match coerced.as_slice() {
                    [] => None,
                    [single] => Some(*single),
                    [first, rest @ ..] => Some(
                        rest.iter()
                            .fold(*first, |acc, &req| self.solver.and(acc, req)),
                    ),
                })
            }
            Err(e) => {
                debug!(
                    "warning: requires guard for {smt_name} spec axioms failed to encode: {e} \
                     — dropping the global spec axioms (ground instances stay requires-guarded)"
                );
                None
            }
        };

        // Assert each successfully encoded ensures clause as a spec axiom.
        // Previously used `.flatten()` which silently dropped encoding errors,
        // meaning spec axioms could vanish without any diagnostic. Now we log
        // dropped errors so "Unknown" results can be traced to missing axioms.
        //
        // Track which ensures clauses encoded successfully for ground pool
        // registration below — only register clauses that the encoder can handle.
        let mut encoded_ensures_indices: Vec<usize> = Vec::new();
        for (i, spec_result) in spec_results.into_iter() {
            let spec_term = match spec_result {
                Ok(term) => term,
                Err(e) => {
                    unsoundness::increment(unsoundness::UnsoundnessCategory::SpecAxiomDropped);
                    debug!(
                        "warning: spec axiom {i} for {smt_name} failed to encode: {e} \
                         — callers will not have this postcondition available"
                    );
                    continue;
                }
            };
            encoded_ensures_indices.push(i);
            if Self::result_match_branch_instances_should_replace_raw(&logic_fn.ensures()[i]) {
                debug!("  spec axiom for {smt_name}: result-match branch instances only");
                continue;
            }
            if !assert_global_axioms {
                debug!("  spec axiom for {smt_name}: ground instances only");
                continue;
            }
            // Guard the axiom with the (encoded) requires clauses. When the
            // guard failed to encode, drop the global axiom entirely — never
            // assert an ensures wider than its proven precondition.
            let Some(requires_guard) = requires_guard else {
                unsoundness::increment(unsoundness::UnsoundnessCategory::SpecAxiomDropped);
                debug!("  spec axiom {i} for {smt_name}: dropped (unencodable requires guard)");
                continue;
            };
            let spec_term = match requires_guard {
                Some(guard) => {
                    let consequent = self.coerce_bool_operand(spec_term);
                    self.solver.implies(guard, consequent)
                }
                None => spec_term,
            };
            if bound_vars.is_empty() {
                // Lemma (no parameters): assert requires => ensures directly.

                debug!("  spec axiom for {smt_name}: assert ensures directly");

                self.assert_solver_term("spec_axiom/lemma", spec_term);
            } else {
                // Function with parameters: quantify over params with trigger on f(params).
                let fn_app_trigger =
                    self.safe_apply("emit_spec_axioms/trigger", func_decl, &bound_vars)?;

                debug!("  spec axiom for {smt_name}: forall params . requires => ensures");

                let spec_axiom =
                    self.solver
                        .forall_with_triggers(&bound_vars, spec_term, &[&[fn_app_trigger]]);
                self.assert_solver_term("spec_axiom/forall", spec_axiom);
            }
        }

        // Register successfully encoded spec axioms with the ground pool
        // (#1965, Lane 5). When ground calls to this function are observed
        // during encoding, the ground pool can re-encode the ensures clause
        // with concrete arguments + result binding to produce ground spec
        // instances. This compensates for ay-dpll's single-round E-matching
        // limitation on spec axiom triggers.
        if !bound_vars.is_empty() {
            use crate::encoder::ground_pool::{AxiomEntry, AxiomKind};

            let return_sort = func_decl.range().clone();
            for &idx in &encoded_ensures_indices {
                self.ground_pool.register_axiom(AxiomEntry {
                    fn_symbol: smt_name.to_string(),
                    params: logic_fn.params().to_vec(),
                    body: logic_fn.ensures()[idx].clone(),
                    requires: logic_fn.requires().to_vec(),
                    func_decl: func_decl.clone(),
                    return_sort: return_sort.clone(),
                    kind: AxiomKind::Spec,
                });
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use ay_dpll::api::{DatatypeConstructor, DatatypeSort, SolveResult, Term, TermKind};
    use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

    use super::*;
    use crate::tests::helpers::int;

    fn assertion_has_forall(encoder: &AYEncoder, assertion: Term) -> bool {
        let solver = encoder.solver();
        let mut stack = vec![assertion];
        let mut seen = std::collections::HashSet::new();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if matches!(solver.term_kind(term), TermKind::Forall) {
                return true;
            }
            stack.extend(solver.term_children(term));
        }
        false
    }

    fn has_forall_assertion(encoder: &AYEncoder) -> bool {
        encoder
            .solver()
            .assertions()
            .into_iter()
            .any(|assertion| assertion_has_forall(encoder, assertion))
    }

    fn list_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "List".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            }],
        }
    }

    fn datatype_logic_fn(name: &str, recursive: bool) -> LogicFnDef {
        let mut logic_fn = LogicFnDef::new(
            name.to_string(),
            format!("test::{name}"),
            vec!["self".to_string()],
            int(0),
        )
        .with_mode(LogicMode::Open)
        .with_param_sorts(vec![Some(ExprSort::Datatype(intern_sort_name("List")))]);
        logic_fn.set_is_recursive(recursive);
        logic_fn
    }

    fn result_nonnegative() -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), Some(ExprSort::Int))),
            BinOp::Ge,
            Arc::new(int(0)),
        )
    }

    fn guarded_spec_logic_fn() -> (LogicFnDef, PureExpr) {
        let require = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
            BinOp::Ge,
            Arc::new(int(0)),
        );
        let mut logic_fn = LogicFnDef::new_with_requires(
            "branch_fact".to_string(),
            "test::branch_fact".to_string(),
            vec!["x".to_string()],
            vec![require.clone()],
            PureExpr::Bool(true),
        )
        .with_opaque(true)
        .with_return_sort(Some(ExprSort::Bool))
        .with_param_sorts(vec![Some(ExprSort::Int)]);
        logic_fn.set_ensures(vec![PureExpr::Var(
            "result".to_string(),
            Some(ExprSort::Bool),
        )]);
        (logic_fn, require)
    }

    fn recursive_quantified_requires_spec_logic_fn() -> LogicFnDef {
        let require = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Bool(true)),
            triggers: vec![],
        };
        let mut logic_fn = LogicFnDef::new_with_requires(
            "pigeon_like".to_string(),
            "test::pigeon_like".to_string(),
            vec!["n".to_string()],
            vec![require],
            PureExpr::Bool(true),
        )
        .with_mode(LogicMode::Open)
        .with_return_sort(Some(ExprSort::Bool))
        .with_param_sorts(vec![Some(ExprSort::Int)]);
        logic_fn.set_is_recursive(true);
        logic_fn.set_ensures(vec![PureExpr::Var(
            "result".to_string(),
            Some(ExprSort::Bool),
        )]);
        logic_fn
    }

    fn bit_count_logic_fn() -> LogicFnDef {
        let val = PureExpr::Var("val".to_string(), Some(ExprSort::Int));
        let leading_zeros = PureExpr::MethodCall {
            receiver: Arc::new(val.clone()),
            method: "leading_zeros_logic".to_string(),
            args: vec![],
        };
        let body = PureExpr::BinOp(Arc::new(int(64)), BinOp::Sub, Arc::new(leading_zeros));
        LogicFnDef::new(
            "ffs_logic".to_string(),
            "test::ffs_logic".to_string(),
            vec!["val".to_string()],
            body,
        )
        .with_mode(LogicMode::Open)
        .with_param_sorts(vec![Some(ExprSort::Int)])
    }

    fn hashmap_list_good_bucket_logic_fn() -> LogicFnDef {
        let body = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::Bool(true)),
            triggers: vec![],
        };
        LogicFnDef::new(
            "good_bucket".to_string(),
            "test::good_bucket".to_string(),
            vec!["self".to_string(), "l".to_string(), "h".to_string()],
            body,
        )
        .with_mode(LogicMode::Open)
        .with_param_sorts(vec![
            Some(ExprSort::Int),
            Some(ExprSort::Int),
            Some(ExprSort::Int),
        ])
    }

    #[test]
    fn recursive_datatype_logic_fn_skips_global_defining_forall() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder.ensure_datatype_declared(&list_datatype());

        encoder
            .register_logic_fn(&datatype_logic_fn("list_len", true))
            .expect("register recursive datatype logic fn");

        assert!(
            !has_forall_assertion(&encoder),
            "recursive datatype logic functions should rely on bounded ground instances"
        );
        assert_eq!(
            encoder.ground_pool_axiom_count(),
            1,
            "recursive datatype defining body must remain available to the ground pool"
        );
    }

    #[test]
    fn recursive_datatype_logic_fn_keeps_global_spec_forall() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder.ensure_datatype_declared(&list_datatype());
        let mut logic_fn = datatype_logic_fn("list_nonneg", true);
        logic_fn.set_mode(LogicMode::Default);
        logic_fn.set_ensures(vec![result_nonnegative()]);

        encoder
            .register_logic_fn(&logic_fn)
            .expect("register recursive datatype logic fn spec");

        assert!(
            has_forall_assertion(&encoder),
            "recursive datatype specs should remain globally available"
        );
        assert_eq!(
            encoder.ground_pool_axiom_count(),
            1,
            "recursive datatype spec axiom must remain available to the ground pool"
        );
        assert!(
            matches!(
                encoder.ground_pool_for_test().axioms()[0].kind,
                crate::encoder::ground_pool::AxiomKind::Spec
            ),
            "ground-pool axiom should be the spec axiom"
        );
    }

    #[test]
    fn spec_axiom_ground_pool_preserves_requires() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let (logic_fn, require) = guarded_spec_logic_fn();

        encoder
            .register_logic_fn(&logic_fn)
            .expect("register guarded spec logic fn");

        assert_eq!(encoder.ground_pool_axiom_count(), 1);
        let axiom = &encoder.ground_pool_for_test().axioms()[0];
        assert_eq!(axiom.kind, crate::encoder::ground_pool::AxiomKind::Spec);
        assert_eq!(
            axiom.requires,
            vec![require],
            "spec ground instances must keep the callee requires as guards"
        );
    }

    #[test]
    fn recursive_quantified_requires_spec_is_ground_pool_only() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let logic_fn = recursive_quantified_requires_spec_logic_fn();

        encoder
            .register_logic_fn(&logic_fn)
            .expect("register recursive quantified-requires spec logic fn");

        assert!(
            !has_forall_assertion(&encoder),
            "recursive specs with quantified requires should not assert global forall specs"
        );
        assert!(
            encoder.ground_pool_for_test().axioms().iter().any(|axiom| {
                matches!(axiom.kind, crate::encoder::ground_pool::AxiomKind::Spec)
            }),
            "spec axiom must remain available to the ground pool"
        );
    }

    #[test]
    fn bit_count_logic_fn_skips_global_defining_forall() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        encoder
            .register_logic_fn(&bit_count_logic_fn())
            .expect("register bit-count logic fn");

        assert!(
            !has_forall_assertion(&encoder),
            "bit-count wrappers should rely on ground instances, not global forall"
        );
        assert_eq!(
            encoder.ground_pool_axiom_count(),
            1,
            "bit-count defining body must remain available to the ground pool"
        );
    }

    #[test]
    fn hashmap_list_good_bucket_skips_global_nested_forall() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        encoder
            .register_logic_fn(&hashmap_list_good_bucket_logic_fn())
            .expect("register hashmap-list good_bucket logic fn");

        assert!(
            !has_forall_assertion(&encoder),
            "hashmap-list good_bucket should use focused ground consequences, not a nested global forall"
        );
        assert_eq!(
            encoder.ground_pool_axiom_count(),
            1,
            "good_bucket defining body must remain available to the ground pool"
        );
    }

    #[test]
    fn non_recursive_datatype_match_logic_fn_uses_exact_ground_defining_axiom() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let datatype = list_datatype();
        encoder.ensure_datatype_declared(&datatype);

        encoder
            .register_logic_fn(&datatype_logic_fn("list_zero", false))
            .expect("register non-recursive datatype logic fn");

        assert!(
            !has_forall_assertion(&encoder),
            "datatype-match definitions avoid a global forall that makes SAT model validation incomplete"
        );
        assert_eq!(
            encoder.ground_pool_axiom_count(),
            1,
            "the skipped global definition must remain available for focused ground instantiation"
        );

        // Check that an observed application receives the exact focused
        // definition semantically instead of depending only on its storage
        // representation.
        let smt_name = trust_wp_core::logic::logic_fn_smt_name("list_zero");
        let declaration = encoder
            .logic_func_decl_cloned(&smt_name)
            .expect("registered logic function declaration");
        let nil = encoder
            .solver_mut()
            .datatype_constructor(&datatype, "Nil", &[]);
        let application = encoder.solver_mut().apply(&declaration, &[nil]);
        let zero = encoder.solver_mut().int_const(0);
        let defining_equality = encoder.solver_mut().eq(application, zero);
        let contradict_definition = encoder.solver_mut().not(defining_equality);
        encoder.solver_mut().assert_term(contradict_definition);

        assert!(
            matches!(
                encoder.solver_mut().check_sat().into_inner(),
                SolveResult::Unsat(_)
            ),
            "an observed datatype-match application must receive its exact ground definition"
        );
    }
}
