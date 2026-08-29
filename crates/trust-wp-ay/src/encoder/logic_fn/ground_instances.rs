// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr, PureExprDepthLimitedTraversalExt as _},
    logic::{LogicFnDef, LogicMode},
};

use crate::{
    encoder::{
        recursive_eval::{
            collect_concrete_logic_fn_calls, simplify_ground, try_evaluate_recursive_cached,
            EvalCache,
        },
        AYEncoder,
    },
    error::EncodingError,
};

impl AYEncoder {
    /// Assert ground instances of recursive logic function axioms (#1292).
    ///
    /// ay-dpll performs only one round of E-matching and has a gap in UF+LIA
    /// interaction — it cannot chain `id(0) = 0` with `id(1) = id(0) + 1` to
    /// deduce `id(1) = 1`. This method works around both limitations by:
    ///
    /// 1. Scanning goal expressions for concrete logic function calls
    /// 2. Fully evaluating the recursive function at the PureExpr level
    ///    (repeated substitution + constant folding until a literal value)
    /// 3. Asserting `f(concrete_args) = computed_value` as a direct
    ///    UF-to-constant equality that ay can handle without chaining
    ///
    /// Only processes recursive, non-opaque logic functions whose effective
    /// mode is Open. The effective mode comes from `mode_overrides` (which
    /// accounts for same-module scoping via `scope_logic_fn_modes`) when
    /// provided, otherwise from the function definition's `.mode` field.
    /// Evaluation is bounded by `max_depth` recursive calls to prevent
    /// non-termination.
    pub(crate) fn assert_recursive_logic_fn_ground_instances(
        &mut self,
        logic_fns: &[LogicFnDef],
        mode_overrides: Option<&[LogicMode]>,
        goal_exprs: &[&PureExpr],
        max_depth: usize,
    ) -> Result<(), EncodingError> {
        // Build lookup: name -> LogicFnDef for recursive functions whose
        // effective mode is Open. The effective mode comes from mode_overrides
        // (which accounts for same-module scoping) when available, otherwise
        // from the function definition. (#1292)
        let recursive_fns: HashMap<&str, &LogicFnDef> = logic_fns
            .iter()
            .enumerate()
            .filter(|(i, lf)| {
                let effective_mode = mode_overrides
                    .and_then(|m| m.get(*i).copied())
                    .unwrap_or(lf.mode());
                lf.is_recursive() && !lf.is_opaque() && effective_mode == LogicMode::Open
            })
            .map(|(_, lf)| (lf.name(), lf))
            .collect();

        if recursive_fns.is_empty() {
            return Ok(());
        }

        // Phase 1: Collect concrete call sites from goal expressions.
        let mut calls: Vec<(String, Vec<PureExpr>)> = Vec::new();
        for expr in goal_exprs {
            collect_concrete_logic_fn_calls(expr, &recursive_fns, &mut calls);
        }
        let mut eval_cache = EvalCache::new();

        // Phase 2: Apply equality constraints from goal_exprs to discover
        // additional ground calls. When requires contain `var == literal`
        // equalities (e.g., `i == 2`), substituting those equalities into
        // logic function calls like `fib(i)` produces `fib(2)` which is
        // ground-evaluable. Without this, calls with symbolic arguments
        // constrained by preconditions are missed entirely. (#1192)
        let eq_substitutions = extract_equality_constraints(goal_exprs);
        if !eq_substitutions.is_empty() {
            let substituted_exprs: Vec<PureExpr> = goal_exprs
                .iter()
                .map(|expr| simplify_ground(&expr.substitute(&eq_substitutions)))
                .collect();
            for expr in &substituted_exprs {
                collect_concrete_logic_fn_calls(expr, &recursive_fns, &mut calls);
            }

            let mut symbolic_calls: Vec<(PureExpr, PureExpr)> = Vec::new();
            for expr in goal_exprs {
                collect_substituted_logic_fn_calls(
                    expr,
                    &recursive_fns,
                    &eq_substitutions,
                    &mut symbolic_calls,
                );
            }

            let mut seen_guarded: HashSet<String> = HashSet::new();
            for (original_call, substituted_call) in symbolic_calls {
                let dedup_key = format!("{original_call:?} => {substituted_call:?}");
                if !seen_guarded.insert(dedup_key) {
                    continue;
                }
                if let Some(evaluated) = try_evaluate_recursive_cached(
                    &substituted_call,
                    &recursive_fns,
                    max_depth,
                    &mut eval_cache,
                ) {
                    let call_term = self.encode_pure(&original_call)?;
                    let value_term = self.encode_pure(&evaluated)?;
                    let equality = self.eq_term(call_term, value_term);
                    let Some(guard) = self.equality_substitution_guard(&eq_substitutions)? else {
                        continue;
                    };
                    let guarded_eq = self.solver.implies(guard, equality);
                    self.assert_solver_term("recursive_ground_eval/symbolic_guarded", guarded_eq);
                }
            }
        }

        // Dedup and process each call. Share one memoization cache across
        // all evaluations so overlapping sub-problems are computed once (#2021).
        let mut seen: HashSet<String> = HashSet::new();

        for (fn_name, concrete_args) in &calls {
            let dedup_key = format!(
                "{}({})",
                fn_name,
                concrete_args
                    .iter()
                    .map(|a| format!("{a:?}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            if seen.contains(&dedup_key) {
                continue;
            }
            seen.insert(dedup_key);

            if !recursive_fns.contains_key(fn_name.as_str()) {
                continue;
            }

            // Try to fully evaluate the function to a concrete value
            let call_expr = PureExpr::LogicFnCall {
                name: fn_name.clone(),
                args: concrete_args.clone(),
            };
            if let Some(evaluated) = try_evaluate_recursive_cached(
                &call_expr,
                &recursive_fns,
                max_depth,
                &mut eval_cache,
            ) {
                // Assert: fn(concrete_args) = evaluated_value
                let call_term = self.encode_pure(&call_expr)?;
                let value_term = self.encode_pure(&evaluated)?;

                let _return_sort = self
                    .logic_func_decl_cloned(&trust_wp_core::logic::logic_fn_smt_name(fn_name))
                    .map_or(Sort::Int, |fd| fd.range().clone());

                let ground_eq = self.eq_term(call_term, value_term);

                debug!(
                    "  recursive eval: {fn_name}({}) = {evaluated:?}",
                    concrete_args
                        .iter()
                        .map(|a| format!("{a:?}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                );

                self.assert_solver_term("recursive_ground_eval", ground_eq);
            }
        }

        // Phase 3: bounded single-pass 1-step unfold. For each recursive-fn
        // application appearing in the goal — INCLUDING symbolic-argument ones
        // that full evaluation above cannot reduce — assert its one-level
        // defining unfold `f(args) == simplify_ground(body[params := args])` as a
        // GROUND equality. This lets the solver relate e.g. num_of_pos(0,i+1,t) to
        // num_of_pos(0,i,t) and discharge monotonicity lemmas the bounded-ground
        // path otherwise misses. SOUND: trust-wp logic fns are total, so the
        // unfold holds unconditionally (no requires guard). TERMINATING: a ground
        // equality carries no trigger, and we collect ONLY goal-present terms in a
        // single pass — the f(smaller) terms it introduces are not re-collected,
        // so there is no unfolding cascade (a global step forall, by contrast,
        // diverges; empirically confirmed). (recursive lemma support)
        let mut all_calls: Vec<(String, Vec<PureExpr>)> = Vec::new();
        for expr in goal_exprs {
            collect_recursive_call_terms(expr, &recursive_fns, &mut all_calls);
        }
        let mut unfolded: HashSet<String> = HashSet::new();
        for (fn_name, args) in &all_calls {
            let Some(lf) = recursive_fns.get(fn_name.as_str()) else {
                continue;
            };
            if lf.params().len() != args.len() {
                continue;
            }
            let key = format!("{fn_name}({args:?})");
            if !unfolded.insert(key) {
                continue;
            }
            let mut subs: HashMap<String, PureExpr> = HashMap::new();
            for (param, arg) in lf.params().iter().zip(args.iter()) {
                subs.insert(param.clone(), arg.clone());
            }
            let unfolded_body = simplify_ground(&lf.body().substitute(&subs));
            let call_expr = PureExpr::LogicFnCall {
                name: fn_name.clone(),
                args: args.clone(),
            };
            // Skip degenerate self-equality (body simplified back to the call).
            if unfolded_body == call_expr {
                continue;
            }
            // SOUNDNESS: trust-wp's defining axiom is REQUIRES-guarded
            // (registration.rs `guard_with_requires`), so `f(args) == body[args]`
            // is only guaranteed where the fn's precondition holds. Build the
            // requires guard FIRST; if any precondition cannot be encoded, SKIP
            // this unfold rather than assert an unsound unguarded equality. An
            // unguarded unfold over-constrains `f` outside its domain and could
            // manufacture a spurious UNSAT (false-accept) for any recursive Open
            // fn carrying a `#[requires]` (e.g. `id` with `#[requires(i>=0)]`,
            // `set_max` with `#[requires(!s.is_empty())]`). Empty requires =>
            // guard is vacuously true, so num_of_pos and friends are unaffected.
            let mut req_terms: Vec<Term> = Vec::with_capacity(lf.requires().len());
            let mut req_ok = true;
            // tract19: `subs` maps logic-fn FORMALS to call arguments, so the
            // substitution erases the binder. A body/requires mentioning `^x`
            // now reads `Final(<argument>)`, and when the argument is a literal
            // the encoder can no longer tell it from the driver's substituted
            // value of a BORROWED PLACE (which must refuse fail-closed). Mark
            // the scope so Phase 1's formal-collapse rule still applies here.
            self.quantifier_state.inc_binder_substitution_depth();
            for req in lf.requires() {
                let req_sub = simplify_ground(&req.substitute(&subs));
                match self.encode_pure(&req_sub) {
                    Ok(t) => req_terms.push(t),
                    Err(_) => {
                        req_ok = false;
                        break;
                    }
                }
            }
            self.quantifier_state.dec_binder_substitution_depth();
            if !req_ok {
                continue;
            }
            let call_term = self.encode_pure(&call_expr)?;
            self.quantifier_state.inc_binder_substitution_depth();
            let body_term = self.encode_pure(&unfolded_body);
            self.quantifier_state.dec_binder_substitution_depth();
            let body_term = body_term?;
            let eq = self.eq_term(call_term, body_term);
            let guarded = if req_terms.is_empty() {
                eq
            } else {
                let mut conj = req_terms[0];
                for &r in &req_terms[1..] {
                    conj = self.solver.and(conj, r);
                }
                self.solver.implies(conj, eq)
            };
            self.assert_solver_term("recursive_one_step_unfold", guarded);
        }

        Ok(())
    }

    fn equality_substitution_guard(
        &mut self,
        substitutions: &HashMap<String, PureExpr>,
    ) -> Result<Option<Term>, EncodingError> {
        let mut guards = Vec::new();
        let mut names: Vec<&String> = substitutions.keys().collect();
        names.sort();
        for name in names {
            let Some(value) = substitutions.get(name) else {
                continue;
            };
            let var_term = self.encode_pure(&PureExpr::Var(name.clone(), None))?;
            let value_term = self.encode_pure(value)?;
            guards.push(self.eq_term(var_term, value_term));
        }

        Ok(guards
            .into_iter()
            .reduce(|acc, guard| self.solver.and(acc, guard)))
    }

    /// Goal-skolem-directed ground instantiation of guarded nested
    /// requires-quantifiers (the recursion IH). (#vcgen)
    ///
    /// A recursive logic function's inductive hypothesis reaches the solver tail
    /// as a precondition of the shape
    ///   `guard ==> (forall<o> P(o)) /\ ...`
    /// (e.g. `set_max`'s
    ///   `... ==> (forall o. sp.contains(o) ==> o <= set_max(sp))
    ///            /\ sp.contains(set_max(sp))`).
    /// ay-dpll's single-round E-matching does not instantiate that nested forall
    /// at the negated-goal Skolem, so the proof stalls (quantifier-unhandled).
    /// This asserts the entailed ground instance
    ///   `guard ==> P(o)[o := sk_v]`
    /// for each negated-goal Skolem `sk_v` — named `sk_<var>` by
    /// `skolemize_negated_universal` for every top-level universally quantified
    /// goal ensure — whose sort matches the forall binder.
    ///
    /// Soundness: the forall appears in POSITIVE polarity (a conjunct of an
    /// implication consequent, reached only through `==>` right-hand sides and
    /// top-level `/\`), so `guard ==> forall o. P(o)` entails
    /// `guard ==> P(sk_v)`. The instance is a logical consequence of the
    /// already-asserted precondition — never a strengthened assumption.
    ///
    /// Must be called AFTER the negated goal is asserted so the `sk_<var>`
    /// constant already exists in the encoder's variable table; the emitted
    /// instance reuses that exact constant.
    pub(crate) fn assert_goal_skolem_guarded_requires_forall_instances(
        &mut self,
        requires: &[PureExpr],
        goal_ensures: &[PureExpr],
    ) {
        // Collect (skolem_name, binder_sort) for every top-level universally
        // quantified goal ensure. These names match exactly the constants
        // `skolemize_negated_universal` introduces for the negated goal.
        let mut skolems: Vec<(String, Option<ExprSort>)> = Vec::new();
        for ensure in goal_ensures {
            let mut current = ensure;
            while let PureExpr::Forall {
                var,
                var_sort,
                body,
                ..
            } = current
            {
                let name = format!("sk_{var}");
                if !skolems.iter().any(|(n, _)| n == &name) {
                    skolems.push((name, var_sort.clone()));
                }
                current = body.as_ref();
            }
        }
        if skolems.is_empty() {
            return;
        }

        for req in requires {
            // Peel positive-polarity implication guards: g1 ==> g2 ==> ... ==> C.
            let mut guards: Vec<&PureExpr> = Vec::new();
            let mut consequent = req;
            while let PureExpr::BinOp(g, BinOp::Implies, c) = consequent {
                guards.push(g.as_ref());
                consequent = c.as_ref();
            }
            // Gather the positive-polarity foralls that are conjuncts of the
            // consequent (a top-level `/\` chain). Only these are safe to
            // instantiate: they occur in positive polarity, so replacing the
            // universal by one instance weakens the precondition, which is
            // entailed by it.
            let mut foralls: Vec<&PureExpr> = Vec::new();
            collect_conjunct_foralls(consequent, &mut foralls);
            for forall in foralls {
                let PureExpr::Forall {
                    var,
                    var_sort,
                    body,
                    ..
                } = forall
                else {
                    continue;
                };
                for (sk_name, sk_sort) in &skolems {
                    if !skolem_binder_sort_compatible(var_sort, sk_sort) {
                        continue;
                    }
                    let mut subs: HashMap<String, PureExpr> = HashMap::new();
                    subs.insert(
                        var.clone(),
                        PureExpr::Var(sk_name.clone(), var_sort.clone()),
                    );
                    let instance_body = body.substitute(&subs);
                    // Rebuild `g1 ==> ... ==> gk ==> instance_body`.
                    let mut clause = instance_body;
                    for guard in guards.iter().rev() {
                        clause = PureExpr::BinOp(
                            Arc::new((*guard).clone()),
                            BinOp::Implies,
                            Arc::new(clause),
                        );
                    }
                    // Encoding failure (an unregistered symbol, etc.) is
                    // non-fatal: the instance is an optimization, never required
                    // for soundness, so skip it rather than abort the solve.
                    if let Ok(term) = self.encode_formula(&clause) {
                        let term = self.coerce_bool_operand(term);
                        self.assert_solver_term("recursive_ground_eval/goal_skolem_ih", term);
                    }
                }
            }
        }
    }
}

/// Collect the positive-polarity foralls that are conjuncts of `expr` (walking
/// only through top-level `/\`). Used by
/// `assert_goal_skolem_guarded_requires_forall_instances` to find the recursion
/// IH's nested universal without descending into negative-polarity positions.
fn collect_conjunct_foralls<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    match expr {
        PureExpr::Forall { .. } => out.push(expr),
        PureExpr::BinOp(l, BinOp::And, r) => {
            collect_conjunct_foralls(l.as_ref(), out);
            collect_conjunct_foralls(r.as_ref(), out);
        }
        _ => {}
    }
}

/// Whether a forall binder sort is compatible with a candidate Skolem sort.
/// Missing sort information on either side is treated as compatible: the
/// instance stays sound regardless, and a sort mismatch at encode time is
/// caught by the non-fatal `encode_formula` fallback.
fn skolem_binder_sort_compatible(binder: &Option<ExprSort>, skolem: &Option<ExprSort>) -> bool {
    match (binder, skolem) {
        (Some(b), Some(s)) => b == s,
        _ => true,
    }
}

/// Extract `Var == Literal` equality constraints from a set of expressions.
///
/// Scans for top-level `BinOp(Var(name), Eq, Int/Bool)` or
/// `BinOp(Int/Bool, Eq, Var(name))` patterns. These represent precondition
/// equalities like `i == 2` that can be substituted into logic function
/// calls to produce ground-evaluable instances. (#1192)
/// Collect every recursive-fn application `(name, args)` appearing anywhere in
/// `expr` — regardless of whether the arguments are ground — for the bounded
/// 1-step unfold in `assert_recursive_logic_fn_ground_instances`. Unlike
/// `collect_concrete_logic_fn_calls` (which requires fully-ground args), this
/// surfaces symbolic-argument calls like `num_of_pos(0, i+1, t)`.
fn collect_recursive_call_terms(
    expr: &PureExpr,
    recursive_fns: &HashMap<&str, &LogicFnDef>,
    out: &mut Vec<(String, Vec<PureExpr>)>,
) {
    use trust_wp_core::formula::PureExprDepthLimitedTraversalExt as _;
    expr.for_each_recursive_with_depth_limit(crate::encoder::MAX_ENCODING_DEPTH, |node| {
        if let PureExpr::LogicFnCall { name, args } = node {
            if recursive_fns.contains_key(name.as_str()) {
                out.push((name.clone(), args.clone()));
            }
        }
    });
}

fn extract_equality_constraints(exprs: &[&PureExpr]) -> HashMap<String, PureExpr> {
    use trust_wp_core::formula::BinOp;

    let mut subs = HashMap::new();
    for expr in exprs {
        if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr {
            match (lhs.as_ref(), rhs.as_ref()) {
                (
                    PureExpr::Var(name, _),
                    PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_),
                ) => {
                    subs.insert(name.clone(), rhs.as_ref().clone());
                }
                (
                    PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_),
                    PureExpr::Var(name, _),
                ) => {
                    subs.insert(name.clone(), lhs.as_ref().clone());
                }
                _ => {}
            }
        }
    }
    subs
}

fn collect_substituted_logic_fn_calls(
    expr: &PureExpr,
    recursive_fns: &HashMap<&str, &LogicFnDef>,
    substitutions: &HashMap<String, PureExpr>,
    out: &mut Vec<(PureExpr, PureExpr)>,
) {
    expr.for_each_recursive_with_depth_limit(crate::encoder::MAX_ENCODING_DEPTH, |node| {
        let PureExpr::LogicFnCall { name, args } = node else {
            return;
        };
        if !recursive_fns.contains_key(name.as_str()) {
            return;
        }
        let substituted_args: Vec<PureExpr> = args
            .iter()
            .map(|arg| simplify_ground(&arg.substitute(substitutions)))
            .collect();
        let original_call = PureExpr::LogicFnCall {
            name: name.clone(),
            args: args.clone(),
        };
        let substituted_call = PureExpr::LogicFnCall {
            name: name.clone(),
            args: substituted_args,
        };
        if original_call != substituted_call {
            out.push((original_call, substituted_call));
        }
    });
}
