// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ground-pool axiom instantiation helpers.
//!
//! Extracted from `ground_pool.rs` as part of encoder decomposition (#1988).

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ay_dpll::api::{FuncDecl, Sort, Term, TermKind};
use trust_wp_core::formula::{BinOp, ExprSort, Pattern, PureExpr, UnOp};

use super::{AxiomEntry, AxiomKind};
use crate::{encoder::match_enc::datatype_constructor_matches, error::EncodingError};

/// Maximum ground instances to assert per axiom.
///
/// Reduced from 200 to 50 (#2674), then raised to 75, then reduced back
/// to 50: the axiom-free probe (Phase 1 of two-phase solving, #2116)
/// now handles simple obligations without axioms, so the ground pool
/// only fires for genuinely axiom-dependent proofs. Combined with
/// priority-sorted axiom ordering (#2674 Phase 2), 50 instances per
/// axiom provides sufficient coverage — the highest-priority axioms
/// (defining, low-arity) get their instances first, and the budget
/// is not wasted on high-arity spec axioms.
const TRUST_WP_CAP_PER_AXIOM: usize = 50;

/// Global budget for total ground instances asserted across all axioms.
///
/// Without a global cap, functions with many axioms (e.g., complex Seq/FMap
/// operations) can produce O(A * TRUST_WP_CAP_PER_AXIOM) instances, overwhelming the
/// solver even when each individual axiom respects its per-axiom cap. The
/// budget is shared across all axioms in priority order.
///
/// Reduced from 500 to 300 (#3313), then to 200 (#2674 Phase 2), then
/// raised back to 300 (#2676): the 200 budget was too aggressive for
/// functions with many user-defined spec axioms from mut-borrow
/// prophecy writebacks (e.g., inc_max_3 with swap chains). With axiom
/// priority scoring (defining > spec, fewer params > more params) and
/// the parameter complexity gate (skip axioms with >4 params), 300
/// instances covers both the typical case and moderately complex
/// mut-borrow verification while preserving the performance benefits
/// of the two-phase solve approach.
const TRUST_WP_TOTAL_INSTANCE_BUDGET: usize = 300;

/// Maximum bounded rounds for one ground-pool flush.
///
/// Re-encoding a defining axiom can expose another ground logic-function
/// application needed by a second axiom. PersistentArray protocol facts rely
/// on this path: `protocol(raw_perm_cell)` exposes `partial_invariant` over the
/// normalized `Snapshot::new(raw_perm_cell)` key. A single snapshot of the pool
/// drops that chained application when the flush is marked complete.
const TRUST_WP_MAX_GROUND_POOL_FLUSH_ROUNDS: usize = 3;

/// Absolute ceiling for standard-library cross-product ground instances.
///
/// These operate at SMT Term level (not PureExpr re-encoding) and can produce
/// cross-product assertions (e.g., push_back x concat, insert x contains,
/// mapping_cst x mapping_get). Unlike the old family-boundary-only budget,
/// this cap is threaded through Seq, FMap, FSet, and Mapping so a single
/// family cannot outrun the shared ceiling before control returns here.
///
/// Set to 500 for #2707: high enough to preserve the coverage needed by
/// mixed Seq/FMap/FSet/Mapping proofs, while preventing the FMap and Mapping
/// cross-products from generating thousands of ground assertions and OOMing
/// the solver.
pub(crate) const TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES: usize = 500;

/// Maximum number of formal parameters an axiom can have before ground
/// instantiation is skipped for that axiom. (#2674 Phase 2)
///
/// Axioms with many parameters (e.g., 5+ arg closure specs, multi-field
/// struct accessors) produce expensive re-encoding: each ground instance
/// requires N variable bindings, N sort lookups, and a full `encode_pure`
/// pass on the body. For high-arity axioms the quantified form with trigger
/// patterns is more efficient — ay-dpll's E-matching handles single-round
/// instantiation for the common case, and the ground pool budget is
/// preserved for lower-arity axioms where instantiation is cheaper.
const TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND: usize = 4;

/// Compute a priority score for an axiom for ground-pool ordering.
///
/// Lower score = higher priority (instantiated first within the global budget).
/// Criteria:
/// - Contract-critical axioms before non-critical (#1296)
/// - Defining axioms before Spec axioms (defining provides equalities that
///   enable further E-matching; spec axioms provide weaker ensures-only facts)
/// - Fewer parameters before more (cheaper instantiation, higher yield)
///
/// Returns a `(critical_rank, kind_rank, param_count)` tuple for use with
/// `sort_by_key`. Contract-critical axioms (referenced in ensures or requires)
/// get `critical_rank = 0`, non-critical get `critical_rank = 1`, ensuring
/// critical axioms are always instantiated first regardless of kind or arity.
fn axiom_priority_score(axiom: &AxiomEntry, is_postcondition_critical: bool) -> (u8, u8, usize) {
    let critical_rank = if is_postcondition_critical { 0 } else { 1 };
    let kind_rank = match axiom.kind {
        AxiomKind::Defining => 0,
        AxiomKind::Spec => 1,
    };
    (critical_rank, kind_rank, axiom.params.len())
}

/// A matched ground instance: (application term, argument terms, argument exprs, path conditions).
type GroundMatch = (Term, Vec<Term>, Vec<PureExpr>, Vec<Term>);

const MAX_MATCH_RESULT_UNIVERSAL_GROUND_TERMS: usize = 24;

fn is_hashmap_list_type_invariant_axiom(axiom: &AxiomEntry) -> bool {
    axiom.kind == AxiomKind::Defining
        && axiom.params.len() == 1
        && axiom.requires.is_empty()
        && axiom.fn_symbol.starts_with("method___trust_wp_invariant_")
        && hashmap_list_type_invariant_body_matches(&axiom.body, &axiom.params[0])
}

fn hashmap_list_type_invariant_body_matches(expr: &PureExpr, self_param: &str) -> bool {
    hashmap_list_invariant_body_has_len_positive(expr, self_param)
        && hashmap_list_invariant_body_has_bucket_predicates(expr, self_param)
}

fn hashmap_list_invariant_body_has_len_positive(expr: &PureExpr, self_param: &str) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        match node {
            PureExpr::BinOp(left, BinOp::Lt, right)
                if matches!(left.as_ref(), PureExpr::Int(0))
                    && seq_len_of_hashmap_buckets(right, self_param) =>
            {
                found = true;
            }
            PureExpr::BinOp(left, BinOp::Gt, right)
                if seq_len_of_hashmap_buckets(left, self_param)
                    && matches!(right.as_ref(), PureExpr::Int(0)) =>
            {
                found = true;
            }
            _ => {}
        }
    });
    found
}

fn hashmap_list_invariant_body_has_bucket_predicates(expr: &PureExpr, self_param: &str) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if found {
            return;
        }
        let PureExpr::Forall { var, body, .. } = node else {
            return;
        };
        if hashmap_list_invariant_forall_body_matches(body, self_param, var) {
            found = true;
        }
    });
    found
}

fn hashmap_list_invariant_forall_body_matches(
    body: &PureExpr,
    self_param: &str,
    index_var: &str,
) -> bool {
    let consequent = match body {
        PureExpr::BinOp(_, BinOp::Implies, consequent) => consequent.as_ref(),
        other => other,
    };
    let mut good_bucket: Option<&PureExpr> = None;
    let mut no_double: Option<&PureExpr> = None;
    for conjunct in flattened_conjuncts(consequent) {
        if good_bucket.is_none() {
            good_bucket = hashmap_list_good_bucket_bucket_arg(conjunct, self_param, index_var);
        }
        if no_double.is_none() {
            no_double = hashmap_list_no_double_binding_bucket_arg(conjunct);
        }
    }
    let (Some(good_bucket), Some(no_double)) = (good_bucket, no_double) else {
        return false;
    };
    expr_same(good_bucket, no_double)
        && hashmap_list_bucket_at_index_expr(good_bucket, self_param, index_var)
}

fn flattened_conjuncts(expr: &PureExpr) -> Vec<&PureExpr> {
    let mut out = Vec::new();
    fn visit<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
        if let PureExpr::BinOp(left, BinOp::And, right) = expr {
            visit(left, out);
            visit(right, out);
        } else {
            out.push(expr);
        }
    }
    visit(expr, &mut out);
    out
}

fn hashmap_list_good_bucket_bucket_arg<'a>(
    expr: &'a PureExpr,
    self_param: &str,
    index_var: &str,
) -> Option<&'a PureExpr> {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if normalize_logic_name(name).ends_with("goodbucket") && args.len() == 3 =>
        {
            (is_param_var(&args[0], self_param) && is_param_var(&args[2], index_var))
                .then_some(&args[1])
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if normalize_logic_name(method).ends_with("goodbucket") && args.len() == 2 => {
            (is_param_var(receiver, self_param) && is_param_var(&args[1], index_var))
                .then_some(&args[0])
        }
        _ => None,
    }
}

fn hashmap_list_no_double_binding_bucket_arg(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if normalize_logic_name(name).ends_with("nodoublebinding") && args.len() == 1 =>
        {
            Some(&args[0])
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if normalize_logic_name(method).ends_with("nodoublebinding") && args.is_empty() => {
            Some(receiver.as_ref())
        }
        _ => None,
    }
}

fn hashmap_list_bucket_at_index_expr(expr: &PureExpr, self_param: &str, index_var: &str) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if normalize_logic_name(name).contains("seqindexrestore") && args.len() == 2 =>
        {
            hashmap_list_buckets_of_self(&args[0], self_param) && is_param_var(&args[1], index_var)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if matches!(method.as_str(), "index" | "index_logic") && args.len() == 1 => {
            hashmap_list_buckets_of_self(receiver, self_param) && is_param_var(&args[0], index_var)
        }
        _ => false,
    }
}

fn seq_len_of_hashmap_buckets(expr: &PureExpr, self_param: &str) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if normalize_logic_name(name).ends_with("seqlen") && args.len() == 1 =>
        {
            hashmap_list_buckets_of_self(&args[0], self_param)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "len" && args.is_empty() => {
            hashmap_list_buckets_of_self(receiver, self_param)
        }
        _ => false,
    }
}

fn hashmap_list_buckets_of_self(expr: &PureExpr, self_param: &str) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if normalize_logic_name(name).ends_with("buckets") && args.len() == 1 =>
        {
            is_param_var(&args[0], self_param)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if normalize_logic_name(method).ends_with("buckets") && args.is_empty() => {
            is_param_var(receiver, self_param)
        }
        _ => false,
    }
}

fn is_param_var(expr: &PureExpr, expected: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == expected)
}

fn expr_same(left: &PureExpr, right: &PureExpr) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(left, right)
}

fn normalize_logic_name(name: &str) -> String {
    name.chars().filter(|ch| *ch != '_').collect()
}

fn pure_expr_contains_quantifier(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Forall { .. } | PureExpr::Exists { .. }))
}

fn ground_substitutions(
    params: &[String],
    arg_exprs: &[PureExpr],
) -> Option<HashMap<String, PureExpr>> {
    if params.len() != arg_exprs.len() {
        return None;
    }
    Some(
        params
            .iter()
            .cloned()
            .zip(arg_exprs.iter().cloned())
            .collect(),
    )
}

fn unknown_ground_requires(
    params: &[String],
    arg_exprs: &[PureExpr],
    requires: &[PureExpr],
) -> Option<Vec<PureExpr>> {
    let Some(substitutions) = ground_substitutions(params, arg_exprs) else {
        return Some(requires.to_vec());
    };
    let mut unknown = Vec::new();
    for require in requires {
        let substituted = require.substitute(&substitutions);
        match eval_ground_bool_expr(&substituted) {
            Some(true) => {}
            Some(false) => return None,
            None => unknown.push(require.clone()),
        }
    }
    Some(unknown)
}

fn ground_body_literal(
    params: &[String],
    arg_exprs: &[PureExpr],
    body: &PureExpr,
) -> Option<PureExpr> {
    let substitutions = ground_substitutions(params, arg_exprs)?;
    let substituted = body.substitute(&substitutions);
    let simplified = simplify_ground_expr(&substituted);
    match simplified {
        PureExpr::Int(_) | PureExpr::Bool(_) => Some(simplified),
        _ => None,
    }
}

fn simplify_ground_expr(expr: &PureExpr) -> PureExpr {
    if let Some(value) = eval_ground_int_expr(expr) {
        return PureExpr::Int(value);
    }
    if let Some(value) = eval_ground_bool_expr(expr) {
        return PureExpr::Bool(value);
    }
    match expr {
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(simplify_ground_expr(left)),
            *op,
            Arc::new(simplify_ground_expr(right)),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, Arc::new(simplify_ground_expr(inner))),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let cond = simplify_ground_expr(cond);
            match cond {
                PureExpr::Bool(true) => simplify_ground_expr(then_expr),
                PureExpr::Bool(false) => simplify_ground_expr(else_expr),
                _ => PureExpr::Ite(
                    Arc::new(cond),
                    Arc::new(simplify_ground_expr(then_expr)),
                    Arc::new(simplify_ground_expr(else_expr)),
                ),
            }
        }
        other => other.clone(),
    }
}

fn eval_ground_int_expr(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        PureExpr::UnOp(UnOp::Neg, inner) => eval_ground_int_expr(inner)?.checked_neg(),
        PureExpr::BinOp(left, op, right) => {
            let left = eval_ground_int_expr(left)?;
            let right = eval_ground_int_expr(right)?;
            match op {
                BinOp::Add => left.checked_add(right),
                BinOp::Sub => left.checked_sub(right),
                BinOp::Mul => left.checked_mul(right),
                BinOp::Div => left.checked_div(right),
                BinOp::Mod => left.checked_rem(right),
                BinOp::DivTrunc => left.checked_div(right),
                BinOp::RemTrunc => left.checked_rem(right),
                _ => None,
            }
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            if eval_ground_bool_expr(cond)? {
                eval_ground_int_expr(then_expr)
            } else {
                eval_ground_int_expr(else_expr)
            }
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            eval_ground_int_expr(inner)
        }
        _ => None,
    }
}

fn eval_ground_bool_expr(expr: &PureExpr) -> Option<bool> {
    match expr {
        PureExpr::Bool(value) => Some(*value),
        PureExpr::UnOp(UnOp::Not, inner) => Some(!eval_ground_bool_expr(inner)?),
        PureExpr::BinOp(left, op, right) => match op {
            BinOp::And => Some(eval_ground_bool_expr(left)? && eval_ground_bool_expr(right)?),
            BinOp::Or => Some(eval_ground_bool_expr(left)? || eval_ground_bool_expr(right)?),
            BinOp::Implies => Some(!eval_ground_bool_expr(left)? || eval_ground_bool_expr(right)?),
            BinOp::Eq => {
                if let (Some(left), Some(right)) =
                    (eval_ground_int_expr(left), eval_ground_int_expr(right))
                {
                    return Some(left == right);
                }
                Some(eval_ground_bool_expr(left)? == eval_ground_bool_expr(right)?)
            }
            BinOp::Ne => {
                if let (Some(left), Some(right)) =
                    (eval_ground_int_expr(left), eval_ground_int_expr(right))
                {
                    return Some(left != right);
                }
                Some(eval_ground_bool_expr(left)? != eval_ground_bool_expr(right)?)
            }
            BinOp::Lt => Some(eval_ground_int_expr(left)? < eval_ground_int_expr(right)?),
            BinOp::Le => Some(eval_ground_int_expr(left)? <= eval_ground_int_expr(right)?),
            BinOp::Gt => Some(eval_ground_int_expr(left)? > eval_ground_int_expr(right)?),
            BinOp::Ge => Some(eval_ground_int_expr(left)? >= eval_ground_int_expr(right)?),
            _ => None,
        },
        PureExpr::Ite(cond, then_expr, else_expr) => {
            if eval_ground_bool_expr(cond)? {
                eval_ground_bool_expr(then_expr)
            } else {
                eval_ground_bool_expr(else_expr)
            }
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            eval_ground_bool_expr(inner)
        }
        _ => None,
    }
}

fn ground_instance_arg_sort_compatible(actual: &Sort, expected: &Sort) -> bool {
    if actual == expected {
        return true;
    }

    // Int is the universal fallback from sort inference (`SortFallbackToInt`).
    // When the *actual* arg sort is Int and the *expected* param sort is a
    // structural sort (Seq/Datatype/Uninterpreted), the Int originated from
    // inference failure — allow the instantiation so the ground instance can
    // proceed. This prevents sort-fallback-to-Int from silently blocking
    // ground pool instantiation for structurally-sorted axioms.
    //
    // The reverse (expected=Int, actual=structural) is also allowed: the
    // axiom was declared with Int before stronger type evidence arrived.
    //
    // NOT allowed: Int vs Bool — Bool is never a fallback sort, so Int/Bool
    // mismatch indicates a genuine sort conflict, not an inference failure. (#2699)
    fn is_structural_sort(sort: &Sort) -> bool {
        matches!(
            sort,
            Sort::Seq(_) | Sort::Datatype(_) | Sort::Uninterpreted(_)
        )
    }
    if *actual == Sort::Int && is_structural_sort(expected) {
        return true;
    }
    if *expected == Sort::Int && is_structural_sort(actual) {
        return true;
    }

    // Use `same_structural_family` for comprehensive cross-sort-type
    // family matching. This covers all combinations of Datatype, Uninterpreted,
    // and Seq sorts in the same family. (#2699)
    if super::super::sort_context::same_structural_family(actual, expected).is_some() {
        return true;
    }

    match (actual, expected) {
        (Sort::Datatype(actual_dt), Sort::Datatype(expected_dt)) => {
            actual_dt.name == expected_dt.name
        }
        (Sort::Uninterpreted(actual_name), Sort::Datatype(expected_dt))
        | (Sort::Datatype(expected_dt), Sort::Uninterpreted(actual_name)) => {
            *actual_name == expected_dt.name
        }
        // Seq vs Seq-family: native Sort::Seq(Int) matches Uninterpreted or
        // Datatype sorts in the Seq family (Vec, VecDeque, etc.). The
        // canonical encoding sort is Seq post-#2080; the Uninterpreted/Datatype
        // comes from struct layout extraction or pre-normalization paths. (#2699)
        (Sort::Seq(_), Sort::Uninterpreted(name)) | (Sort::Uninterpreted(name), Sort::Seq(_)) => {
            super::super::sort_context::sort_coercion::normalize_structural_sort_family(name)
                == "Seq"
        }
        (Sort::Seq(_), Sort::Datatype(dt)) | (Sort::Datatype(dt), Sort::Seq(_)) => {
            super::super::sort_context::sort_coercion::normalize_structural_sort_family(&dt.name)
                == "Seq"
        }
        // Uninterpreted vs Uninterpreted in the same structural family:
        // e.g., Uninterpreted("Option") vs Uninterpreted("OptionInt"). (#2699)
        (Sort::Uninterpreted(a_name), Sort::Uninterpreted(b_name)) => {
            let a_family =
                super::super::sort_context::sort_coercion::normalize_structural_sort_family(a_name);
            let b_family =
                super::super::sort_context::sort_coercion::normalize_structural_sort_family(b_name);
            a_family == b_family
        }
        _ => false,
    }
}

fn forall_var_accepts_int_grounding(var_sort: Option<&ExprSort>) -> bool {
    matches!(var_sort, None | Some(ExprSort::Int))
}

impl super::super::AYEncoder {
    pub(crate) fn encode_bound_result_match_branch_instances(
        &mut self,
        body: &PureExpr,
        result_term: Term,
    ) -> Result<Vec<Term>, EncodingError> {
        let old_result = self.insert_var("result".to_string(), result_term);
        let old_result_sort =
            self.insert_var_sort("result".to_string(), self.solver.get_sort(result_term));
        self.bind_quantifier_var("result".to_string());

        let result = self.encode_spec_match_result_branch_instances(body, result_term);

        self.unbind_quantifier_var("result");
        self.restore_var_sort("result", old_result_sort);
        self.restore_var("result", old_result);

        result
    }

    fn conjoin_ground_terms(&mut self, terms: &[Term]) -> Option<Term> {
        let (first, rest) = terms.split_first()?;
        Some(
            rest.iter()
                .fold(*first, |acc, &term| self.solver.and(acc, term)),
        )
    }

    fn guarded_ground_instance(&mut self, guards: &[Term], instance: Term) -> Term {
        match self.conjoin_ground_terms(guards) {
            Some(guard) => self.solver.implies(guard, instance),
            None => instance,
        }
    }

    fn encode_spec_match_result_branch_instances(
        &mut self,
        body: &PureExpr,
        fn_app: Term,
    ) -> Result<Vec<Term>, EncodingError> {
        let PureExpr::Match { scrutinee, arms } = body else {
            return Ok(Vec::new());
        };
        if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
            return Ok(Vec::new());
        }

        let mut branch_instances = Vec::with_capacity(arms.len());
        let mut prior_patterns_failed = None;
        for arm in arms {
            let condition = self.encode_pattern_condition_impl(fn_app, &arm.pattern, None, None)?;
            let active_condition = match prior_patterns_failed {
                Some(prior) => self.solver.and(prior, condition),
                None => condition,
            };
            if Self::ground_result_pattern_bindings_supported(&arm.pattern) {
                if !matches!(arm.body, PureExpr::Forall { .. }) {
                    let arm_body =
                        self.encode_ground_result_match_arm_body(fn_app, &arm.pattern, &arm.body)?;
                    branch_instances.push(self.solver.implies(active_condition, arm_body));
                }
                for universal_instance in self.encode_ground_result_match_arm_universal_instances(
                    fn_app,
                    &arm.pattern,
                    &arm.body,
                )? {
                    branch_instances
                        .push(self.solver.implies(active_condition, universal_instance));
                }
            }

            let not_condition = self.solver.not(condition);
            prior_patterns_failed = Some(match prior_patterns_failed {
                Some(prior) => self.solver.and(prior, not_condition),
                None => not_condition,
            });
        }

        Ok(branch_instances)
    }

    pub(crate) fn result_match_branch_instances_should_replace_raw(body: &PureExpr) -> bool {
        let PureExpr::Match { scrutinee, arms } = body else {
            return false;
        };
        if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
            return false;
        }
        arms.iter()
            .all(|arm| Self::ground_result_pattern_bindings_supported(&arm.pattern))
            && arms
                .iter()
                .any(|arm| matches!(arm.body, PureExpr::Forall { .. }))
    }

    fn encode_ground_result_match_arm_universal_instances(
        &mut self,
        scrutinee: Term,
        pattern: &Pattern,
        body: &PureExpr,
    ) -> Result<Vec<Term>, EncodingError> {
        let PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        } = body
        else {
            return Ok(Vec::new());
        };
        if !forall_var_accepts_int_grounding(var_sort.as_ref()) {
            return Ok(Vec::new());
        }

        let candidates = self.ground_int_candidate_terms();
        if candidates.is_empty() {
            return Ok(Vec::new());
        }
        let pattern_bindings = self.ground_result_pattern_bindings(scrutinee, pattern)?;
        let mut instances = Vec::with_capacity(candidates.len());

        for candidate in candidates {
            let mut old_bindings = Vec::with_capacity(pattern_bindings.len() + 1);
            let mut old_sorts = Vec::with_capacity(pattern_bindings.len() + 1);
            let mut logical_bindings = Vec::with_capacity(pattern_bindings.len() + 1);
            for (name, term, sort) in &pattern_bindings {
                let old_term = self.insert_var(name.clone(), *term);
                let old_sort = self.insert_var_sort(name.clone(), sort.clone());
                old_bindings.push((name.clone(), old_term));
                old_sorts.push((name.clone(), old_sort));
                self.bind_quantifier_var(name.clone());
                logical_bindings.push(name.clone());
            }

            let old_term = self.insert_var(var.clone(), candidate);
            let old_sort = self.insert_var_sort(var.clone(), Sort::Int);
            old_bindings.push((var.clone(), old_term));
            old_sorts.push((var.clone(), old_sort));
            self.bind_quantifier_var(var.clone());
            logical_bindings.push(var.clone());

            let encoded = self.encode_pure(body);

            for name in logical_bindings.iter().rev() {
                self.unbind_quantifier_var(name);
            }
            for (name, old_sort) in old_sorts.into_iter().rev() {
                self.restore_var_sort(&name, old_sort);
            }
            for (name, old_binding) in old_bindings.into_iter().rev() {
                self.restore_var(&name, old_binding);
            }

            instances.push(encoded?);
        }

        Ok(instances)
    }

    fn ground_int_candidate_terms(&self) -> Vec<Term> {
        let mut seen = HashSet::new();
        let mut terms = Vec::new();

        for assertion in self.solver.assertions() {
            self.collect_int_candidate_terms(assertion, true, &mut seen, &mut terms);
            if terms.len() >= MAX_MATCH_RESULT_UNIVERSAL_GROUND_TERMS {
                return terms;
            }
        }

        for entry in self.ground_pool.by_symbol.values().flatten() {
            for term in std::iter::once(&entry.application)
                .chain(entry.arg_terms.iter())
                .chain(entry.path_conditions.iter())
            {
                if self.is_ground_int_candidate_term(*term) && seen.insert(*term) {
                    terms.push(*term);
                    if terms.len() >= MAX_MATCH_RESULT_UNIVERSAL_GROUND_TERMS {
                        return terms;
                    }
                }
            }
        }

        for assertion in self.solver.assertions() {
            self.collect_int_candidate_terms(assertion, false, &mut seen, &mut terms);
            if terms.len() >= MAX_MATCH_RESULT_UNIVERSAL_GROUND_TERMS {
                return terms;
            }
        }

        terms
    }

    fn collect_int_candidate_terms(
        &self,
        term: Term,
        vars_only: bool,
        seen: &mut HashSet<Term>,
        out: &mut Vec<Term>,
    ) {
        if out.len() >= MAX_MATCH_RESULT_UNIVERSAL_GROUND_TERMS {
            return;
        }

        let is_var = match self.solver.term_kind(term) {
            TermKind::Forall | TermKind::Exists => return,
            TermKind::Var { .. } => true,
            _ => false,
        };
        if (!vars_only || is_var) && self.is_ground_int_candidate_term(term) && seen.insert(term) {
            out.push(term);
            if out.len() >= MAX_MATCH_RESULT_UNIVERSAL_GROUND_TERMS {
                return;
            }
        }

        for child in self.solver.term_children(term) {
            self.collect_int_candidate_terms(child, vars_only, seen, out);
            if out.len() >= MAX_MATCH_RESULT_UNIVERSAL_GROUND_TERMS {
                return;
            }
        }
    }

    fn is_ground_int_candidate_term(&self, term: Term) -> bool {
        self.solver.get_sort(term) == Sort::Int && !self.term_contains_quantifier_var(term)
    }

    fn ground_result_pattern_bindings_supported(pattern: &Pattern) -> bool {
        match pattern {
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Binding(_) => true,
            Pattern::Alias { pattern, .. } => {
                Self::ground_result_pattern_bindings_supported(pattern)
            }
            Pattern::Constructor { inner, .. } => inner
                .as_deref()
                .is_none_or(Self::ground_result_pattern_bindings_supported),
            Pattern::Tuple(elements) => elements
                .iter()
                .all(Self::ground_result_pattern_bindings_supported),
            #[allow(unreachable_patterns)]
            _ => pattern.bound_names().is_empty(),
        }
    }

    fn encode_ground_result_match_arm_body(
        &mut self,
        scrutinee: Term,
        pattern: &Pattern,
        body: &PureExpr,
    ) -> Result<Term, EncodingError> {
        let bindings = self.ground_result_pattern_bindings(scrutinee, pattern)?;
        if bindings.is_empty() {
            return self.encode_pure(body);
        }

        let mut old_bindings = Vec::with_capacity(bindings.len());
        for (name, term, sort) in &bindings {
            let old_term = self.insert_var(name.clone(), *term);
            let old_sort = self.insert_var_sort(name.clone(), sort.clone());
            old_bindings.push((name.clone(), old_term, old_sort));
            // Binder-scoped view collapse: mark arm binders so wrapper/view
            // encodings (`a@`, `old(a)`) resolve to the bound payload term
            // instead of a shared global `{name}_view` constant (#1635 analog;
            // mirrors `encode_match_arm_body`).
            self.bind_quantifier_var(name.clone());
        }

        let body_result = self.encode_pure(body);

        for (name, old_term, old_sort) in old_bindings.into_iter().rev() {
            self.unbind_quantifier_var(&name);
            self.restore_var_sort(&name, old_sort);
            self.restore_var(&name, old_term);
        }

        body_result
    }

    fn ground_result_pattern_bindings(
        &mut self,
        scrutinee: Term,
        pattern: &Pattern,
    ) -> Result<Vec<(String, Term, Sort)>, EncodingError> {
        let scrutinee_sort = self.solver.get_sort(scrutinee);
        self.pattern_bindings(scrutinee, pattern, None, Some(&scrutinee_sort), None)
    }

    fn option_some_tester_for_ground_term(&mut self, term: Term) -> Result<Term, EncodingError> {
        if let Ok(tester) = self.solver.try_datatype_tester("Some", term) {
            return Ok(tester);
        }

        let term_sort = self.solver.get_sort(term);
        let tester = self.get_or_declare_constructor_tester_for_sort("is_some", &term_sort);
        self.safe_apply(
            "ground_pool/hashmap_list_good_bucket::is_some",
            &tester,
            &[term],
        )
    }

    fn option_some_value_sort(sort: &Sort) -> Option<Sort> {
        let Sort::Datatype(datatype) = sort else {
            return None;
        };
        datatype
            .constructors
            .iter()
            .find(|ctor| ctor.name == "Some" && ctor.fields.len() == 1)
            .map(|ctor| ctor.fields[0].sort.clone())
    }

    fn hashmap_list_pair_sort(sort: &Sort) -> bool {
        match sort {
            Sort::Int => true,
            Sort::Uninterpreted(name) => name.contains("Tuple") || name.contains("tuple"),
            Sort::Datatype(datatype) => {
                datatype.name.contains("Tuple")
                    || datatype.name.contains("tuple")
                    || datatype.constructors.iter().any(|ctor| {
                        ctor.fields.len() == 2
                            && (ctor.name.contains("Tuple") || ctor.name.contains("tuple"))
                    })
            }
            _ => false,
        }
    }

    fn hashmap_list_list_sort(sort: &Sort) -> bool {
        match sort {
            Sort::Uninterpreted(name) => name.contains("List"),
            Sort::Datatype(datatype) => {
                datatype.name.contains("List")
                    || datatype
                        .constructors
                        .iter()
                        .any(|ctor| ctor.name == "Cons" || ctor.name == "Nil")
            }
            _ => false,
        }
    }

    fn hashmap_list_cons_selector_fields(
        &self,
        list_sort: &Sort,
    ) -> Option<((String, Sort), (String, Sort))> {
        let datatype = match list_sort {
            Sort::Datatype(datatype) => Some(datatype.clone()),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
            _ => None,
        }?;
        let constructor = datatype
            .constructors
            .iter()
            .find(|ctor| datatype_constructor_matches(&datatype, &ctor.name, "Cons"))?;
        let [head, tail] = constructor.fields.as_slice() else {
            return None;
        };
        Some((
            (head.name.clone(), head.sort.clone()),
            (tail.name.clone(), tail.sort.clone()),
        ))
    }

    fn app_term_children_named(&self, term: Term, expected: &str) -> Option<Vec<Term>> {
        let TermKind::App { name, .. } = self.solver.term_kind(term) else {
            return None;
        };
        if name == expected || name == format!("logic_{expected}") {
            Some(self.solver.term_children(term))
        } else {
            None
        }
    }

    fn assert_hashmap_list_get_cons_head_ground_instance(
        &mut self,
        get_decl: &FuncDecl,
        get_app: Term,
        arg_terms: &[Term],
    ) -> Result<usize, EncodingError> {
        let [list_term, key_term] = arg_terms else {
            return Ok(0);
        };
        let list_sort = self.solver.get_sort(*list_term);
        if !Self::hashmap_list_list_sort(&list_sort) {
            return Ok(0);
        }
        let mut guards = Vec::new();
        let (head_tuple, tail_term) = if let Some(cons_args) =
            self.app_term_children_named(*list_term, "Cons")
        {
            let [head_tuple, tail] = cons_args.as_slice() else {
                return Ok(0);
            };
            (*head_tuple, *tail)
        } else if let Some(((head_name, head_sort), (tail_name, tail_sort))) =
            self.hashmap_list_cons_selector_fields(&list_sort)
        {
            let head_tuple = self
                .solver
                .try_datatype_selector(&head_name, *list_term, head_sort)
                .map_err(|err| {
                    EncodingError::solver_error(format!(
                        "ground_pool/hashmap_list_get_cons_head::{head_name}: {err}"
                    ))
                })?;
            let tail_term = self
                .solver
                .try_datatype_selector(&tail_name, *list_term, tail_sort)
                .map_err(|err| {
                    EncodingError::solver_error(format!(
                        "ground_pool/hashmap_list_get_cons_head::{tail_name}: {err}"
                    ))
                })?;
            let is_cons = if let Ok(tester) = self.solver.try_datatype_tester("Cons", *list_term) {
                tester
            } else {
                let tester = self.solver.declare_fun(
                    "is-Cons",
                    std::slice::from_ref(&list_sort),
                    Sort::Bool,
                );
                self.safe_apply(
                    "ground_pool/hashmap_list_get_cons_head::is-Cons",
                    &tester,
                    &[*list_term],
                )?
            };
            guards.push(is_cons);
            (head_tuple, tail_term)
        } else {
            let tuple_sort = Sort::Uninterpreted("Tuple2".to_string());
            let cons_head = self.get_or_declare_logic_func(
                "hashmap_list_cons_0",
                std::slice::from_ref(&list_sort),
                tuple_sort,
            );
            let head_tuple = self.safe_apply(
                "ground_pool/hashmap_list_get_cons_head::hashmap_list_cons_0",
                &cons_head,
                &[*list_term],
            )?;
            let cons_tail = self.get_or_declare_logic_func(
                "hashmap_list_cons_1",
                std::slice::from_ref(&list_sort),
                list_sort.clone(),
            );
            let tail_term = self.safe_apply(
                "ground_pool/hashmap_list_get_cons_head::hashmap_list_cons_1",
                &cons_tail,
                &[*list_term],
            )?;
            let is_cons = if let Ok(tester) = self.solver.try_datatype_tester("Cons", *list_term) {
                tester
            } else {
                let tester = self.solver.declare_fun(
                    "is-Cons",
                    std::slice::from_ref(&list_sort),
                    Sort::Bool,
                );
                self.safe_apply(
                    "ground_pool/hashmap_list_get_cons_head::is-Cons",
                    &tester,
                    &[*list_term],
                )?
            };
            guards.push(is_cons);
            (head_tuple, tail_term)
        };
        if !Self::hashmap_list_pair_sort(&self.solver.get_sort(head_tuple)) {
            return Ok(0);
        }
        let get_sort = self.solver.get_sort(get_app);
        let value_sort = Self::option_some_value_sort(&get_sort).unwrap_or(Sort::Int);
        if self.solver.get_sort(*key_term) != Sort::Int {
            return Ok(0);
        }

        let tuple_sort = self.solver.get_sort(head_tuple);
        let tuple_get_0 = if tuple_sort == Sort::Int {
            self.get_or_declare_spec_fn("__trust_wp_tuple_get_0", &[Sort::Int], Sort::Int)
        } else {
            self.get_or_declare_logic_func(
                "logic_____trust_wp__tuple__get__0__placeholder_u5475706c6532__ret_i",
                &[tuple_sort.clone()],
                Sort::Int,
            )
        };
        let tuple_get_1 = if tuple_sort == Sort::Int {
            self.get_or_declare_spec_fn("__trust_wp_tuple_get_1", &[Sort::Int], value_sort.clone())
        } else {
            self.get_or_declare_logic_func(
                "logic_____trust_wp__tuple__get__1__placeholder_u5475706c6532__ret_i",
                &[tuple_sort],
                value_sort.clone(),
            )
        };
        let head_key = self.safe_apply(
            "ground_pool/hashmap_list_get_cons_head::tuple_get_0",
            &tuple_get_0,
            &[head_tuple],
        )?;
        let head_value = self.safe_apply(
            "ground_pool/hashmap_list_get_cons_head::tuple_get_1",
            &tuple_get_1,
            &[head_tuple],
        )?;

        let some_value = if let Sort::Datatype(datatype) = get_sort.clone() {
            self.solver
                .try_datatype_constructor(&datatype, "Some", &[head_value])
                .map_err(|err| {
                    EncodingError::solver_error(format!(
                        "ground_pool/hashmap_list_get_cons_head::Some: {err}"
                    ))
                })?
        } else {
            let head_value_sort = self.solver.get_sort(head_value);
            let some_decl = self
                .solver
                .declare_fun("Some", &[head_value_sort], get_sort.clone());
            self.safe_apply(
                "ground_pool/hashmap_list_get_cons_head::Some",
                &some_decl,
                &[head_value],
            )?
        };
        let conclusion = self.eq_term(get_app, some_value);

        let deep_model_decl =
            self.get_or_declare_spec_fn("method_deep_model_1_i", &[Sort::Int], Sort::Int);
        let head_key_deep_model = self.safe_apply(
            "ground_pool/hashmap_list_get_cons_head::deep_model",
            &deep_model_decl,
            &[head_key],
        )?;
        let direct_key_match = self.eq_term(*key_term, head_key);
        let deep_key_match = self.eq_term(*key_term, head_key_deep_model);
        let head_match = self.solver.or(direct_key_match, deep_key_match);
        let mut head_guards = guards.clone();
        head_guards.push(head_match);
        if let Some(guard) = self.conjoin_ground_terms(&head_guards) {
            let implication = self.solver.implies(guard, conclusion);
            self.assert_solver_term("ground_pool/hashmap_list_get_cons_head", implication);
        }

        let tail_sort = self.solver.get_sort(tail_term);
        if Self::hashmap_list_list_sort(&tail_sort) {
            // Reuse the defining axiom's registered handle. Re-declaring from
            // term-store sorts is not identity-preserving: AY canonicalizes a
            // datatype range such as `OptionInt` to its uninterpreted carrier,
            // while the native declaration retains `Sort::Datatype`. AY
            // correctly rejects that second surface-name declaration.
            let expected_domain = [tail_sort, Sort::Int];
            if get_decl.domain().len() != expected_domain.len()
                || !get_decl
                    .domain()
                    .iter()
                    .zip(&expected_domain)
                    .all(|(declared, expected)| {
                        ground_instance_arg_sort_compatible(
                            &declared.as_term_sort(),
                            &expected.as_term_sort(),
                        )
                    })
            {
                return Ok(1);
            }
            let tail_get_app = self.safe_apply(
                "ground_pool/hashmap_list_get_cons_tail::logic_get",
                get_decl,
                &[tail_term, *key_term],
            )?;
            let tail_conclusion = self.eq_term(get_app, tail_get_app);
            let direct_key_mismatch = self.eq_term(*key_term, head_key);
            let deep_key_mismatch = self.eq_term(*key_term, head_key_deep_model);
            let not_direct_key_match = self.solver.not(direct_key_mismatch);
            let not_deep_key_match = self.solver.not(deep_key_mismatch);
            let mut tail_guards = guards;
            tail_guards.push(not_direct_key_match);
            tail_guards.push(not_deep_key_match);
            if let Some(guard) = self.conjoin_ground_terms(&tail_guards) {
                let implication = self.solver.implies(guard, tail_conclusion);
                self.assert_solver_term("ground_pool/hashmap_list_get_cons_tail", implication);
                self.ground_pool
                    .register_term_application_with_path_conditions(
                        "logic_get",
                        tail_get_app,
                        vec![tail_term, *key_term],
                        tail_guards,
                    );
            }
        }

        Ok(2)
    }

    /// Hashmap-list's `good_bucket(self, l, h)` definition expands to a
    /// `forall k v` body. Re-encoding that full body as a ground equality
    /// leaves nested quantifiers in otherwise ground obligations and dominates
    /// the focused hashmap-list replays. Instead, assert the ground consequence
    /// needed by the fixture for already-observed `logic_get(l, k)` calls:
    ///
    /// `good_bucket(self, l, h) && is-Some(logic_get(l, k)) => bucket_ix(self, k) == h`.
    fn assert_hashmap_list_good_bucket_ground_instances(
        &mut self,
        good_app: Term,
        arg_terms: &[Term],
        path_conditions: &[Term],
    ) -> Result<usize, EncodingError> {
        let [map_term, list_term, bucket_ix_term] = arg_terms else {
            return Ok(0);
        };
        let get_entries = self
            .ground_pool
            .entries_for("logic_get")
            .map(<[_]>::to_vec)
            .unwrap_or_default();
        if get_entries.is_empty() {
            return Ok(0);
        }

        let map_sort = self.solver.get_sort(*map_term);
        let bucket_ix_decl =
            self.get_or_declare_logic_func("logic_bucket__ix", &[map_sort, Sort::Int], Sort::Int);

        let mut count = 0;
        for get_entry in get_entries {
            if self.ground_entry_contains_quantifier_var(
                get_entry.application,
                &get_entry.arg_terms,
                &get_entry.path_conditions,
            ) {
                continue;
            }
            let [get_list_term, key_term] = get_entry.arg_terms.as_slice() else {
                continue;
            };
            if *get_list_term != *list_term || self.solver.get_sort(*key_term) != Sort::Int {
                continue;
            }

            let bucket_ix_app = self.safe_apply(
                "ground_pool/hashmap_list_good_bucket::bucket_ix",
                &bucket_ix_decl,
                &[*map_term, *key_term],
            )?;
            let conclusion = self.eq_term(bucket_ix_app, *bucket_ix_term);
            let is_some = self.option_some_tester_for_ground_term(get_entry.application)?;

            let mut guards =
                Vec::with_capacity(path_conditions.len() + get_entry.path_conditions.len() + 2);
            guards.extend_from_slice(path_conditions);
            guards.extend_from_slice(&get_entry.path_conditions);
            guards.push(good_app);
            guards.push(is_some);
            let Some(guard) = self.conjoin_ground_terms(&guards) else {
                continue;
            };

            let implication = self.solver.implies(guard, conclusion);
            self.assert_solver_term("ground_pool/hashmap_list_good_bucket", implication);
            count += 1;
        }

        Ok(count)
    }

    fn assert_hashmap_list_invariant_ground_instances(
        &mut self,
        inv_app: Term,
        arg_terms: &[Term],
        path_conditions: &[Term],
        assert_len_positive: bool,
    ) -> Result<usize, EncodingError> {
        let [map_term] = arg_terms else {
            return Ok(0);
        };
        let map_sort = self.solver.get_sort(*map_term);
        let seq_sort = self.get_seq_sort();
        let buckets_decl =
            self.get_or_declare_logic_func("myhashmap_buckets", &[map_sort.clone()], seq_sort);
        let buckets = self.safe_apply(
            "ground_pool/hashmap_list_invariant::myhashmap_buckets",
            &buckets_decl,
            &[*map_term],
        )?;
        let buckets_sort = self.solver.get_sort(buckets);
        let buckets_len = self.seq_len_term(buckets)?;
        let zero = self.solver.int_const(0);

        let mut count = 0;
        if assert_len_positive {
            let len_positive = self.solver.lt(zero, buckets_len);
            let mut guards = Vec::with_capacity(path_conditions.len() + 1);
            guards.extend_from_slice(path_conditions);
            guards.push(inv_app);
            if let Some(guard) = self.conjoin_ground_terms(&guards) {
                let fact = self.solver.implies(guard, len_positive);
                self.assert_solver_term("ground_pool/hashmap_list_invariant::len", fact);
                count += 1;
            }
        }

        let mut bucket_candidates: Vec<(Term, Term, Sort, Vec<Term>)> = Vec::new();
        for index_entry in self
            .ground_pool
            .entries_for("__seq_index_restore_List")
            .map(<[_]>::to_vec)
            .unwrap_or_default()
        {
            if self.ground_entry_contains_quantifier_var(
                index_entry.application,
                &index_entry.arg_terms,
                &index_entry.path_conditions,
            ) {
                continue;
            }
            let [entry_buckets, bucket_ix] = index_entry.arg_terms.as_slice() else {
                continue;
            };
            if *entry_buckets != buckets || self.solver.get_sort(*bucket_ix) != Sort::Int {
                continue;
            }
            let indexed_bucket = index_entry.application;
            let list_sort = self.solver.get_sort(indexed_bucket);
            bucket_candidates.push((
                *bucket_ix,
                indexed_bucket,
                list_sort,
                index_entry.path_conditions,
            ));
        }

        for good_entry in self
            .ground_pool
            .entries_for("logic_good__bucket")
            .map(<[_]>::to_vec)
            .unwrap_or_default()
        {
            if self.ground_entry_contains_quantifier_var(
                good_entry.application,
                &good_entry.arg_terms,
                &good_entry.path_conditions,
            ) {
                continue;
            }
            let [entry_map, list_term, bucket_ix] = good_entry.arg_terms.as_slice() else {
                continue;
            };
            if *entry_map != *map_term || self.solver.get_sort(*bucket_ix) != Sort::Int {
                continue;
            }

            let list_sort = self.solver.get_sort(*list_term);
            let index_decl = self.get_or_declare_logic_func(
                "__seq_index_restore_List",
                &[buckets_sort.clone(), Sort::Int],
                list_sort.clone(),
            );
            let indexed_bucket = self.safe_apply(
                "ground_pool/hashmap_list_invariant::__seq_index_restore_List",
                &index_decl,
                &[buckets, *bucket_ix],
            )?;
            if bucket_candidates
                .iter()
                .any(|(seen_ix, seen_bucket, _, _)| {
                    *seen_ix == *bucket_ix && *seen_bucket == indexed_bucket
                })
            {
                continue;
            }
            bucket_candidates.push((
                *bucket_ix,
                indexed_bucket,
                list_sort,
                good_entry.path_conditions,
            ));
        }

        for (bucket_ix, indexed_bucket, list_sort, candidate_path_conditions) in bucket_candidates {
            let inbounds_lower = self.solver.le(zero, bucket_ix);
            let inbounds_upper = self.solver.lt(bucket_ix, buckets_len);

            let good_decl = self.get_or_declare_logic_func(
                "logic_good__bucket",
                &[map_sort.clone(), list_sort.clone(), Sort::Int],
                Sort::Bool,
            );
            let good_app = self.safe_apply(
                "ground_pool/hashmap_list_invariant::good_bucket",
                &good_decl,
                &[*map_term, indexed_bucket, bucket_ix],
            )?;

            let no_double_decl = self.get_or_declare_logic_func(
                "logic_no__double__binding",
                &[list_sort],
                Sort::Bool,
            );
            let no_double_app = self.safe_apply(
                "ground_pool/hashmap_list_invariant::no_double_binding",
                &no_double_decl,
                &[indexed_bucket],
            )?;

            let mut guards =
                Vec::with_capacity(path_conditions.len() + candidate_path_conditions.len() + 3);
            guards.extend_from_slice(path_conditions);
            guards.extend_from_slice(&candidate_path_conditions);
            guards.push(inv_app);
            guards.push(inbounds_lower);
            guards.push(inbounds_upper);
            let Some(guard) = self.conjoin_ground_terms(&guards) else {
                continue;
            };

            for conclusion in [good_app, no_double_app] {
                let fact = self.solver.implies(guard, conclusion);
                self.assert_solver_term("ground_pool/hashmap_list_invariant", fact);
                count += 1;
            }
            self.ground_pool
                .register_term_application_with_path_conditions(
                    "logic_good__bucket",
                    good_app,
                    vec![*map_term, indexed_bucket, bucket_ix],
                    guards,
                );
        }

        Ok(count)
    }

    fn term_contains_quantifier_var(&self, term: Term) -> bool {
        match self.solver.term_kind(term) {
            TermKind::Var { name } => {
                name.starts_with("qvar_")
                    || name.starts_with("logic_param_")
                    || name.starts_with("spec_param_")
            }
            _ => self
                .solver
                .term_children(term)
                .into_iter()
                .any(|child| self.term_contains_quantifier_var(child)),
        }
    }

    fn ground_terms_contain_quantifier_var(&self, terms: &[Term]) -> bool {
        terms
            .iter()
            .any(|term| self.term_contains_quantifier_var(*term))
    }

    fn ground_entry_contains_quantifier_var(
        &self,
        application: Term,
        arg_terms: &[Term],
        path_conditions: &[Term],
    ) -> bool {
        self.term_contains_quantifier_var(application)
            || self.ground_terms_contain_quantifier_var(arg_terms)
            || self.ground_terms_contain_quantifier_var(path_conditions)
    }

    /// Register a term-only ground application in the pool, guarded by
    /// `quantifier_depth == 0`. Convenience wrapper used by Seq/FMap/FSet
    /// encoding paths. (#2288)
    pub(crate) fn register_standard_ground_application(
        &mut self,
        symbol: &str,
        application: Term,
        arg_terms: Vec<Term>,
    ) {
        if self.quantifier_state.quantifier_depth() == 0 {
            self.ground_pool
                .register_term_application_with_path_conditions(
                    symbol,
                    application,
                    arg_terms,
                    self.active_path_conditions_cloned(),
                );
        }
    }

    /// Assert ground instances of registered axioms using collected ground terms.
    ///
    /// For each registered axiom `forall params. requires => f(params) = body`,
    /// this finds matching ground entries for `f` and re-encodes the body with
    /// concrete arguments to produce ground instances. This compensates for
    /// ay-dpll's single-round E-matching limitation.
    ///
    /// Called from the verification layer before `check_sat()`.
    ///
    /// Idempotent: if the pool hasn't changed since the last flush, this is a
    /// no-op returning `Ok(0)`.
    #[allow(clippy::too_many_lines)] // Cohesive instantiation loop with index-management bookkeeping
    pub(crate) fn assert_ground_pool_instances(&mut self) -> Result<usize, EncodingError> {
        // Idempotency: skip if no new entries or axioms since last flush.
        if !self.ground_pool.needs_flush() {
            return Ok(0);
        }

        let relevance_filter = self.ground_pool.relevance_symbols.clone();
        let effective_budget = self
            .ground_pool
            .per_slice_budget()
            .unwrap_or(TRUST_WP_TOTAL_INSTANCE_BUDGET);

        let mut count = 0;
        let mut instantiated_apps: Vec<(usize, Term)> = Vec::new();

        for _round in 0..TRUST_WP_MAX_GROUND_POOL_FLUSH_ROUNDS {
            // Collect axiom + ground entry pairs to instantiate. The boolean
            // flag tracks whether the axiom is contract-critical (#1296).
            // We clone the needed data out of the pool to avoid borrowing
            // `self` during re-encoding (which needs `&mut self`).
            let mut work: Vec<(usize, AxiomEntry, Vec<GroundMatch>, bool)> = Vec::new();

            for (axiom_index, axiom) in self.ground_pool.axioms.iter().enumerate() {
                // Check if this axiom's function symbol appears in a contract
                // (ensures or requires). Contract-critical axioms bypass the
                // parameter complexity gate because their ground instances are
                // essential for proving the postcondition or establishing
                // precondition facts. Without the exemption, a logic function
                // with 5+ parameters referenced in `#[ensures(...)]` or
                // `#[requires(...)]` would have its ground instances dropped,
                // causing solver Unknown results. (#1296)
                let is_hashmap_list_invariant = is_hashmap_list_type_invariant_axiom(axiom);
                let is_postcondition_critical =
                    self.ground_pool.is_postcondition_symbol(&axiom.fn_symbol);

                // Parameter complexity gate (#2674 Phase 2): skip axioms with
                // too many formal parameters. High-arity axioms (e.g., 5-arg
                // closure specs) produce expensive re-encoding and consume
                // budget that is better spent on low-arity defining axioms. The
                // quantified form with triggers handles these via E-matching.
                //
                // Exemption (#1296): contract-critical axioms bypass this gate
                // because their ground instances are required to prove the goal.
                if axiom.params.len() > TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND
                    && !is_postcondition_critical
                {
                    tracing::debug!(
                        symbol = %axiom.fn_symbol,
                        params = axiom.params.len(),
                        max = TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND,
                        "ground_pool: skipping high-arity axiom (#2674)"
                    );
                    continue;
                }
                if let Some(ref relevant) = relevance_filter {
                    if !is_postcondition_critical
                        && !is_hashmap_list_invariant
                        && !relevant.contains(&axiom.fn_symbol)
                    {
                        tracing::debug!(
                            symbol = %axiom.fn_symbol,
                            "ground_pool: skipping irrelevant axiom (#2674)"
                        );
                        continue;
                    }
                }
                let Some(entries) = self.ground_pool.by_symbol.get(&axiom.fn_symbol) else {
                    continue;
                };
                let matching: Vec<GroundMatch> = entries
                    .iter()
                    .filter(|entry| {
                        entry.arg_exprs.len() == axiom.params.len()
                            || (entry.arg_exprs.is_empty()
                                && entry.arg_terms.len() == axiom.params.len())
                    })
                    .filter(|entry| {
                        !self.ground_entry_contains_quantifier_var(
                            entry.application,
                            &entry.arg_terms,
                            &entry.path_conditions,
                        )
                    })
                    .filter(|entry| {
                        !instantiated_apps.iter().any(|(done_axiom, done_app)| {
                            *done_axiom == axiom_index && *done_app == entry.application
                        })
                    })
                    .take(TRUST_WP_CAP_PER_AXIOM)
                    .map(|entry| {
                        (
                            entry.application,
                            entry.arg_terms.clone(),
                            entry.arg_exprs.clone(),
                            entry.path_conditions.clone(),
                        )
                    })
                    .collect();
                if !matching.is_empty() {
                    work.push((
                        axiom_index,
                        AxiomEntry {
                            fn_symbol: axiom.fn_symbol.clone(),
                            params: axiom.params.clone(),
                            body: axiom.body.clone(),
                            requires: axiom.requires.clone(),
                            func_decl: axiom.func_decl.clone(),
                            return_sort: axiom.return_sort.clone(),
                            kind: axiom.kind.clone(),
                        },
                        matching,
                        is_postcondition_critical,
                    ));
                }
            }

            if work.is_empty() {
                break;
            }

            // Priority-sort axioms so the global budget is spent on the
            // highest-value instances first: contract-critical axioms first
            // (#1296), then defining axioms (equalities) before spec axioms
            // (ensures), and lower-arity before higher-arity. (#2674 Phase 2)
            work.sort_by_key(|(_, axiom, _, is_critical)| {
                axiom_priority_score(axiom, *is_critical)
            });

            for (axiom_index, axiom, entries, is_critical) in &work {
                // Enforce global budget: stop asserting instances once the
                // total budget is exhausted, even if individual axioms have
                // room. (#2674) Contract-critical axioms bypass the budget gate
                // (#1296): they are essential for proving the goal and must
                // always get their ground instances regardless of budget
                // pressure.
                if count >= effective_budget && !is_critical {
                    tracing::debug!(
                        budget = effective_budget,
                        "ground_pool: total instance budget exhausted (#2674)"
                    );
                    break;
                }
                let domain = axiom.func_decl.domain();
                for (application, arg_terms, arg_exprs, path_conditions) in entries {
                    if count >= effective_budget && !is_critical {
                        break;
                    }
                    if domain.len() != arg_terms.len() {
                        return Err(EncodingError::solver_error(format!(
                            "ground_pool::{}::fn_app arity mismatch: domain has {} sorts but {} argument(s) were registered",
                            axiom.fn_symbol,
                            domain.len(),
                            arg_terms.len()
                        )));
                    }

                    // Same-name datatype carriers can drift across encoder
                    // paths (#2189). In that case the call site already
                    // encoded a valid application term under a collision
                    // declaration; reuse that term instead of re-applying the
                    // axiom declaration.
                    let compatible_sorts_match =
                        arg_terms.iter().zip(domain).all(|(&arg, expected)| {
                            ground_instance_arg_sort_compatible(
                                &self.solver.get_sort(arg),
                                &expected.as_term_sort(),
                            )
                        });
                    if !compatible_sorts_match {
                        tracing::debug!(
                            symbol = %axiom.fn_symbol,
                            expected = ?domain,
                            actual = ?arg_terms.iter().map(|t| self.solver.get_sort(*t)).collect::<Vec<_>>(),
                            "ground_pool: skipping incompatible instance (#2567)"
                        );
                        continue;
                    }
                    let fn_app = *application;

                    if is_hashmap_list_type_invariant_axiom(axiom) {
                        let asserted = self.assert_hashmap_list_invariant_ground_instances(
                            fn_app,
                            arg_terms,
                            path_conditions,
                            hashmap_list_invariant_body_has_len_positive(
                                &axiom.body,
                                &axiom.params[0],
                            ),
                        )?;
                        instantiated_apps.push((*axiom_index, *application));
                        count += asserted;
                        continue;
                    }

                    if axiom.kind == AxiomKind::Defining
                        && axiom.fn_symbol == "logic_good__bucket"
                        && axiom.params.len() == 3
                        && axiom.requires.is_empty()
                    {
                        let asserted = self.assert_hashmap_list_good_bucket_ground_instances(
                            fn_app,
                            arg_terms,
                            path_conditions,
                        )?;
                        instantiated_apps.push((*axiom_index, *application));
                        count += asserted;
                        continue;
                    }

                    if axiom.kind == AxiomKind::Defining
                        && axiom.fn_symbol == "logic_get"
                        && axiom.params.len() == 2
                        && axiom.requires.is_empty()
                    {
                        let asserted = self.assert_hashmap_list_get_cons_head_ground_instance(
                            &axiom.func_decl,
                            fn_app,
                            arg_terms,
                        )?;
                        if asserted > 0 {
                            instantiated_apps.push((*axiom_index, *application));
                            count += asserted;
                            continue;
                        }
                    }

                    let replace_raw_match_body = axiom.kind == AxiomKind::Spec
                        && Self::result_match_branch_instances_should_replace_raw(&axiom.body);
                    if axiom.kind == AxiomKind::Spec
                        && axiom.requires.iter().any(pure_expr_contains_quantifier)
                    {
                        continue;
                    }
                    let Some(unknown_requires) =
                        unknown_ground_requires(&axiom.params, arg_exprs, &axiom.requires)
                    else {
                        instantiated_apps.push((*axiom_index, *application));
                        continue;
                    };
                    if axiom.kind == AxiomKind::Defining
                        && !axiom.requires.is_empty()
                        && !unknown_requires.is_empty()
                    {
                        continue;
                    }
                    if axiom.kind == AxiomKind::Spec
                        && unknown_requires.iter().any(pure_expr_contains_quantifier)
                    {
                        continue;
                    }
                    if axiom.kind == AxiomKind::Spec
                        && !Self::result_match_branch_instances_should_replace_raw(&axiom.body)
                        && pure_expr_contains_quantifier(&axiom.body)
                    {
                        continue;
                    }

                    // Bind parameters to ground SMT terms
                    let mut old_bindings: Vec<(String, Option<Term>)> = Vec::new();
                    let mut old_sorts: Vec<(String, Option<Sort>)> = Vec::new();
                    let mut logical_bindings: Vec<String> = Vec::with_capacity(
                        axiom.params.len() + usize::from(axiom.kind == AxiomKind::Spec),
                    );
                    for (param, &term) in axiom.params.iter().zip(arg_terms.iter()) {
                        let old = self.insert_var(param.clone(), term);
                        old_bindings.push((param.clone(), old));
                        let old_sort =
                            self.insert_var_sort(param.clone(), self.solver.get_sort(term));
                        old_sorts.push((param.clone(), old_sort));
                        // Ground instantiation re-encodes the axiom body under
                        // the original formal parameter names. Treat those
                        // names as bound logical values so View/Deref/Old
                        // collapse to the concrete ground argument instead of
                        // synthesizing a fresh `{param}_view` placeholder.
                        // (#1635)
                        self.bind_quantifier_var(param.clone());
                        logical_bindings.push(param.clone());
                    }

                    // For spec axioms, also bind "result" to f(ground_args)
                    // so ensures clauses referencing `result` resolve
                    // correctly.
                    if axiom.kind == AxiomKind::Spec {
                        let old = self.insert_var("result".to_string(), fn_app);
                        old_bindings.push(("result".to_string(), old));
                        let old_sort = self
                            .insert_var_sort("result".to_string(), self.solver.get_sort(fn_app));
                        old_sorts.push(("result".to_string(), old_sort));
                        self.bind_quantifier_var("result".to_string());
                        logical_bindings.push("result".to_string());
                    }

                    // Re-encode body and requires with ground bindings. Literal
                    // simplification keeps concrete cases like `max(5, 3)` out
                    // of ay's AUFLIA E-matching hot path on the latest ay pin.
                    let body_literal = ground_body_literal(&axiom.params, arg_exprs, &axiom.body);
                    let body_result = if replace_raw_match_body {
                        Ok(self.solver.bool_const(true))
                    } else if let Some(body) = body_literal.as_ref() {
                        self.encode_pure(body)
                    } else {
                        self.encode_pure(&axiom.body)
                    };
                    let requires_results: Result<Vec<Term>, EncodingError> = unknown_requires
                        .iter()
                        .map(|requires| self.encode_pure(requires))
                        .collect();
                    let branch_results = if axiom.kind == AxiomKind::Spec {
                        self.encode_spec_match_result_branch_instances(&axiom.body, fn_app)
                    } else {
                        Ok(Vec::new())
                    };

                    // Restore all bindings (always, even on error)
                    for name in logical_bindings.iter().rev() {
                        self.unbind_quantifier_var(name);
                    }
                    for (name, old_sort) in old_sorts {
                        self.restore_var_sort(&name, old_sort);
                    }
                    for (name, old_binding) in old_bindings {
                        self.restore_var(&name, old_binding);
                    }

                    // Propagate encoding errors
                    let body_term = body_result?;
                    let requires_terms = requires_results?;
                    let branch_instances = branch_results?;

                    // Build the ground instance based on axiom kind
                    let instance = match axiom.kind {
                        AxiomKind::Defining
                            if axiom.return_sort == Sort::Bool
                                && pure_expr_contains_quantifier(&axiom.body)
                                && !*is_critical =>
                        {
                            self.solver.implies(fn_app, body_term)
                        }
                        AxiomKind::Defining => {
                            // Defining: f(ground_args) = body_encoded
                            self.eq_term(fn_app, body_term)
                        }
                        AxiomKind::Spec => {
                            // Spec: ensures[params:=ground_args,
                            // result:=f(ground_args)]. The body IS the ensures
                            // clause, already re-encoded with ground bindings
                            // (including result -> f(ground_args)).
                            body_term
                        }
                    };

                    // Guard with requires if present
                    let mut guards = path_conditions.clone();
                    guards.extend(requires_terms.iter().copied());
                    let guarded = self.guarded_ground_instance(&guards, instance);

                    self.assert_solver_term("ground_pool/instantiate", guarded);
                    for branch_instance in branch_instances {
                        let guarded_branch = self.guarded_ground_instance(&guards, branch_instance);
                        self.assert_solver_term(
                            "ground_pool/instantiate_match_result_arm",
                            guarded_branch,
                        );
                    }
                    instantiated_apps.push((*axiom_index, *application));
                    count += 1;
                }
            }
        }

        self.ground_pool.mark_flushed();
        Ok(count)
    }

    /// Assert ground instances of standard-library axioms (Seq/FMap/FSet) using
    /// term-only ground applications collected during encoding. (#2288, Phase 3)
    ///
    /// Unlike `assert_ground_pool_instances` (which re-encodes PureExpr bodies),
    /// this pass operates entirely at SMT Term level: it looks up declared UF
    /// symbols, finds matching ground entries, and directly asserts concrete
    /// axiom instances.
    ///
    /// Called from `assert_standard_axioms()` after the quantified axioms are
    /// asserted.
    ///
    /// Uses a shared cross-product budget (#2707): each axiom family receives
    /// the remaining budget, so a single Seq/FMap/FSet/Mapping cross-product
    /// cannot exceed the global cap before the next family runs.
    pub(crate) fn assert_standard_ground_instances(&mut self) -> usize {
        let mut count = 0;
        let mut remaining = TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES;

        // Seq instances are asserted first (highest priority for iterator/
        // collection proofs). FMap, FSet, and Mapping follow in decreasing
        // priority order.
        count += self.assert_seq_ground_instances(remaining);
        remaining = TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES.saturating_sub(count);
        if remaining == 0 {
            tracing::debug!(
                count,
                budget = TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                "standard ground instances: global cross-product budget exhausted after Seq (#2707)"
            );
            return count;
        }

        count += self.assert_fmap_ground_instances(remaining);
        remaining = TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES.saturating_sub(count);
        if remaining == 0 {
            tracing::debug!(
                count,
                budget = TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                "standard ground instances: global cross-product budget exhausted after FMap (#2707)"
            );
            return count;
        }

        count += self.assert_fset_ground_instances(remaining);
        remaining = TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES.saturating_sub(count);
        if remaining == 0 {
            tracing::debug!(
                count,
                budget = TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                "standard ground instances: global cross-product budget exhausted after FSet (#2707)"
            );
            return count;
        }

        count += self.assert_mapping_ground_instances(remaining);
        if count >= TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES {
            tracing::debug!(
                count,
                budget = TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
                "standard ground instances: global cross-product budget exhausted after Mapping (#2707)"
            );
        }
        count
    }
}
